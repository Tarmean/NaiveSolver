{-# OPTIONS_GHC -Wno-orphans -Wno-name-shadowing #-}
{-# LANGUAGE DerivingVia, DerivingStrategies, UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Boilerplate to lift propagation from values to propagation from pairs, and to translate between different type-classes which mean the same thing
-- Most of this code should move to OverEasy, and the rest should be removed by unifying the type-classes
module Boilerplate where
import Types
import Overeasy.EGraph
import Overeasy.Diff
import Overeasy.EquivFind
import Overeasy.Assoc (assocPartialLookupByKey)
import GHC.Generics ((:+:)(..), Generic)
import GHC.Stack (HasCallStack)
import qualified IntLike.Map as ILM
import Data.Bifunctor(second)
import qualified IntLike.Set as ILS
import Control.Monad.State hiding (StateT, modify', execStateT, runStateT, evalStateT)
import Control.Monad.Trans.State.Strict (execStateT)
import Control.Applicative (Alternative)

import Prettyprinter
import Data.Hashable

import Range
import FiniteDomains

import qualified Data.BitVector as BV


-- Code which should live in OverEasy

instance (Diff (a,b) (c,d), DiffApply a c, DiffApply b d) => DiffApply (a,b) (c,d) where
    applyDiff (a,b) (c,d) = (,) <$> applyDiff a c <*>  applyDiff b d
instance (Lattice (c,d), Diff a c, Diff b d) => Diff (a,b) (c,d) where
    diff (a,b) (c,d) = (diff a c, diff b d)
instance (Lattice a, Lattice b) => Lattice (a,b) where
    lintersect (la, lb ) (ra, rb) = case (lintersect la ra , lintersect lb rb) of
        (Just a, Just b) -> Just $ (,) a b
        (Nothing, Just b) -> Just $ (,) ltop b
        (Just a, Nothing) -> Just $ (,) a ltop
        _ -> Nothing
    lunion (la, lb) (ra, rb) = (,) <$> lunion la ra <*> lunion lb rb
    ltop = (ltop, ltop)

instance Eq a => Diff (Maybe a) (Maybe a) where
    diff a b
      | a == b = Nothing
      | otherwise = b
instance Eq a => Lattice (Maybe a) where
    lunion = (<?>)
    lintersect a b = case (<||>) a  b of
        IsTop -> Nothing
        Is x -> Just x
        IsBot -> error "union on bot"
    ltop = Nothing
instance Eq a => DiffApply (Maybe a) (Maybe a) where
    applyDiff = (<?>)

instance Lattice () where
    lunion _ _ = Just ()
    lintersect _ _ = Just ()
    ltop = pempty
instance (Diff a ()) => DiffApply a () where
    applyDiff () a  = Just a
instance (Lattice d, Pretty d) => PLattice (EDiff d) where
    (<||>) a b = case lintersect a b of
        Just x -> Is x
        Nothing -> IsTop
instance (Pretty d) => Pretty (EDiff d) where
    pretty (EDiff _ (Merges a) (MapDiff b)) = pretty (ILM.toList b) <> pretty (map (second ILS.toList) $ ILM.toList (efFwd a))

class InjectAna a b where
   injectAna :: a -> b
instance PMonoid b => InjectAna a (a,b) where
    injectAna a = (a, pempty)
instance PMonoid b => InjectAna a (b,a) where
    injectAna a = (pempty, a)
instance (Diff o i, Eq i, Pretty i, Hashable (f EClassId), Traversable f, EAnalysis o f) => PSemigroup (EGraph o f) where
    l <?> r = (egUnion l r)
instance (Diff o i, Eq i, Pretty i, Hashable (f EClassId), Traversable f, EAnalysis o f) => PMonoid (EGraph o f) where
    pempty = egNew
instance (Diff o i, Eq i, Pretty i, Show (f EClassId), EAnalysisIntersection o, Hashable (f EClassId), Traversable f, EAnalysis o f) => PLattice (EGraph o f) where
    l <||> r = case egIntersectGraphs l r of
        Nothing -> IsBot
        Just o -> Is o
instance (Diff o i, Eq i, Pretty i, Traversable f, Eq o, EAnalysis o f,  Hashable (f EClassId)) => RegularSemigroup (EGraph o f) where
    (==>?) a b
      | a == b = Nothing
      | otherwise = Just b
class Inject f g where
    inject :: f a -> g a
instance {-# OVERLAPPING #-}Inject f (f :+: g) where
    inject = L1
instance {-# OVERLAPPABLE #-}(Inject f k) => Inject f (g :+: k) where
    inject = R1 . inject
instance  Inject f f where
    inject = id

instance  (BoundedLattice a, BoundedLattice b) => EAnalysisIntersection (a,b)  where
    eaMeet (la, lb) (ra, rb) = (la ||| ra, lb ||| rb)  

instance {-# OVERLAPPING #-} (Pretty a, Pretty b, Ord a, Ord b, Functor f, Default a, Default b, EAnalysis a f, EAnalysis b f) => EAnalysis (a,b) f where
    eaMake  d = (eaMake (fmap fst d), eaMake (fmap snd d))
    eHook  cls = do
        unFirstHook (eHook cls)
        unSecondHook (eHook cls)
    eHook1  cls f  = do
        unFirstHook (eHook1 cls f)
        unSecondHook (eHook1 cls f)
instance (Pretty a, Pretty b, Default a, Default b, Ord a, Ord b, EAnalysisMerge a, EAnalysisMerge b) => EAnalysisMerge (a,b) where
    eaJoin (d1,d2) ls = (eaJoin d1 (fmap fst ls), eaJoin d2 (fmap snd ls))

    eaWhat (a,b) (c,d) = fromLR (updateL wl || updateL wr) (updateR wl || updateR wr)
      where
        wl = eaWhat a c
        wr = eaWhat b d
        updateL UpdateBoth = True
        updateL UpdateLeft = True
        updateL _ = False
        updateR UpdateBoth = True
        updateR UpdateRight = True
        updateR _ = False
        fromLR True True = UpdateBoth
        fromLR True False = UpdateLeft
        fromLR False True = UpdateRight
        fromLR _ _ = UpdateNone

type Default a = PMonoid a
theDefault :: PMonoid a => a
theDefault = pempty

newtype FirstHook m a = FirstHook {unFirstHook :: m a}
  deriving newtype (Functor, Applicative, Monad, Alternative)
newtype SecondHook m a = SecondHook {unSecondHook :: m a}
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadState s)
instance (EAnalysis (d,d2) f, EAnalysisHook m (d,d2) f, Default d2, Functor m) => EAnalysisHook (FirstHook m) d f where
    eaClassData cid = do
      (l,_) <- FirstHook (eaClassData cid)
      pure l
    eaAddTerm tid = FirstHook (eaAddTerm tid)
    eaMerge cid cid2 = FirstHook (eaMerge cid cid2)
    eaRefineAnalysis cid d = FirstHook (eaRefineAnalysis cid (d, theDefault))
    eaHalt = FirstHook eaHalt
    eaClassTerms = FirstHook . eaClassTerms
instance (EAnalysis (d,d2) f, EAnalysisHook m (d,d2) f, Default d, Functor m) => EAnalysisHook (SecondHook m) d2 f where
    eaClassData cid = do
      (_,r) <- SecondHook (eaClassData cid)
      pure r
    eaAddTerm tid = SecondHook (eaAddTerm tid)
    eaMerge cid cid2 = SecondHook (eaMerge cid cid2)
    eaRefineAnalysis cid d = SecondHook (eaRefineAnalysis cid (theDefault, d))
    eaHalt = SecondHook eaHalt
    eaClassTerms = SecondHook . eaClassTerms
newtype LeftHook m a = LeftHook {unLeftHook :: m a}
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadState s)
newtype RightHook m a = RightHook {unRightHook :: m a}
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadState s)
instance (Functor f, Functor g, Hashable (g EClassId), Hashable (f EClassId), EAnalysis d g, EAnalysisHook m d (f:+:g)) => EAnalysisHook (LeftHook m) d f where
    eaClassData cid = LeftHook (eaClassData cid)
    eaAddTerm tid = LeftHook (eaAddTerm (L1 tid))
    eaMerge cid cid2 = LeftHook (eaMerge cid cid2)
    eaRefineAnalysis cid d = LeftHook (eaRefineAnalysis cid d)
    eaHalt = LeftHook eaHalt
    eaClassTerms = LeftHook . fmap projL . eaClassTerms
      where projL ls = [x | L1 x <- ls]
instance (Functor g, Hashable (g EClassId), Hashable (f EClassId), EAnalysis d f, Functor f, EAnalysisHook m d (f:+:g)) => EAnalysisHook (RightHook m) d g where
    eaClassData cid = RightHook (eaClassData cid)
    eaAddTerm tid = RightHook (eaAddTerm (R1 tid))
    eaMerge cid cid2 = RightHook (eaMerge cid cid2)
    eaRefineAnalysis cid d = RightHook (eaRefineAnalysis cid d)
    eaHalt = RightHook eaHalt
    eaClassTerms = RightHook . fmap projR . eaClassTerms
      where projR ls = [x | R1 x <- ls]

instance (Pretty (f a), Pretty (g a)) => Pretty ((f :+: g) a) where
    pretty (L1 a) = pretty a
    pretty (R1 a) = pretty a

instance (Hashable (f a), Hashable (g a)) => Hashable ((f :+: g) a)
instance {-# INCOHERENT #-}  (Functor f, Functor g, Hashable (g EClassId), Hashable (f EClassId), EAnalysis a f, EAnalysis a g) => EAnalysis a (f :+: g) where
    eaMake (L1 a) = eaMake a 
    eaMake (R1 a) = eaMake a 
    eHook c = do
      unLeftHook (eHook c)
      unRightHook (eHook c)
    eHook1 c (L1 a)= unLeftHook (eHook1 c a)
    eHook1 c (R1 a)= unRightHook (eHook1 c a)
      -- unLeftHook (eHook c)
      -- unRightHook (eHook c)
instance Pretty Epoch where
    pretty (Epoch p) = pretty p
instance (Pretty d, Pretty (f EClassId)) => Pretty (EGraph d f) where
    pretty eg = "EGraph" <> shouldRebuild <> shouldCompact <> softline <>  align (encloseSep "{ " "}" ", " ([ prettyClass cid cls | (cid, cls) <- ILM.toList (egClassMap eg)]))
      where
        shouldRebuild = if egNeedsRebuild eg then "[needs rebuild]" else ""
        shouldCompact = if egCanCompact eg then "[can compact]" else ""
        prettyClass cid cls = pretty cid  <> brackets (prettyData cls)<> braces (pretty (ILM.partialLookup cid timestamps)) <+> ":=" <> softline <> align (encloseSep "(" ")" ", " [ prettyNode node | node <- ILS.toList (eciNodes cls)])
        prettyNode nid = pretty (assocPartialLookupByKey nid (egNodeAssoc eg))

        prettyData cls = pretty (eciData cls)
        timestamps = lastAnaChanges eg






-- some orphan instances which would go away by merging type classes
instance (PMonoid a, PMonoid b, RegularSemigroup a, RegularSemigroup b) => RegularSemigroup (a,b) where
 (la,lb) ==>? (ra,rb) = case (la ==>? ra, lb ==>? rb) of
    (Nothing, Nothing) -> Nothing
    (Just oa, Just ob) -> Just (oa,ob)
    (Just oa, Nothing) -> Just (oa,rb)
    (Nothing, Just ob) -> Just (ra,ob)
instance PMonoid () where
    pempty = ()
instance PSemigroup () where
    (<?>) _ _ = Just ()
instance (Lattice d, Pretty d) => PMonoid (EDiff d) where
    pempty = ltop
instance  Eq a => (PMonoid (Maybe a)) where
   pempty = Nothing
instance Eq a => RegularSemigroup (Maybe a) where
   a ==>? b
     | a == b = Nothing
     | otherwise = Just b
instance  Eq a => (PSemigroup (Maybe a)) where
   Nothing <?> r = Just r
   l <?> Nothing = Just l
   (Just a) <?> (Just b)
     | a == b = Just (Just a)
   _ <?> _ = Nothing
instance  Eq a => (PLattice (Maybe a)) where
   Nothing <||> _ = IsTop
   _ <||> Nothing = IsTop
   Just l <||> Just r
     | l == r = Is (Just l)
     | otherwise = IsBot

instance BoundedLattice a => PMonoid (Neg a) where
    pempty = Neg bot
instance (Enum a, Bounded a, Ord a) => Lattice (FiniteDomain a) where
    lintersect a b = case (<||>) a  b of
        IsTop -> Nothing
        Is x -> Just x
        IsBot -> error "union on bot"
    lunion = (<?>)
    ltop = pempty
newtype Neg a = Neg a
  deriving newtype (Eq, Ord, Show, Hashable, Generic)
instance (Lattice a, BoundedLattice a) => Lattice (Neg a) where
    lunion (Neg a) (Neg b)= fmap Neg (lintersect a b)
    lintersect (Neg a) (Neg b) = fmap Neg (lunion a b)
    ltop = Neg bot
instance (BoundedLattice a, PLattice a) => PSemigroup (Neg a) where
    (<?>) (Neg a0) (Neg b0) = case (<||>) a0 b0 of
        IsTop -> Nothing
        IsBot -> Just (Neg bot)
        Is a -> Just (Neg a)
instance (Lattice d) => PSemigroup (EDiff d) where
    (<?>) = lunion
instance  (Pretty a, Bounded a, Enum a, Ord a) => EAnalysisMerge (FiniteDomain a)  where
    eaJoin l rs = foldr (&&&) l rs

instance  (Bounded a, Enum a, Ord a) => EAnalysisIntersection (FiniteDomain a)  where
    eaMeet l rs =  (|||) l rs


instance (Show a, Ord a, Num a) => DiffApply (Range a) (Range a) where
    applyDiff l r = l <?> r
instance Semigroup (Range Integer) where
    a <> b = a &&& b
lastAnaChanges :: EGraph d f -> ILM.IntLikeMap EClassId Epoch
lastAnaChanges g = ILM.fromListWith  max [(v, k) | (k, v) <- ILM.toList (egAnaTimestamps g)]

instance (Enum a, Bounded a, Ord a) => DiffApply (FiniteDomain a) (Neg (FiniteDomain a))where
    applyDiff (Neg (FD b)) (FD a) 
      | out == BV.empty = Nothing
      | otherwise = Just $ FD out
      where out = BV.difference a b
instance (Show a, Ord a, Num a) => Diff (Range a) (Range a) where
    diff a b
      | a == b = top
      | otherwise = b -- = (==>)
instance (Ord a, Num a) => Lattice (Range a) where
    lintersect a b = case (<||>) a  b of
        IsTop -> Nothing
        Is x -> Just x
        IsBot -> error "union on bot"
    lunion = (<?>)
    ltop = pempty
instance Pretty a => Pretty (Neg a) where
    pretty (Neg a) = "-" <> pretty a
instance (Enum a, Bounded a, Ord a) => Diff (FiniteDomain a) (Neg (FiniteDomain a)) where
    diff (FD a) (FD b) = Neg $ FD (BV.difference a b)

egUnion :: (Diff d i, Eq i, Pretty i, EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> EGraph d f -> Maybe (EGraph d f)
egUnion l r = (rebuildInPlace . fst) =<< egUnionGraphs l r
rebuildInPlace :: (Diff d i, Pretty i, Eq i, EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> Maybe (EGraph d f)
rebuildInPlace = execStateT (egRebuild')
egRebuild' :: (HasCallStack, Pretty i, Diff d i, Eq i, MonadState (EGraph d f) m, EAnalysisHook m d f, EAnalysis d f, Traversable f, Hashable (f EClassId))  => m ()
egRebuild' = do
    _ <- egRebuild
    egCompact
instance Pretty ENodeId where
    pretty (ENodeId i) = "n" <> pretty i
instance Pretty EClassId where
    pretty (EClassId i) = "v" <> pretty i
