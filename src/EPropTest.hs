{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
-- | I forked a library to make propagation work,
-- this module sits between chairs because it references internals from both.
module EPropTest where
import ClusterEGraph

import Data.BitVector as BV
import DecisionDiagram
import GenericProp
import Debug.Trace (traceM)
import Control.Monad (forM_, when, void)
import Control.Applicative (Alternative(..), liftA2)
import Debug.Trace (trace)
import Control.Monad.State (MonadState)

import Data.List (transpose, sortOn)
import Control.Monad.Trans.State.Strict
import Range
import FiniteDomains
import Types
import Data.Utils (pprint, pshow, zipFoldableWith)
import GHC.Generics ((:+:)(..))
import Data.Functor.Foldable
import qualified Data.Foldable as F
import Data.Fix (Fix(..))
import qualified Data.Set as S
import Data.Maybe (mapMaybe, fromJust, isNothing, catMaybes)

import Data.Void (Void, absurd)
import qualified Data.Map as M

import Control.DeepSeq (NFData)
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Prettyprinter

import Overeasy.EGraph
import Overeasy.EDiff hiding (Base)
import Overeasy.Assoc (assocPartialLookupByKey, assocPartialLookupByValue)
import Overeasy.Classes (Changed(..))
import Overeasy.EquivFind (efFindRoot)

import qualified IntLike.Map as ILM
import qualified IntLike.Set as ILS
import GHC.IO (unsafePerformIO)

data Arith =
    ArithPlus Arith Arith
  | ArithTimes Arith Arith
  | ArithShiftL Arith !Int
  | ArithShiftR Arith !Int
  | ArithConst !Int
  | ArithNonDet !Int !Int
  deriving stock (Ord, Eq, Show, Generic)
  deriving anyclass (Hashable, NFData)

makeBaseFunctor ''Arith
deriving stock instance Eq a => Eq (ArithF a)
deriving stock instance Ord a => Ord (ArithF a)
deriving stock instance Show a => Show (ArithF a)
deriving stock instance Generic (ArithF a)
deriving anyclass instance Hashable a => Hashable (ArithF a)
deriving anyclass instance NFData a => NFData (ArithF a)



instance {-# OVERLAPPABLE #-}(DecideIfEdgeLife f a, DecideIfEdgeLife g a) => DecideIfEdgeLife (f :+: g) a where
    decideIfEdgeLife d (L1 x) = L1 (decideIfEdgeLife d x)
    decideIfEdgeLife d (R1 y) = R1 (decideIfEdgeLife d y)
instance {-# INCOHERENT #-} (Traversable f, DecideIfEdgeLife f a, DecideIfEdgeLife f b) => DecideIfEdgeLife f (a,b) where
    decideIfEdgeLife d x = zipFoldableWith (||) l r
      where
        l = decideIfEdgeLife (fst d) (fmap fst x)
        r = decideIfEdgeLife (snd d) (fmap snd x)
instance {-#OVERLAPPING #-} (Pretty s)=> DecideIfEdgeLife (FiniteDomainF s) (FiniteDomain s) where
    decideIfEdgeLife (FD s) a = o
      where
       o 
         | BV.size s == 1 = False <$ a
         | otherwise = fmap (\(FD s) -> BV.size s /= 1) a
instance {-# OVERLAPPABLE #-}Functor a => DecideIfEdgeLife a (FiniteDomain s) where
    decideIfEdgeLife _ a = False <$ a
instance {-#OVERLAPPING #-}DecideIfEdgeLife ArithF (Range Int) where
    decideIfEdgeLife _ a = fmap (isNothing . toPoint) a
instance {-# OVERLAPPABLE #-}DecideIfEdgeLife ArithF a where
    decideIfEdgeLife _ a = False <$ a
instance {-# OVERLAPPABLE #-}Functor a => DecideIfEdgeLife a (Range Int) where
    decideIfEdgeLife _ a = False <$ a



data BoolF a = TrueF | FalseF
  deriving stock (Ord, Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)
instance Pretty (BoolF a) where
   pretty TrueF = "True"
   pretty FalseF = "False"

data FiniteDomainF s a = DifferentFrom [a] | FDLiteral s
  deriving stock (Ord, Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

data VarF a = Var Int
  deriving stock (Ord, Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

var :: Int -> VarF Void
var = Var

instance Pretty (f (Fix f)) => Pretty (Fix f) where
   pretty (Fix f) = pretty f
instance Pretty SudokuNum where
   pretty (SD s) = pretty (1+s)
instance (Enum s, Bounded s, Pretty s) => Pretty (FiniteDomain s) where
    pretty (FD a) = "Dom" <> (pretty (BV.toList a))
instance (Pretty (s), Pretty a) => Pretty (FiniteDomainF s a) where
    pretty (DifferentFrom xs) = "not-in" <+> (pretty xs)
    pretty (FDLiteral s) = pretty s
instance Pretty (VarF a) where
    pretty (Var xs) = "l" <> pretty xs

instance Semigroup (Range Int) where
    a <> b = a &&& b

type Eg = EGraph (Range Int) (ArithF :+: BoolF)

instance Pretty ENodeId where
    pretty (ENodeId i) = "n" <> pretty i
instance Pretty EClassId where
    pretty (EClassId i) = "v" <> pretty i
instance Pretty x => Pretty (ArithF x) where
    pretty = \case
        ArithPlusF a b -> pretty a <+> "+" <+> pretty b
        ArithTimesF a b -> pretty a <+> "*" <+> pretty b
        ArithShiftLF a l -> pretty a <+> "<<" <+> pretty l
        ArithShiftRF a l -> pretty a <+> ">>" <+> pretty l
        ArithNonDetF a l -> pretty a <> "..." <> pretty l
        ArithConstF c -> pretty c
instance Pretty Arith where
    pretty = pretty . show

instance (Pretty d, Pretty (f EClassId)) => Pretty (EGraph d f) where
    pretty eg = "EGraph" <> shouldRebuild <> shouldCompact <> softline <>  align (encloseSep "{ " "}" ", " [ prettyClass cid cls | (cid, cls) <- ILM.toList (egClassMap eg)])
      where
        shouldRebuild = if egNeedsRebuild eg then "[needs rebuild]" else ""
        shouldCompact = if egCanCompact eg then "[can compact]" else ""
        prettyClass cid cls = pretty cid  <> brackets (prettyData cls)<+> ":=" <> line <> encloseSep "(" ")" ", " [ prettyNode node | node <- ILS.toList (eciNodes cls)]
        prettyNode nid = pretty (assocPartialLookupByKey nid (egNodeAssoc eg))

        prettyData cls = pretty (eciData cls)
sudokuExample :: M.Map Int Int
sudokuExample = toIndex [
    " 7   2  5",
    "         ",
    "9    4 8 ",

    "  32   5 ",
    "   63    ",
    "2    9 1 ",

    "  9 46  7",
    "3       6",
    "8    5  4"
 ]
 where
   toIndex = M.fromList . mapMaybe2 toDig . zip [0..] . concat
   toDig ' ' = Nothing
   toDig c = Just (fromEnum c - fromEnum '0')
   mapMaybe2 f = mapMaybe (traverse f)

printSudoku = print . printGrid . toGrid
toGrid :: Eg2 -> M.Map Var (FiniteDomain SudokuNum)
toGrid eg0 = M.fromList [ (i-1, egLookupData eg0 (egLookupClass eg0 (inject $ Var i :: TermF EClassId))) | i <- [1..81] ]
  where
    egLookupNode :: Eg2 -> TermF EClassId -> ENodeId
    egLookupNode eg t = assocPartialLookupByValue t (egNodeAssoc eg)
    egLookupNodeClass :: Eg2 -> ENodeId -> EClassId
    egLookupNodeClass eg t = ILM.partialLookup t (egHashCons eg)
    egLookupClass :: Eg2 -> TermF EClassId -> EClassId
    egLookupClass eg = egLookupNodeClass eg . egLookupNode eg
    egLookupData eg c = snd $ eciData (ILM.partialLookup c (egClassMap eg))

instance (Hashable (f a), Hashable (g a)) => Hashable ((f :+: g) a)
instance {-# INCOHERENT #-}  (Functor f, Functor g, Hashable (g EClassId), Hashable (f EClassId), EAnalysis a f, EAnalysis a g) => EAnalysis a (f :+: g) where
    eaMake (L1 a) = eaMake a 
    eaMake (R1 a) = eaMake a 
    eHook c = do
      unLeftHook (eHook c)
      unRightHook (eHook c)

instance  (EAnalysisMerge a, PMonoid a) => EAnalysis a VarF where
    eaMake _ = pempty
    eHook _ = pure ()
instance  (Pretty a, Num a, Integral a, Bounded a, Enum a, Ord a) => EAnalysis (FiniteDomain a) ArithF where
    eaMake = \case
        ArithPlusF a b -> a + b
        ArithTimesF a b -> a * b
        ArithShiftLF a l -> a * 2^l
        ArithShiftRF a l -> a `div` 2^l
        ArithConstF c -> fromIntegral c
        ArithNonDetF a b -> FD (BV.fromList [fromIntegral a..fromIntegral b])
    eHook _ = pure ()
instance  EAnalysis (Range Int) (FiniteDomainF a) where
    eaMake _ = pempty
    eHook _ = pure ()
instance  (Pretty a, Hashable a, Ord a, Enum a, Bounded a) => EAnalysis (FiniteDomain a) (FiniteDomainF a) where
    eaMake (DifferentFrom ls) = dumbArcConsistent pempty ls
    eaMake (FDLiteral l) = domSingleton l
    eHook cls = do
        dat <- eaClassData cls
        when (isBot dat) eaHalt
        case domPoint dat of 
            Just o -> do
              -- traceM ("ehook2" <> pshow (cls, dat))
              t <- eaAddTerm (FDLiteral o)
              eaMerge cls t
            Nothing -> pure ()

instance  EAnalysis (Range Int) ArithF where
    eaMake = \case
        ArithPlusF a b -> a + b
        ArithTimesF a b -> a * b
        ArithShiftLF a l -> a * 2^l
        ArithShiftRF a l -> a `div` 2^l
        ArithConstF c -> fromIntegral c
        ArithNonDetF a b -> a...b
    eHook cls = do
        dat <- eaClassData cls
        when (isBot dat) (eaHalt)
        case toPoint dat of 
            Just o -> do
              -- traceM "ehook1"
              t <- eaAddTerm (ArithConstF o)
              eaMerge cls t
            Nothing -> pure ()
instance  EAnalysisMerge (Range Int)  where
    eaJoin l rs =  foldr (&&&) l rs
instance  EAnalysisIntersection (Range Int)  where
    eaMeet l rs =  (|||) l rs
instance  (BoundedLattice a, BoundedLattice b) => EAnalysisIntersection (a,b)  where
    eaMeet (la, lb) (ra, rb) = (la ||| ra, lb ||| rb)  
instance  (Pretty a, Bounded a, Enum a, Ord a) => EAnalysisMerge (FiniteDomain a)  where
    eaJoin l rs = foldr (&&&) l rs

    -- eaWhat l r
    --   | l == r = trace ("equal: " <> pshow l <> " " <> pshow r) UpdateNone
    --   | otherwise = trace ("unequal: " <> pshow l <> " " <> pshow r) UpdateBoth
instance  (Bounded a, Enum a, Ord a) => EAnalysisIntersection (FiniteDomain a)  where
    eaMeet l rs =  (|||) l rs

instance {-# OVERLAPPING #-} (Pretty a, Pretty b, Ord a, Ord b, Functor f, Default a, Default b, EAnalysis a f, EAnalysis b f) => EAnalysis (a,b) f where
    eaMake  d = (eaMake (fmap fst d), eaMake (fmap snd d))
    eHook  cls = do
        unFirstHook (eHook cls)
        unSecondHook (eHook cls)
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
instance (EAnalysis (d,d2) f, EAnalysisHook m (d,d2) f, Default d, Functor m) => EAnalysisHook (SecondHook m) d2 f where
    eaClassData cid = do
      (_,r) <- SecondHook (eaClassData cid)
      pure r
    eaAddTerm tid = SecondHook (eaAddTerm tid)
    eaMerge cid cid2 = SecondHook (eaMerge cid cid2)
    eaRefineAnalysis cid d = SecondHook (eaRefineAnalysis cid (theDefault, d))
    eaHalt = SecondHook eaHalt
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
instance (Functor g, Hashable (g EClassId), Hashable (f EClassId), EAnalysis d f, Functor f, EAnalysisHook m d (f:+:g)) => EAnalysisHook (RightHook m) d g where
    eaClassData cid = RightHook (eaClassData cid)
    eaAddTerm tid = RightHook (eaAddTerm (R1 tid))
    eaMerge cid cid2 = RightHook (eaMerge cid cid2)
    eaRefineAnalysis cid d = RightHook (eaRefineAnalysis cid d)
    eaHalt = RightHook eaHalt

instance (Pretty (f a), Pretty (g a)) => Pretty ((f :+: g) a) where
    pretty (L1 a) = pretty a
    pretty (R1 a) = pretty a
instance EAnalysis (Range Int) BoolF where
   eaMake _ = pempty

testEg, testEg2 :: Maybe Eg
testEg = flip execStateT egNew $ do
    (_,_c1pc2) <- egAddTerm (genFix $ ArithPlus (ArithNonDet 1 3) (ArithConst 2))
    -- egMerge c1pc2 c3
    _ <- egRebuild
    egCompact

class GeneralizeFix f g where
    genFix :: f -> Fix g
instance (Recursive t, Inject (Base t) g) => GeneralizeFix t g where
    genFix = Fix . inject . fmap genFix . project

testEg2 = flip execStateT egNew $ do
    (_,c13) <- egAddTerm (genFix $ ArithNonDet 1 3)
    egAddAnalysis c13 [3...3]
    (_,_c1pc2) <- egAddTerm (genFix $ ArithPlus (ArithNonDet 1 3) (ArithConst 2))

    -- egMerge c13 c3
    _ <- egRebuild
    egCompact

-- testEg3 = flip execState egNew $ do
--     (_,c13) <- egAddTerm (ArithNonDetF 1 3)
--     egAddAnalysis c13 [2...4]
--     _ <- egRebuild
--     egCompact

class Inject f g where
    inject :: f a -> g a
instance {-# OVERLAPPING #-}Inject f (f :+: g) where
    inject = L1
instance {-# OVERLAPPABLE #-}(Inject f k) => Inject f (g :+: k) where
    inject = R1 . inject
instance  Inject f f where
    inject = id
class  InjectFix v g where
    injectFix :: v -> Fix g
instance  {-# OVERLAPPABLE #-}(Functor f, Inject f g, InjectFix (h a) g) => InjectFix (f (h a)) g where
    injectFix = Fix . inject . fmap injectFix
instance  {-# OVERLAPPING #-} (Functor f, Inject f g) => InjectFix (f Void) g where
    injectFix = Fix . inject . fmap absurd
-- instance (Functor f, Inject x (Fix g), Inject (f (Fix g)) (g (Fix g))) => Inject (f x) (Fix g) where
--     inject x = Fix (inject @_ @(g (Fix g))(fmap (inject @_ @(Fix g)) x))
-- instance Inject Void (Fix g) where
--     inject = absurd
    
type TermF = (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
type Term = Fix TermF
mkVar :: (EAnalysisHook m (Range Int, FiniteDomain SudokuNum)
                          (ArithF :+: (FiniteDomainF SudokuNum :+: VarF)), MonadState Eg2 m) => Int -> m EClassId
mkVar v = fmap snd $ egAddTerm (injectFix (var v) :: Term)
testEg4 :: Eg2
testEg4 = fromJust $ flip execStateT egNew $ do
    vs <- mapM mkVar [1..81]
    let vMap = M.fromList (zip [0..] vs)
        get1 x = case M.lookup x vMap of
            Just v -> v
            Nothing -> error ("testEg4: no such variable " <> show x)

    mapM_ (allDifferent . fmap get1) (rows <> cols <> squares)
    forM_ (M.toList sudokuExample) $ \(idx,dig) -> do
        let v = get1 idx
        egAddAnalysis v [(pempty, domSingleton (SD $ dig-1))]
    -- allDifferent [v1, v2, v3]
    _ <- egRebuild
    egCompact
  where
    base = cellWidth * cellWidth
    rows = chunksOf base [0..base*base-1]
    cols = transpose rows
    squares = fmap concat $ concatMap (chunksOf cellWidth) $ transpose $ map (chunksOf cellWidth) rows
testEg5 :: Maybe Eg2
testEg5 = flip execStateT egNew $ do
    -- (_,v1) <- egAddTerm (Fix $ R1(R1(Var 5)))
    v2 <- mkVar 2
    v3 <- mkVar 3
    -- egAddAnalysis v2 [(pempty, FD $ BV.fromList [1,2])]
    egAddAnalysis v2 [(pempty, FD $ BV.fromList [2])]
    egAddAnalysis v3 [(pempty, FD $ BV.fromList [3])]
    _ <- egMerge v2 v3
    _ <- egRebuild
    egCompact
    pure ()
testEg6 :: Eg2
testEg6 = fromJust $ flip execStateT egNew $ do
    v1 <- mkVar 62
    egAddAnalysis v1 [(pempty, FD $ BV.fromList [2])]

egUnion :: (EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> EGraph d f -> Maybe (EGraph d f)
egUnion l r = (rebuildInPlace . fst) =<< egUnionGraphs l r

type Eg2 = EGraph (Range Int, FiniteDomain SudokuNum) (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
allDifferent :: (EAnalysisHook m (Range Int, FiniteDomain SudokuNum)
                          (ArithF :+: (FiniteDomainF SudokuNum :+: VarF)), MonadState Eg2 m) => [EClassId] -> m ()
allDifferent ls = do
   forM_ (slices [] ls) $ \(x,xs) -> do
       (_, cls) <- egAddFlatTerm (R1 $ L1 (DifferentFrom xs))
       egMerge x cls
  where
    slices acc (x:xs) = (x,acc<>xs) : slices (x:acc) xs
    slices _ [] = []

rebuildInPlace :: (EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> Maybe (EGraph d f)
rebuildInPlace = execStateT (egRebuild *> egCompact)



instance (Hashable (f EClassId), Traversable f, EAnalysis o f) => PSemigroup (EGraph o f) where
    l <?> r = (egUnion l r)
instance (Hashable (f EClassId), Traversable f, EAnalysis o f) => PMonoid (EGraph o f) where
    pempty = egNew
instance (Show (f EClassId), EAnalysisIntersection o, Hashable (f EClassId), Traversable f, EAnalysis o f) => PLattice (EGraph o f) where
    l <||> r = case egIntersectGraphs l r of
        Nothing -> IsBot
        Just o -> Is o
instance (Traversable f, Eq o, EAnalysis o f,  Hashable (f EClassId)) => RegularSemigroup (EGraph o f) where
    (==>?) a b
      | a == b = Nothing
      | otherwise = Just b

class InjectAna a b where
   injectAna :: a -> b
instance PMonoid b => InjectAna a (a,b) where
    injectAna a = (a, pempty)
instance PMonoid b => InjectAna a (b,a) where
    injectAna a = (pempty, a)
instance (Inject BoolF f, EAnalysisIntersection o, Show (f EClassId), Traversable f, Eq o, EAnalysis o f,  Hashable (f EClassId), Show o) => IsLit (EClassId, f EClassId) (EGraph o f) where
   isL (v, e) = fromJust $ flip execStateT egNew $  do
       (_,t) <- egAddFlatTerm e
       egMerge v t >>= \case
          Nothing -> error "isL var not found failed"
          Just c -> when (c == ChangedYes) (void egRebuild)
   notL v  = pempty -- fromJust $ flip execStateT egNew $  do
       -- (_,t) <- egAddFlatTerm (inject FalseF)
       -- egMerge (EClassId v) t >>= \case
       --    Nothing -> error "notL var not found failed"
       --    Just c -> when (c == ChangedYes) (void egRebuild)
   evalVar (v, f) e 
     | trueNode == Just vRoot = Just True
     | otherwise = Nothing
     where
      trueNode = egFindNode f e
      falseNode = egFindNode (inject FalseF) e
      vRoot = case efFindRoot v (egEquivFind e) of
          Nothing -> error "evalVar: var not in egraph"
          Just o -> o
   splitLit (v,f) e = Just (l,Iff e)
        where
          toIff = maybe IsFalse Iff
          l = toIff $ flip execStateT e $ do
                  (_, t) <- egAddFlatTerm f
                  m <- egMerge v t
                  case m of
                    Nothing -> error "splitLit: true failed"
                    Just _ -> egRebuild
          -- r = toIff $ flip execStateT e $ do
                  -- (_, f) <- egAddFlatTerm (inject FalseF)
                  -- m <- egMerge (EClassId v) f
                  -- case m of
                  --   Nothing -> error "splitLit: false failed"
                  --   Just _ -> egRebuild
   maxSplitVar _ = undefined
   --    egAddAnalysis v [injectAna 

-- instance (PSemigroup a, PSemigroup b) => PSemigroup (a,b) where
--     (a,b) <?> (c,d) = liftA2 (,) (a <?> c) (b <?> d)
-- instance (PMonoid a, PMonoid b) => PMonoid (a,b) where
--     pempty = (pempty,pempty)
instance (PMonoid a, PMonoid b, RegularSemigroup a, RegularSemigroup b) => RegularSemigroup (a,b) where
 (la,lb) ==>? (ra,rb) = case (la ==>? ra, lb ==>? rb) of
    (Nothing, Nothing) -> Nothing
    (Just oa, Just ob) -> Just (oa,ob)
    (Just oa, Nothing) -> Just (oa,rb)
    (Nothing, Just ob) -> Just (ra,ob)

class AnaSplits f a where
    anaSplits :: a -> [S.Set (f EClassId)]
instance {-# OVERLAPPING #-} (Ord s, Enum s, Bounded s) => AnaSplits (FiniteDomainF s) (FiniteDomain s)  where
    anaSplits (FD a) 
      | BV.size a == 1 = []
      | otherwise = pure $ S.fromList $ map FDLiteral $ BV.toList a
instance {-# OVERLAPPABLE #-}AnaSplits a (FiniteDomain s)  where
    anaSplits _ = []
instance AnaSplits a (Range s)  where
    anaSplits _ = []
instance (Ord (f EClassId), Ord (g EClassId), AnaSplits f a, AnaSplits g a) => AnaSplits (f :+: g) a where
    anaSplits a = toL la <|> toR lb
        where
          la = anaSplits a
          lb = anaSplits a
          toL = fmap (S.map L1)
          toR = fmap (S.map R1)
instance {-# INCOHERENT #-}(AnaSplits f a, AnaSplits f b) => AnaSplits f (a,b) where
    anaSplits (a,b) = anaSplits a <|> anaSplits b

genSplits :: AnaSplits f o => EGraph o f -> [(EClassId, S.Set (f EClassId))]
genSplits eg = sortOn (S.size . snd) [ (c, x) | (c, ec) <- ILM.toList (egClassMap eg), (x:_) <- [sortOn S.size $ anaSplits (eciData ec)]]

-- trySplit :: (EAnalysisIntersection o, Hashable (f EClassId), Traversable f, AnaSplits f o, EAnalysis o f) => EGraph o f -> EGraph o f
trySplit idx eg = (catMaybes [ setVal c s eg  | s <- S.toList ss ])
      -- [] -> pempty
      -- x:xs -> foldr orBranch x xs
  where
    (c, ss) = genSplits eg !! idx
    orBranch a b = case egIntersectGraphs a b of
      Nothing -> error "oh no"
      Just a -> a
      -- IsBot -> error "oh no"
    setVal c s e = flip execStateT e $ do
      (_, t) <- egAddFlatTerm s
      m <- egMerge c t
      case m of
        Nothing -> error "setVal: merge failed"
        Just _ -> egRebuild
      pure ()

fixMeee = threeWayDiff testEg4 (fromJust $ setVal (EClassId 28) (R1 $ L1 $ FDLiteral 7)  testEg4)
fixMeee2 = threeWayDiff testEg4 (fromJust $ setVal (EClassId 28) (R1 $ L1 $ FDLiteral 8)  testEg4)
choicesToDiffs eg0 (h,bs) = [threeWayDiff eg0 o | b <- S.toList bs, Just o <- [setVal h b eg0]]


tryShrink1 eg0 = foldl (\acc cur -> acc >>= flip stepShrink cur) (Just eg0) $ takeWhile ((<4) . S.size . snd) (genSplits eg0)
  where
   stepShrink eg1 bs = applyDiff eg1 (mergeDiffsN (choicesToDiffs eg1 bs))

tryShrink2 eg0 = foldl (\acc cur -> acc >>= flip stepShrink cur) (Just eg0) $ pairs $ takeWhile ((<=3) . S.size . snd) (genSplits eg0)
  where
   stepShrink eg1 bs = applyDiff eg1 (mergeDiffsN (choicesToDiffs2 eg1 bs))
   pairs a = liftA2 (,) a a
   choicesToDiffs2 eg0 ((h1,xs), (h,bs)) = trace ("choicesToDiffs2: " ++ show (length out)) out

     where out = threeWayDiff eg0 <$> [ p | x <- S.toList xs, Just o <- [setVal h1 x eg0], b <- S.toList bs, Just p <- [setVal h b eg0]]

mergeDiffsN [] = EDiff mempty mempty mempty
mergeDiffsN (x:xs) = foldr mergeDiffs x xs
setVal c s e = flip execStateT e $ do
  (_, t) <- egAddFlatTerm s
  m <- egMerge t c
  case m of
    Nothing -> error "setVal: merge failed"
    Just _ -> egRebuild
  pure ()

instance (Pretty (f EClassId), Pretty d) => Pretty (EDiff d f) where
    pretty (EDiff a b c) = pretty (ILM.toList b) <> pretty (map ILS.toList $ ILM.elems a)

testChoiceTree eg0 = choiceTree eg0 $ take 3 $ takeWhile ((==2) . S.size . snd) (genSplits eg0)

instance (Pretty (f EClassId), Hashable (f EClassId), Pretty d) => PSemigroup (EDiff d f) where
    (<?>) = undefined
instance (Pretty (f EClassId), Hashable (f EClassId), Pretty d) => PLattice (EDiff d f) where
    (<||>) = undefined
instance (Pretty (f EClassId), Hashable (f EClassId), Pretty d) => PMonoid (EDiff d f) where
    pempty = EDiff mempty mempty mempty

type Choices f = [(EClassId, S.Set (f EClassId))]
choiceTree :: forall d f.(Eq d, Hashable (f EClassId), RegularSemigroup d, PLattice d, Pretty d, EAnalysis d f, Traversable f) =>  EGraph d f -> Choices f -> DD (EClassId, f EClassId) (EDiff d f)
choiceTree eg0 xs = go eg0 xs
 where
   goM Nothing _ = IsFalse
   goM (Just eg1) ls = go eg1 ls

   go :: EGraph d f -> Choices f -> DD (EClassId, f EClassId) (EDiff d f)
   go eg ((b,bs):xs) = goI eg b (S.toList bs) (\x -> goM (setVal b x eg) xs)
   go eg [] = Iff (threeWayDiff eg0 eg)

   goI :: EGraph d f -> EClassId -> [f EClassId] -> (f EClassId -> DD (EClassId, f EClassId) (EDiff d f)) -> DD (EClassId, f EClassId) (EDiff d f)
   goI eg b (a:as) k = mkIf (b, a) (k a) (goI eg b as k)
   goI _ _ _ _ = IsFalse

   mkIf v IsFalse r  = r
   mkIf v  l IsFalse = l
   mkIf v l r 
     | l == r = l
     | otherwise = If v merged l r
     where

       merged = case (valOf l, valOf r) of
         (Just a, Just b) -> mergeDiffs a b
         (Just a, Nothing) -> a
         (Nothing, Just b) -> b
         (Nothing, Nothing) -> EDiff mempty mempty mempty
valOf (If _ v _ _) = Just v
valOf (Iff s) = Just s
valOf _ = Nothing


fixChoice eg0 = go eg0
  where
    go eg = 
      let
        choiceTree = (testChoiceTree eg)
        Just diff = valOf choiceTree
        eg' = execState egCompact $ fromJust (applyDiff eg diff)
      in if (diff == pempty || eg' == eg)
      then eg
      else trace (pshow diff<> "\n" <> show (printGrid (toGrid eg)))$ go $ eg'
  

instance (Pretty (a), PLattice a, RegularSemigroup a) => DeltaAnalysis a where
    deltaAnalysis a b = (a ==>? b)
    intersectAnalysis a b = case a <||> b of
       IsBot -> error "bot should not be in egraph"
       IsTop ->  Nothing
       Is o -> Just o


collectNew :: (Traversable f, EAnalysis o f, Hashable (f EClassId), RegularSemigroup o) => EGraph o f -> EGraph o f -> [(EClassId, o, o)]
collectNew l r = [ (cid, dl,  o) | (cid, cr) <- ILM.toList (egClassMap r), let dl = lData cid, Just o <- [dl ==>? eciData cr]]
  where
    lData c = eciData $ fromJust $ ILM.lookup (ILM.partialLookup c m) (egClassMap l)
    (_, m) = fromJust (egUnionGraphs l r)


