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
module EPropTest where

import Control.Monad (forM_, when, void)

import Data.List (transpose)
import Control.Monad.Trans.State.Strict
import Range
import FiniteDomains
import Types
import Data.Utils (pprint, pshow)
import GHC.Generics ((:+:)(..))
import Data.Functor.Foldable
import Data.Fix (Fix(..))
import qualified Data.Set as S
import Data.Maybe (mapMaybe)

import Data.Void (Void, absurd)
import qualified Data.Map as M

import Control.DeepSeq (NFData)
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Prettyprinter

import Overeasy.EGraph
import Overeasy.Assoc (assocPartialLookupByKey)
import Overeasy.Classes (Changed(..))
import Overeasy.EquivFind (efFindRoot)

import qualified IntLike.Map as ILM
import qualified IntLike.Set as ILS
import Debug.Trace

data Arith =
    ArithPlus Arith Arith
  | ArithTimes Arith Arith
  | ArithShiftL Arith !Int
  | ArithShiftR Arith !Int
  | ArithConst !Int
  | ArithNonDet !Int !Int
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable, NFData)

makeBaseFunctor ''Arith
deriving stock instance Eq a => Eq (ArithF a)
deriving stock instance Show a => Show (ArithF a)
deriving stock instance Generic (ArithF a)
deriving anyclass instance Hashable a => Hashable (ArithF a)
deriving anyclass instance NFData a => NFData (ArithF a)


data BoolF a = TrueF | FalseF
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)
instance Pretty (BoolF a) where
   pretty TrueF = "True"
   pretty FalseF = "False"

data FiniteDomainF s a = DifferentFrom [a] | FDLiteral s
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

data VarF a = Var Int
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

var :: Int -> VarF Void
var = Var

instance Pretty (f (Fix f)) => Pretty (Fix f) where
   pretty (Fix f) = pretty f
instance Pretty SudokuNum where
   pretty (SD s) = pretty (1+s)
instance (Pretty s) => Pretty (FiniteDomain s) where
    pretty (FD a) = "Dom" <> (pretty (S.toList a))
instance (Pretty (s), Pretty a) => Pretty (FiniteDomainF s a) where
    pretty (DifferentFrom xs) = "not-in" <+> (pretty xs)
    pretty (FDLiteral s) = pretty s
instance Pretty (VarF a) where
    pretty (Var xs) = "l" <> pretty xs

instance Semigroup (Range Int) where
    a <> b = a &&& b

type Eg = EGraph (Range Int) (ArithF :+: BoolF)

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
        ArithNonDetF a b -> FD (S.fromList [fromIntegral a..fromIntegral b])
    eHook _ = pure ()
instance  EAnalysis (Range Int) (FiniteDomainF a) where
    eaMake _ = pempty
    eHook _ = pure ()
instance  (Pretty a, Hashable a, Ord a, Enum a, Bounded a) => EAnalysis (FiniteDomain a) (FiniteDomainF a) where
    eaMake (DifferentFrom ls) = remainder ls
    eaMake (FDLiteral l) = domSingleton l
    eHook cls = do
        dat <- eaClassData cls
        case domPoint dat of 
            Just o -> do
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
        -- when (isBot dat) (eaHalt)
        case toPoint dat of 
            Just o -> do
              t <- eaAddTerm (ArithConstF o)
              eaMerge cls t
            Nothing -> pure ()
instance  EAnalysisMerge (Range Int)  where
    eaJoin l rs =  foldr (&&&) l rs
instance  EAnalysisIntersection (Range Int)  where
    eaMeet l rs =  (|||) l rs
instance  (Pretty a, Bounded a, Enum a, Ord a) => EAnalysisMerge (FiniteDomain a)  where
    eaJoin l rs =  foldr (&&&) l rs

    -- eaWhat l r
    --   | l == r = trace ("equal: " <> pshow l <> " " <> pshow r) UpdateNone
    --   | otherwise = trace ("unequal: " <> pshow l <> " " <> pshow r) UpdateBoth
instance  (Bounded a, Enum a, Ord a) => EAnalysisIntersection (FiniteDomain a)  where
    eaMeet l rs =  (|||) l rs
    -- eaWhat _ l r 
    --  | l == r = trace ("eawhat none" <> pshow (l,r)) UpdateNone
    --  | otherwise = trace ("eawhat both" <> pshow (l,r)) UpdateBoth

instance {-# OVERLAPPING #-} (Ord a, Ord b, Functor f, Default a, Default b, EAnalysis a f, EAnalysis b f) => EAnalysis (a,b) f where
    eaMake  d = (eaMake (fmap fst d), eaMake (fmap snd d))
    eHook  cls = do
        unFirstHook (eHook cls)
instance (Default a, Default b, Ord a, Ord b, EAnalysisMerge a, EAnalysisMerge b) => EAnalysisMerge (a,b) where
    eaJoin (d1,d2) ls = (eaJoin d1 (fmap fst ls), eaJoin d2 (fmap snd ls))

type Default a = PMonoid a
theDefault :: PMonoid a => a
theDefault = pempty

newtype FirstHook m a = FirstHook {unFirstHook :: m a}
  deriving newtype (Functor, Applicative, Monad)
newtype SecondHook m a = SecondHook {unSecondHook :: m a}
  deriving newtype (Functor, Applicative, Monad)
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
  deriving newtype (Functor, Applicative, Monad)
newtype RightHook m a = RightHook {unRightHook :: m a}
  deriving newtype (Functor, Applicative, Monad)
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

testEg, testEg2 :: Eg
testEg = flip execState egNew $ do
    (_,_c1pc2) <- egAddTerm (genFix $ ArithPlus (ArithNonDet 1 3) (ArithConst 2))
    -- egMerge c1pc2 c3
    _ <- egRebuild
    egCompact

class GeneralizeFix f g where
    genFix :: f -> Fix g
instance (Recursive t, Inject (Base t) g) => GeneralizeFix t g where
    genFix = Fix . inject . fmap genFix . project

testEg2 = flip execState egNew $ do
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
    
type Term = Fix (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
mkVar :: Int -> State Eg2 EClassId
mkVar v = fmap snd $ egAddTerm (injectFix (var v) :: Term)
testEg4 :: Eg2
testEg4 = flip execState egNew $ do
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
    cellWidth = 3
    base = cellWidth * cellWidth
    rows = chunksOf base [0..base*base-1]
    cols = transpose rows
    squares = fmap concat $ concatMap (chunksOf cellWidth) $ transpose $ map (chunksOf cellWidth) rows
testEg5 :: Eg2
testEg5 = flip execState egNew $ do
    (_,v1) <- egAddTerm (Fix $ R1(R1(Var 1)))
    (_,v2) <- egAddTerm (Fix $ R1(R1(Var 2)))
    egAddAnalysis v2 [(pempty, FD $ S.fromList [1,2])]
    egAddAnalysis v1 [(pempty, FD $ S.fromList [2])]
    _ <- egRebuild
    egCompact
egUnion l r = rebuildInPlace $ fst $ egUnionGraphs l r

type Eg2 = EGraph (Range Int, FiniteDomain SudokuNum) (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
allDifferent :: [EClassId] -> State Eg2 ()
allDifferent ls = do
   forM_ (slices [] ls) $ \(x,xs) -> do
       (_, cls) <- egAddFlatTerm (R1 $ L1 (DifferentFrom xs))
       egMerge x cls
  where
    slices acc (x:xs) = (x,acc<>xs) : slices (x:acc) xs
    slices _ [] = []
    

rebuildInPlace :: (EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> EGraph d f
rebuildInPlace = execState (egRebuild *> egCompact)



instance (Hashable (f EClassId), Traversable f, EAnalysis o f) => PSemigroup (EGraph o f) where
    l <?> r = Just (egUnion l r)
instance (Hashable (f EClassId), Traversable f, EAnalysis o f) => PMonoid (EGraph o f) where
    pempty = egNew
instance (EAnalysisIntersection o, Hashable (f EClassId), Traversable f, EAnalysis o f) => PLattice (EGraph o f) where
    l <||> r
      | otherwise = Is out
      where out = egIntersectGraphs l r
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
instance (Inject BoolF f, EAnalysisIntersection o, Show (f EClassId), Traversable f, Eq o, EAnalysis o f,  Hashable (f EClassId), Show o) => IsLit (EGraph o f) where
   isL v = flip execState egNew $  do
       (_,t) <- egAddFlatTerm (inject TrueF)
       egMerge (EClassId v) t >>= \case
          Nothing -> error "isL var not found failed"
          Just c -> when (c == ChangedYes) (void egRebuild)
   notL v = flip execState egNew $  do
       (_,t) <- egAddFlatTerm (inject FalseF)
       egMerge (EClassId v) t >>= \case
          Nothing -> error "notL var not found failed"
          Just c -> when (c == ChangedYes) (void egRebuild)
   evalVar v e
     | trueNode == Just vRoot = Just True
     | falseNode == Just vRoot = Just False
     | otherwise = Nothing
     where
      trueNode = egFindNode (inject TrueF) e
      falseNode = egFindNode (inject FalseF) e
      vRoot = case efFindRoot (EClassId v) (egEquivFind e) of
          Nothing -> error "evalVar: var not in egraph"
          Just o -> o
   splitLit v e = Just (Iff l,Iff r)
        where
          l = flip execState e $ do
                  (_, t) <- egAddFlatTerm (inject TrueF)
                  m <- egMerge (EClassId v) t
                  case m of
                    Nothing -> error "splitLit: true failed"
                    Just _ -> egRebuild
          r = flip execState e $ do
                  (_, f) <- egAddFlatTerm (inject FalseF)
                  m <- egMerge (EClassId v) f
                  case m of
                    Nothing -> error "splitLit: false failed"
                    Just _ -> egRebuild
   maxSplitVar _ = (-1)
     
   --    egAddAnalysis v [injectAna 
