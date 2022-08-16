{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-name-shadowing #-}
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
-- | I had to fork the Overeasy EGraph library to make propagation work
-- this module sits between chairs because it references internals from both.
module EPropTest where

import GHC.Stack

import Control.Arrow (second)
import Data.BitVector as BV
import Control.Applicative (Alternative(..), asum)
import Control.Monad.State hiding (StateT, modify', execStateT, runStateT, evalStateT)

import Data.List (transpose, sortBy, sortOn)
import Data.Ord (comparing)
import Control.Monad.Trans.State.Strict (StateT, execStateT, runStateT, evalStateT)
import Range
import FiniteDomains
import Types
import Data.Utils (pprint, pshow)
import GHC.Generics ((:+:)(..))
import Data.Functor.Foldable
import qualified Data.Foldable as F
import Data.Fix (Fix(..))
import qualified Data.Set as S
import Data.Maybe (mapMaybe, fromJust, catMaybes)

import Data.Void (Void, absurd)
import qualified Data.Map as M

import Control.DeepSeq (NFData)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Prettyprinter

import Overeasy.EGraph
import Overeasy.Diff
import Overeasy.Assoc (assocPartialLookupByKey, assocPartialLookupByValue)
import Overeasy.Classes (Changed(..))
import Overeasy.EquivFind

import qualified IntLike.Map as ILM
import qualified IntLike.Set as ILS

data Arith =
    ArithPlus Arith Arith
  | ArithMinus Arith Arith
  | ArithTimes Arith Arith
  | ArithMod Arith Arith
  | ArithDiv Arith Arith
  | ArithTryDiv Arith Arith
  | ArithConst !Integer
  | ArithShiftL Arith !Integer
  | ArithShiftR Arith !Integer
  | ArithInvDiv Arith Arith Arith
  deriving stock (Ord, Eq, Show, Generic)
  deriving anyclass (Hashable, NFData)
data ArithF s =
    ArithPlusF s s
  | ArithMinusF s s
  | ArithTimesF s s
  | ArithModF s s
  | ArithDivF s s
  | ArithTryDivF s s
  | ArithConstF !Integer
  | ArithShiftLF s !Integer
  | ArithShiftRF s !Integer
  | ArithInvDivF s s s
  deriving (Functor, Foldable, Traversable)
data IfF s =
   IfB s s s | EqB s s
  deriving (Functor, Foldable, Traversable, Generic, Ord, Eq, Show)
  deriving anyclass (Hashable, NFData)
type instance Base Arith = ArithF
instance Recursive Arith where
    project (ArithPlus a b) = ArithPlusF a b
    project (ArithMinus a b) = ArithMinusF a b
    project (ArithMod a b) = ArithModF a b
    project (ArithDiv a b) = ArithDivF a b
    project (ArithTryDiv a b) = ArithTryDivF a b
    project (ArithTimes a b) = ArithTimesF a b
    project (ArithShiftL a n) = ArithShiftLF a n
    project (ArithShiftR a n) = ArithShiftRF a n
    project (ArithConst n) = ArithConstF n
    project (ArithInvDiv a b c) = ArithInvDivF a b c
instance Corecursive Arith where
    embed (ArithPlusF a b) = ArithPlus a b
    embed (ArithMinusF a b) = ArithMinus a b
    embed (ArithTimesF a b) = ArithTimes a b
    embed (ArithShiftLF a n) = ArithShiftL a n
    embed (ArithShiftRF a n) = ArithShiftR a n
    embed (ArithConstF n) = ArithConst n
    embed (ArithInvDivF a b c) = ArithInvDiv a b c
    embed (ArithModF a b) = ArithMod a b
    embed (ArithDivF a b) = ArithDiv a b
    embed (ArithTryDivF a b) = ArithTryDiv a b

-- makeBaseFunctor ''Arith
deriving stock instance Eq a => Eq (ArithF a)
deriving stock instance Ord a => Ord (ArithF a)
deriving stock instance Show a => Show (ArithF a)
deriving stock instance Generic (ArithF a)
deriving anyclass instance Hashable a => Hashable (ArithF a)
deriving anyclass instance NFData a => NFData (ArithF a)

mkPlus :: EClassId -> EClassId -> StateT Eg3 Maybe EClassId
mkPlus a b = do
    (_, c) <- egAddFlatTerm (inject $ ArithPlusF a b)
    (_, cma) <- egAddFlatTerm (inject $ ArithMinusF c a)
    (_, cmb) <- egAddFlatTerm (inject $ ArithMinusF c b)
    _ <- egMerge cma b
    _ <- egMerge cmb a
    pure c
mkDiv :: EClassId -> EClassId -> StateT Eg3 Maybe EClassId
mkDiv a b = do
    (_, c) <- egAddFlatTerm (inject $ ArithDivF a b)
    (_, a') <- egAddFlatTerm (inject $ ArithInvDivF c b a)
    _ <- egMerge a a'
    pure c
divTest :: Maybe Eg3
divTest  = flip execStateT egNew $ do
    l1 <- snd <$> egAddFlatTerm (inject $ Var 1)
    l2 <- snd <$> egAddFlatTerm (inject $ Var 2)
    _ <- egAddAnalysis l1 [injectAna (5...(10::Integer))]
    _ <- egAddAnalysis l2 [injectAna (1...(2::Integer))]
    _ <- mkDiv l1 l2
    egRebuild'
    pure ()
timesTest :: Maybe Eg3
timesTest  = flip execStateT egNew $ do
    l1 <- snd <$> egAddFlatTerm (inject $ Var 1)
    l2 <- snd <$> egAddFlatTerm (inject $ Var 2)
    _ <- egAddAnalysis l1 [injectAna (5...(10::Integer))]
    _ <- egAddAnalysis l2 [injectAna (0...(2::Integer))]
    _ <- mkTimes l1 l2
    egRebuild'
    pure ()
mkTimes :: EClassId -> EClassId -> StateT Eg3 Maybe EClassId
mkTimes a b = do
    (_, c) <- egAddFlatTerm (inject $ ArithTimesF a b)
    (_, cma) <- egAddFlatTerm (inject $ ArithTryDivF c a)
    (_, cmb) <- egAddFlatTerm (inject $ ArithTryDivF c b)
    _ <- egMerge cma b
    _ <- egMerge cmb a
    pure c
testStep :: Integer -> Integer -> Integer -> EClassId -> EClassId -> StateT Eg3 Maybe EClassId
testStep an bn cn constw z = do
    -- (_,z) <- egAddTerm (genFix $ ArithConst 0)
    (_, constan) <- egAddFlatTerm $ inject (ArithConstF an)
    (_, constbn) <- egAddFlatTerm $ inject (ArithConstF bn)
    (_, constcn) <- egAddFlatTerm $ inject (ArithConstF cn)
    (_, const26) <- egAddFlatTerm $ inject (ArithConstF 26)

    lhs <- mkDiv z constbn
    round26 <- mkTimes lhs const26
    rhs2 <- mkPlus constw round26
    rhs3 <- mkPlus constcn rhs2

    (_, mod26) <- egAddFlatTerm (inject $ ArithModF z const26)
    p <- mkPlus constan mod26
    -- (_, theTruth) <- egAddFlatTerm (inject $ IfB p constcn constw)
    (_, cond) <- egAddFlatTerm $ inject $  EqB p constw
    (_, out) <- egAddFlatTerm (inject $ IfB cond lhs rhs3)
    -- (_,o1) <- egAddFlatTerm (inject $ EqB c13 c1pc2)
    -- (_, o) <- egAddFlatTerm (inject $ IfB o1 c13 c1pc2)
    -- _ <- egRebuild'
    -- egCompact
    pure out


extractVars :: Eg3 -> [(Int, Range Integer)]
extractVars eg = fromJust $ flip evalStateT eg $ do
   let get1 i = do
        (_, cls) <- egAddFlatTerm (inject (Var i))
        EP (r, _) <- (egGetAnalysis cls)
        pure (i, r)
   traverse get1 [1..14]

newVars :: Int -> StateT Eg3 Maybe [EClassId]
newVars i = do
    let
      var1 i = do
        o <- fmap snd $ egAddFlatTerm (inject $ Var i)
        _ <- egAddAnalysis o [injectAna (1...(9::Integer))]
        pure o
    os <- (traverse var1 [1..i])
    -- _ <- egRebuild'
    -- egCompact
    pure os

lastAnaChanges :: EGraph d f -> ILM.IntLikeMap EClassId Epoch
lastAnaChanges g = ILM.fromListWith  max [(v, k) | (k, v) <- ILM.toList (egAnaTimestamps g)]

constants :: [(Integer, Integer, Integer)]
constants =
    [(12,1,7), (13,1,8), (13,1,10), (-2,26,4), (-10,26,4), (13,1,6),
     (-14,26,11), (-5,26,13), (15,1,1), (15,1,8), (-14,26,4), (10,1,13),
     (-14,26,4), (-5,26,14)]

-- inp = [1,1, 1,9, 1]
-- inp = [1, 7, 1, 9, 5, 9, 1, 3, 7, 7, 1, 2, 1, 3]
inp :: [Range Integer]
inp = []
-- inp = [7, 9, 1, 9, 7, 9, 1, 9, 9, 9, 3, 9, 8, 5]
mkAocStep :: Integral a => a -> ((a, a, a), a) -> a
mkAocStep  acc ((a, b, c), digit)
  | mod acc 26 + a == digit = div acc b
  | otherwise = 26 * (div acc  b) + c + digit
-- testDigits = scanl (mkAocStep) (0::Integer) (zip (constants) inp) 
--   where


egResolveUnsafe :: MonadState (EGraph d f) m =>
                         EClassId -> m EClassId
egResolveUnsafe s = do
    ef <- gets egEquivFind
    pure (efFindRootAll s ef)
mkInput :: StateT Eg3 Maybe (EClassId, [EClassId])
mkInput = do
    vars <- newVars (length constants)
    let
      go ((idx, (a,b,c)):xs) (var:vars) z = do
          o <- testStep a b c var z
          ov <- snd <$> egAddFlatTerm (inject (Var (100+idx)))
          _ <- egMerge o ov
          go xs vars o
      go [] [] z = pure z
      go _ _  _ = error "illegal"
    z0 <- fmap snd $ egAddFlatTerm (inject $ ArithConstF 0)
    o <- go (zip [0..] constants) vars z0
    o <- egResolveUnsafe o
    _ <- egMerge z0 o
    -- egMerge o z0
    -- egAddAnalysis o [injectAna (0...(9 :: Integer))]
    egRebuild'
    pure (o, vars)
diffFor :: [Range Integer] -> EDiff EP
diffFor inp = diff eg1 egr
  where
    ((_o, vars), eg1) = fromJust $ runStateT mkInput egNew
    (_, egr) = fromJust $ flip runStateT eg1 $ do
       forM_ (zip inp vars) $ \(r, x) -> egAddAnalysis x [injectAna r]
       egRebuild'
aocRiddle :: Eg3
aocRiddle = fromJust $ execStateT (search1[]) egNew

gamePlan :: [(EClassId, Eg3 -> [(Int, Int, Eg3)])]
gamePlan = [(EClassId cls, stepFor (EClassId cls))|  cls <- [0..13]]
stepFor :: EClassId -> Eg3 -> [(Int, Int, Eg3)]
stepFor ec eg = map fixer $ flip runStateT eg $ do
    i <- asum (map pure [1..9])
    ec <- egResolveUnsafe ec
    _ <- egAddAnalysis ec [injectAna (i...(i::Integer))]
    egRebuild'
    pure i
  where 
    fixer :: (Integer, s) -> (Int, Int, s)
    fixer (a,b) = (fromIntegral a, (14 - idx)^(10::Int) * (fromIntegral a),b)
    EClassId idx = ec
search1 :: [Range Integer] -> StateT Eg3 Maybe ()
search1 sinp = do
   (_, (ls)) <- mkInput
   egRebuild'
   forM_ (zip sinp ls) $ \(r, x) -> egAddAnalysis x [injectAna r]
   egRebuild'


testEg7 :: Eg3
testEg7 = fromJust $ flip execStateT egNew $ do
    (_,_c13) <- egAddTerm (genFix $ ArithConst 3)
    (_,_c1pc2) <- egAddTerm (genFix $ ArithMod (ArithConst 7) (ArithConst 3))
    -- (_,o1) <- egAddFlatTerm (inject $ EqB c13 c1pc2)
    -- (_, o) <- egAddFlatTerm (inject $ IfB o1 c13 c1pc2)
    egRebuild'

instance  Eq a => (PSemigroup (Maybe a)) where
   Nothing <?> r = Just r
   l <?> Nothing = Just l
   (Just a) <?> (Just b)
     | a == b = Just (Just a)
   _ <?> _ = Nothing

instance Pretty f => Pretty (IfF f) where
    pretty (IfB a b c) = "if (" <> pretty a <> ") then (" <> pretty b <> ") else (" <> pretty c <> ")"
    pretty (EqB a b) = pretty a <+> "==" <+> pretty b
instance Pretty EP where
    pretty = pretty . toTup
instance  Eq a => (PLattice (Maybe a)) where
   Nothing <||> _ = IsTop
   _ <||> Nothing = IsTop
   Just l <||> Just r
     | l == r = Is (Just l)
     | otherwise = IsBot
instance  Eq a => (PMonoid (Maybe a)) where
   pempty = Nothing
instance Eq a => RegularSemigroup (Maybe a) where
   a ==>? b
     | a == b = Nothing
     | otherwise = Just b

newtype EP = EP (Range Integer,Maybe Bool)
  deriving newtype (Eq, Ord, Show, PSemigroup, PMonoid, PLattice, EAnalysisMerge, InjectAna (Range Integer), InjectAna (Maybe Bool), Lattice, RegularSemigroup)
instance Eq a => Lattice (Maybe a) where
    lunion = (<?>)
    lintersect a b = case (<||>) a  b of
        IsTop -> Nothing
        Is x -> Just x
        IsBot -> error "union on bot"
    ltop = Nothing

instance Eq a => Diff (Maybe a) (Maybe a) where
    diff a b
      | a == b = Nothing
      | otherwise = b
instance Diff EP EP where
    diff (EP l) (EP r) = EP (diff l r)
instance Eq a => DiffApply (Maybe a) (Maybe a) where
    applyDiff = (<?>)
instance DiffApply EP EP where
    applyDiff (EP l) (EP r) = fmap EP (applyDiff l r)
toTup :: EP -> (Range Integer, Maybe Bool)
toTup (EP a) = a
fromTup :: (Range Integer, Maybe Bool) -> EP
fromTup (a) = EP a
instance EAnalysis (Maybe Bool) BoolF where
    eaMake TrueF = Just True
    eaMake FalseF = Just True
    eHook _ = pure ()
instance EAnalysis (Maybe Bool) ArithF where
    eaMake _ = top
    eHook _ = pure ()
instance EAnalysis EP ArithF where
    eaMake f
      | isBot (fst out)  = (fromTup out)
      | otherwise = fromTup out
      where out =  eaMake (fmap toTup f)
    eHook cls = do
        EP (l, _) <- eaClassData cls
        when (isBot l) (eaHalt)
        case toPoint l of 
            Just o -> do
              t <- eaAddTerm (ArithConstF o)
              eaMerge cls t
            Nothing -> pure ()
        pure ()
         -- unFirstHook (eHook  cls)

instance EAnalysis EP BoolF where
    eaMake f = fromTup (eaMake $ fmap toTup f)
    eHook _ = pure ()
instance  EAnalysis EP IfF where
    eaMake (EqB (EP (r1, _)) (EP (r2, _)))
      | Just v1 <- toPoint r1
      , Just v2 <- toPoint r2
      , v1 == v2 = EP (top, Just True)
      | o == Just LT || o == Just GT = EP (top, (Just False))
      | otherwise = top
      where o = compareP r1 r2
    eaMake (IfB (EP (_, (Just p))) l r) = if p then l else r
    eaMake (IfB _ l r) = case l <||> r of
       IsBot -> EP (bot, top)
       Is a -> a
       IsTop -> top
    eHook cls = do
        EP (l, _) <- eaClassData cls
        when (isBot l) (eaHalt)
        terms <- eaClassTerms cls
        forM_  terms $ \t -> eHook1 cls t
        pure ()
    eHook1 cls (EqB a b) = do
        EP (_, p) <- eaClassData cls
        case p of 
            Just True -> do
              eaMerge a b
            Just False -> do
              when (a == b) eaHalt
            Nothing -> pure ()
        pure ()
    eHook1 cls (IfB a b c) = do
        EP (_, aD) <- eaClassData a
        case aD of
            Just True -> eaMerge cls b
            Just False -> eaMerge cls c
            Nothing -> do
              EP outD <- eaClassData cls
              EP bD <- eaClassData b
              EP cD <- eaClassData c
              -- traceM $ pshow (cls, a,(b,c)) <> " " <> pshow ( outD,(), (bD, cD))
              case outD <?> bD of
                  Nothing -> do
                      -- traceM "doL"
                      eaRefineAnalysis a (injectAna (Just False))
                      eaMerge cls c
                  Just _ ->  pure ()
              case outD <?> cD of
                  Nothing -> do
                      -- eaRefineAnalysis a (injectAna (Just True))
                      -- traceM "doR"
                      eaMerge cls b
                  Just _ -> pure ()
type Eg3 = EGraph EP (ArithF :+: BoolF :+: IfF :+: VarF)

instance EAnalysisMerge (Maybe Bool) where
    eaJoin l rs = guardAllSame $ catMaybes (l:rs)
      where
        guardAllSame (x:xs)
          | all (==x) xs = (Just x)
          | otherwise = Nothing
        guardAllSame [] = Nothing






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

instance Semigroup (Range Integer) where
    a <> b = a &&& b

type Eg = EGraph (Range Integer) (ArithF :+: BoolF)

instance Pretty ENodeId where
    pretty (ENodeId i) = "n" <> pretty i
instance Pretty EClassId where
    pretty (EClassId i) = "v" <> pretty i
instance Pretty x => Pretty (ArithF x) where
    pretty = \case
        ArithPlusF a b -> pretty a <+> "+" <+> pretty b
        ArithMinusF a b -> pretty a <+> "-" <+> pretty b
        ArithTimesF a b -> pretty a <+> "*" <+> pretty b
        ArithModF a b -> pretty a <+> "%" <+> pretty b
        ArithDivF a b -> pretty a <+> "/" <+> pretty b
        ArithTryDivF a b -> pretty a <+> "/?" <+> pretty b
        ArithShiftLF a l -> pretty a <+> "<<" <+> pretty l
        ArithShiftRF a l -> pretty a <+> ">>" <+> pretty l
        ArithInvDivF a l _ -> pretty a <+> "/inv" <+> pretty l
        ArithConstF c -> pretty c
instance Pretty Arith where
    pretty = pretty . show

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
sudokuExample :: M.Map Int Int
sudokuExample = toIndex [
    "1  |  7| 9 ",
    " 3 | 2 |  8",
    "  9|6  |5  ",
    -------------
    "  5|3  |9  ",
    " 1 | 8 |  2",
    "6  |  4|   ",
    -------------
    "3  |   | 1 ",
    " 4 |   |  7",
    "  7|   |3  "
 ]
 where
   toIndex = M.fromList . mapMaybe2 toDig . zip [0..] . filter (/= '|') . concat
   toDig ' ' = Nothing
   toDig c = Just (fromEnum c - fromEnum '0')
   mapMaybe2 f = mapMaybe (traverse f)

printSudoku :: Eg2 -> IO ()
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
    eHook1 c (L1 a)= unLeftHook (eHook1 c a)
    eHook1 c (R1 a)= unRightHook (eHook1 c a)
      -- unLeftHook (eHook c)
      -- unRightHook (eHook c)

instance  (EAnalysisMerge a, PMonoid a) => EAnalysis a VarF where
    eaMake _ = pempty
    eHook _ = pure ()
instance  (Pretty a, Num a, Integral a, Bounded a, Enum a, Ord a) => EAnalysis (FiniteDomain a) ArithF where
    eaMake = \case
        ArithPlusF a b -> a + b
        ArithMinusF a b -> a - b
        ArithTimesF a b -> a * b
        ArithModF a b -> mod a b
        ArithDivF a b -> div a b
        ArithTryDivF a b -> let out = div a b in if isBot out then top else out
        ArithConstF c -> fromIntegral c
        ArithShiftLF a l -> a * 2^l
        ArithShiftRF a l -> a `div` 2^l
        ArithInvDivF _ _ _ -> undefined --- (foldr1 (|||) [c + domSingleton i | i <- [fromIntegral a..fromIntegral b]])
    eHook _ = pure ()
instance  EAnalysis (Range Integer) (FiniteDomainF a) where
    eaMake _ = pempty
    eHook _ = pure ()
instance  (Pretty a, Hashable a, Ord a, Enum a, Bounded a) => EAnalysis (FiniteDomain a) (FiniteDomainF a) where
    eaMake (DifferentFrom ls) = F.foldl' domDifference universe ls-- dumbArcConsistent pempty ls
    eaMake (FDLiteral l) = domSingleton l
    eHook cls = do
        dat <- eaClassData cls
        when (isBot dat) eaHalt
        case domPoint dat of 
            Just o -> do
              t <- eaAddTerm (FDLiteral o)
              eaMerge cls t
            Nothing -> pure ()

instance  EAnalysis (Range Integer) ArithF where
    eaMake = \case
        ArithPlusF a b -> a + b
        ArithMinusF a b -> a - b
        ArithTimesF a b -> a * b
        ArithModF a b -> mod a b
        ArithDivF a b -> div a b
        ArithTryDivF a b -> let out = div a b in if isBot out then top else out
        ArithConstF c -> fromIntegral c
        ArithShiftLF a l -> a * 2^l
        ArithShiftRF a l -> a `div` 2^l
        ArithInvDivF aDivB b _ -> (aDivB + (0||| signum b)) * b
          where
    eHook cls = do
        dat <- eaClassData cls
        when (isBot dat) (eaHalt)
        case toPoint dat of 
            Just o -> do
              t <- eaAddTerm (ArithConstF o)
              eaMerge cls t
            Nothing -> pure ()
instance  EAnalysisMerge (Range Integer)  where
    eaJoin l rs
       | isBot out = out
       | otherwise = out
      where
        out = foldr (&&&) l rs
instance  EAnalysisIntersection (Range Integer)  where
    eaMeet l rs =  (|||) l rs
instance  (BoundedLattice a, BoundedLattice b) => EAnalysisIntersection (a,b)  where
    eaMeet (la, lb) (ra, rb) = (la ||| ra, lb ||| rb)  
instance  (Pretty a, Bounded a, Enum a, Ord a) => EAnalysisMerge (FiniteDomain a)  where
    eaJoin l rs = foldr (&&&) l rs

instance  (Bounded a, Enum a, Ord a) => EAnalysisIntersection (FiniteDomain a)  where
    eaMeet l rs =  (|||) l rs

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
instance EAnalysis (Range Integer) BoolF where
   eaMake _ = pempty

testEg :: Maybe Eg
testEg = flip execStateT egNew $ do
    (_,_c1pc2) <- egAddTerm (genFix $ ArithPlus (ArithConst 1) (ArithConst 2))
    -- egMerge c1pc2 c3
    egRebuild'

class GeneralizeFix f g where
    genFix :: f -> Fix g
instance (Recursive t, Inject (Base t) g) => GeneralizeFix t g where
    genFix = Fix . inject . fmap genFix . project

testEg2, testEg3 :: Eg
testEg2 = fromJust $ flip execStateT egNew $ do
    (_,_c13) <- egAddTerm (genFix $ ArithConst 3)
    (_,_c1pc2) <- egAddTerm (genFix $ ArithPlus (ArithConst 1) (ArithConst 2))

    -- egMerge c13 c3
    egRebuild'

testEg3 = fromJust $ flip execStateT testEg2 $ do
    (_,c13) <- egAddTerm (genFix $ ArithConst 1)
    _ <- egAddAnalysis c13 [1...1]
--     (_,c13) <- egAddTerm (ArithInvDivF 1 3)
--     egAddAnalysis c13 [2...4]
    -- (_,c13) <- egAddTerm (genFix $ ArithConst 3)
    -- (_,c1pc2) <- egAddTerm (genFix $ ArithPlus (ArithConst 1) (ArithConst 2))
    -- egMerge c13 c1pc2
    egRebuild'
    pure ()

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
mkVar :: (EAnalysisHook m (Range Integer, FiniteDomain SudokuNum)
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
    egRebuild'
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
    _ <- egAddAnalysis v2 [(pempty, FD $ BV.fromList [2])]
    _ <- egAddAnalysis v3 [(pempty, FD $ BV.fromList [3])]
    _ <- egMerge v2 v3
    _ <- egRebuild'
    egCompact
    pure ()
testEg6 :: Eg2
testEg6 = fromJust $ flip execStateT egNew $ do
    v1 <- mkVar 62
    egAddAnalysis v1 [(pempty, FD $ BV.fromList [2])]

egUnion :: (Diff d i, Eq i, Pretty i, EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> EGraph d f -> Maybe (EGraph d f)
egUnion l r = (rebuildInPlace . fst) =<< egUnionGraphs l r

type Eg2 = EGraph (Range Integer, FiniteDomain SudokuNum) (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
allDifferent :: (EAnalysisHook m (Range Integer, FiniteDomain SudokuNum)
                          (ArithF :+: (FiniteDomainF SudokuNum :+: VarF)), MonadState Eg2 m) => [EClassId] -> m ()
allDifferent ls = do
   forM_ (slices [] ls) $ \(x,xs) -> do
       (_, cls) <- egAddFlatTerm (R1 $ L1 (DifferentFrom xs))
       egMerge x cls
  where
    slices acc (x:xs) = (x,acc<>xs) : slices (x:acc) xs
    slices _ [] = []

rebuildInPlace :: (Diff d i, Pretty i, Eq i, EAnalysis d f, Hashable (f EClassId), Traversable f) => EGraph d f -> Maybe (EGraph d f)
rebuildInPlace = execStateT (egRebuild')



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

class InjectAna a b where
   injectAna :: a -> b
instance PMonoid b => InjectAna a (a,b) where
    injectAna a = (a, pempty)
instance PMonoid b => InjectAna a (b,a) where
    injectAna a = (pempty, a)
instance (Diff o i, Pretty i, Eq i, Inject BoolF f, EAnalysisIntersection o, Show (f EClassId), Traversable f, Eq o, EAnalysis o f,  Hashable (f EClassId), Show o) => IsLit (EClassId, f EClassId) (EGraph o f) where
   isL (v, e) = fromJust $ flip execStateT egNew $  do
       (_,t) <- egAddFlatTerm e
       egMerge v t >>= \case
          Nothing -> error "isL var not found failed"
          Just c -> when (c == ChangedYes) (void egRebuild')
   notL _  = pempty -- fromJust $ flip execStateT egNew $  do
       -- (_,t) <- egAddFlatTerm (inject FalseF)
       -- egMerge (EClassId v) t >>= \case
       --    Nothing -> error "notL var not found failed"
       --    Just c -> when (c == ChangedYes) (void egRebuild)
   evalVar (v, f) e 
     | trueNode == Just vRoot = Just True
     | otherwise = Nothing
     where
      trueNode = egFindNode f e
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
                    Just _ -> egRebuild'
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

genSplits :: (Ord (f EClassId), AnaSplits f o) => EGraph o f -> [(EClassId, S.Set (f EClassId))]
genSplits eg = sortBy theOrd [ (c, x) | (c, ec) <- ILM.toList (egClassMap eg), (x:_) <- [sortOn S.size $ anaSplits (eciData ec)]]
   where theOrd = comparing (S.size . snd) <> comparing snd

trySplit :: (Ord (f EClassId), AnaSplits f d, EAnalysis d f, Diff d i, Pretty i, Traversable f, Hashable (f EClassId), Eq i) => Int -> EGraph d f -> [EGraph d f]
trySplit idx eg = (catMaybes [ setVal c s eg  | s <- S.toList ss ])
  where
    (c, ss) = genSplits eg !! idx





mergeDiffsN :: Lattice d => [d] -> d
mergeDiffsN [] = ltop
mergeDiffsN (l:ls) = foldr (\x y -> fromJust (lintersect x y)) l ls

setVal :: (EAnalysis d f, MonadPlus m, Diff d i, Pretty i, Traversable f, Hashable (f EClassId), Eq i) =>
                EClassId -> f EClassId -> EGraph d f -> m (EGraph d f)
setVal c s e = flip execStateT e (setValM c s)
setValM :: (Pretty i, Diff d i, MonadState (EGraph d f) m,
                  EAnalysisHook m d f, EAnalysis d f, Traversable f,
                  Hashable (f EClassId), Eq i) =>
                 EClassId -> f EClassId -> m ()
setValM c s =  do
  (_, t) <- egAddFlatTerm s
  m <- egMerge t c
  case m of
    Nothing -> error "setVal: merge failed"
    Just _ -> egRebuild'
  pure ()

instance (Pretty d) => Pretty (EDiff d) where
    pretty (EDiff _ (Merges a) (MapDiff b)) = pretty (ILM.toList b) <> pretty (map (second ILS.toList) $ ILM.toList (efFwd a))

-- tSplits eg0 = take 14 $ (genSplits eg0)

instance (Lattice d) => PSemigroup (EDiff d) where
    (<?>) = lunion
instance (Lattice d, Pretty d) => PLattice (EDiff d) where
    (<||>) a b = case lintersect a b of
        Just x -> Is x
        Nothing -> IsTop
instance (Lattice d, Pretty d) => PMonoid (EDiff d) where
    pempty = ltop

listDom :: [SudokuNum] -> FiniteDomain SudokuNum
listDom = FD . BV.fromList 


valOf :: DD v a -> Maybe a
valOf (If _ v _ _) = Just v
valOf (Iff s) = Just s
valOf _ = Nothing


  
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
instance BoundedLattice a => PMonoid (Neg a) where
    pempty = Neg bot
instance (Enum a, Bounded a, Ord a) => Lattice (FiniteDomain a) where
    lintersect a b = case (<||>) a  b of
        IsTop -> Nothing
        Is x -> Just x
        IsBot -> error "union on bot"
    lunion = (<?>)
    ltop = pempty
instance (Diff (a,b) (c,d), DiffApply a c, DiffApply b d) => DiffApply (a,b) (c,d) where
    applyDiff (a,b) (c,d) = (,) <$> applyDiff a c <*>  applyDiff b d
instance (Enum a, Bounded a, Ord a) => Diff (FiniteDomain a) (Neg (FiniteDomain a)) where
    diff (FD a) (FD b) = Neg $ FD (BV.difference a b)
instance (Diff a ()) => DiffApply a () where
    applyDiff () a  = Just a
instance Pretty a => Pretty (Neg a) where
    pretty (Neg a) = "-" <> pretty a
instance (Enum a, Bounded a, Ord a) => DiffApply (FiniteDomain a) (Neg (FiniteDomain a))where
    applyDiff (Neg (FD b)) (FD a) 
      | out == BV.empty = Nothing
      | otherwise = Just $ FD out
      where out = BV.difference a b
instance (Show a, Ord a, Num a) => DiffApply (Range a) (Range a) where
    applyDiff l r = l <?> r
instance (Show a, Ord a, Num a) => Diff (Range a) (Range a) where
    diff a b
      -- | trace ("rdiff " <> show a <> " " <> show b) False = undefined
      | a == b = top
      | otherwise = b -- = (==>)
instance (Ord a, Num a) => Lattice (Range a) where
    lintersect a b = case (<||>) a  b of
        IsTop -> Nothing
        Is x -> Just x
        IsBot -> error "union on bot"
    lunion = (<?>)
    ltop = pempty
instance Lattice () where
    lunion _ _ = Just ()
    lintersect _ _ = Just ()
    ltop = pempty
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
instance PMonoid () where
    pempty = ()
instance PSemigroup () where
    (<?>) _ _ = Just ()


collectNew :: (Traversable f, EAnalysis o f, Hashable (f EClassId), RegularSemigroup o) => EGraph o f -> EGraph o f -> [(EClassId, o, o)]
collectNew l r = [ (cid, dl,  o) | (cid, cr) <- ILM.toList (egClassMap r), let dl = lData cid, Just o <- [dl ==>? eciData cr]]
  where
    lData c = eciData $ fromJust $ ILM.lookup (ILM.partialLookup c m) (egClassMap l)
    (_, m) = fromJust (egUnionGraphs l r)

egRebuild' :: (HasCallStack, Pretty i, Diff d i, Eq i, MonadState (EGraph d f) m, EAnalysisHook m d f, EAnalysis d f, Traversable f, Hashable (f EClassId))  => m ()
egRebuild' = do
    _ <- egRebuild
    egCompact
    -- pre <- gets id
    -- modify $ \s -> s { egAnaWorklist = ILS.fromList (ILM.keys (egHashCons s)) }
    -- _ <- egRebuild
    -- egCompact
    -- post <- gets id
    -- let d =  diff pre post 
    -- if isNonEmpty d
    -- then error ("Missed analysis: " <> pshow d)
    -- else pure ()
  where
    isNonEmpty (EDiff _ a (MapDiff b)) = a /= ltop || not (ILM.null b)


-- used for clustering
-- instance {-# OVERLAPPABLE #-}(DecideIfEdgeLife f a, DecideIfEdgeLife g a) => DecideIfEdgeLife (f :+: g) a where
--     decideIfEdgeLife d (L1 x) = L1 (decideIfEdgeLife d x)
--     decideIfEdgeLife d (R1 y) = R1 (decideIfEdgeLife d y)
-- instance {-# INCOHERENT #-} (Traversable f, DecideIfEdgeLife f a, DecideIfEdgeLife f b) => DecideIfEdgeLife f (a,b) where
--     decideIfEdgeLife d x = zipFoldableWith (||) l r
--       where
--         l = decideIfEdgeLife (fst d) (fmap fst x)
--         r = decideIfEdgeLife (snd d) (fmap snd x)
-- instance {-#OVERLAPPING #-} (Pretty s)=> DecideIfEdgeLife (FiniteDomainF s) (FiniteDomain s) where
--     decideIfEdgeLife (FD s) a = o
--       where
--        o 
--          | BV.size s == 1 = False <$ a
--          | otherwise = fmap (\(FD s) -> BV.size s /= 1) a
-- instance {-# OVERLAPPABLE #-}Functor a => DecideIfEdgeLife a (FiniteDomain s) where
--     decideIfEdgeLife _ a = False <$ a
-- instance {-#OVERLAPPING #-}DecideIfEdgeLife ArithF (Range Integer) where
--     decideIfEdgeLife _ a = fmap (isNothing . toPoint) a
-- instance {-# OVERLAPPABLE #-}DecideIfEdgeLife ArithF a where
--     decideIfEdgeLife _ a = False <$ a
-- instance {-# OVERLAPPABLE #-}Functor a => DecideIfEdgeLife a (Range Integer) where
--     decideIfEdgeLife _ a = False <$ a
