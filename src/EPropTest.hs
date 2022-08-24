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
-- | Use E-Graph propagation to build a simple solver, and solve AoC 2021 day 24 with it
module EPropTest where

import Control.Applicative (asum)
import Control.Monad.State hiding (StateT, modify', execStateT, runStateT, evalStateT)

import Control.Monad.Trans.State.Strict (StateT, execStateT, runStateT, evalStateT)
import Range
import FiniteDomains
import Types
import GHC.Generics ((:+:)(..))
import Data.Maybe (fromJust, catMaybes)

import Control.DeepSeq (NFData)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Prettyprinter

import Overeasy.EGraph
import Overeasy.Diff
import Overeasy.EquivFind

import Boilerplate

-- We require some syntax types to build our terms:
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
  deriving (Functor, Foldable, Traversable, Generic, Ord, Eq, Show, Hashable, NFData)
data IfF s = IfB s s s | EqB s s
  deriving (Functor, Foldable, Traversable, Generic, Ord, Eq, Show)
  deriving anyclass (Hashable, NFData)
data BoolF a = TrueF | FalseF
  deriving stock (Ord, Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)
data VarF a = Var Int
  deriving stock (Ord, Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

-- Our abstract domain supports bools and integer ranges
newtype EP = EP (Range Integer,Maybe Bool)
  deriving newtype (Eq, Ord, Show, PSemigroup, PMonoid, PLattice, EAnalysisMerge, InjectAna (Range Integer), InjectAna (Maybe Bool), Lattice, RegularSemigroup)

-- The E-Graph type we use
type Eg3 = EGraph EP (ArithF :+: BoolF :+: IfF :+: VarF)

instance Diff EP EP where
    diff (EP l) (EP r) = EP (diff l r)
instance DiffApply EP EP where
    applyDiff (EP l) (EP r) = fmap EP (applyDiff l r)

-- And some propagation rules for math.
-- eaMake computes the abstract meaning of a term from the meaning of its children
-- eHook allows arbitrary rewrites of the E-Graph when the meaning is updated
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
    eHook cls = do
        dat <- eaClassData cls
        when (isBot dat) (eaHalt)
        case toPoint dat of 
            Just o -> do
              t <- eaAddTerm (ArithConstF o)
              eaMerge cls t
            Nothing -> pure ()

-- To propagate bidirectionally, we also insert new terms for the backwards directions
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
    (_, cond) <- egAddFlatTerm $ inject $  EqB p constw
    (_, out) <- egAddFlatTerm (inject $ IfB cond lhs rhs3)
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
    pure os

-- Build the problem instance
constants :: [(Integer, Integer, Integer)]
constants =
    [(12,1,7), (13,1,8), (13,1,10), (-2,26,4), (-10,26,4), (13,1,6),
     (-14,26,11), (-5,26,13), (15,1,1), (15,1,8), (-14,26,4), (10,1,13),
     (-14,26,4), (-5,26,14)]

egResolveUnsafe :: MonadState (EGraph d f) m => EClassId -> m EClassId
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
    egRebuild'
    pure (o, vars)
aocRiddle :: Eg3
aocRiddle = fromJust $ execStateT (mkInput) egNew

-- Build the decision tree branching
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

toTup :: EP -> (Range Integer, Maybe Bool)
toTup (EP a) = a
fromTup :: (Range Integer, Maybe Bool) -> EP
fromTup (a) = EP a

-- The remaining propagation rules, would be more concise with a rewrite rule DSL
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
              case outD <?> bD of
                  Nothing -> do
                      eaRefineAnalysis a (injectAna (Just False))
                      eaMerge cls c
                  Just _ ->  pure ()
              case outD <?> cD of
                  Nothing -> do
                      eaMerge cls b
                  Just _ -> pure ()
instance  (EAnalysisMerge a, PMonoid a) => EAnalysis a VarF where
    eaMake _ = pempty
    eHook _ = pure ()
instance EAnalysis (Range Integer) BoolF where
   eaMake _ = pempty
instance EAnalysisMerge (Maybe Bool) where
    eaJoin l rs = guardAllSame $ catMaybes (l:rs)
      where
        guardAllSame (x:xs)
          | all (==x) xs = (Just x)
          | otherwise = Nothing
        guardAllSame [] = Nothing
instance  EAnalysisMerge (Range Integer)  where
    eaJoin l rs
       | isBot out = out
       | otherwise = out
      where
        out = foldr (&&&) l rs
instance  EAnalysisIntersection (Range Integer)  where
    eaMeet l rs =  (|||) l rs

-- pretty printing
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
instance Pretty (VarF a) where
    pretty (Var xs) = "l" <> pretty xs
instance Pretty (BoolF a) where
   pretty TrueF = "True"
   pretty FalseF = "False"
instance Pretty f => Pretty (IfF f) where
    pretty (IfB a b c) = "if (" <> pretty a <> ") then (" <> pretty b <> ") else (" <> pretty c <> ")"
    pretty (EqB a b) = pretty a <+> "==" <+> pretty b
instance Pretty EP where
    pretty = pretty . toTup
