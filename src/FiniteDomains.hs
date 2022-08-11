{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingVia #-}
-- | Finite domain abstract domain
-- join {1,2,3} {3,4} = {3}
-- Should definitely use bitsets instead of patricia trees
module FiniteDomains where

import qualified Data.BitVector as S
import Types
import Test.QuickCheck
    ( Testable(property), Property, quickCheckAll )
import Propagator
import Control.Monad.State
import Data.Data
import Control.Monad.Except
import Data.List (transpose, foldl')
import qualified Data.List as L
import Data.Ord (comparing)
import qualified Data.Map as M
import Debug.Trace (traceM)
import Data.Char (digitToInt)
import GHC.Generics (Generic)
import Data.GridPrint
import Data.Hashable 
import Data.Coerce (coerce)

import Data.Maybe (listToMaybe)


-- allDiffProp :: forall a m s0. (Ord a, MonadState s0 m, HasType (PropEnv (FiniteDomain a)) s0, Show a, Typeable a, Bounded a, Enum a) => AllDifferent -> AProp AllDifferent m s0
-- allDiffProp a = toRule $ mapM_ (uncurry (propagate1 @a)) (splits mempty a.vars)
--   where
--     splits _ [] = []
--     splits l (r:rs) = (r, l <> S.fromList rs) : splits (S.insert r l) rs

-- propagate1 :: forall a m. (MonadProp (FiniteDomain a) m, Ord a, Bounded a, Enum a) => Var -> S.Set Var -> m ()
-- propagate1 v os = do
--   a <- ev @(FiniteDomain a) v
--   case S.toList a.members of
--     [x] -> mapM_ (outOver  @(FiniteDomain a) "allDiff" universe (delDomain x))  os
--     [] -> throwError (Just (S.singleton v))
--     _ -> pure ()


domDifference :: Ord a => FiniteDomain a -> FiniteDomain a -> FiniteDomain a
domDifference a b 
  | S.size b.members == 1 = FD (S.difference (a.members) (b.members))
  | otherwise = a


dumbArcConsistent :: (Enum a, Bounded a, Ord a) => FiniteDomain a -> [FiniteDomain a] -> FiniteDomain a
dumbArcConsistent (FD l) ls0 = FD (S.filterS handle1 (S.difference l triv))
  where
    triv = foldr S.union S.empty $ filter (\x -> S.size x == 1) $ coerce ls0
    handle1 s = dumbSolver (map (S.delete s . members) ls0)
dumbSolver :: (Enum a, Bounded a, Ord a) => [S.BitArray a] -> Bool
dumbSolver = go
  where
     go [] = True
     go xs = any (\n' -> go (map (S.delete n') xs')) ns
       where
        (n, xs') = pickMinBy S.size xs
        ns = S.toList n
     pickMinBy f ls = (m, L.delete m ls)
       where m = L.minimumBy (comparing f) ls
-- dumbRemainder :: Ord a => FiniteDomain a ->  [FiniteDomain a] -> FiniteDomain a
-- dumbRemainder (FD a) ls = 

domPoint :: (Enum a, Bounded a) => FiniteDomain a -> Maybe a
domPoint (FD a) = case (S.toList a) of
  [x] -> Just x
  _ -> Nothing


remainder :: (Ord a, Bounded a, Enum a) => [FiniteDomain a] -> FiniteDomain a
remainder = foldl' (domDifference) universe

delDomain :: (Enum a) => a -> FiniteDomain a -> FiniteDomain a
delDomain v fd = FD outp
  where outp = S.delete v fd.members
domSingleton :: (Enum a, Bounded a) => a -> FiniteDomain a
domSingleton v = FD (S.singleton v)

newtype FiniteDomain a = FD { members :: S.BitArray a }
  deriving (Eq, Ord, Show, Typeable, Generic)
instance Hashable a => Hashable (FiniteDomain a)

-- fdMin :: Ord a => FiniteDomain a -> a
-- fdMin (FD s) = S.findMin s

-- fdMax :: Ord a => FiniteDomain a -> a
-- fdMax (FD s) = S.findMin s

newtype SudokuNum = SD { digit :: Int}
  deriving (Num, Real, Integral, Eq, Ord, Show, Enum, Hashable) via Int

liftDom2 :: (Enum a, Bounded a, Ord a) => (a -> a -> a) -> FiniteDomain a -> FiniteDomain a -> FiniteDomain a
liftDom2 f (FD a) (FD b) = FD (S.fromList [o| x <- S.toList a, y <- S.toList b, let o = f x y, inBound o])
  where inBound x = x >= minBound && x <= maxBound
liftDom :: (Enum a, Bounded a, Ord a) => (a -> a) -> FiniteDomain a -> FiniteDomain a
liftDom f (FD a) = FD (S.filterS inBound $ S.mapS f a)
  where inBound x = x >= minBound && x <= maxBound
instance (Enum a, Bounded a, Ord a, Num a) => Real (FiniteDomain a) where
    toRational = undefined
instance (Enum a, Bounded a, Ord a, Num a) => Num (FiniteDomain a) where
    fromInteger = domSingleton . fromInteger
    (+) = liftDom2 (+)
    (*) = liftDom2 (*)
    (-) = liftDom2 (-)
    abs = liftDom abs
    signum = liftDom signum
    negate = liftDom negate
instance Enum (FiniteDomain a) where
   toEnum = undefined
   fromEnum = undefined
    
instance (Enum a, Bounded a, Ord a, Integral a) => Integral (FiniteDomain a) where
    quot = liftDom2 quot
    rem = liftDom2 rem
    div = liftDom2 div
    mod = liftDom2 mod
    toInteger a = case (domPoint a) of
      Just x -> toInteger x
      Nothing -> error "Illegal toInteger"

instance Bounded SudokuNum where
  minBound = SD 0
  maxBound = SD (cellWidth^(2::Int)-1)
class Universe a where
    universe :: a
instance (Ord a, Bounded a, Enum a) => Universe (FiniteDomain a) where
    universe = FD $ S.fromList [minBound..maxBound]
instance (Ord a) => PContains (FiniteDomain a) where
  containment (FD l) (FD r)
      | l == r = Just EQ
      | l `S.isSubsetOf` r = Just LT
      | r `S.isSubsetOf` l = Just GT
      | otherwise = Nothing

instance (Ord a) => PSemigroup (FiniteDomain a) where
  
  (<?>) (FD a) (FD b)
    | S.null intersect = Nothing
    | otherwise = Just $ FD intersect
    where intersect = S.intersection a b
instance (Enum a, Bounded a, Ord a) => PLattice (FiniteDomain a) where
  (<||>) (FD a) (FD b)
    | isTop out = IsTop
    | otherwise = Is out
   where out = FD $ S.union a b

isTop :: forall a. (Enum a, Bounded a, Ord a) => FiniteDomain a -> Bool
isTop (FD a) = 1+fromEnum (maxBound :: a) - fromEnum (minBound :: a) == S.size a

instance (Bounded a, Enum a, Ord a) => RegularSemigroup (FiniteDomain a) where
  FD a ==>? FD b
    | isTop out = Nothing -- isBot FD a || a == b || top ==  b = Nothing
    | otherwise = Just out
    where out = FD (b `S.union` S.difference ((universe :: FiniteDomain a).members)  a)
-- Just b -- 
instance (Bounded a, Enum a, Ord a) => PMonoid (FiniteDomain a) where
  pempty = universe
instance (Bounded a, Enum a, Ord a) => BoundedLattice (FiniteDomain a) where
  bot = FD S.empty
  isBot (FD a) = S.null a

ft :: [Int] -> FiniteDomain SudokuNum
ft = FD . S.fromList . map (SD . succ . (`mod` cellWidth))

newtype AllDifferentE a = AllDifferent { vars :: [a] }
  deriving (Eq, Ord, Show, Foldable, Functor)
type AllDifferent = AllDifferentE Var


-- data ADTest = ADTest { testBool :: (PropEnv (Val Bool)), testEnv :: (PropEnv (FiniteDomain SudokuNum)), testAD :: (S.Set AllDifferent) }
--   deriving (Eq, Ord, Show, Generic)

-- instance (MonadState ADTest m) => PropsFor m ADTest  where
--   theProps = do
--      dirtNums <- popDirty @(FiniteDomain SudokuNum)
--      onStruct @(S.Set AllDifferent) dirtNums (allDiffProp @SudokuNum)
--      pure $ not $ S.null dirtNums


printCell :: FiniteDomain SudokuNum -> Grid
printCell fd = box $ map hsep $ chunksOf (cellWidth) $ [ if S.member (SD $ d-1) fd.members then prettyGrid (show d) else prettyGrid " " | d <- [1..cellWidth*cellWidth]]
  where
    box ls = vsep  (ov : [prettyGrid "|" <+> l <+> prettyGrid "|" | l <- ls] <> [ov])
    ov = prettyGrid (replicate (2+cellWidth)'-')

printGrid :: M.Map Int (FiniteDomain SudokuNum) -> Grid
printGrid known = vsep $ map hsep $ chunksOf (cellWidth^(2::Int)) $ [ case known M.!? d of Just c ->  printCell c; Nothing -> printCell universe | d <- [0..cellWidth^(4::Int)-1]]

cellWidth :: Int
cellWidth = 3
-- testPropAD :: (Either (S.Set Var) (), ADTest)
-- testPropAD = flip runState (ADTest emptyPropEnv emptyPropEnv allDiffs) $ runExceptT $ do
--     toRule $ 
--       forM_ (zip [(0::Int)..] givens) $ \(idx, g) -> 
--         case g of
--           Nothing -> pure ()
--           Just v -> out @(FiniteDomain SudokuNum) "" idx (FD $ S.singleton $ SD v)
--     void theProps
--     traceM "hi"
--     traceM . show . printGrid . (.testEnv)  =<< get
--     void theProps
--     traceM "hi2"
--     traceM . show . printGrid . (.testEnv)  =<< get
--     void theProps
--     traceM "hi3"
--     traceM . show . printGrid . (.testEnv)  =<< get
--     void theProps
--     traceM "hi4"
--     traceM . show . printGrid . (.testEnv)  =<< get
--     void theProps
--     pure ()
--   where
--     allDiffs = S.fromList $ map AllDifferent (rows <> cols <> squares)
--       where
--         base = cellWidth * cellWidth
--         rows = chunksOf base [0..base*base-1]
--         cols = transpose rows
--         squares = fmap concat $ concatMap (chunksOf cellWidth) $ transpose $ map (chunksOf cellWidth) rows

--     givenss = ["53  7    "
--              ,"6  195   "
--              ," 98    6 "

--              ,"8   6   3"
--              ,"4  8 3  1"
--              ,"7   2   6"

--              ," 6    28 "
--              ,"   419  5"
--              ,"    8  79"]

--     givens = [if c == ' ' then n else j (digitToInt c) |  c <- concat givenss]
--     j = Just . pred
--     n = Nothing

singleFD :: Int -> FiniteDomain SudokuNum
singleFD d = FD $ S.singleton $ SD d





-- fixme: do stateful propagators with watched literal schemes
-- incremental propagation is then folding over ops

prop_impl_conj_r, prop_impl_conj_l, prop_impl_refl , prop_impl_full  , prop_impl_empty :: Property
prop_impl_conj_l = property $ \l r -> ((ft l ==> ft r) &&& ft l) == ft l &&& ft r
prop_impl_conj_r = property $ \l r -> ((ft l ==> ft r) &&& ft r) == ft r
prop_impl_refl = property $ \a -> top == (ft a ==> ft a)
prop_impl_full = property $ \a -> top == (ft a ==> top)
prop_impl_empty = property $ \l -> bot ==> ft l== top
prop_conj_assoc, prop_conj_idempotent, prop_conj_commutative, prop_conj_absorbing, prop_conj_neutral, prop_conj_shrinking :: Property
prop_conj_assoc = property $ \a b c -> (ft a &&& ft b) &&& ft c == ft a &&& (ft b &&& ft c)
prop_conj_idempotent = property $ \a -> (ft a &&& ft a) == ft a
prop_conj_commutative = property $ \a b -> (ft a &&& ft b) == (ft b &&& ft a)
prop_conj_absorbing = property $ \a -> ft a &&& top == ft a
prop_conj_neutral = property $ \a -> ft a &&& bot == bot
prop_conj_shrinking = property $ \a b -> ft a &&& ft b `contains` ft a

prop_disj_assoc, prop_disj_idempotent, prop_disj_commutative, prop_disj_absorbing, prop_disj_neutral, prop_disj_growing :: Property
prop_disj_assoc = property $ \a b c -> (ft a ||| ft b) ||| ft c == ft a ||| (ft b ||| ft c)
prop_disj_idempotent = property $ \a -> (ft a ||| ft a) == ft a
prop_disj_commutative = property $ \a b -> (ft a ||| ft b) == (ft b ||| ft a)
prop_disj_absorbing = property $ \a -> ft a ||| top == top
prop_disj_neutral = property $ \a -> ft a ||| bot == ft a
prop_disj_growing = property $ \a b -> ft a `contains` (ft a ||| ft b)
--
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf i s = a : chunksOf i b
 where (a,b) = splitAt i s

return []
checkAll :: IO Bool
checkAll = $quickCheckAll
