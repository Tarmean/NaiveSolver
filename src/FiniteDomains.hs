{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DerivingVia #-}
module FiniteDomains where

import qualified Data.Set as S
import Types
import Test.QuickCheck
    ( Testable(property), Property )
import Propagator
import Control.Monad.State
import Data.Data
import Control.Monad.Except
import Data.List (transpose)
-- import Prettyprinter
import qualified Data.Map as M
import Debug.Trace (traceM)
import Data.Char (digitToInt)


newtype AllDifferentE a = AllDifferent { vars :: [a] }
  deriving (Eq, Ord, Show, Foldable, Functor)
type AllDifferent = AllDifferentE Var

allDiffProp :: forall a m s0. (Ord a, MonadState s0 m, Has s0 (PropEnv (FiniteDomain a)), Show a, Typeable a, Bounded a, Enum a) => AllDifferent -> AProp AllDifferent m s0
allDiffProp a = toRule $ mapM_ (uncurry (propagate1 @a)) (splits mempty a.vars)
  where
    splits _ [] = []
    splits l (r:rs) = (r, l <> S.fromList rs) : splits (S.insert r l) rs

propagate1 :: forall a m. (MonadProp (FiniteDomain a) m, Ord a, Bounded a, Enum a) => Var -> S.Set Var -> m ()
propagate1 v os = do
  a <- ev @(FiniteDomain a) v
  case S.toList a.members of
    [x] -> mapM_ (outOver  @(FiniteDomain a) "allDiff" universe (delDomain x))  os
    [] -> throwError (Just (S.singleton v))
    _ -> pure ()

delDomain :: Ord a => a -> FiniteDomain a -> FiniteDomain a
delDomain v fd = FD outp
  where outp = S.delete v fd.members

data FiniteDomain a = FD { members :: S.Set a }
  deriving (Eq, Ord, Show, Typeable)

newtype SudokuNum = SD { digit :: Int}
  deriving (Eq, Ord, Show, Enum) via Int
instance Bounded SudokuNum where
  minBound = SD 0
  maxBound = SD (cellWidth^(2::Int)-1)
class Universe a where
    universe :: a
instance (Ord a, Bounded a, Enum a) => Universe (FiniteDomain a) where
    universe = FD $ S.fromList [minBound..maxBound]
instance (Ord a) => PContains (FiniteDomain a) where
  compareC (FD l) (FD r)
      | l == r = Just EQ
      | l `S.isSubsetOf` r = Just LT
      | r `S.isSubsetOf` l = Just GT
      | otherwise = Nothing

instance (Ord a) => PSemigroup (FiniteDomain a) where
  
  (<?>) (FD a) (FD b)
    | S.null intersect = Nothing
    | otherwise = Just $ FD intersect
    where intersect = S.intersection a b
instance (Ord a) => PLattice (FiniteDomain a) where
  (<||>) (FD a) (FD b) = Is $ FD $ S.union a b

instance (Bounded a, Enum a, Ord a) => RegularSemigroup (FiniteDomain a) where
  FD a ==> FD b = FD (b `S.union` S.difference ((universe :: FiniteDomain a).members)  a)
instance (Bounded a, Enum a, Ord a) => PMonoid (FiniteDomain a) where
  pempty = universe
instance (Bounded a, Enum a, Ord a) => BoundedLattice (FiniteDomain a) where
  bot = FD S.empty
  isBot (FD a) = S.null a

ft :: [Int] -> FiniteDomain SudokuNum
ft = FD . S.fromList . map (SD . succ . (`mod` cellWidth))


data ADTest = ADTest { testBool :: (PropEnv (Val Bool)), testEnv :: (PropEnv (FiniteDomain SudokuNum)), testAD :: (S.Set AllDifferent) }
  deriving (Eq, Ord, Show)

instance (MonadState ADTest m) => PropsFor m ADTest  where
  theProps = do
     dirtNums <- popDirty @(FiniteDomain SudokuNum)
     onStruct @(S.Set AllDifferent) dirtNums (allDiffProp @SudokuNum)
     pure $ not $ S.null dirtNums
instance Has ADTest (PropEnv (Val Bool)) where
    getL =  (.testBool)
    putL v s = s { testBool = v }
instance Has ADTest (PropEnv (FiniteDomain SudokuNum)) where
    getL =  (.testEnv)
    putL v s = s { testEnv = v }
instance Has ADTest (S.Set AllDifferent) where
    getL =  (.testAD)
    putL v s = s { testAD = v }


data Grid = Grid { rows :: [String] }
instance Show Grid where
    show g = unlines g.rows
(<+>) :: Grid -> Grid -> Grid
(<+>) l r = Grid $ zipWith (<>) (padGrid l).rows (padGrid r).rows
(<->)  :: Grid -> Grid -> Grid
(<->) l r = Grid $ l.rows <> r.rows

padGrid :: Grid -> Grid
padGrid gr = Grid $ map (padTo maxW) gr.rows
  where
    maxW = maximum $ map length gr.rows
padTo :: Int -> String -> String
padTo i0 w = (replicate l ' ') <> w <> replicate r ' '
  where
    i = i0 - length w
    l = i `div` 2
    r = i - l
-- (<+>) :: Grid -> Grid -> Grid
-- (<+>) l r = 
cellWidth :: Int
cellWidth = 3
testPropAD :: (Either (S.Set Var) (), ADTest)
testPropAD = flip runState (ADTest emptyPropEnv emptyPropEnv allDiffs) $ runExceptT $ do
    toRule $ 
      forM_ (zip [(0::Int)..] givens) $ \(idx, g) -> 
        case g of
          Nothing -> pure ()
          Just v -> out @(FiniteDomain SudokuNum) "" idx (FD $ S.singleton $ SD v)
    theProps
    traceM "hi"
    traceM . show . printGrid . (.testEnv)  =<< get
    theProps
    traceM "hi2"
    traceM . show . printGrid . (.testEnv)  =<< get
    theProps
    traceM "hi3"
    traceM . show . printGrid . (.testEnv)  =<< get
    theProps
    traceM "hi4"
    traceM . show . printGrid . (.testEnv)  =<< get
    theProps
    pure ()
  where
    allDiffs = S.fromList $ map AllDifferent (rows <> cols <> squares)
      where
        base = cellWidth * cellWidth
        rows = chunksOf base [0..base*base-1]
        cols = transpose rows
        squares = fmap concat $ concatMap (chunksOf cellWidth) $ transpose $ map (chunksOf cellWidth) rows

    givenss = ["53  7    "
             ,"6  195   "
             ," 98    6 "

             ,"8   6   3"
             ,"4  8 3  1"
             ,"7   2   6"

             ," 6    28 "
             ,"   419  5"
             ,"    8  79"]

    givens = [if c == ' ' then n else j (digitToInt c) |  c <- concat givenss]
    j = Just . pred
    n = Nothing

singleFD :: Int -> FiniteDomain SudokuNum
singleFD d = FD $ S.singleton $ SD d
printCell :: FiniteDomain SudokuNum -> Grid
printCell fd = box $ map hsep $ chunksOf (cellWidth) $ [ if S.member (SD $ d-1) fd.members then pretty (show d) else pretty " " | d <- [1..cellWidth*cellWidth]]
  where
    box ls = vsep  (ov : [pretty "|" <+> l <+> pretty "|" | l <- ls] <> [ov])
    ov = pretty (replicate (2+cellWidth)'-')

hsep :: [Grid] -> Grid
hsep = foldl1 (<+>)
vsep :: [Grid] -> Grid
vsep = foldl1 (<->)
pretty :: String -> Grid
pretty s = Grid [s]
printGrid :: PropEnv (FiniteDomain SudokuNum) -> Grid
printGrid (penv :: PropEnv (FiniteDomain SudokuNum)) = vsep $ map hsep $ chunksOf (cellWidth^(2::Int)) $ [ case penv.known M.!? d of Just c ->  printCell c; Nothing -> printCell universe | d <- [0..cellWidth^(4::Int)-1]]




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
-- return []
-- checkAll :: IO Bool
-- checkAll = $quickCheckAll
--
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf i s = a : chunksOf i b
 where (a,b) = splitAt i s
