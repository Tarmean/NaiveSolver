{-# LANGUAGE DeriveGeneric #-}
module Types where
import qualified Data.Set as S
import Control.Monad

import Test.QuickCheck
import GHC.Generics (Generic)
import Generic.Random
    ( withBaseCase, genericArbitraryRec, genericArbitraryU, (%) )
import qualified Data.Map as M
import Control.Monad.State
import Debug.Trace (traceM, trace)
import Data.List (partition)
import Data.Either (partitionEithers)




type Var = Int
data DD s
  = If Var (DD s) (DD s)
  | IsTrue
  | IsFalse
  | And (S.Set (DD s))
  | Leaf s
  deriving (Eq, Ord, Show)

type BDD = DD Lit

data Tag = Absorbing | Neutral

varOf :: BDD -> Var
varOf (If v _ _) = v
varOf (And ls) = minimum $ map varOf $ S.toList ls
varOf (Leaf (L v _)) = v
varOf a = (-1)

mAnd :: [DD Lit] -> DD Lit
mAnd inp
  | trace ("mAnd: " ++ show inp) False = undefined
mAnd inp = evalState (go $ M.fromListWith (<>) (concatMap mkTag inp)) M.empty
  where
    step ls e' = do
         (done, ls') <- partitionEithers <$> traverse simplify ls
         traceM $ "simplified: " ++ show (ls, done, ls', e')
         let ls'' = filter (/=IsTrue) ls'
         if any (== IsFalse) ls''
          then pure IsFalse
          else do
             let q' = M.fromListWith (<>) (concatMap mkTag ls'')
             out <- go $ M.unionWith (<>) e' q'
             pure $ gAnd (S.fromList $ out : done)

    go e
      | M.null e = pure IsTrue
    go e = case M.minViewWithKey e of
        Nothing -> pure IsTrue
        Just ((v, ls), e') ->  do
         -- traceM $ "go: " ++ show (v, ls)
         pre <- get
         if v `M.member` pre
         then step ls e'
         else do
             put (M.insert v True pre)
             t <- step ls e'
             put (M.insert v False pre)
             f <- step ls e'
             put pre
             pure $ iff v t f
    mkTag (And ls) = concatMap mkTag (S.toList ls)
    mkTag i = [(varOf i, [i])]


foo :: DD Lit
foo =  mAnd [If 0 IsTrue IsFalse, If 1 IsTrue IsFalse]


simplify :: BDD -> State (M.Map Var Bool) (Either BDD BDD)
simplify (And ls) = error "And in simplify"
    -- (a,b) <- traverse simplify $ S.toList ls
    -- pure $ Right $ gAnd $ S.fromList ls'
simplify (If v l r) = do
    k <- gets $ M.lookup v
    case k of
        Nothing -> pure $ Right $ If v l r
        Just True -> simplify l
        Just False -> simplify r
simplify IsTrue = pure $ Right IsTrue
simplify IsFalse = pure $ Right IsFalse
simplify (Leaf (L k v)) = do
  env <- get
  case env M.!? k of
    Nothing -> do
      modify $ M.insert k v
      pure $ Left $ Leaf (L k v)
    Just o -> if v == o then pure $ Right IsTrue else pure $ Right IsFalse


data Lit = L Var Bool
  deriving (Eq, Ord, Show)
flipLit :: Lit -> Lit
flipLit (L v b) = L v (not b)



type SolveEnv = M.Map Var Bool
-- solver :: SolveEnv -> S.Set BDD -> Bool
-- solver = _

mNot :: BDD -> BDD
mNot (If v t f) = If v (mNot t) (mNot f)
mNot (And xs) = mAnd $ map mNot $ S.toList xs
mNot IsTrue = IsFalse
mNot IsFalse = IsTrue
mNot (Leaf (L v b)) = Leaf $ L v (not b)

mOr = mNot . mAnd . S.toList . S.map mNot

mLit :: Var -> BDD
mLit v = Leaf $ L v True



isL :: Var -> Lit
isL v = L v True
notL :: Var -> Lit
notL v = L v False

(&) :: Ord a => S.Set a -> a -> S.Set a
a & b = S.insert b a

iff :: Var -> DD Lit -> DD Lit -> DD Lit
iff _ a b | a == b = a
-- iff v IsTrue a = litOr (isL v) a 
-- iff v a IsTrue = litOr (notL v) a
iff v IsFalse a = litAnd (notL v) a
iff v a IsFalse = litAnd (isL v) a
iff v a b
  | Just o <- cofactor (isL v) a b = o
  | Just o <- cofactor (notL v) b a = o
iff v (And ls) (And rs)
  |  not (S.null inters) = gAnd (inters & iff' v (gAnd (ls S.\\ rs)) (gAnd (rs S.\\ ls)))
  where inters = S.intersection ls rs
iff v a b = If v a b

cofactor :: Lit -> BDD -> BDD -> Maybe BDD
-- cofactor v l (And ls)
--   | l `S.member` ls = Just $ gAnd' [l, mOr (S.delete l ls & Leaf v)]
cofactor _ _ _ = Nothing

testCofactor = cofactor (isL 3) (Leaf $ isL 1) (gAnd' [Leaf $ isL 1, Leaf $ isL 2])
gAnd' b = gAnd (S.fromList b)
-- v & x | !v & (x | y)
-- x | (!v & y)
--
-- v & x | !v & (x & y)
-- x & (v | y)
--
--
-- v & x | !v & (w & x | !w & y)
-- v & x | !v & w & x | !v & !w & y
-- x & (v | w) | !v & w & y



gAnd :: (Show s, Ord s) => S.Set (DD s) -> DD s
gAnd ls = case filter (/= top) $ concatMap flatten $ S.toList ls of
    [] -> top
    [a] -> a
    xs
      | bot `S.member` S.fromList xs -> bot
    xs -> And (S.fromList xs)
  where
    flatten (And ls) = S.toList ls
    flatten a = [a]
    bot = IsFalse
    top = IsTrue

boolToDD :: Bool -> BDD
boolToDD True = IsTrue
boolToDD False = IsFalse
testGroupAnd :: IO ()
testGroupAnd = quickCheck $ \bs -> And (S.fromList $ map boolToDD bs) == boolToDD (and bs)
testGroupOr :: IO ()
testGroupOr = quickCheck $ \bs -> And (S.fromList $ map boolToDD bs) == boolToDD (and bs)
  
iff' v l r = If v l r

-- litOr :: Lit -> BDD -> BDD
-- litOr = undefined
-- litOr l (Group Or as)
--   | Leaf (flipLit l) `S.member` as = IsTrue
--   | otherwise = group And (S.insert (Leaf l) as)
-- litOr l a = group Or $ S.fromList [a, Leaf l]

litAnd :: Lit -> BDD -> BDD
litAnd l (And as) = gAnd (S.insert (Leaf l) as)
litAnd l a = gAnd $ S.fromList [a, Leaf l]

-- splitOn :: Var -> DD s -> (DD s, DD s)
-- splitOn v e@(If c t e)
--   | c == v = (t, e)
--   | otherwise = (e, e)

-- appAnd :: Env -> [BDD] -> BDD
-- appAnd env bdds = 

data BLit = B1 | B2 | B3 | B4
  deriving (Eq, Ord, Show, Generic, Enum, Bounded)
instance Arbitrary BLit where
    arbitrary = genericArbitraryU
data BExpr = BAnd BExpr BExpr | BOr BExpr BExpr | BNot BExpr | BLit BLit
  deriving (Eq, Ord, Show, Generic)
instance Arbitrary BExpr where
    arbitrary = genericArbitraryRec (2 % 2 % 1 % 1 % ()) `withBaseCase` (BLit <$> arbitrary)
type BExprEnv = (Bool, Bool, Bool, Bool)
getEnv :: BExprEnv -> BLit -> Bool
getEnv (b1, b2, b3, b4) B1 = b1
getEnv (b1, b2, b3, b4) B2 = b2
getEnv (b1, b2, b3, b4) B3 = b3
getEnv (b1, b2, b3, b4) B4 = b4
evalBExpr :: BExprEnv -> BExpr -> Bool
evalBExpr env (BAnd e1 e2) = evalBExpr env e1 && evalBExpr env e2
evalBExpr env (BOr e1 e2) = evalBExpr env e1 || evalBExpr env e2
evalBExpr env (BNot e) = not $ evalBExpr env e
evalBExpr env (BLit l) = getEnv env l
toNNF :: BExpr -> BExpr
toNNF (BAnd e1 e2) = BAnd (toNNF e1) (toNNF e2)
toNNF (BOr e1 e2) = BOr (toNNF e1) (toNNF e2)
toNNF (BNot (BAnd l r)) = BOr (toNNF (BNot l)) (toNNF (BNot r))
toNNF (BNot (BOr l r)) = BAnd (toNNF (BNot l)) (toNNF (BNot r))
toNNF (BNot (BNot e)) = toNNF e
toNNF a@(BLit l) = a
toNNF a@(BNot (BLit l)) = a
getEnvUnsafe :: BExprEnv -> Var -> Bool
getEnvUnsafe env v = getEnv env (toEnum v)
reduceNaive :: BExprEnv -> BDD -> Bool
reduceNaive env (If c t e) =
  if getEnvUnsafe env c
  then reduceNaive env t
  else reduceNaive env e
reduceNaive env IsTrue = True
reduceNaive env IsFalse = False
reduceNaive env (And ds) = all (reduceNaive env) ds
reduceNaive env (Leaf (L v b)) = flipper $ getEnvUnsafe env v
  where flipper = if b then id else not
toBDDNaive :: BExpr -> BDD
toBDDNaive (BAnd e1 e2) = mAnd [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BOr e1 e2) = mOr $ S.fromList [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BNot (BLit idx)) = Leaf (L (fromEnum idx) False)
toBDDNaive (BLit idx) = Leaf (L (fromEnum idx) True)
toBDDNaive (BNot e) = error $ "Not in NNF " ++ show e
mkBDD :: BExpr -> BDD
mkBDD = toBDDNaive . toNNF
checkNaive :: IO ()
checkNaive = quickCheck $ \env expr -> evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))
