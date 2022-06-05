{-# LANGUAGE DeriveGeneric #-}
module Types where
import qualified Data.Set as S
import Control.Monad

import Test.QuickCheck
import GHC.Generics (Generic)
import Generic.Random
    ( withBaseCase, genericArbitraryRec, genericArbitraryU, (%) )
import qualified Data.Map as M






type Var = Int
data GTyp = And | Or
  deriving (Eq, Ord, Show)
data DD s
  = If Var (DD s) (DD s)
  | IsTrue
  | IsFalse
  | Group GTyp (S.Set (DD s))
  | Leaf s
  deriving (Eq, Ord, Show)

data Lit = L Var Bool
  deriving (Eq, Ord, Show)
flipLit :: Lit -> Lit
flipLit (L v b) = L v (not b)

type BDD = DD Lit


type SolveEnv = M.Map Var Bool
solver :: SolveEnv -> S.Set BDD -> Bool
solver = _


isL :: Var -> Lit
isL v = L v True
notL :: Var -> Lit
notL v = L v False

(&) :: Ord a => S.Set a -> a -> S.Set a
a & b = S.insert b a

iff :: Var -> DD Lit -> DD Lit -> DD Lit
iff _ a b | a == b = a
iff v IsTrue a = litOr (isL v) a 
iff v a IsTrue = litOr (notL v) a
iff v IsFalse a = litAnd (notL v) a
iff v a IsFalse = litAnd (isL v) a
iff v a b
  | Just o <- cofactor (isL v) a b = o
  | Just o <- cofactor (notL v) b a = o
iff v (Group l ls) (Group r rs)
  | l == r, not (S.null inters) = group l (inters & iff' v (group l (ls S.\\ rs)) (group l (rs S.\\ ls)))
  where inters = S.intersection ls rs
iff v a b = If v a b

cofactor :: Lit -> BDD -> BDD -> Maybe BDD
cofactor v l (Group And ls)
  | l `S.member` ls = Just $ group' And [l, group Or (S.delete l ls & Leaf v)]
cofactor v l (Group Or ls)
  | l `S.member` ls = Just $ group' Or [l, group And (S.delete l ls & Leaf (flipLit v))]
cofactor _ _ _ = Nothing

testCofactor = cofactor (isL 3) (Leaf $ isL 1) (group' And [Leaf $ isL 1, Leaf $ isL 2])
group' a b = group a (S.fromList b)
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



group :: Ord s => GTyp -> S.Set (DD s) -> DD s
group t ls = case filter (/= top t) $ concatMap (flatten t) $ S.toList ls of
    [] -> top t
    [a] -> a
    xs
      | bot t `S.member` S.fromList xs -> bot t
    xs -> Group t (S.fromList xs)
  where
    flatten t (Group q ls) 
      | t == q = S.toList ls
    flatten _ a = [a]
    bot And = IsFalse
    bot Or = IsTrue
    top And = IsTrue
    top Or = IsFalse

boolToDD :: Bool -> BDD
boolToDD True = IsTrue
boolToDD False = IsFalse
testGroupAnd :: IO ()
testGroupAnd = quickCheck $ \bs -> group And (S.fromList $ map boolToDD bs) == boolToDD (and bs)
testGroupOr :: IO ()
testGroupOr = quickCheck $ \bs -> group And (S.fromList $ map boolToDD bs) == boolToDD (and bs)
  
iff' v l r = If v l r

litOr :: Lit -> BDD -> BDD
litOr l (Group Or as)
  | Leaf (flipLit l) `S.member` as = IsTrue
  | otherwise = group And (S.insert (Leaf l) as)
litOr l a = group Or $ S.fromList [a, Leaf l]

litAnd :: Lit -> BDD -> BDD
litAnd l (Group And as)
  | Leaf (flipLit l) `S.member` as = IsFalse
  | otherwise = group And (S.insert (Leaf l) as)
litAnd l a = group And $ S.fromList [a, Leaf l]

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
reduceNaive env (Group And ds) = all (reduceNaive env) ds
reduceNaive env (Group Or ds) = any (reduceNaive env) ds
reduceNaive env (Leaf (L v b)) = flipper $ getEnvUnsafe env v
  where flipper = if b then id else not
toBDDNaive :: BExpr -> BDD
toBDDNaive (BAnd e1 e2) = group' And [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BOr e1 e2) = group' Or [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BNot (BLit idx)) = Leaf (L (fromEnum idx) False)
toBDDNaive (BLit idx) = Leaf (L (fromEnum idx) True)
mkBDD :: BExpr -> BDD
mkBDD = toBDDNaive . toNNF
checkNaive :: IO ()
checkNaive = quickCheck $ \env expr -> evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))
