{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Types where
import qualified Data.Set as S

import Test.QuickCheck ( quickCheck, Arbitrary(arbitrary) )
import GHC.Generics (Generic)
import Generic.Random
    ( withBaseCase, genericArbitraryRec, genericArbitraryU, (%) )
import qualified Data.Map as M
import Control.Monad.State
    ( evalState, runState, MonadState(get, put), State )
import Data.List (partition)
import Data.Either (partitionEithers)
import qualified Data.Map.Merge.Lazy as M
import Data.Maybe (isJust, isNothing)
import Control.Applicative ( Alternative(empty) )
import Control.Monad.Trans.Maybe ( MaybeT(..) )
import System.Timeout (timeout)
import Test.QuickCheck.Property (within)
import Debug.Trace (trace, traceShowId)

main :: IO ()
main = print "bdd"

class PContains s where
   -- compareC a b == Just LT
   -- \forall x \in a. x \in b
   compareC :: s -> s -> Maybe Ordering
contains :: PContains a => a -> a -> Bool
contains a b = case compareC a b of
   Just LT -> True
   Just EQ -> True
   _ -> False
class POrd s where
   -- compareP a b == Just LT
   -- \forall x \in a. \forall y \in b. x <= y
   compareP :: s -> s -> Maybe Ordering
(<=?) :: POrd a => a -> a -> Bool
(<=?) a b = case compareP a b of
   Just LT -> True
   Just EQ -> True
   _ -> False
class (PMonoid s, RegularSemigroup s, PLattice s, Show s, Ord s) => IsLit s where
  -- | construct `var=True`
  isL :: Var -> s
  -- | construct `var=False`
  notL :: Var -> s
  -- | largest unknown var
  maxSplitVar :: s -> Var
  -- | Conditions on variable, `split x s` return
  --     Just (s|x=True, s|x=False)
  -- if x occurs in s. Afterwards, the results shouldn't refer to x.
  -- This could be implemented via `<?>`, `maxSplitVar`, and `==>` but a more performant implementation might be possible
  splitLit :: Var -> s -> Maybe (DD s,DD s)
  -- Check if the variable is definitely True/False
  evalVar :: Var -> s -> Maybe Bool

-- | Partial meet of data, a AND b is true so union their info
class PSemigroup s where
    -- | laws: associative, commutative, idempotent
    (<?>) :: s -> s -> Maybe s
-- | Partial merging with default
class PSemigroup s => PMonoid s where
    -- | no information. neutral element of <?>, absorbing element of <||>
    pempty :: s

-- | Partial join of data, a OR b is true so intersect their info
class (PSemigroup s) => PLattice s where
    -- | laws: associative, commutative, idempotent
    -- usually not distributive over <?>, applying it early loses information
    -- (that's why we do case distinction via bdd)
    (<||>) :: s -> s -> LatticeVal s
data LatticeVal a = IsTop | IsBot | Is a
  deriving (Eq, Ord, Show)

-- | deduplicates information which is saved elsewhere
-- FIXME: i defined this ad-hoc because I needed the operation, but is this just heyting algebras?
class PSemigroup a => RegularSemigroup a  where
    -- | a ==> b returns the (ideally minimum) x such that
    --  (a ==> b) &&& a  == a &&& b
    --
    -- for bounded lattices:
    -- a ==> a = pempty
    -- a <&> (a ==> b) = a <&> b
    -- b <&> (a ==> b) = b
    -- c ==> (a <&> b) ~ (c ==> a) <&> (c ==> b), if <&> is defined
    (==>) :: a -> a -> a
top :: PMonoid a => a
top = pempty
class (PMonoid s, PLattice s) => BoundedLattice s where
    bot :: s
    isBot :: s -> Bool
    (&&&) :: s -> s -> s
    a &&& b = case a <?> b of
      Nothing -> bot
      Just s -> s
    (|||) :: s -> s -> s
    a ||| b = case a <||> b of
       IsBot -> bot
       IsTop -> top
       Is s -> s

-- | more accurate than pseudoinverse in RegularSemigroup
-- (a <> x) <> inv a  = x
class PSemigroup a => InverseSemigroup a  where
    inv :: a -> a

bddTestEnv :: (Bool, Bool, Bool, Bool)
bddTestEnv = (False,True,False,False)
bddTest :: BExpr
bddTest = BOr (BAnd (BOr (BAnd (BLit B2) (BOr (BAnd (BOr (BLit B4) (BLit B3)) (BNot (BLit B4))) (BOr (BAnd (BLit B4) (BLit B2)) (BNot (BLit B1))))) (BLit B1)) (BAnd (BAnd ( BAnd (BOr (BOr (BLit B3) (BLit B4)) (BLit B2)) (BNot (BAnd (BLit B3) (BLit B1)))) (BOr (BLit B1) (BAnd (BOr (BLit B2) (BLit B4)) (BNot (BLit B1))))) (BLit B1))) ( BLit B1)



type Var = Int
data DD s
  = If Var (DD s) (DD s)
  | IsTrue
  | IsFalse
  | And s (S.Set (DD s))
  deriving (Eq, Ord, Show)

type BDD = DD (PMap Var (Val Bool))

kOp :: IsLit a => (DD a -> DD a -> Maybe (DD a)) -> DD a -> DD a -> DD a
kOp f = go
  where
    -- go p l r
    --   | trace (p <> "kop go " ++ show (l,r)) False = undefined
 -- trace (p <> "kop out: " <> show o)
    go l r
      | Just o <- f l r = o
    go l r =  iff v lhs rhs
      where
        -- lhs = trace (p <> "kop iff lhs" <> show v) $ showThis (p <> "kop lhs out: ") (go ('-':p)lx rx)
        lhs = (go lx rx)
        rhs = (go ly ry)
        -- showThis tag a = a `seq` trace (tag <> show a) a
        (lx, ly) 
          | lv == v = split v l
          | otherwise = (l,l)
        (rx, ry)
          | rv == v = split v r
          | otherwise = (r,r)
        v = max lv rv
        lv = varOf l
        rv = varOf r
kAnd :: IsLit a => DD a -> DD a -> DD a
kAnd = kOp step
  where
    step IsTrue a = Just a
    step a IsTrue = Just a
    step IsFalse _ = Just IsFalse
    step _ IsFalse = Just IsFalse
    step a b 
      | a == b = Just a
    step _ _ = Nothing
kOr :: IsLit a => DD a -> DD a -> DD a
kOr = kOp step
  where
    step IsFalse a = Just a
    step a IsFalse = Just a
    step IsTrue _ = Just IsTrue
    step _ IsTrue = Just IsTrue
    step a b 
      | a == b = Just a
    step _ _ = Nothing



data Tag = Absorbing | Neutral

varOf :: IsLit s => DD s -> Var
varOf (If v _ _) = v
varOf (And s ls) = maxSplitVar s `max` (maximum $ (-1:) $ map varOf $ S.toList ls)
varOf _ = (-1)

splitMap :: (a -> (b,c)) -> [a] -> ([b], [c])
splitMap f ls = (fmap fst ls', fmap snd ls')
    where ls' = fmap f ls

mOr :: IsLit s => [DD s] -> DD s
mOr inp = go (inj inp)
  where
    goRec :: IsLit s => [DD s] -> M.Map Var [DD s] -> DD s
    goRec a e'
      | IsTrue `elem` a = IsTrue
      | otherwise = go (M.unionWith (<>) (inj $ filter (/= IsFalse) a) e')
    -- go :: M.Map Var [DD s] -> DD s
    go :: IsLit s => M.Map Var [DD s] -> DD s
    go e
      | trace ("mOr go " ++ show e) False = undefined
    -- FIXME: this is horribly inefficient:
    -- If we have invariants at the top we should keep the union of those invariants at the top
    -- - the union environment is weaker than any input environment
    -- - the original environments are stronger so any optimizations had been possible previously => no existing branches become impossible
    -- - we want to keep the union environment on the surface
    -- - we want to subtract the union environment from per-node environemtns
    -- - if an environemnt becomes empty we can replace the node with IsTrue and halt
    go e = case M.maxViewWithKey e of
        Nothing -> IsFalse
        Just ((v, ls0), e') -> 
            let
                 ls = filter (/= IsFalse) ls0
                 (a,b) = splitMap (split v) ls
                 l = goRec a e'
                 r = goRec b e'
            in 
              if  
                | null ls -> IsFalse
                | IsTrue `elem` ls -> IsTrue
                | otherwise -> iff v l r
    inj :: IsLit s => [DD s] -> M.Map Var [DD s]
    inj = M.fromListWith (<>) . map mkTag
    mkTag i@(And s _)
      | sVar > lVar = (sVar, [i])
      | otherwise = (lVar, [i])
      where
        sVar = maxSplitVar s
        lVar = varOf i
    mkTag i = (varOf i, [i])
split :: IsLit s => Var -> DD s -> (DD s, DD s)
split v (If v' l r)
  | v == v' = (l, r)
  | otherwise = error $ "illegal split: " <> show v <> ", " <> show (If v' l r)
split v (And s ls) = 
    case splitLit v s of
       Just (sL, sR) -> (gAnd $ S.fromList $ sL : relL <> invariant, gAnd $ S.fromList $ sR : relR <> invariant)
       Nothing -> (gAndS s $ S.fromList $ relL <> invariant, gAndS s $ S.fromList $ relR <> invariant)
  where
    (rel,invariant) = partition (\i -> varOf i == v) $ S.toList ls
    (relL, relR) = splitMap (split v) rel
split _ a = (a,a)

-- testSplit = split 1 $ And (
-- mAnd :: forall s. (IsLit s, PMonoid s) => [DD s] -> DD s
-- mAnd inp
--   | trace ("mAnd: " ++ show inp) False = undefined
-- mAnd inp = flip evalState pempty $ do
--    mo <- runMaybeT (allFlatAnds inp)
--    case mo of
--      Nothing -> pure IsFalse
--      Just (s,o) -> addEnv s <$> go (inj o)
--   where
--     step ls e' = do
--          (done, ls') <- partitionEithers <$> traverse simplifyAnd ls
--          runMaybeT (allFlatAnds ls') >>= \case
--            Nothing -> pure IsFalse
--            Just (s, flatLs) -> 
--              let ls'' = filter (/= IsTrue) flatLs
--              in
--              if any (== IsFalse) ls''
--               then pure IsFalse
--               else do
--                  out <- go $ M.unionWith (<>) e' (inj ls'')
--                  pure $ gAndS s (S.fromList $ out : done)

--     go e
--       | M.null e = pure IsTrue
--     go e = case M.maxViewWithKey e of
--         Nothing -> pure IsTrue
--         Just ((v, ls), e') ->  do
--          -- traceM $ "go: " ++ show (v, ls)
--          pre <- get
--          if isJust (evalVar @s v pre)
--          then do
--            -- traceM ("skip 1: " ++ show (v, ls))
--            step ls e'
--          else do
--              -- traceM ("split 1: " ++ show (v, ls))
--              t <- withEnv @s (isL v) $ step ls e'
--              -- traceM ("split 2: " ++ show (v, ls))
--              f <- withEnv @s (notL v) $ step ls e'
--              pure $ iff v t f

--     allFlatAnds :: IsLit s => [DD s] -> MaybeT (State s) (s, [DD s])
--     allFlatAnds ls = do
--         env <- get
--         (Just o,s) <- pure (runState (runMaybeT $ traverse flatAnds ls) pempty)
--         env' <- liftMaybe $ env <?> s
--         put env'
--         pure $ (env ==> s, concat o)

--     flatAnds :: IsLit s => DD s -> MaybeT (State s) [DD s]
--     flatAnds (And s ls) = do
--        tellEnv s
--        lls <- traverse flatAnds $ S.toList ls
--        pure $ concat lls
--     flatAnds a = pure [a]

--     tellEnv s = do
--        env <- get
--        case s <?> env of
--            Nothing -> empty
--            Just s' -> put s'

--     inj = M.fromListWith (<>) . map (\i -> (varOf i, [i]))

liftMaybe :: Applicative m => Maybe s -> MaybeT m s
liftMaybe = MaybeT . pure

withEnv :: IsLit s => s -> State s a -> State s a
withEnv s m = do
  env <- get
  o <- case s <?> env of
    Nothing -> error ("Illegal env: " <> show s <> ", " <> show env)
    Just env' -> put env' *> m
  put env
  pure o


-- foo :: BDD
-- foo =  mAnd [If 2 IsTrue IsFalse, If 1 IsTrue IsFalse]


simplify :: forall s. IsLit s => DD s -> State s (Either (DD s) (DD s))
simplify (And s ls) = do
    (a,b) <- partitionEithers <$> (traverse simplify $ S.toList ls)
    env <- get
    pure $ Right $  gAndS (env ==> s) $ S.fromList (a <> b)
simplify (If v l r) = do
    env <- get
    case evalVar @s v env of
        Nothing -> pure $ Right $ If v l r
        Just True -> simplify l
        Just False -> simplify r
simplify IsTrue = pure $ Right IsTrue
simplify IsFalse = pure $ Right IsFalse
-- simplify a@(Leaf _) = pure $ Right a
simplifyAnd :: IsLit s => DD s -> State s (Either (DD s) (DD s))
-- simplifyAnd (Leaf l) = do
--   env <- get
--   case inEnv env l of
--     Nothing -> pure $ Right $ IsFalse
--     Just o -> do
--        case intoEnv l <?> env of
--            Nothing -> pure $ Right $ IsFalse
--            Just env' -> do
--              put env'
--              pure $ Right $ o
  -- case env M.!? k of
  --   Nothing -> do
  --     modify $ M.insert k v
  --     pure $ Left $ Leaf (L k v)
  --   Just o -> if v == o then pure $ Right IsTrue else pure $ Right IsFalse
simplifyAnd a = simplify a


data Lit = L Var Bool
  deriving (Eq, Ord, Show)
flipLit :: Lit -> Lit
flipLit (L v b) = L v (not b)



type SolveEnv = M.Map Var Bool

mNot :: (InverseSemigroup s, IsLit s) => DD s -> DD s
mNot (If v t f) = If v (mNot t) (mNot f)
mNot (And s xs) = mOr $ (And (inv s) mempty:) $ map mNot $ S.toList xs
mNot IsTrue = IsFalse
mNot IsFalse = IsTrue


mLit :: Var -> BDD
mLit v = And (isL v) mempty

mLitN :: Var -> BDD
mLitN v = And (notL v) mempty


isV :: IsLit s => Var -> Bool -> s
isV v b = if b then isL v else notL v

instance (Ord k, PLattice v) => PLattice (PMap k v) where
  (<||>) (PMap l) (PMap r) = toIs $ fmap PMap $ M.mergeA M.dropMissing M.dropMissing (M.zipWithMaybeAMatched (\_ a b -> wrap $ a <||> b)) l r
    where
      wrap IsBot = Nothing
      wrap IsTop = Just Nothing
      wrap (Is a) = Just (Just a)
      toIs Nothing = IsBot
      toIs (Just a) = Is a
getLatticeVal :: BoundedLattice a => LatticeVal a -> a
getLatticeVal IsBot = bot
getLatticeVal (Is a) = a
getLatticeVal IsTop = top
notBot :: PMonoid a => LatticeVal a -> Maybe a
notBot IsBot = Nothing
notBot (Is a) = Just a
notBot IsTop = Just top

newtype Val a = Val {unVal :: a}
  deriving (Eq, Ord, Show)
instance Eq a => PContains (Val a) where
    compareC a b
      | a == b = Just EQ
      | otherwise = Nothing
instance Eq a => POrd (Val a) where
    compareP a b
      | a == b = Just EQ
      | otherwise = Nothing
instance Eq a => PSemigroup (Val a) where
    (<?>) (Val a) (Val b) = if a == b then Just (Val a) else Nothing
instance (Eq a) => PLattice (Val a) where
    (<||>) (Val a) (Val b) = if a == b then Is (Val a) else IsTop
 
data PMap k v = PMap (M.Map k v)
  deriving (Eq, Ord, Show)
(??) :: (Ord k) => PMap k v -> k -> Maybe v
(??) (PMap m) k = M.lookup k m
instance (Ord k, PSemigroup v) => PSemigroup (PMap k v) where
    (<?>) (PMap m) (PMap m') = case M.mergeA M.preserveMissing M.preserveMissing (M.zipWithAMatched both) m m' of
      Just o -> Just (PMap o)
      Nothing -> Nothing
      where
        both _ x y = x <?> y
instance (Ord k, PSemigroup v) => PMonoid (PMap k v) where
    pempty = PMap M.empty

emptyPMap :: PMap k v
emptyPMap = PMap M.empty

instance (Ord k, Eq v, PSemigroup v) => RegularSemigroup (PMap k v) where
    (==>) (PMap m') (PMap m) = PMap $ M.merge M.preserveMissing M.dropMissing (M.zipWithMaybeMatched f) m m'
      where
       f _ x y
         | x == y = Nothing
         | otherwise = Just x
        
orBot :: Ord s => Maybe s -> DD s
orBot Nothing = IsFalse
orBot (Just s) = And s mempty

removeVar :: IsLit s => Var -> Bool -> s -> DD s
removeVar v b s = case s <?> isV v b of
    Nothing -> IsFalse
    Just s' -> And (isV v b ==> s') mempty

instance IsLit (PMap Var (Val Bool)) where
    isL v = PMap $ M.singleton v (Val True)
    notL v = PMap $ M.singleton v (Val False)
    maxSplitVar (PMap p) = case M.maxViewWithKey p of
      Nothing -> -1
      Just ((v,_),_) -> v
    splitLit v env
      | isNothing (evalVar v env) = Nothing
      | otherwise = Just (removeVar v True env, removeVar v False env)
    evalVar v env = fmap unVal $ env ?? v

(&) :: Ord a => S.Set a -> a -> S.Set a
a & b = S.insert b a

iff :: (IsLit s) => Var -> DD s -> DD s -> DD s
iff v a b
  | Just o <- cofactor True v a b = o
  | Just o <- cofactor False v b a = o
iff v (And sl vl) (And sr vr)
  | merged == IsBot  = IsFalse
  | Is a <- merged = mkOut a
  | merged == IsTop = mkOut pempty
  | not (S.null inters) = mkOut pempty
  where
    merged = sl <||> sr
    mkOut o = gAndS o  (inters & ifFixme v (gAndS (o ==> sl) (vl S.\\ vr)) (gAndS (o ==> sr)(vr S.\\ vl)))
    -- FIXME!!!
    ifFixme = iffNRec
    inters = S.intersection vl vr
iff v a b = iffNRec v a b

iffNRec :: IsLit s => Var -> DD s -> DD s -> DD s
iffNRec _ a b | a == b = a
iffNRec v IsFalse a = litAnd (notL v) a
iffNRec v a IsFalse = litAnd (isL v) a
iffNRec v a b = If v a b

cofactor :: IsLit s => Bool -> Var -> (DD s) -> (DD s) -> Maybe (DD s)
cofactor b v l (And s ls)
  | l `S.member` ls = Just $ gAnd' [l,  iff' v b IsTrue (gAndS s $ S.delete l ls)]
   where
     iff' a True x y  = iff a x y
     iff' a False x y = iff a y x
cofactor _ _ _ _ = Nothing

-- testCofactor = cofactor (isL 3) (Leaf $ isL 1) (gAnd' [Leaf $ isL 1, Leaf $ isL 2])
gAnd' :: IsLit s => [DD s] -> DD s
gAnd' b = gAnd (S.fromList b)
gAndS :: IsLit s => s -> S.Set (DD s) -> DD s
gAndS s b = addEnv s $ gAnd b
-- 


addEnv :: (Eq s, PMonoid s) => s -> DD s -> DD s
addEnv _ IsFalse = IsFalse
addEnv s a
  | s == pempty = a
addEnv s (And t ls) = case s <?> t of
    Nothing -> IsFalse
    Just q -> And q ls
addEnv s IsTrue = And s S.empty
addEnv s t = And s (S.singleton t)

gAnd :: (IsLit s) => S.Set (DD s) -> DD s
gAnd ls = 
  case flattenEnv (S.toList ls) of
    Nothing -> IsFalse
    Just env -> 
       case filter (/= IsTrue) $ concatMap flatten $ S.toList ls of
        [] -> addEnv env IsTrue
        [a] -> addEnv env a
        xs
          | IsFalse `S.member` S.fromList xs -> IsFalse
        xs -> And env (S.fromList xs)
  where
    flattenEnv :: (IsLit s) => [DD s] -> Maybe s
    flattenEnv es = foldl merge1 (Just pempty) [s | And s _ <- es]
    merge1 Nothing _ = Nothing
    merge1 (Just m) s = m <?> s
    flatten (And _ es) = S.toList es
    flatten a = [a]

boolToDD :: Bool -> BDD
boolToDD True = IsTrue
boolToDD False = IsFalse
testGroupAnd :: IO ()
testGroupAnd = quickCheck $ \bs -> And pempty (S.fromList $ map boolToDD bs) == boolToDD (and bs)
testGroupOr :: IO ()
testGroupOr = quickCheck $ \bs -> And pempty (S.fromList $ map boolToDD bs) == boolToDD (and bs)
  
litAnd :: (IsLit s) => s -> DD s -> DD s
litAnd l a = addEnv l a



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
getEnv (b1, _, _, _) B1 = b1
getEnv (_, b2, _, _) B2 = b2
getEnv (_, _, b3, _) B3 = b3
getEnv (_, _, _, b4) B4 = b4
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
toNNF a@(BLit {}) = a
toNNF a@(BNot (BLit {})) = a
getEnvUnsafe :: BExprEnv -> Var -> Bool
getEnvUnsafe env v = getEnv env (toEnum (v-1))
reduceNaive :: BExprEnv -> BDD -> Bool
reduceNaive env (If c t e) =
  if getEnvUnsafe env c
  then reduceNaive env t
  else reduceNaive env e
reduceNaive _ IsTrue = True
reduceNaive _ IsFalse = False
reduceNaive env (And s ds) = isJust (toEnv env <?> s) && all (reduceNaive env) ds
  where
    toEnv (a,b,c,d) = PMap $ M.fromList $ zip [1..] (map Val [a,b,c,d])
toBDDNaive :: BExpr -> BDD
toBDDNaive (BAnd e1 e2) = kAnd (toBDDNaive e1) (toBDDNaive e2)
toBDDNaive (BOr e1 e2) = kOr (toBDDNaive e1) (toBDDNaive e2)
toBDDNaive (BNot (BLit idx)) = And (notL (1+fromEnum idx)) mempty
toBDDNaive (BLit idx) = And (isL (1+fromEnum idx)) mempty
toBDDNaive (BNot e) = error $ "Not in NNF " ++ show e
mkBDD :: BExpr -> BDD
mkBDD = toBDDNaive . toNNF
checkEquiv :: BExprEnv -> BExpr -> Bool
checkEquiv env expr = evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))
checkNaive :: IO ()
checkNaive = quickCheck $  \env expr -> within 1000 $ evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))

searchNonDet :: BExpr -> IO BExpr
searchNonDet = go
  where
    go :: BExpr -> IO BExpr
    go (BAnd l r) = rec BAnd l r
    go (BOr l r) = rec BOr l r
    go a = pure a
    rec f l r = do
        a <- doesTerminate l
        b <- doesTerminate r
        if a && b
        then  do
          putStrLn $ "Terminating: " <> show l
          putStrLn $ "Also Terminating: " <> show r
          pure $ f l r
        else if a then do
          putStrLn $ "Not terminating: " <> show r
          go r
        else do
          putStrLn $ "Not terminating: " <> show l
          go l
doesTerminate :: BExpr -> IO Bool
doesTerminate = fmap isJust . timeout 1200 . (\x -> x `seq` pure ()) . toBDDNaive

-- !2 && !3 || 2 && 3 && 4 || 2
-- = !3 || 2

