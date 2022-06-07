{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
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
import qualified Data.Map.Merge.Lazy as M
import Data.IntMap.Merge.Strict (SimpleWhenMissing)
import Data.Maybe (isJust, isNothing)
import Control.Applicative
import Control.Monad.Trans.Maybe

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
  -- This could be implemented via `<?>`, `maxSplitVar`, and `<->` but a more performant implementation might be possible
  splitLit :: Var -> s -> Maybe (DD s,DD s)
  -- Check if the variable is definitely True/False
  evalVar :: Var -> s -> Maybe Bool

-- | laws: associative, commutative, idempotent
class PSemigroup s where
    (<?>) :: s -> s -> Maybe s
-- | laws: neutral element of <?>, absorbing element of <||>
class PSemigroup s => PMonoid s where
    pempty :: s

-- | absorbing element of <?>, neutral element of <||>
class PSemigroup s => SemiLattice s where
    isBot :: s -> Bool
    bot :: s
-- | laws: associative, commutative, idempotent
-- not distributive over <?>, and usually less accurate
-- (that's why we do case distinction via bdd)
class (PSemigroup s) => PLattice s where
    (<||>) :: s -> s -> Maybe s

-- | a <-> b returns the (ideally minimum) x such that
--   x <??> b  == a
-- intuitively this deduplicates information which is saved elsewhere
-- idempotent
class PSemigroup a => RegularSemigroup a  where
    (<->) :: a -> a -> a

-- | more accurate than pseudoinverse in RegularSemigroup
-- (a <> x) <> inv a  = x
class PSemigroup a => InverseSemigroup a  where
    inv :: a -> a

failedEnv = (False,True,False,False)
failedTest = BOr (BAnd (BOr (BAnd (BLit B2) (BOr (BAnd (BOr (BLit B4) (BLit B3)) (BNot (BLit B4))) (BOr (BAnd (BLit B4) (BLit B2)) (BNot (BLit B1))))) (BLit B1)) (BAnd (BAnd ( BAnd (BOr (BOr (BLit B3) (BLit B4)) (BLit B2)) (BNot (BAnd (BLit B3) (BLit B1)))) (BOr (BLit B1) (BAnd (BOr (BLit B2) (BLit B4)) (BNot (BLit B1))))) (BLit B1))) ( BLit B1)

subT = mkBDD (BAnd (BOr (BAnd (BLit B2) (BOr (BAnd (BOr (BLit B4) (BLit B3)) (BNot (BLit B4))) (BOr (BAnd (BLit B4) (BLit B2)) (BNot (BLit B1))))) (BLit B1)) (BAnd (BAnd ( BAnd (BOr (BOr (BLit B3) (BLit B4)) (BLit B2)) (BNot (BAnd (BLit B3) (BLit B1)))) (BOr (BLit B1) (BAnd (BOr (BLit B2) (BLit B4)) (BNot (BLit B1))))) (BLit B1)))


subb = iff 4 (mLitN 3) (mAnd [mLit 2, mLitN 3])


type Var = Int
data DD s
  = If Var (DD s) (DD s)
  | IsTrue
  | IsFalse
  | And s (S.Set (DD s))
  deriving (Eq, Ord, Show)

type BDD = DD (PMap Var (Val Bool))

data Tag = Absorbing | Neutral

varOf :: IsLit s => DD s -> Var
varOf (If v _ _) = v
varOf (And s ls) = maxSplitVar s `max` (maximum $ (-1:) $ map varOf $ S.toList ls)
varOf a = (-1)

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
    -- go e
      -- | trace ("mOr go " ++ show e) False = undefined
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
    mkTag i@(And s ls)
      | sVar > lVar = (sVar, [i])
      | otherwise = (lVar, [i])
      where
        sVar = maxSplitVar s
        lVar = varOf i
    mkTag i = (varOf i, [i])
split :: IsLit s => Var -> DD s -> (DD s, DD s)
split v (If v' l r)
  | v == v' = (l, r)
  | otherwise = error "illegal split"
split v (And s ls) = 
    case splitLit v s of
       Just (sL, sR) -> (gAnd $ S.fromList $ sL : relL <> invariant, gAnd $ S.fromList $ sR : relR <> invariant)
       Nothing -> (gAndS s $ S.fromList $ relL <> invariant, gAndS s $ S.fromList $ relR <> invariant)
  where
    (rel,invariant) = partition (\i -> varOf i == v) $ S.toList ls
    (relL, relR) = splitMap (split v) rel
split _ a = (a,a)

-- testSplit = split 1 $ And (
mAnd :: forall s. (IsLit s, PMonoid s) => [DD s] -> DD s
-- mAnd inp
--   | trace ("mAnd: " ++ show inp) False = undefined
mAnd inp = flip evalState pempty $ do
   mo <- runMaybeT (allFlatAnds inp)
   case mo of
     Nothing -> pure IsFalse
     Just (s,o) -> addEnv s <$> go (inj o)
  where
    step ls e' = do
         (done, ls') <- partitionEithers <$> traverse simplifyAnd ls
         runMaybeT (allFlatAnds ls') >>= \case
           Nothing -> pure IsFalse
           Just (s, flatLs) -> 
             let ls'' = filter (/= IsTrue) flatLs
             in
             if any (== IsFalse) ls''
              then pure IsFalse
              else do
                 out <- go $ M.unionWith (<>) e' (inj ls'')
                 pure $ gAndS s (S.fromList $ out : done)

    go e
      | M.null e = pure IsTrue
    go e = case M.maxViewWithKey e of
        Nothing -> pure IsTrue
        Just ((v, ls), e') ->  do
         -- traceM $ "go: " ++ show (v, ls)
         pre <- get
         if isJust (evalVar @s v pre)
         then do
           -- traceM ("skip 1: " ++ show (v, ls))
           step ls e'
         else do
             -- traceM ("split 1: " ++ show (v, ls))
             t <- withEnv @s (isL v) $ step ls e'
             -- traceM ("split 2: " ++ show (v, ls))
             f <- withEnv @s (notL v) $ step ls e'
             pure $ iff v t f

    allFlatAnds :: IsLit s => [DD s] -> MaybeT (State s) (s, [DD s])
    allFlatAnds ls = do
        env <- get
        (Just o,s) <- pure (runState (runMaybeT $ traverse flatAnds ls) pempty)
        env' <- liftMaybe $ env <?> s
        put env'
        pure $ (s <-> env, concat o)
                

    flatAnds :: IsLit s => DD s -> MaybeT (State s) [DD s]
    flatAnds (And s ls) = do
       tellEnv s
       lls <- traverse flatAnds $ S.toList ls
       pure $ concat lls
    flatAnds a = pure [a]

    tellEnv s = do
       env <- get
       case s <?> env of
           Nothing -> empty
           Just s' -> put s'

    inj = M.fromListWith (<>) . map (\i -> (varOf i, [i]))

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


foo :: BDD
foo =  mAnd [If 2 IsTrue IsFalse, If 1 IsTrue IsFalse]


simplify :: forall s. IsLit s => DD s -> State s (Either (DD s) (DD s))
simplify (And s ls) = do
    (a,b) <- partitionEithers <$> (traverse simplify $ S.toList ls)
    env <- get
    pure $ Right $  gAndS (s <-> env) $ S.fromList (a <> b)
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


broken = BAnd (BOr (BLit B4) (BAnd (BLit B2) (BLit B2))) (BOr (BAnd (BLit B2) (BLit B3)) ( BNot (BLit B4)))

type SolveEnv = M.Map Var Bool
-- solver :: SolveEnv -> S.Set BDD -> Bool
-- solver = _

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
  (<||>) (PMap l) (PMap r) = Just $ PMap $ M.merge M.dropMissing M.dropMissing (M.zipWithMaybeMatched (const (<||>))) l r

newtype Val a = Val {unVal :: a}
  deriving (Eq, Ord, Show)
instance Eq a => PSemigroup (Val a) where
    (<?>) (Val a) (Val b) = if a == b then Just (Val a) else Nothing
instance (Eq a) => PLattice (Val a) where
    (<||>) (Val a) (Val b) = if a == b then Just (Val a) else Nothing
 
data PMap k v = PMap (M.Map k v)
  deriving (Eq, Ord, Show)
(??) :: (Ord k) => PMap k v -> k -> Maybe v
(??) (PMap m) k = M.lookup k m
instance (Ord k, PSemigroup v) => PSemigroup (PMap k v) where
    (<?>) (PMap m) (PMap m') = case M.mergeA M.preserveMissing M.preserveMissing (M.zipWithAMatched both) m m' of
      Just o -> Just (PMap o)
      Nothing -> Nothing
      where
        both k x y = x <?> y
instance (Ord k, PSemigroup v) => PMonoid (PMap k v) where
    pempty = PMap M.empty

emptyPMap :: PMap k v
emptyPMap = PMap M.empty

instance (Ord k, Eq v, PSemigroup v) => RegularSemigroup (PMap k v) where
    (<->) (PMap m) (PMap m') = PMap $ M.merge M.preserveMissing M.dropMissing (M.zipWithMaybeMatched f) m m'
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
    Just s' -> And (s' <-> isV v b) mempty

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
iff _ a b | a == b = a
-- iff v IsTrue a = litOr (isL v) a 
-- iff v a IsTrue = litOr (notL v) a
iff v IsFalse a = litAnd (notL v) a
iff v a IsFalse = litAnd (isL v) a
iff v a b
  | Just o <- cofactor True v a b = o
  | Just o <- cofactor False v b a = o
iff v (And sl vl) (And sr vr)
  | Just o <-  sl <||> sr = mkOut o
  | not (S.null inters) = mkOut pempty
  where
    mkOut o = gAndS o  (inters & iff' v (gAndS (sl <-> o) (vl S.\\ vr)) (gAndS (sr <-> o)(vr S.\\ vl)))
    inters = S.intersection vl vr
    o =  sl <||> sr
iff v a b = If v a b

cofactor :: IsLit s => Bool -> Var -> (DD s) -> (DD s) -> Maybe (DD s)
cofactor b v l (And s ls)
  | l `S.member` ls = Just $ gAnd' [l,  iff' v b IsTrue (gAndS s $ S.delete l ls)]
   where
     iff' v True l r  = iff v l r
     iff' v False r l = iff v l r
cofactor _ _ _ _ = Nothing

-- testCofactor = cofactor (isL 3) (Leaf $ isL 1) (gAnd' [Leaf $ isL 1, Leaf $ isL 2])
gAnd' b = gAnd (S.fromList b)
gAndS s b = addEnv s $ gAnd b
-- 


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
       case filter (/= top) $ concatMap flatten $ S.toList ls of
        [] -> addEnv env top
        [a] -> addEnv env a
        xs
          | bot `S.member` S.fromList xs -> bot
        xs -> And env (S.fromList xs)
  where
    flattenEnv :: (IsLit s) => [DD s] -> Maybe s
    flattenEnv ls = foldl merge1 (Just pempty) [s | And s _ <- ls]
    merge1 Nothing _ = Nothing
    merge1 (Just m) s = m <?> s
    flatten (And _ ls) = S.toList ls
    flatten a = [a]
    bot = IsFalse
    top = IsTrue

boolToDD :: Bool -> BDD
boolToDD True = IsTrue
boolToDD False = IsFalse
testGroupAnd :: IO ()
testGroupAnd = quickCheck $ \bs -> And pempty (S.fromList $ map boolToDD bs) == boolToDD (and bs)
testGroupOr :: IO ()
testGroupOr = quickCheck $ \bs -> And pempty (S.fromList $ map boolToDD bs) == boolToDD (and bs)
  
iff' v l r = If v l r

-- litOr :: Lit -> BDD -> BDD
-- litOr = undefined
-- litOr l (Group Or as)
--   | Leaf (flipLit l) `S.member` as = IsTrue
--   | otherwise = group And (S.insert (Leaf l) as)
-- litOr l a = group Or $ S.fromList [a, Leaf l]

litAnd :: (IsLit s) => s -> DD s -> DD s
litAnd l a = addEnv l a

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
getEnvUnsafe env v = getEnv env (toEnum (v-1))
reduceNaive :: BExprEnv -> BDD -> Bool
reduceNaive env (If c t e) =
  if getEnvUnsafe env c
  then reduceNaive env t
  else reduceNaive env e
reduceNaive env IsTrue = True
reduceNaive env IsFalse = False
reduceNaive env (And s ds) = case toEnv env <?> s of
    Just env' -> all (reduceNaive env) ds
    Nothing -> False
  where
    toEnv (a,b,c,d) = PMap $ M.fromList $ zip [1..] (map Val [a,b,c,d])
toBDDNaive :: BExpr -> BDD
toBDDNaive (BAnd e1 e2) = mAnd [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BOr e1 e2) = mOr $ [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BNot (BLit idx)) = And (notL (1+fromEnum idx)) mempty
toBDDNaive (BLit idx) = And (isL (1+fromEnum idx)) mempty
toBDDNaive (BNot e) = error $ "Not in NNF " ++ show e
mkBDD :: BExpr -> BDD
mkBDD = toBDDNaive . toNNF
checkEquiv env expr = evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))
checkNaive :: IO ()
checkNaive = quickCheck $ \env expr -> evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))
