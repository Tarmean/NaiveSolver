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
import Data.Maybe (isJust)
import Control.Applicative
import Control.Monad.Trans.Maybe




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
    go e
      | trace ("mOr go " ++ show e) False = undefined
    -- FIXME: The And lattice element has to be split here
    -- But technically it doesn't have ot cause the split?
    -- Like, one half of the split is always 0
    -- So maybe:
    -- - add an operator which specializes the lattice for v=True/v=False? isn't this the same as merging?
    -- - apply it when needed?
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
    mkTag i = (varOf i, [i])
split :: IsLit s => Var -> DD s -> (DD s, DD s)
split v (If v' l r)
  | v == v' = (l, r)
  | otherwise = error "illegal split"
split v (And s ls) = (gAndS s $ S.fromList $ relL <> invariant, gAnd $ S.fromList $ relR <> invariant)
  where
    -- ((sL, sR), se) = case splitLit v s of
    --    Just o -> (o, mempty)
    --    Nothing -> (undefined, s)
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
         traceM $ "go: " ++ show (v, ls)
         pre <- get
         if isJust (evalVar @s v pre)
         then do
           traceM ("skip 1: " ++ show (v, ls))
           step ls e'
         else do
             traceM ("split 1: " ++ show (v, ls))
             t <- withEnv @s (isL v) $ step ls e'
             traceM ("split 2: " ++ show (v, ls))
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

-- mNot :: IsLit s => DD s -> DD s
mNot (If v t f) = If v (mNot t) (mNot f)
mNot (And s xs) = undefined -- mOr $ map mNot $ S.toList xs
mNot IsTrue = IsFalse
mNot IsFalse = IsTrue
-- mNot (Leaf (L v b)) = Leaf $ L v (not b)


mLit :: Var -> BDD
mLit v = And (isL v) mempty



class (Show s, RegularSemigroup s, PMonoid s, Show s, Ord s) => IsLit s where
  -- type Env s
  -- type Env s = ()
  isL :: Var -> s
  notL :: Var -> s
  maxSplitVar :: s -> Var
  splitLit :: Var -> s -> Maybe (DD s,DD s)
  evalVar :: Var -> s -> Maybe Bool
  -- intoEnv :: s -> s
  -- inEnv :: Env s -> s -> Maybe (DD s)
class PSemigroup s => SemiLattice s where
    isBot :: s -> Bool
    bot :: s
class PSemigroup s where
    (<?>) :: s -> s -> Maybe s
newtype Val a = Val {unVal :: a}
  deriving (Eq, Ord, Show)
instance Ord a => PSemigroup (Val a) where
    (<?>) (Val a) (Val b) = if a == b then Just (Val a) else Nothing
class PSemigroup a => InverseSemigroup a  where
    inv :: a -> a
class PSemigroup a => RegularSemigroup a  where
    (<->) :: a -> a -> a
 
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
class PSemigroup s => PMonoid s where
    pempty :: s
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
        
instance IsLit (PMap Var (Val Bool)) where
    isL v = PMap $ M.singleton v (Val True)
    notL v = PMap $ M.singleton v (Val False)
    maxSplitVar (PMap p) = case M.maxViewWithKey p of
      Nothing -> -1
      Just ((v,_),_) -> v
    splitLit _ _ = Nothing
      -- Nothing -> Nothing
      -- Just (Val True) -> Just (p, PMap $ M.singleton v (Val False))
      -- | v == v' = case b of
      --   True -> Just (IsTrue, IsFalse)
      --   False -> Just (IsFalse, IsTrue)
      -- | otherwise = Nothing
    evalVar v env = fmap unVal $ env ?? v
    -- type Env Lit = PMap Var (Val Bool)
    -- intoEnv (L v b) = PMap $ M.singleton v (Val b)
    -- inEnv env (L v b) = case env ?? v of
    --    Nothing -> Just $ Leaf (L v b)
    --    Just (Val b')
    --      | b == b' -> Just $ IsTrue
    --      | otherwise -> Just IsFalse

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
  |  not (S.null inters)
   = case sl <?> sr of
     Nothing -> IsFalse
     Just o -> gAndS o  (inters & iff' v (gAndS (sl <-> o) (vl S.\\ vr)) (gAndS (sr <-> o)(vr S.\\ vl)))
  where inters = S.intersection vl vr
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
getEnvUnsafe env v = getEnv env (toEnum v)
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
    toEnv (a,b,c,d) = PMap $ M.fromList $ zip [0..] (map Val [a,b,c,d])
toBDDNaive :: BExpr -> BDD
toBDDNaive (BAnd e1 e2) = mAnd [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BOr e1 e2) = mOr $ [toBDDNaive e1, toBDDNaive e2]
toBDDNaive (BNot (BLit idx)) = And (notL (fromEnum idx)) mempty
toBDDNaive (BLit idx) = And (isL (fromEnum idx)) mempty
toBDDNaive (BNot e) = error $ "Not in NNF " ++ show e
mkBDD :: BExpr -> BDD
mkBDD = toBDDNaive . toNNF
checkNaive :: IO ()
checkNaive = quickCheck $ \env expr -> evalBExpr env expr == reduceNaive env (toBDDNaive (toNNF expr))
