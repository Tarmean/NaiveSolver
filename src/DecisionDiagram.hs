{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
-- | Decision trees labeled by lattices
-- Propagates information that holds accross branches upwards
module DecisionDiagram where
import Types
import Test.QuickCheck hiding ((==>))
import GHC.Generics (Generic)
import Generic.Random
    ( withBaseCase, genericArbitraryRec, genericArbitraryU, (%) )
import qualified Data.Map as M
import System.Timeout (timeout)
import Debug.Trace (trace)
import qualified Data.Set as S

import Control.Monad.State ( MonadState(get, put), State , gets, modify, execState)
import Data.List (partition)
import Data.Either (partitionEithers)
import Data.Maybe (isJust)
import Control.Monad.Trans.Maybe ( MaybeT(..) )
import qualified Prettyprinter as P
import Data.Utils (docToString)
import qualified Data.Foldable as F


bddTestEnv :: (Bool, Bool, Bool, Bool)
bddTestEnv = (False,True,False,False)
bddTest :: BExpr
bddTest = BOr (BAnd (BOr (BAnd (BLit B2) (BOr (BAnd (BOr (BLit B4) (BLit B3)) (BNot (BLit B4))) (BOr (BAnd (BLit B4) (BLit B2)) (BNot (BLit B1))))) (BLit B1)) (BAnd (BAnd ( BAnd (BOr (BOr (BLit B3) (BLit B4)) (BLit B2)) (BNot (BAnd (BLit B3) (BLit B1)))) (BOr (BLit B1) (BAnd (BOr (BLit B2) (BLit B4)) (BNot (BLit B1))))) (BLit B1))) ( BLit B1)

toDDF :: DD v s -> DDF v s (DD v s)
toDDF IsTrue = IsTrueF
toDDF IsFalse = IsFalseF
toDDF (Iff v) = IffF v
toDDF (If v s l r) = IfF v s l r

countCard :: (Ord v, Ord s) => DD v s -> M.Map Int Int
countCard bdd = M.fromListWith (+) [(card, 1) | card <- M.elems occs]
  where
    terms = execState (hashCons bdd) mempty
    occs = M.fromListWith (+) [(ref, 1) | term <- M.keys terms, ref <- F.toList term]
hashCons :: (Ord s, Ord v) => DD v s -> State (M.Map (DDF v s Int) Int) Int
hashCons x = do
   xi <- traverse hashCons (toDDF x)
   gets (M.!? xi) >>= \case
       Just o -> pure o
       Nothing -> do
            i <- gets (M.size)
            modify (M.insert xi i)
            pure i


type BDD = DD Var (PMap Var (Val Bool))

kOp :: (Ord v, P.Pretty a, IsLit v a) => a -> (DD v a -> DD v a -> Maybe (DD v a)) -> DD v a -> DD v a -> DD v a
kOp ctx0 f = go ctx0
  where
    -- go p l r
    --   | trace (p <> "kop go " ++ show (l,r)) False = undefined
 -- trace (p <> "kop out: " <> show o)
    -- go l r
    --   | trace (docToString $ P.pretty l P.<> P.pretty " OP " P.<> P.pretty r) False = undefined
    go ctx l r
      | Just o <- f l r = o
    go ctx l r =  ifte v lhs rhs
      where
        -- lhs = trace (p <> "kop iff lhs" <> show v) $ showThis (p <> "kop lhs out: ") (go ('-':p)lx rx)
        lhs = case isL v <?> ctx of
            Nothing -> IsFalse
            Just ctxL -> go ctxL lx rx
        -- rhs = (go ly ry)
        rhs = case notL v <?> ctx of
            Nothing -> IsFalse
            Just ctxL -> go ctxL ly ry
        -- showThis tag a = a `seq` trace (tag <> show a) a
        (lx, ly) = split v l
        (rx, ry) = split v r
        v = maxM lv rv
        lv = varOf l
        rv = varOf r
        maxM Nothing Nothing = error "boo"
        maxM Nothing (Just a) = a
        maxM (Just a) Nothing = a
        maxM (Just a) (Just b) = max a b
kAnd :: (Ord v, P.Pretty a, IsLit v a) => DD v a -> DD v a -> DD v a
kAnd = kOp pempty step
  where
    step IsTrue a = Just a
    step a IsTrue = Just a
    step IsFalse _ = Just IsFalse
    step _ IsFalse = Just IsFalse
    step (Iff l) (Iff r) = case l <?> r of
        Just v -> Just (Iff v)
        Nothing -> Just IsFalse
    step a b 
      | a == b = Just a
    step _ _ = Nothing
kOr :: (Ord v, P.Pretty a, IsLit v a) => DD v a -> DD v a -> DD v a
kOr = kOp pempty step
  where
    step IsFalse a = Just a
    step a IsFalse = Just a
    step IsTrue _ = Just IsTrue
    step _ IsTrue = Just IsTrue
    -- step (Iff l) (Iff r) = case l <||> r of
    --     Is v -> Just (Iff v)
    --     IsTop -> Just IsTrue
    --     IsBot -> Just IsFalse
    step a b 
      | a == b = Just a
    step _ _ = Nothing



data Tag = Absorbing | Neutral

varOf :: (Ord v) => DD v s -> Maybe v
varOf (If v s _ _) = Just v -- max (maxSplitVar s) v
varOf (Iff  s) = Nothing -- maxSplitVar s
varOf _ = Nothing

splitMap :: (a -> (b,c)) -> [a] -> ([b], [c])
splitMap f ls = (fmap fst ls', fmap snd ls')
    where ls' = fmap f ls

-- mOr :: IsLit v s => [DD v s] -> DD v s
-- mOr inp = go (inj inp)
--   where
--     goRec :: IsLit v s => [DD v s] -> M.Map Var [DD v s] -> DD v s
--     goRec a e'
--       | IsTrue `elem` a = IsTrue
--       | otherwise = go (M.unionWith (<>) (inj $ filter (/= IsFalse) a) e')
--     -- go :: M.Map Var [DD v s] -> DD v s
--     go :: IsLit v s => M.Map Var [DD v s] -> DD v s
--     go e
--       | trace ("mOr go " ++ show e) False = undefined
--     -- FIXME: this is horribly inefficient:
--     -- If we have invariants at the top we should keep the union of those invariants at the top
--     -- - the union environment is weaker than any input environment
--     -- - the original environments are stronger so any optimizations had been possible previously => no existing branches become impossible
--     -- - we want to keep the union environment on the surface
--     -- - we want to subtract the union environment from per-node environemtns
--     -- - if an environemnt becomes empty we can replace the node with IsTrue and halt
--     go e = case M.maxViewWithKey e of
--         Nothing -> IsFalse
--         Just ((v, ls0), e') -> 
--             let
--                  ls = filter (/= IsFalse) ls0
--                  (a,b) = splitMap (split v) ls
--                  l = goRec a e'
--                  r = goRec b e'
--             in 
--               if  
--                 | null ls -> IsFalse
--                 | IsTrue `elem` ls -> IsTrue
--                 | otherwise -> iff v l r
--     inj :: IsLit v s => [DD v s] -> M.Map Var [DD v s]
--     inj = M.fromListWith (<>) . map mkTag
--     -- mkTag i@(And s _)
--     --   | sVar > lVar = (sVar, [i])
--     --   | otherwise = (lVar, [i])
--     --   where
--     --     sVar = maxSplitVar s
--     --     lVar = varOf i
--     mkTag i = (varOf i, [i])
split :: (Eq v, IsLit v s )=> v -> DD v s -> (DD v s, DD v s)
split v w@(If v' s l r)
  | v == v' = case splitLit v s of
     Nothing -> (withDomain s l, withDomain s r)
     Just (sl, sr) -> (splitMkAnd sl l, splitMkAnd sr r)
  | otherwise = case splitLit v s of
     Nothing -> (w,w)
     Just (sl, sr) -> (splitMkIf v' sl l r, splitMkIf v' sr l r)

  where
    splitMkIf var IsTrue x y = If var pempty x y
    splitMkIf _ IsFalse _ _ = IsFalse
    splitMkIf var (Iff s') x y = If var s' x y
    splitMkIf _ _ _ _ = undefined
    splitMkAnd :: IsLit v s => DD v s -> DD v s -> DD v s
    splitMkAnd IsTrue a = a
    splitMkAnd IsFalse _ = IsFalse
    splitMkAnd (Iff s') a = withDomain s' a
    splitMkAnd _ _ = error "Illegal splitMkAnd"
-- split v (And s ls) = 
--     case splitLit v s of
--        Just (sL, sR) -> (gAnd $ S.fromList $ sL : relL <> invariant, gAnd $ S.fromList $ sR : relR <> invariant)
--        Nothing -> (gAndS s $ S.fromList $ relL <> invariant, gAndS s $ S.fromList $ relR <> invariant)
--   where
--     (rel,invariant) = partition (\i -> varOf i == v) $ S.toList ls
--     (relL, relR) = splitMap (split v) rel
split v (Iff s) = case splitLit v s of
    Just (sl, sr) -> (sl, sr)
    Nothing -> (iff s, iff s)
split _ a = (a,a)

withDomain :: IsLit v s => s -> DD v s -> DD v s
withDomain s (If v s' l r) = case s <?> s' of
   Nothing -> IsFalse
   Just s'' -> If v s'' l r
withDomain s IsTrue = iff s
withDomain s IsFalse = IsFalse
withDomain s (Iff s') = case s <?> s' of
   Nothing -> IsFalse
   Just s'' -> iff s''



liftMaybe :: Applicative m => Maybe s -> MaybeT m s
liftMaybe = MaybeT . pure

withEnv :: IsLit v s => s -> State s a -> State s a
withEnv s m = do
  env <- get
  o <- case s <?> env of
    Nothing -> error ("Illegal env: " <> show s <> ", " <> show env)
    Just env' -> put env' *> m
  put env
  pure o


-- foo :: BDD
-- foo =  mAnd [If 2 IsTrue IsFalse, If 1 IsTrue IsFalse]


simplify :: forall s v. IsLit v s => DD v s -> State s (Either (DD v s) (DD v s))
-- simplify (And s ls) = do
--     (a,b) <- partitionEithers <$> (traverse simplify $ S.toList ls)
--     env <- get
--     pure $ Right $  gAndS (env ==> s) $ S.fromList (a <> b)
-- simplify (Iff v l r) = do
simplify (If v s l r) = do
    env <- get
    case s <?> env of
      Nothing -> pure (Right IsFalse)
      Just env' -> do
        put env'
        o <- case evalVar @v @s v env of
            Nothing -> pure $ Right $ If v (env ==> env') l r
            Just True -> simplify l
            Just False -> simplify r
        put env
        pure o
simplify (Iff s) = do
    env <- get
    case s <?> env of
      Nothing -> pure (Right IsFalse)
      Just env' -> pure (Right $ iffMaybe (env ==>? env'))
simplify IsTrue = pure $ Right IsTrue
simplify IsFalse = pure $ Right IsFalse
-- simplify a@(Leaf _) = pure $ Right a
simplifyAnd :: IsLit v s => DD v s -> State s (Either (DD v s) (DD v s))
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

mNot :: (Ord v, InverseSemigroup s, IsLit v s) => DD v s -> DD v s
mNot (If v s t f) = If v (inv s) (mNot t) (mNot f)
mNot (Iff s) = iff (inv s)
-- mNot (And s xs) = mOr $ (And (inv s) mempty:) $ map mNot $ S.toList xs
mNot IsTrue = IsFalse
mNot IsFalse = IsTrue


mLit :: Var -> BDD
mLit v = Iff (isL v)

mLitN :: Var -> BDD
mLitN v = Iff (notL v)




orBot :: Maybe s -> DD v s
orBot Nothing = IsFalse
orBot (Just s) = Iff s


minusDomain :: RegularSemigroup s => s -> DD v s -> DD v s
minusDomain s1 (Iff s2) = case s1 ==>? s2 of
    Nothing -> IsTrue
    Just s -> Iff s
minusDomain s1 (If v s2 a b) = If v (s1 ==> s2) a b
minusDomain _ a = a

(&) :: Ord a => S.Set a -> a -> S.Set a
a & b = S.insert b a

joinDomain :: PMonoid s => DD v s -> DD v s -> Maybe s
joinDomain (If _ s1 _ _) (If _ s2 _ _) = s1 <?> s2
joinDomain (Iff s1) (If _ s2 _ _) = s1 <?> s2
joinDomain (If _ s1 _ _) (Iff s2) = s1 <?> s2
joinDomain (Iff s1) (Iff s2) = s1 <?> s2
joinDomain _ _ = Just pempty
meetDomain :: (PLattice s) => DD v s -> DD v s -> LatticeVal s
meetDomain (If _ s1 _ _) (If _ s2 _ _) = s1 <||> s2
meetDomain (Iff s1) (If _ s2 _ _) = s1 <||> s2
meetDomain (If _ s1 _ _) (Iff s2) = s1 <||> s2
meetDomain (Iff s1) (Iff s2) = s1 <||> s2
meetDomain _ _ = IsTop

ifte :: (Eq v, IsLit v s) => v -> DD v s -> DD v s -> DD v s
ifte v a b = case meetDomain a b of
   IsTop -> ifteNRec v a b
   IsBot -> IsFalse
   Is s -> withDomain s $ ifteNRec v (minusDomain s a) (minusDomain s b)

ifteNRec :: (Eq v, IsLit v s) => v -> DD v s -> DD v s -> DD v s
ifteNRec _ a b | a == b = a
ifteNRec v IsFalse a = withDomain (notL v) a
ifteNRec v a IsFalse = withDomain (isL v) a
ifteNRec v a b = If v pempty a b


-- testCofactor = cofactor (isL 3) (Leaf $ isL 1) (gAnd' [Leaf $ isL 1, Leaf $ isL 2])
gAnd' :: IsLit v s => [DD v s] -> DD v s
gAnd' b = gAnd b
gAndS :: IsLit v s => s -> [DD v s] -> DD v s
gAndS s b = withDomain s $ gAnd b
-- 



gAnd :: (IsLit v s) => [DD v s] -> DD v s
gAnd ls 
  | null ls = IsTrue
  | otherwise = foldr1 flatAnd ls
  where
    flatAnd (Iff a) (Iff b) = case a <?> b of
        Nothing -> IsFalse
        Just s -> Iff s
    flatAnd IsTrue a = a
    flatAnd a IsTrue = a
    flatAnd IsFalse _ = IsFalse
    flatAnd _ IsFalse = IsFalse
    flatAnd _ _ = error "flatAnd not flat"
  -- case flattenEnv (S.toList ls) of
  --   Nothing -> IsFalse
  --   Just env -> 
  --      case filter (/= IsTrue) $ concatMap flatten $ S.toList ls of
  --       [] -> withDomain env IsTrue
  --       [a] -> withDomain env a
  --       xs
  --         | IsFalse `S.member` S.fromList xs -> IsFalse
  --       xs -> And env (S.fromList xs)
  -- where
  --   flattenEnv :: (IsLit v s) => [DD v s] -> Maybe s
  --   flattenEnv es = pempty -- foldl merge1 (Just pempty) [s | And s _ <- es]
  --   merge1 Nothing _ = Nothing
  --   merge1 (Just m) s = m <?> s
  --   -- flatten (And _ es) = S.toList es
  --   flatten a = [a]

boolToDD :: Bool -> BDD
boolToDD True = IsTrue
boolToDD False = IsFalse
testGroupAnd :: IO ()
testGroupAnd = quickCheck $ \bs ->  gAnd (map boolToDD bs) == boolToDD (and bs)
testGroupOr :: IO ()
testGroupOr = quickCheck $ \bs -> gAnd (map boolToDD bs) == boolToDD (and bs)
  
litAnd :: (IsLit v s) => s -> DD v s -> DD v s
litAnd l a = withDomain l a



data BLit = B1 | B2 | B3 | B4
  deriving (Eq, Ord, Show, Generic, Enum, Bounded)
instance Arbitrary BLit where
    arbitrary = genericArbitraryU
data BExpr = BAnd BExpr BExpr | BOr BExpr BExpr | BNot BExpr | BLit BLit
  deriving (Eq, Ord, Show, Generic)
instance Arbitrary BExpr where
    arbitrary = genericArbitraryRec (2 % 2 % 1 % 1 % ()) `withBaseCase` (BLit <$> arbitrary)
    shrink = genericShrink
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
reduceNaive env (Iff s) = isJust (toEnv env <?> s)
  where    toEnv (a,b,c,d) = PMap $ M.fromList $ zip [1..] (map Val [a,b,c,d])
reduceNaive env (If c s t e) =
  isJust (toEnv env <?> s) && if getEnvUnsafe env c
                              then reduceNaive env t
                              else reduceNaive env e
  where    toEnv (a,b,c,d) = PMap $ M.fromList $ zip [1..] (map Val [a,b,c,d])
reduceNaive _ IsTrue = True
reduceNaive _ IsFalse = False
-- reduceNaive env (And s ds) = isJust (toEnv env <?> s) && all (reduceNaive env) ds
--   where
toBDDNaive :: BExpr -> BDD
toBDDNaive (BAnd e1 e2) = kAnd (toBDDNaive e1) (toBDDNaive e2)
toBDDNaive (BOr e1 e2) = kOr (toBDDNaive e1) (toBDDNaive e2)
toBDDNaive (BNot (BLit idx)) = Iff (notL (1+fromEnum idx))
toBDDNaive (BLit idx) = Iff (isL (1+fromEnum idx))
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
doesTerminate = fmap isJust . timeout 12000 . (\x -> x `seq` pure ()) . toBDDNaive

-- testSplit = split 1 $ And (
-- mAnd :: forall s. (IsLit v s, PMonoid s) => [DD v s] -> DD v s
-- mAnd inp
--   | trace ("mAnd: " ++ show inp) False = undefined
-- mAnd inp = flip evalState pempty $ do
--    mo <- runMaybeT (allFlatAnds inp)
--    case mo of
--      Nothing -> pure IsFalse
--      Just (s,o) -> withDomain s <$> go (inj o)
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

--     allFlatAnds :: IsLit v s => [DD v s] -> MaybeT (State s) (s, [DD v s])
--     allFlatAnds ls = do
--         env <- get
--         (Just o,s) <- pure (runState (runMaybeT $ traverse flatAnds ls) pempty)
--         env' <- liftMaybe $ env <?> s
--         put env'
--         pure $ (env ==> s, concat o)

--     flatAnds :: IsLit v s => DD v s -> MaybeT (State s) [DD v s]
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
