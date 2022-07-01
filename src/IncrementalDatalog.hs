{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module IncrementalDatalog where
import Language.KURE as K

-- Input: Streams of values
-- Data flow DAG with Prior(x) command
-- use of Prior(x) => x requires storage
--
-- We diff and incrementalize values
-- - diff(x) = Prior(x) - x
-- - integrate(v) = letI x = (v + Prior(x)) in x
--
-- Idea: give streams names?


import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as MM
import Control.Applicative
import qualified Data.IntMap as IM
import qualified Data.Set as S
import Control.Lens hiding (Context, transform)
import Data.String
import GHC.IO.Unsafe (unsafePerformIO)
import qualified Data.IORef as IOR


{-# NOINLINE uniq_hack #-}
uniq_hack :: IOR.IORef Int
uniq_hack = unsafePerformIO (IOR.newIORef 0)
{-# INLINE genUniq #-}
genUniq :: Int
genUniq = unsafePerformIO $ do
    IOR.modifyIORef uniq_hack (+1)
    (IOR.readIORef uniq_hack)

data Info = Monotone | Incremental | None
    deriving (Show, Eq, Ord)
data Var = Var { ident :: !Ident, uniq :: !Int }
    deriving (Show, Eq, Ord)
data ADT d = App Var [ADT d] | V Var | Prior (ADT d) | Diff (ADT d) | Integrate (ADT d) | Let [(d, Var, (ADT d))] (ADT d) | Abs Var (ADT d)
    deriving (Show, Eq, Ord)
newtype Ident = Ident String
    deriving (Show, Eq, Ord)
data Context = Ctx { in_scope :: M.Map Ident Int, shifted :: M.Map Ident Int }
    deriving (Show, Eq, Ord)
emptyContext :: Context
emptyContext = Ctx mempty mempty
addVar :: Ident -> Context -> Context
addVar v (Ctx s t) = Ctx (s & at v . non 0 +~ 1) t
addVars :: [Ident] -> Context -> Context
addVars vs c = foldr addVar c vs
dropVars :: M.Map Ident Int -> Context -> Context
dropVars vs Ctx{..} = Ctx{in_scope = MM.merge MM.preserveMissing (MM.mapMissing (const negate)) (MM.zipWithMaybeMatched $ \_ a b -> iff (/= 0) (a - b)) in_scope vs, ..}
  where
    iff p v
      | p v = Just v
      | otherwise = Nothing
instance K.Walker Context (ADT d) where
  allR f = transform $ \c v -> case v of
    App s ts -> App s <$> traverse (applyT f c) ts
    V s -> pure $ V s
    Prior x -> Prior <$> applyT f c x
    Diff x -> Diff <$> applyT f c x
    Integrate x -> Integrate <$> applyT f c x
    Let xs x -> Let <$> traverse (\(t,n,b) -> (t,n,) <$> applyT f c b) xs <*> applyT f c x
    Abs s x -> Abs s <$> applyT f c x




instance IsString Ident where
  fromString = Ident
instance IsString Var where
  fromString a = Var (Ident a) genUniq



test :: ADT Info
test = (Let [(None, b, App "nono" [])] (Let [(None, a, (V a))] (V a))) 
  where
    a = "a"
    b = "b"

testAp :: IO (ADT Info)
testAp = applyR (substitute (M.singleton "a" (V "b")) ) emptyContext test

substitute :: MonadCatch m => M.Map Var (ADT d) -> Rewrite Context m (ADT d)
substitute m = alltdR $ transform $ \_ -> \case
    V v | Just o <- m M.!? v -> pure o
    o -> pure o



pushDiff :: Applicative m => ADT d -> m (ADT d)
pushDiff (Diff (Prior x)) = (Prior <$> (pushDiff (Diff x)))
pushDiff (Diff (App s adt)) = pure $ mkDiff s adt
pushDiff (Diff (Integrate a)) = pure a
pushDiff a = pure a

mkDiff = undefined

data Table k v = Table { old :: M.Map k v, new :: M.Map k v, def :: Maybe v }
  deriving (Show, Eq, Ord, Functor)

instance Ord k => Alternative (Table k) where
  empty = Table M.empty M.empty Nothing
  Table o n d <|> Table o' n' d' = Table (M.union o o') (M.union n n') (d <|> d')

instance Ord k => Applicative (Table k) where
    pure x = Table mempty mempty (Just x)
    Table f g h <*> Table x y z = Table (M.map unwrap $ merge2 newL newR f x) newMerged  (h <*> z)
      where
        newMerged = M.map unwrap $ merge2 newL newR g y +++ merge2 old newR f y +++ merge2 newL old g x
        merge2 :: (MM.SimpleWhenMissing k (a -> b) (Either b b)
                  -> MM.SimpleWhenMissing k a (Either b b)
                  -> M.Map k (a -> b)
                  -> M.Map k a
                  -> M.Map k (Either b b))
        merge2 onL onR = MM.merge onL onR (MM.zipWithMatched (\_ c v -> Right (c v)))

        (+++) :: M.Map k (Either b b) -> M.Map k (Either b b) -> M.Map k (Either b b)
        (+++) = MM.merge (MM.preserveMissing) (MM.preserveMissing) (MM.zipWithMatched merge1)
        unwrap (Left a) = a
        unwrap (Right a) = a
        merge1 _ (Right a) _ = Right a
        merge1 _ (Left _) (Right a) = Right a
        merge1 _ a _ = a
        newL = MM.mapMaybeMissing (\_ c -> Left . c <$> z)
        newR = MM.mapMaybeMissing (\_ v -> (\c -> Left (c v)) <$> h)
        old = MM.dropMissing

type Id = Int
data DB k v = DB { table :: IM.IntMap v, index :: M.Map k (S.Set Id) }
  deriving (Eq, Ord, Show, Functor)
-- Idea: seperate indices from tables
-- Table: IntMap Id a
-- Index: Map k (S.IdSet)
--
-- - We pull indices to the front using some combinator
-- - Applicative merges on indices, giving a stream `[(Id,Id)]`
-- - Join tables on those indices
-- - Later, re-add default fallback for outer joins 


userTable :: Table Int String
userTable = Table (M.fromList [(2, "Bob"), (3, "Charlie")]) (M.fromList [(1, "Alice")])  Nothing


heightTable :: Table Int Int
heightTable = Table (M.fromList [(1, 25), (2, 7)]) (M.fromList [(4, 14)])  Nothing



class Apply s a where
    apply :: s -> a -> Maybe a
newtype Removed a = Removed { _0 :: a}
    deriving (Eq, Ord, Show)
newtype Remaining a = Remaining { _0 :: S.Set a}
    deriving (Eq, Ord, Show)
instance Ord a => Apply (Removed a) (Remaining a) where
    apply removed remaining
      | removed._0 `S.member` remaining._0 = Just $ Remaining (removed._0 `S.delete` remaining._0)
      | otherwise = Nothing

-- data Stream = Diff Stream | Integrate Stream | Let Tag Var Stream Stream | Prev Stream | Inp String | DOp String [Stream] | Op String [Stream] | Ref String


-- foldM step zero ls = do
--     s <- store zero
--     make $ do
--         x <- read (diff ls)
--         s0 <- read (prevP s)
--         put s (step s0 x)
-- test = (Let Idempotent "s" (DOp "f" [Prev (Ref "s"), Diff (Inp "Delete")]) (Inp "s"))
-- Delete 1 1; Delete 1 2; Delete 1 3;
--
--
-- Table Delete
-- Leftover, idempotent, replacing: Delete(s,b) = Pure (s \\ b)
-- leftover(a,r): leftover_mem(a) := r
--
-- Delete(s,b) | S.member b s._0 = Just (drop b s)
-- Remaining(s,fold(universe, b => delete x b, Delete(s,x)));
--
-- temp_insert;
-- on: Delete(s,x); Remaining(s, temp_insert.getOr(s, universe) - x)
-- on: Remaining(s,out): temp_insert.insert(s, out); 

-- all_different(g,l), leftover(l, s), digit=singleton(s) 

-- not_equals(var: Cell, digit: SudokuNum)
-- for (k,v) in not_equals.group(var).fold(universe, (x,y) => x \\ y): leftover(k,v)
--
--for (g,l) in all_different:
--     for {digit} in leftover[0=l]:
    --     for r in all_different[0=g]:
    --         if l != r:
    --           not_equals(r, digit)
    --
    -- (g,l) <- all_different
    -- digits <- leftover[0=l]
-- not_equals(var2: Cell, digit: SudokuNum) :- all_different(vars: Set<Cell>), in(var, vars), leftover(var, {digit}), in(var2, vars), var2 /= var

data Datalog s k a where
    Map :: (a -> b) -> Datalog s k a -> Datalog s k b
    Filter :: (k -> a -> Bool) -> Datalog s k a -> Datalog s k a
    Pure :: a -> Datalog s k a
    Source :: s k a -> Datalog s k a
    IndexBy :: (a -> g) -> Datalog s k a -> Datalog s (k,g) a
    Zip :: Datalog s k a -> Datalog s k b -> Datalog s k (a,b)
    Broadcast :: Datalog s l a -> Datalog s r b -> Datalog s (l,r) (a,b)
    -- Alt :: Datalog k a -> Datalog k a -> Datalog k a
    -- Empty :: Datalog k a
    -- Default :: a -> Datalog k a -> Datalog k a
