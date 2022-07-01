{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
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
import Optics
import Data.String
import GHC.IO.Unsafe (unsafePerformIO)
import qualified Data.IORef as IOR
import GHC.Generics (Generic)
import Debug.Trace (trace, traceM)
import Control.Arrow
import Data.Kind (Type)
import Control.Monad.State.Strict



-- ala Lazy depth first search and linear graph algorithms in Haskell
-- we mostly use the scc algorithm for dependency analysis to split recursive
-- binding groups
type Graph k = M.Map k (S.Set k)
transposeG :: Ord k => Graph k -> Graph k
transposeG g = M.fromListWith S.union $ do
  (k, s) <- M.toList g
  k' <- S.toList s
  return (k', S.singleton k)
data RoseTree a = Node { val ::  a, children :: [RoseTree a] }
    deriving (Generic, Eq, Ord, Show)
type Forest a = [RoseTree a]
dfs :: Ord k => [k] -> Graph k -> Forest k
dfs ls g = concat $ evalState (traverse go ls) S.empty
  where
    go l = do
        s <- get
        if S.member l s
        then pure []
        else do
            put (S.insert l s)
            cs <- traverse go $ S.toList $ M.findWithDefault mempty l g
            pure [Node l (concat cs)]
dff :: Ord k => Graph k -> Forest k
dff g = dfs (M.keys g) g
postOrder :: RoseTree k -> [k]
postOrder (Node k ls) = concatMap postOrder ls ++ [k]
inOrder :: Ord k => RoseTree k -> [k]
inOrder (Node k ls) = k : concatMap inOrder ls
postOrd :: Ord k => Graph k -> [k]
postOrd = concatMap postOrder . dff
topoSort :: Ord k => Graph k -> [k]
topoSort = reverse . postOrd

scc :: Ord k => Graph k -> [RoseTree k]
scc g = dfs (topoSort (transposeG g)) g


sccTest :: M.Map Var (S.Set Var)
sccTest = M.fromList
        [ (a, S.fromList [b,c])
        , (b, S.fromList [a,f])
        , (e, S.fromList [a,f])
        , (f, S.fromList [g])
        , (c, S.fromList [b,g,h])
        , (d, S.fromList [c])
        , (g, S.fromList [f])
        , (h, S.fromList [g,d])
        , (i, S.fromList [d,h])
        ]
  where
    a = "a"
    b = "b"
    c = "c"
    d = "d"
    e = "e"
    f = "f"
    g = "g"
    h = "h"
    i = "i"
-- >>> inOrder <$> scc sccTest 
-- [[f_4,g_7],[a_1,b_2,c_5,h_8,d_6],[e_3],[i_9]]

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
    deriving (Eq, Ord)
instance Show Var where
    show Var {..} = ident._0 <> "_" <> show uniq
data ADT d = App d Var [ADT d] | V Var | Prior d (ADT d) | Diff d (ADT d) | Integrate d (ADT d) | Let d [(Var, (ADT d))] (ADT d) | Abs d Var (ADT d) | Iff d (ADT d) (ADT d) (ADT d)
    deriving (Show, Eq, Ord)

algebra :: Algebra d s => d s -> s
algebra = algebraM
instance AlgebraM a s () where
   algebraM _ = ()
   
class Analysis s where
   inAlt :: s -> s -> s
   inSeq :: s -> s -> s
   inCall :: s -> s -> s
   diffA :: s -> s -> s
   default diffA :: (Eq s) => s -> s -> s
   diffA l r
     | l == r = topA
     | otherwise = l
   topA :: s
   botA :: s
data MAna k v = MAna { elems :: M.Map k v } | MBot
    deriving (Show, Eq, Ord)
instance WithoutVars (MAna Var v) where
    withoutVars ls (MAna v) = MAna (foldr M.delete v ls)
    withoutVars _ MBot = MBot
instance WithoutVars () where
    withoutVars _ _ = ()
instance (Eq s, Ord k, Analysis s) => Analysis (MAna k s) where
   inAlt MBot a = a
   inAlt a MBot = a
   inAlt (MAna l) (MAna r) = MAna $ MM.merge (MM.mapMissing (const $ inAlt topA)) (MM.mapMissing (const $ flip inAlt topA)) (MM.zipWithMaybeMatched step) l r
     where
       step _ a b
         | out == topA = Nothing
         | otherwise = Just out
         where out = inAlt a b
   inSeq (MAna l) (MAna r)
     =  MAna $ MM.merge MM.preserveMissing MM.preserveMissing (MM.zipWithMatched step) l r
      where
       step _ a b = out
         where out = inSeq a b
   inSeq _ _ = MBot
   inCall _ _ = undefined
   botA = MBot
   topA = MAna mempty
   diffA (MAna l) (MAna r) = MAna (MM.merge MM.preserveMissing MM.dropMissing (MM.zipWithMaybeMatched step) l r)
     where
       step _ a b
         | a == b = Nothing
         | otherwise = Just a
   diffA l _ = l
allJoinA :: (Ord k, Eq s, Analysis s) => s -> MAna k s -> MAna k s
allJoinA _ MBot = MBot
allJoinA s (MAna l) = MAna $  M.map step l
 where
   step b = inCall s b

findFixpointBW :: forall k s. (Show k, Show s, Ord k, Eq s, Analysis s) => M.Map k (MAna k s) -> MAna k s -> MAna k s
findFixpointBW step r0 
  -- | trace ("findFixpointBW" <> show (step, r0)) False = undefined
  | otherwise = go r0 r0
  where
    go :: (Ord k, Eq s, Analysis s) => MAna k s -> MAna k s -> MAna k s
    go _ MBot = MBot
    go seen frontier
      | topA == frontier = seen
      -- | trace (show ("go", seen, frontier, steppedFrontier, new)) False = undefined
      | otherwise = go global  (diffA global seen)
     where
       global = inSeq seen new
       new = foldr inSeq topA steppedFrontier
       steppedFrontier = M.intersectionWith allJoinA frontier.elems step

-- findFixpointFW :: forall k s. (Show k, Show s, Ord k, Eq s, Analysis s) => M.Map k (MAna k Arity) -> M.Map k s -> M.Map k s
-- findFixpointFW step r0 
--   -- | trace ("findFixpoint" <> show (step, r0)) False = undefined
--   | otherwise = go r0 r0'
--   where
--     r0' = MAna $ M.union r0.elems (M.fromList [(k, botA) | k <- M.keys step])
--     go :: (Ord k, Eq s, Analysis s) => MAna k s -> MAna k s -> MAna k s
--     go _ MBot = MBot
--     go seen frontier
--       | topA == frontier = seen
--       -- | trace (show ("go", seen, frontier, steppedFrontier, new)) False = undefined
--       | otherwise = go global  (diffA global seen)
--      where
--        global = inSeq seen new
--        new = foldr inSeq topA steppedFrontier
--        steppedFrontier = M.intersectionWith allJoinA frontier.elems step


findFixpointBW' :: (Show Var, Show s, Eq s, Analysis s) => [(Var, MAna Var s)] -> MAna Var s -> MAna Var s
findFixpointBW' l r = findFixpointBW (M.fromList l) r

mkAna :: Var -> s -> MAna Var s
mkAna v s = MAna $ M.singleton v s
data ADTF r = AppF Var [r] | VF Var | PriorF r | DiffF r | IntegrateF r | LetF [(Var, r)] r | AbsF Var r | IffF r r r
    deriving (Show, Eq, Ord, Foldable, Functor)
instance AlgebraM ADTF (MAna Var Arity) (MAna Var Arity) where
  algebraM (VF var) = mkAna var usedOnce
  algebraM (PriorF f) = f
  algebraM (AppF f ls) = foldr inSeq topA (mkAna f usedOnce : ls)
  algebraM (DiffF f) = f
  algebraM (IntegrateF f) = f
  algebraM (LetF l f) = findFixpointBW' l f
  algebraM (AbsF _ f) = f
  algebraM (IffF v l r) = inSeq v (l `inAlt` r)

--            Zero-Many
--             /     \
--      Zero-Once    Once-Many
--          /     \ /     \
--  Zero-Zero  Once-Once  Many-Many
--          \      |      /
--           --    |    --
--              \  |   /
--                ABot
--
data Arity1 = Zero | Once | Many
    deriving (Show, Eq, Ord, Bounded, Enum)
arPlus :: Arity1 -> Arity1 -> Arity1
arPlus Zero a = a
arPlus a Zero = a
arPlus _ _ = Many
arMult :: Arity1 -> Arity1 -> Arity1
arMult Zero _ = Zero
arMult _ Zero = Zero
arMult Once a = a
arMult a Once = a
arMult _ _ = Many
usedOnce :: Arity
usedOnce = Arity Once Once
data Arity = Arity { lb :: Arity1, ub :: Arity1 } | ABot
    deriving (Show, Eq, Ord)
mkArity :: Arity1 -> Arity1 -> Arity
mkArity l r 
  | l > r = ABot
  | otherwise = Arity l r
instance Analysis Arity where
  inAlt l@Arity{} r@Arity{} = mkArity (min l.lb r.lb) (max l.ub r.ub)
  inAlt ABot a = a
  inAlt a ABot = a
  inSeq l@Arity{} r@Arity{} = mkArity (l.lb `arPlus` r.lb) (l.ub `arPlus` r.ub)
  inSeq _ _ = ABot
  inCall l@Arity{} r@Arity{} = mkArity (l.lb `arMult` r.lb) (l.ub `arMult` r.ub)
  inCall _ _ = ABot
  topA = Arity Zero Zero
  botA = ABot

data Terminates = Terminates | MayDiverge | DoesNotTerminate
    deriving (Show, Eq, Ord)
instance Analysis Terminates where
  inAlt a b 
    | a == b = a
  inAlt _ _ = MayDiverge
  inSeq a b
    | a == b = a
  inSeq DoesNotTerminate _ = DoesNotTerminate
  inSeq _ DoesNotTerminate = DoesNotTerminate
  inSeq _ _ = MayDiverge

  inCall _ b = b
  topA = Terminates
  botA = DoesNotTerminate

type family Step d :: Type -> Type
class Functor (Step d) => InjStep d where
    injStep :: d -> Step d d
type instance Step (ADT d) = ADTF
instance InjStep (ADT d) where
    injStep (V v) = VF v
    injStep (Prior _ f) = PriorF f
    injStep (App _ f ls) = AppF f ls
    injStep (Diff _ f) = DiffF f
    injStep (Integrate _ f) = IntegrateF f
    injStep (Let _ l f) = LetF l f
    injStep (Abs _ v f) = AbsF v f
    injStep (Iff _ v l r) = IffF v l r

mutual :: (InjStep d) => (Step d (a,b) -> a) -> (Step d (a,b) -> b) -> d -> (a,b)
mutual f g = (f &&& g) . fmap (mutual f g) . injStep

cata :: (InjStep d, Algebra (Step d) a) => d -> a
cata = algebra . fmap cata . injStep

class AlgebraM d s t where
   algebraM :: d s -> t
type Algebra d s = AlgebraM d s s

newtype Used = Used { vars :: S.Set Var}
    deriving (Show, Eq, Ord)
    deriving (Semigroup, Monoid) via S.Set Var
    deriving Generic

newtype Ident = Ident { _0 :: String}
    deriving (Show, Eq, Ord)
data Context = Ctx { in_scope :: M.Map Ident Int, shifted :: M.Map Ident Int }
    deriving (Show, Eq, Ord)
emptyContext :: Context
emptyContext = Ctx mempty mempty
addVar :: Ident -> Context -> Context
addVar v (Ctx s t) = Ctx (s & at v % non 0 %~ (+1)) t
addVars :: [Ident] -> Context -> Context
addVars vs c = foldr addVar c vs
dropVars :: M.Map Ident Int -> Context -> Context
dropVars vs Ctx{..} = Ctx{in_scope = MM.merge MM.preserveMissing (MM.mapMissing (const negate)) (MM.zipWithMaybeMatched $ \_ a b -> iff (/= 0) (a - b)) in_scope vs, ..}
  where
    iff p v
      | p v = Just v
      | otherwise = Nothing
instance (WithoutVars d, Algebra ADTF d) => K.Walker Context (ADT d) where
  allR f = transform $ \c v -> case v of
    App _ s ts -> appT  s <$> traverse (applyT f c) ts
    V s -> pure $ V s
    Prior _ x -> priorT <$> applyT f c x
    Diff _ x -> diffT <$> applyT f c x
    Integrate _ x -> integrateT <$> applyT f c x
    Let _ xs x -> letT <$> traverse (\(n,b) -> (n,) <$> applyT f c b) xs <*> applyT f c x
    Abs _ s x -> absT s <$> applyT f c x
    Iff _ s x y -> iffT <$> applyT f c s <*> applyT f c x <*> applyT f c y

class WithoutVars d where
    withoutVars :: [Var] -> d -> d

getAna :: forall d. (WithoutVars d, Algebra ADTF d) => ADT d -> d
getAna (V v) = algebra (VF v)
getAna (Prior d _) = d
getAna (App d _ _) = d
getAna (Diff d _) = d
getAna (Integrate d _) = d
getAna (Let d ls _) = withoutVars (map fst ls) d
getAna (Abs d v _) = withoutVars [v]d
getAna (Iff d _ _ _) = d

letT :: (WithoutVars d, Algebra ADTF d) => [(Var, ADT d)] -> ADT d -> ADT d
letT ls r = Let (algebra $ LetF [ (v, getAna f) | (v, f) <- ls ] (getAna r)) ls r

integrateT :: (WithoutVars d, Algebra ADTF d) => ADT d -> ADT d
integrateT d = Integrate (algebra $ IntegrateF (getAna d)) d

diffT :: (WithoutVars d, Algebra ADTF d) => ADT d -> ADT d
diffT d = Diff (algebra $ DiffF (getAna d)) d

priorT :: (WithoutVars d, Algebra ADTF d) => ADT d -> ADT d
priorT p = Prior (algebra $ PriorF (getAna p)) p

appT :: (WithoutVars d, Algebra ADTF d) => Var -> [ADT d] -> ADT d
appT v ls = App (algebra $ AppF v (map getAna ls)) v ls

absT :: (WithoutVars d, Algebra ADTF d) => Var -> ADT d -> ADT d
absT v l = Abs (algebra (AbsF v (getAna l))) v l

iffT :: (WithoutVars d, Algebra ADTF d) => ADT d -> ADT d -> ADT d -> ADT d
iffT e l r = Iff (algebra $ IffF (getAna e) (getAna l) (getAna r)) e l r




instance IsString Ident where
  fromString = Ident
instance IsString Var where
  fromString a = Var (Ident a) genUniq



test :: ADT (MAna Var Arity)
test = (letT [(b, appT "nono" [])] (letT [(a, (iffT (V b) (V b) (V a)))] (V a))) 
  where
    a = "a"
    b = "b"
-- >>> cata test
-- MAna {elems = fromList [(a_3,Arity {lb = Once, ub = Many}),(b_1,Arity {lb = Many, ub = Many}),(nono_2,Arity {lb = Many, ub = Many})]}
-- Todo: seperate lets and functions?
-- The repeated usage of 'b' only corresponds to repeated usage of "nono" if it is inlined or called each time

testAp :: IO (ADT (MAna Var Arity))
testAp = applyR (substitute (M.singleton "a" (V "b")) ) emptyContext test

substitute :: (WithoutVars d, Algebra ADTF d, MonadCatch m)=> M.Map Var (ADT d) -> Rewrite Context m (ADT d)
substitute m = alltdR $ transform $ \_ -> \case
    V v | Just o <- m M.!? v -> pure o
    o -> pure o



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
