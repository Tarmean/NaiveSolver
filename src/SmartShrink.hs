{-# LANGUAGE RecordPuns #-}
-- {-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module SmartShrink where

import Twee.Pretty
import PyF

-- import Data.Express
-- import Data.Express.Utils.Typeable (tyArity)
import Control.Monad.State 
import Control.Monad.Cont
import Control.Applicative (Alternative (..), Applicative (..))
import Data.Data hiding (TyCon)
import Data.Kind (Type)
import GHC.Stack (HasCallStack)
import Control.Monad.Writer (MonadWriter(tell), WriterT (runWriterT), Endo (..), execWriterT)
import GHC.Stack (HasCallStack)
import qualified Data.Map.Strict as M
import qualified Data.Map.Lazy as ML
import Data.Dynamic
import GHC.Generics

import Data.Typeable
import qualified Type.Reflection as TR
import Type.Reflection (SomeTypeRep)
import Control.Monad.Identity
import GHC.TypeLits (type (+), Nat, type (-), KnownNat, natVal, natVal')
import qualified IndexedWalk as Ix
import GHC.IO (unsafePerformIO)
import Data.IORef
import qualified Twee.Base as TB
import qualified Twee.Term as T
import qualified Data.Label as T
-- import Data.Express.Utils (sortOn)
-- import Test.Extrapolate
-- import Test.Extrapolate.Core (grounds)
-- import qualified Test.Speculate.Expr as SE
-- import Test.Speculate.Engine (theoryAndRepresentativesFromAtoms)
-- import GHC.Base (TyCon(..))
import qualified Data.List as L
import QuickSpec.Internal.Term
import qualified QuickSpec.Internal.Type as QT
import QuickSpec.Internal.Haskell (con, Constant)
import qualified QuickSpec.Internal.Haskell as QH
import QuickSpec.Internal.Type (Typed(..))
import Monad.Zipper
import Monad.StateT2
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Debug.Trace
import Data.Foldable (asum, foldl')
import Control.Zipper
import Control.Lens
import Data.Monoid (Last(..))
import qualified Control.Category as C
import Data.Data.Lens (uniplate)
import Control.Lens.Internal.Indexed (Indexing)
import System.Timeout (timeout)
import Control.DeepSeq
import qualified Monad.Levels as L

replaceWithChild :: (MonadZipper o m, Plated o, Alternative m) => m ()
replaceWithChild = do
    s <- cursor
    replacement <- pick (toListOf plate s)
    setCursor replacement

showTypRep :: TypeRep  -> String
showTypRep (TR.SomeTypeRep r) = showTypRep' r

showTypRep' :: TR.TypeRep a  -> String
showTypRep' rep = case rep of
  TR.Fun f a -> showTypRep' f <> " -> " <> showTypRep' a
  TR.App f a -> "App { l = " <> showTypRep' f <> ", r =" <> showTypRep' a <> " }"
  TR.Con c -> "Cons { cons = " <> show c <> " }"

-- showTyCon :: TyCon -> String
-- showTyCon s = case s of
--     TyCon a b c d _ f -> "TyCon " <> show (c,d,f)
data Pos = AStruct TypeRep String | PartialApp String TypeRep Int
  deriving Show
data ArgKind = Recursive | Arg TypeRep
  deriving Show
type FunTyp = ([TypeRep], TypeRep)

getArgs :: TypeRep -> FunTyp
getArgs (TR.SomeTypeRep tyRep) = go tyRep []
  where
    go :: TR.TypeRep a -> [TypeRep] -> FunTyp
    go (TR.Fun a r) acc = go r (TR.SomeTypeRep a : acc)
    go r acc = (reverse acc, TR.SomeTypeRep r)
recArgs :: FunTyp -> [Int]
recArgs (args, r) = [i | (arg, i) <- zip args [0..], arg == r]
nonRecArgs :: FunTyp -> [(Int, TypeRep)]
nonRecArgs (args, r) = [(i,arg) | (arg, i) <- zip args [0..], arg /= r]


data Bin f a = App f (Bin f a) (Bin f a) | Leaf f a | IVar f Var
    deriving (Show, Eq, Ord, Typeable, Generic)
notVar :: Bin f a -> Bool
notVar (IVar _ _) = False
notVar _ = True
instance Plated (Bin f a) where
    plate f (App k a b) = App k <$> f a <*> f b
    plate _ a = pure a
instance Typed a => Typed (Bin () a) where
  typ (Leaf _ a) = typ a
  typ (IVar _ v) = typ v
  typ (App _ f x) = typ f `QT.applyType` typ x

  typeSubst_ s t = case t of
    Leaf f a -> Leaf f (typeSubst_ s a)
    IVar f v -> IVar f (typeSubst_ s v)
    App f x y -> App f (typeSubst_ s x) (typeSubst_ s y)

instance (Pretty f, Pretty a) => Pretty (Bin f a) where
  pPrint (App _ l r) = pPrint l <> pPrint "(" <> pPrint r <> pPrint ")"
  pPrint (Leaf _ a) = pPrint a
  pPrint (IVar _ v) = pPrint v

-- newtype ShrinkT x o (r::Type) m a = ShrinkT { unShrink :: ZipperT x o (ContT r m) a }
newtype ShrinkT o (r::Type) m a = ShrinkT { unShrink :: ZipperT o (ContT r m) a }
  deriving (Functor, Applicative, Monad)
deriving instance MonadZipper o (ShrinkT (Zipper h i o) r m)
deriving instance MonadZipper o (ShrinkT (SomeZipper r o) x m)
deriving instance RecView o (ShrinkT (SomeZipper r o) x m)
instance (Zipping h o) => HasRec o (ShrinkT (Zipper h Int o) x m) (ShrinkT (SomeZipper (Zipper h Int o) o) x m) where
    recursive (ShrinkT m) = ShrinkT $ recursive m

instance (Ord idx, Ord idx1, zip ~ Zipper h idx1 o, zip2 ~ Zipper zip idx i) => HasView (ShrinkT zip r m) (ShrinkT zip2 r m) o i idx where
   idownwardM l m = ShrinkT $ idownwardM l (unShrink m)
   iwithinM l m = ShrinkT $ iwithinM l (unShrink m)

downwardM :: (HasView m n o i Int) =>  (forall f. Functor f => (i -> Indexing f i) -> o -> Indexing f o) -> n a -> m a
downwardM l m = idownwardM (indexing l) m
withinM :: (Monoid a, HasView m n o i Int) =>  (forall f. Applicative f => (i -> Indexing f i) -> o -> Indexing f o) -> n a -> m a
withinM l m = iwithinM (indexing l) m
    
    
-- deriving instance Monad m => MonadState (ShrinkState f o) (ShrinkT' f o r m)

shrinkT :: (t -> ((a, t) -> m r) -> m r) -> ShrinkT t r m a
shrinkT f = ShrinkT $ ZipperT $ StateT $ \s -> ContT $ \k -> f s k
runShrinkT :: p -> ((a, Top :>> p) -> m r) ->ShrinkT (Top :>> p) r m a ->  m r
runShrinkT o k m = runContT (runZipperT (unShrink m) (zipper o)) k

data OraclingT m a = O (m (a, (Bool -> OraclingT m a)))
newtype RoseForestT m a = RoseF { unForestT :: m (RoseCell m a)}
  deriving (Functor)
deriving instance (Show (m (RoseCell m a)), Show a) => Show (RoseForestT m a)
data RoseCell m a = RoseNil | RoseCell a (RoseForestT m a) (RoseForestT m a)
  deriving (Functor)

printRose :: Show a => RoseForestT Identity a  -> IO ()
printRose r0 = putStrLn $ unlines $ go 0 r0 []
  where
    go i (RoseF (Identity rose)) = case rose of
        RoseNil -> id
        RoseCell c m r -> ((pad i <> "|" <> show c) :) . go (i+2) m . go i r
    pad i = replicate i ' '
deriving instance (Show (RoseForestT m a), Show a) => Show (RoseCell m a)
instance Applicative m => Applicative (RoseForestT m) where
  pure = RoseF . pure . pure
  f <*> a = RoseF $ liftA2 (<*>) (unForestT f) (unForestT a)
instance Applicative m => Applicative (RoseCell m) where
  pure a = RoseCell a (RoseF $ pure RoseNil) (RoseF $ pure RoseNil)
  RoseNil <*> _ = RoseNil
  _ <*> RoseNil = RoseNil
  RoseCell f fl fr <*> RoseCell a al ar = RoseCell (f a) (fl <*> al) (fr <*> ar)
instance Applicative m => Semigroup (RoseForestT m a) where
   l <> r = l <|> r
instance Applicative m => Monoid (RoseForestT m a) where
   mempty = empty
instance Applicative m => Alternative (RoseForestT m) where
  empty = RoseF $ pure empty
  l <|> r = RoseF $ liftA2 (<|>) (unForestT l) (unForestT r)

instance Applicative m => Alternative (RoseCell m) where
  empty = RoseNil
  RoseNil <|> a = a
  (RoseCell a l m) <|> r = RoseCell a l (RoseF $ fmap (<|> r) $ unForestT m )
  
class Monad m => MonadVar m where
    mkVar :: QT.Type -> m Var
    default mkVar :: (m ~ t n, MonadTrans t, MonadVar n) => QT.Type -> m Var
    mkVar = lift . mkVar
runVarT :: Monad m => VarT m a -> m a
runVarT (VarT m) = evalStateT m 0

instance MonadVar m => MonadVar (ZipperT zip m)
instance MonadVar m => MonadVar (StateT o m)
newtype VarT m a = VarT { unVarT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadWriter s, MonadTrans, Alternative, MonadOut o r, MonadOracle)
instance MonadZipper o m => MonadZipper o (VarT m) where
instance HasView m n o i idx => HasView (VarT m) (VarT n) o i idx where
    idownwardM l m  = VarT $ StateT $ \i -> idownwardM l (runStateT (unVarT m) i)
    iwithinM l m  = VarT $ StateT $ \i -> fmap (swizzle i) $ iwithinM l (fmap inj $ runStateT (unVarT m) i)
      where
        -- swizzle f Nothing = (Nothing, f)
        swizzle _ (s,Last (Just r)) = (s, r)
        swizzle _ _ = error "weird things"
        inj (a,b) = (a, Last (Just b))

instance MonadState s m => MonadState s (VarT m) where
  get = VarT (lift get)
  put = VarT . lift . put
instance Monad m => MonadVar (VarT m) where
    mkVar t = VarT $ do
      i <- get
      put (i+1)
      pure (V t i)
instance (Monoid o, MonadVar m) => MonadVar (WriterT o m)
-- class MonadZipper o m => MonadExtract m o | m -> o where
    
class Monad m => MonadOracle m where
    checkpoint :: m ()
    default checkpoint :: (m ~ t n, MonadTrans t, MonadOracle n) => m ()
    checkpoint = lift checkpoint
instance MonadOracle m => MonadOracle (StateT s m)
instance (Monoid s, MonadOracle m) => MonadOracle (WriterT s m)

-- (doRewrite >> checkPoint ) `orElse` doNothing

-- i <- oneOf [1,2,3]
-- doRewrite i
-- checkpoint

joinForest :: Monad m => m (RoseForestT m a) -> RoseForestT m a
joinForest = RoseF . join . fmap unForestT
instance (MonadOut o r (ShrinkT zip (RoseForestT m r) m), Monad m) => MonadOracle (ShrinkT zip (RoseForestT m r) m) where
    checkpoint = do
        o <- getOut
        shrinkT $ \s k -> do
             pure $ RoseF $ pure (RoseCell o (joinForest $ k ((), s)) empty)

instance (Zipping h o, r ~ Zipped h o, Monad m) => MonadOut o r (ShrinkT (Zipper h i o) x m) where
    getOut = ShrinkT getOut
    withZipper' f = ShrinkT  (withZipper' f)
instance (Monad m, TopZip (SomeZipper h o) ~ r, ReZipping (SomeZipper h o)) => MonadOut o r (ShrinkT (SomeZipper h o) x m) where
    getOut = ShrinkT getOut
    withZipper' f = ShrinkT  (withZipper' f)

runShrinkForest :: (Monad m) => x -> ShrinkT (Top :>> x) (RoseForestT m x) m a -> RoseForestT m x
runShrinkForest o m = joinForest $ runShrinkT o (\(_,a) -> pure empty) m
   --   where 
  --   foo :: Applicative m => x -> m (RoseForestT m x)
  --   foo x = pure (pure x)

-- runShrinkList :: o -> ShrinkT o o a [] a -> [a]
-- runShrinkList e (ShrinkT m) = runContT (evalZipperT pure e m) pure

class Applicative m => Propagate m o | o -> m where
    mkApp:: o -> o -> m o
    fromLeaf :: Constant -> m o
    fromVar :: Var -> m o
-- infixl 9 @:
-- (@:) :: Bin o a -> Bin o a -> m (Bin o a)
newtype UniqTag = UT { getUniq :: Int }
popNext :: StateT Int Identity Int
popNext = do
   s <- get
   put (s+1) 
   pure s
instance Propagate (State Int) Int where
    mkApp _ _ = popNext
    fromLeaf _ = popNext
    fromVar _ = popNext
(@:) :: Bin () a -> Bin () a -> Bin () a
(@:) l r = App () l r
leaf :: Propagate m o => Constant -> m (Bin o Constant)
leaf c = flip Leaf c <$> fromLeaf c
-- varLeaf :: Propagate m o => Var -> m (Bin o Constant)
-- varLeaf c = Leaf <$> fromLeaf c

-- l @: r = App () l r
class MkExpr a where
   expr :: a -> (Bin () Constant)
instance (Typeable a, Typeable b, MkExpr a, MkExpr b) => MkExpr (a,b)  where
   expr a = Leaf () (con "(,)" ((,) :: a -> b -> (a,b))) @: expr (fst a) @: expr (snd a)
instance (Typeable a, Typeable b, Typeable c, MkExpr a, MkExpr b, MkExpr c) => MkExpr (a,b,c)  where
   expr (a,b,c) = Leaf () (con "(,,)" ((,,) :: a -> b -> c -> (a,b,c))) @: expr a @: expr b @: expr c
instance (Typeable a, MkExpr a) => MkExpr [a]  where
   expr a = go a
     where
       go (x:xs) = Leaf () (con ":" ((:) @a)) @: expr x @: go xs
       go [] = Leaf () (con "[]" ([] :: [a]))
instance MkExpr Char  where
    expr c = Leaf () (con (show c) c)
instance MkExpr Int  where
    expr c = Leaf () (con (show c) c)

-- runNumbering :: State Int a -> a
-- runNumbering = evalState 
-- test :: RoseForestT Identity Expr
-- test = runShrinkForest (expr ('a', "bcd")) $ do
--     assertCtor @((Char, String)) $ do
--        intoField @1 $ do
--            isField @String
--            replace ""
--            checkpoint
           -- assertCtor @(Char ': String) $ do
             -- pure ()
           -- intoField @0 $ do
-- test2 :: [Expr]

test2 ::RoseForestT Identity (Bin Int Constant)
test2 = runShrinkForest (mkIndices $ expr (1::Int,[2::Int,1,3], "xxy"::String)) $ runVarT $ do
    varUniqs @Int (ileafs . filtered notFunctionType)


test3 :: [(Int, String)]
test3 = fmap (rezip . snd) $ runIdentity $ runShrinkT (1::Int, "abc" :: String) (\x -> Identity [x]) $
    downwardM _2 do
      withinM traversed do
        pull rightward
        setCursor 'c'
     -- replaceWithChild
    -- downwardM _2

withRec :: (Data o, HasRec o m n, Alternative n) => o -> m x
withRec a =
   recursive do
     layerDown uniplate
     right
     setCursor a
     up
     undefined

class HasIdx o k | o -> k where
   theIdx :: o -> k

eachChild :: (MonadZipper o m, RecView o m) => Traversal' o o -> m () -> m ()
eachChild l m = do
    block l do
      let loops = m >> nextTooth rightward loops
      loops

depsMap :: (RecView o m, HasIdx o k, Ord k) => Traversal' o o -> WriterT (MergeMap k (S.Set k)) m ()
depsMap l = do
   parent <- cursor
   eachChild l $ do
     child <- cursor
     tellDep (theIdx parent) (theIdx child)
     depsMap l
  where tellDep k v = tell (MergeMap $ M.singleton k (S.singleton v))

data FlatTree ids = FT {
  node_sizes_transitive :: M.Map ids Int,
  node_children :: M.Map ids (S.Set ids),
  unremovable_nodes :: S.Set ids,
  transitive_important_nodes :: S.Set ids
 }
 deriving (Eq, Ord, Show)
transitive :: Ord ids => ids -> M.Map ids (S.Set ids) -> S.Set ids
transitive x0 m = go S.empty (S.singleton x0)
  where
   go seen pending
     | S.null pending = seen
   go seen pending
     | S.member next seen = go seen pending'
     | otherwise = go (S.insert next seen) (S.union pending' neighbors)
     where
       (next,pending') = S.deleteFindMin pending
       neighbors = M.findWithDefault S.empty next m S.\\ seen
transitive1 :: Ord t => t -> M.Map t t -> S.Set t
transitive1 x0 m = go mempty x0
  where
    go acc x
      | Just x' <- M.lookup x m = go (S.insert x' acc) x'
      | otherwise = acc

data BiMap m k = BM {
  fst_map :: M.Map k m,
  snd_map :: M.Map m (S.Set k)
 }
 deriving (Eq, Ord, Show)

removeKeys :: (Ord k, Ord m) => BiMap m k -> S.Set k -> BiMap m k
removeKeys (BM f m) ks = BM (foldl' (flip M.delete) f ks) (M.mapMaybe (delMaybe ks) m)
  where
delMaybe :: Ord a => S.Set a -> S.Set a -> Maybe (S.Set a)
delMaybe ks x = let m' = x S.\\ ks in if S.null m' then Nothing else Just m'

reduceKeys :: (Ord k, Ord m, Num m) => m -> BiMap m k -> S.Set k -> BiMap m k
reduceKeys i (BM f m) ks = BM (foldr (M.adjust (\x -> x - i)) f ks) (M.unionWith (<>) oldVals m')
  where
    m' = (M.mapMaybe (delMaybe ks) m)
    oldVals = M.fromListWith (<>) [(x - i, S.singleton  k) | k <- S.toList ks, Just x <- [f M.!? k]]

mkBiMap :: Ord ids => M.Map ids (S.Set ids) -> BiMap Int ids
mkBiMap m = BM sizes revSizes
  where
    sizes = M.fromList [(x,1) | x <- S.toList leafOnly] <> ML.fromList [(x, (1::Int)+sum ls) | (x, vs) <- M.toList m, let ls = map  (sizes !!!) (S.toList vs)]
    leafOnly = mconcat (M.elems m) S.\\ S.fromList (M.keys m)
    revSizes = M.fromListWith (<>) [(x, S.singleton k) | (k, x) <- M.toList sizes]
restrictBiMap :: (Ord k, Ord m) => BiMap m k -> S.Set k -> BiMap m k
restrictBiMap (BM f m) ks = removeKeys (BM f m) notKs
  where
    notKs = S.fromList (M.keys f) S.\\ ks
keepChildren :: Ord k => S.Set k -> M.Map k (S.Set k) -> M.Map k (S.Set k)
keepChildren kept m = m''
  where
    tab = ML.fromList [(k, undefined) | k <- S.toList kept]
    m' = M.intersection m tab
    m'' = M.map (S.intersection kept) m'
removeChildren :: Ord k => S.Set k -> M.Map k (S.Set k) -> M.Map k (S.Set k)
removeChildren removed m = m''
  where
    m' = foldr M.delete m removed
    m'' = M.map (S.\\ removed) m'

type Parents m = M.Map m m
type Children m = M.Map m (S.Set m)

pathFromRoot :: Ord m => Parents m -> m -> [m]
pathFromRoot parents x = reverse (go x)
  where
    go x
      | Just x' <- M.lookup x parents = x : go x'
      | otherwise = [x]
navigator :: (Show k, RecView o m, HasIdx o k, Ord k) => Parents k -> Traversal' o o -> k -> m ()
navigator pars l = \k -> do
   let path = pathFromRoot pars k
       keys = S.fromList path
    
       toPath = do
          k' <- cursors theIdx
          -- traceM [fmt|toPath {show k'}|]
          if k' `S.member`  keys
          then downPath (tail $ dropWhile (/= k') path)
          else orThrow upBool >> toPath
       downPath (x:xs) = downTo x *> downPath xs
       downPath [] = pure ()

       downTo x = do
           -- traceM [fmt|downTo {show x}|]
           orThrow (layerDownBool l)
           mapZipper leftmost
           let
             seek = do
               k <- cursors theIdx
               -- traceM [fmt|downTo seek {show k}|]
               if k == x then pure ()
               else orThrow (pullBool rightward) *> seek
           seek
   -- traceM [fmt|navigator path {show path}|]
   toPath

           
  

removeNode :: (Alternative m, Eq p, HasIdx o p, RecView o m, Plated o) => (p -> m ()) -> p -> m ()
removeNode nav k = do
   nav k
   replaceWithChild

isRelevant :: (Ord m) => Children m -> m -> (m -> Bool)
isRelevant c l0 t = flip evalState mempty (go l0)
  where
    go f
      | f == t = pure True
      | otherwise = do
          let next = M.findWithDefault mempty f c
          next <- gets (next S.\\)
          modify (S.union next)
          anyM go (S.toList next)

    anyM _ [] = pure False
    anyM m (x:xs) =
       m x >>= \case
         True -> pure True
         False -> anyM m xs

pickChild :: (MonadZipper o m, Alternative m) => m ()
pickChild = do
    pull (Just . leftmost)
    let loop = pure () <|> (nextTooth rightward loop)
    loop
findFirst :: (RecView o m) => Traversal' o o -> m () -> m ()
findFirst t m = () <$ L.toMaybe loop
  where loop = lift m <|> L.delay (layerDown t >> pickChild >> loop)

instance MonadZipper o m => MonadZipper o (L.LevelsT m)
instance RecView o m => RecView o (L.LevelsT m)



appSearch :: (Monad m, Alternative m) => [p] -> (p -> m ()) -> m ()
appSearch p0 d = search p0
  where
    tryRemove p l r = (mapM_ d p >> l) <|> r
    search ls =
       tryRemove ls
         (pure ())
         (has_fault ls)
    has_fault [_] = pure ()
    has_fault ls = tryRemove l (has_fault r) (has_fault l >> search r)
      where (l,r) = split ls
    split ls = splitAt (length ls `div` 2) ls

-- removeSubset :: (MonadZipperI k a m, Alternative m) => m () -> S.Set k -> m ()
-- removeSubset m fs = do
--     let
--       loop ps
--         | S.null fs = pure ()
--         | otherwise = do
--            let (p,ps') = S.deleteFindMin ps
--            pullI (moveTo p)
--            m
--            loop ps'
--     old <- cursorKey
--     loop fs
--     pullI (moveTo old)

ix3 :: Applicative f => ([a] -> f [a]) -> [a] -> f [a]
ix3 f (a:b:c) = ([a,b]++) <$> f c
ix3 _ a = pure a


fillQuota :: (HasCallStack, Ord m, Show m) => Int -> Parents m -> Children m -> BiMap Int m -> (BiMap Int m, S.Set m, S.Set m)
fillQuota quota0 parents0 childEdges0 m0 = go mempty mempty quota0 m0
  where
    parents = M.intersection parents0 (fst_map m0)
    liveIds = S.fromList (M.keys $ fst_map m0)
    childEdges = M.map (S.intersection liveIds) $ M.intersection childEdges0 (fst_map m0)
    go consumed seen 0 m = (m, seen, consumed)
    go consumed seen quota m = go (S.union consumed newlyTaken) (S.insert v seen) (quota - k) m''
      where
        (k,v,snd_map') = case largestNodeSmallerThan quota (snd_map m) of
          Nothing -> error ("Partial largestNodeSmallerThan " <> show m0 <> ", " <> show quota0)
          Just o -> o
        m' = m { snd_map = snd_map' }
        (m'', newlyTaken)  = useKey v k childEdges parents  m'
useKey :: Ord m => m -> Int -> Children m -> Parents m -> BiMap Int m -> (BiMap Int m, S.Set m)
useKey v val childEdges parents m = (remove (reduce m), usedNodes)
  where
    reduce m' = reduceKeys val m' affectedNodes
    remove m' = removeKeys m' usedNodes
    affectedNodes = transitive1 v parents
    usedNodes = S.insert v (transitive v childEdges)

testValue :: (Num k, Ord k) => BiMap Int k
testValue = BM {fst_map = M.fromList [(1,2),(3,1) ,(5,1)], snd_map = M.fromList [(1,S.fromList [3,5]),(2,S.fromList [1])]}
data BTree a = BT {
  test :: a,
  quota :: Int,
  on_true :: BTree a,
  on_false :: BTree a
 } | Success | LearnCritical a (BTree a) | LearnFalse a  (BTree a)
 deriving (Eq, Ord, Show, Generic, Data, Typeable)
instance NFData a => NFData (BTree a)


shrinkTree :: (RecView o m, HasIdx o k, Ord k, Show k, Alternative m, MonadOracle m) => Traversal' o o -> (o -> o) -> m ()
shrinkTree l minFor = do
    deps <- unMergeMap <$> execWriterT (depsMap l)
    let nav = navigator (flipChildren deps) l
        focus x = do
           old <- cursors theIdx
           -- traceM [fmt|seeking from {show old} to {show x}|]
           nav x
        has_conflict c = do
          if M.size c <= 1
          then pure ()
          else do
              -- traceM [fmt|has conflict: {show c}|]
              let biMap = mkBiMap c
                  quota = M.size c `div` 2
                  (_, roots, consumed) = fillQuota quota (flipChildren c) c biMap
                  inner = keepChildren consumed c
                  leftover = removeChildren consumed c
              -- traceM [fmt|removed roots {show roots}, which killed {show consumed}|]
              (mapM_ removeOne roots >> checkpoint >> has_conflict leftover) <|> (has_conflict inner >> shrink leftover)
        shrink x = do
          -- traceM [fmt|shrinking: {show x}|]
          mapM_ removeOne roots <|> has_conflict x
          where roots = rootsFor x
        removeOne k = focus k >> modifyCursor minFor
    has_conflict deps
rootsFor :: Ord m => Children m -> S.Set m
rootsFor c = S.fromList (M.keys c) S.\\ mconcat (M.elems c)

modifyCursor :: MonadZipper o m => (o -> o) -> m ()
modifyCursor f = cursor >>= setCursor . f



mkSearch :: forall m. (Ord m, Show m) => Children m -> BTree (S.Set (m))
mkSearch children = evalState (runContT (hasFault halfSize) (\_ -> pure Success)) bim0  
  where
    pars = flipChildren children
    bim0 = mkBiMap children
    halfSize = (M.size (fst_map bim0))
    allNodes = S.fromList $ M.keys $ fst_map bim0
    

    hasFault :: Int -> ContT (BTree (S.Set (m))) (State (BiMap Int m))  ()
    hasFault 0 = pure () -- get >>= \s -> traceM [fmt|zero quota {show s}|]
    hasFault q = do
        m <- get
        -- traceM [fmt|hasFault state {show m}, quota {q}|]
        case M.toList (fst_map m) of
          [] -> pure ()
          [(p,pv)] -> do
              -- traceM [fmt|singleton {show p}, size {pv}, for quota {q}|]
              ContT $ \k -> (LearnCritical (S.singleton p) <$> (k ()))
          _ -> do
            let q_half = q - (q `div` 2)
            let (mPost, k', affectedNodes) = fillQuota q_half pars children m
            -- traceM [fmt|post fillQuota {show mPost}, quota {q}, picked {show k'}, affectedNodes {show affectedNodes}|]
            let mInner = restrictBiMap m affectedNodes
            -- let after = modify (flip removeKeys affectedNodes)
            ContT $ \c -> do
                let with s mo = put s *> mo
                let execWith s mo = runState (runContT mo c) s
                let
                  onFailure = do
                    -- traceM [fmt|onFailure {show mInner}, affected {show affectedNodes}, orig {show m}, post {show mPost}|]
                    with mInner (hasFault q_half)
                    with mPost (maybeFault (q - q_half))
                let onSuc = fst $ execWith mPost (hasFault (q - q_half))
                let onFail = fst $ execWith m onFailure
                pure $ BT affectedNodes q onSuc onFail 
    maybeFault :: Int -> ContT (BTree (S.Set (m))) (State (BiMap Int m))  ()
    maybeFault i = do
        m <- get
        ContT $ \c -> do
            let l = evalState (c ()) m
            let r = evalState (runContT (hasFault i) c ) m
            pure $ BT (S.fromList $ M.keys $ fst_map m) (M.size $ fst_map m) l r
briefly :: NFData p => p -> IO (Maybe p)
briefly x = fmap (x <$) $ timeout 5000000 (x `deepseq` print "hi")
-- todo: track whether we are in a binary search
-- half the quota from the get-go if so

unionBim :: (Ord m, Show m) => BiMap Int m -> BiMap Int m -> BiMap Int m
unionBim l@(BM f g) r@(BM a b) 
  | trace ("unionBim " <> show l <> ", " <> show r) False = undefined
  | otherwise = BM (M.unionWith undefined f a) (M.unionWith (<>) g b)
        
    

flipChildren :: Ord m => Children m -> Parents m
flipChildren m = M.fromList [(c, p) | (p, cs) <- M.toList m, c <- S.toList cs]
instance HasIdx (Tree k) k where
   theIdx (Node k _) = k

treeFor :: M.Map Int (S.Set Int)
treeFor = unMergeMap $ runIdentity $ runShrinkT (Node (1::Int) [Node 2 [], Node 3 [Node 4 [], Node 5 []]]) (\(a,_) -> pure a) (execWriterT $ recursive $ depsMap uniplate) 

    

largestNodeSmallerThan :: (HasCallStack, Ord k, Ord v) => k -> M.Map k (S.Set v) -> Maybe (k,v,M.Map k (S.Set v))
largestNodeSmallerThan k m 
  | M.null m = Nothing
  | otherwise = Just (theKey, theVal, m')
  where
    theKey
      | M.member k m = k
      | otherwise = maxKey (fst (M.split k m))
    theSet = m !!! theKey
    (theVal, theSet') = S.deleteFindMin theSet
    m' = if S.null theSet'
         then M.delete theKey m
         else M.insert theKey theSet' m
    maxKey ms = case M.minViewWithKey ms of
       Nothing -> error "map checked for emptiness, should have nodes with size=1"
       Just ((k',_),_) -> k'

(!!!) :: (Ord k, HasCallStack) => M.Map k a -> k -> a
m !!! k = case M.lookup k m of
    Nothing -> error ("key not found")
    Just a -> a
      -- | Just vs <- m !!!? k
      -- , Just (v, vs') <- S.deleteFindMin vs = (k,v,M.insert k vs' m)
        -- Nothing -> Nothing
        -- Just (k,_) -> k

data Tree a = Node a [Tree a]
  deriving (Show, Eq, Ord, Data, Typeable)
instance Data a => Plated (Tree a) where
   plate = uniplate

drop1Child :: (MonadZipper o m, Plated o, HasRec o m n, Alternative n) => m ()
drop1Child = do
   recursive do
     layerDown plate
     replaceWithChild

newtype MergeMap k v = MergeMap { unMergeMap :: M.Map k v }
  deriving (Eq, Ord, Show)
instance (Ord k, Semigroup v) => Semigroup (MergeMap k v) where
    (MergeMap a) <> (MergeMap b) = MergeMap $ M.unionWith (<>) a b
instance (Semigroup v, Ord k) => Monoid (MergeMap k v) where
    mempty = MergeMap M.empty
-- childDeps :: (HasIndex o, Ord k, RecView o m, Semigroup v) => Traversal' o o -> WriterT (MergeMap k v) m ()
-- childDeps l = do 
--     t <- readZipper tooth
  -- M.singleton i $ S.fromList $ f a



   -- z <- readZipper (\x -> x)
   -- o <- lift $ (runZipperT m s) (SomeZipper z)
-- shrinkBO :: (MonadZipper o m, MonadOracle m, Monad m, MonadVar m) => Traversal' o o -> m a -> m a
-- shrinkBO :: (Monoid a, RecView m i Int) => (Traversal' i i) -> n a
-- shrinkBO l = do
--    () <- withinM l (shrinkBO l)
--    undefined


mkIndices :: Bin () Constant -> Bin Int Constant
mkIndices s = evalState (go s) 0
  where
    go (App _ l r) = App <$> popNext <*> go l <*> go r
    go (Leaf _ c) = Leaf <$> popNext <*> pure c
    go (IVar _ v) = IVar <$> popNext <*> pure v

pick :: Alternative f => [a] -> f a
pick = asum . map pure
tryModify :: (MonadZipper (Bin () Constant) m, Typeable a, MkExpr a) => (a -> a) -> m ()
tryModify f = do
    s <- cursor
    case s of
      Leaf _ c -> case QT.fromValue (QH.con_value c) of
        Just (Identity (o :: a)) -> do
          let l' = expr (f o)
          setCursor $ l'
        _ -> pure ()
      _ -> pure ()
          
    -- varUniqs (eachLeaf . onlyIf notFunction)
--     try (groupExprs @Char >> checkpoint)

try :: Alternative f => f () -> f ()
try m = m <|> pure ()

tryEager :: Alternative f => f () -> f ()
tryEager m = m <|> pure ()

pop :: MonadState [a] m => m (Maybe a)
pop = do
    s <- get
    case s of
        [] -> pure Nothing
        (x:xs) -> put xs >> pure (Just x)

type Visitor o = (forall n. MonadZipper o n => n () -> n ())
-- viewing :: (MonadZipper o n) => Visitor o -> ZipperT r [o] n () -> n ()
-- viewing vis x = do
--    undefined
   -- o <- execWriterT $ vis (cursor >>= tell . Endo . (:))
   -- o' <- extractZipperT rez (appEndo o []) x
   -- evalStateT (vis (pop >>= maybe (pure ()) setCursor)) o'

   

isVar :: Bin k o -> Bool
isVar (IVar _ _) = True
isVar _ = False

    

groupedView :: forall idx i m n o k. (HasView m n o i idx, Ord k) => IndexedTraversal' idx o i -> (i -> k) -> (k -> n ()) -> m ()
groupedView v k m = do
   ks <- cursors (toListOf v)
   forM_ (S.fromList (map k ks)) $ \theKey -> do
       iwithinM (v . filtered (\x -> k x == theKey)) (m theKey)

varUniqs :: forall idx m n o. (
    HasView m n o (Either Var Constant) idx,
    Alternative n,
    MonadVar n,
    MonadOracle n
 ) => IndexedTraversal' idx  o (Either Var Constant) -> m ()
varUniqs p = groupedView @idx p id $ \k -> do
    s <- readZipper teeth
    when (s > 1) $ try $ do
        v <- mkVar (typ k)
        mapNeighborhood $ (\_ -> Left v)
        checkpoint

notFunctionType :: Typed a => a -> Bool
notFunctionType v = case typ v of
    (T.App (T.F _ QT.Arrow) _) -> False
    _ -> True

modCursor :: MonadZipper o m => (o -> o) -> m ()
modCursor p = do
  s <- cursor
  setCursor (p s)
setListVal :: (MonadZipper [o] m) => o -> m ()
setListVal x = do
    ls <- cursor
    case ls of
      [] -> pure ()
      (_:xs) -> setCursor (x:xs)

-- rewriteConstants :: forall m n o. (Typed o, HasView m n o [o] idx) => QT.Type -> n () -> m ()
-- rewriteConstants ty = listView (leafsWithType ty)

shrinkList :: MonadZipper [o] m  => m ()
shrinkList = undefined

-- leafsWithType :: (MonadZipper p m, Typed p) => QT.Type -> m () -> m ()
-- leafsWithType theType m = eachLeaf (onlyIf typMatches m)
--   where typMatches e = typ e == theType

typeRepOf :: forall a. Typeable a => QT.Type
typeRepOf = QT.typeRep ( undefined :: proxy a )


listHead :: MonadZipper [o] m => m (Maybe o)
listHead = cursor >>= \case
  (x:_) -> pure (Just x)
  [] -> pure Nothing
--    changeList es = flipped
--      where
--        m = M.fromListWith (++) (zip es $ map pure [(0::Int)..])
--        flipped :: [Bin f o]
--        flipped = map snd $ L.sortOn fst [(v,vr) | (k,vs) <- M.toList m, v <- vs, vr <- mkVar k <$> vs]
--        mkVar k vs
--          | length vs <= 1 = k
--          | otherwise =  mkVar (V (QT.typ k) (head vs))
         

dynamicOf :: SomeTypeRep -> Dynamic
dynamicOf (TR.SomeTypeRep tr)
  | Just HRefl <- checkKind tr = Dynamic tr undefined
  | otherwise = error ("Invalid typerep for var " <> show tr)

checkKind :: TR.TypeRep (a :: k) -> Maybe (k :~~: Type)
checkKind tr = TR.eqTypeRep (TR.typeRepKind tr) (TR.typeRep @Type)


--
--
--  
   


isApp :: Bin k o -> Bool
isApp (App _ _ _) = True
isApp _= False
-- leavesOf :: (MonadZipper o m, Bounded (Dir o), Enum (Dir o)) => (o -> Bool) -> m () -> m ()
-- leavesOf p m = eachLeaf (doWhen p m)
whenType :: (Typed o, MonadZipper o m) => QT.Type -> m () -> m ()
whenType ty m = do
    s <- cursor
    if (typ s == ty)
    then m
    else pure ()

instance MonadTrans (ShrinkT o r) where
    lift sm = ShrinkT $ lift $ lift sm

constContT :: m r -> ContT r m a
constContT m = ContT $ \_ -> m
instance (Applicative m, Monoid r) => Alternative (ShrinkT o r m) where
    empty = ShrinkT $ lift $ constContT $ pure @m (mempty @r)
    ShrinkT x <|> ShrinkT y = ShrinkT $ ZipperT $ StateT $ \z -> ContT $ \c -> liftA2 (<>) (ml x z c) (ml y z c)
      where
        ml m z c = (runContT (runStateT (unZipperT m) z) c)
instance (Applicative m, Monoid r) => MonadFail (ShrinkT o r m) where
    fail _ = empty
instance (Monoid r, Applicative m) => MonadPlus (ShrinkT o r m) where
    mzero = empty
    mplus = (<|>)

-- consArg :: forall t m k o x. (o ~ Bin k x, Typeable t, MonadZipper o m, Alternative m, Typed o) => t -> Int -> m ()
-- consArg t i = do
--    replicateM_ (argCount - i - 1) (step BinFun)
--    block $ do
--        -- briefly go the rest of the way to check the constructor is correct
--        replicateM_ (i+1) (step BinFun)
--        assertTy tyrep
   -- traceM $ render (pPrint ks)
assertTy :: (Typed o, MonadZipper o m, Alternative m) => QT.Type -> m ()
assertTy tyrep = do
    s <- cursor
    guard (typ s == tyrep)
-- selfs :: (Data a, Typed a) => Traversal' (Bin () a) (Bin () a)
-- selfs = deep id . filtered notFunction

leafs :: Traversal' (Bin () a) (Bin () a)
leafs f (App k x y) = App k <$> leafs f x <*> leafs f y
leafs _ (IVar k x) = pure (IVar k x)
leafs f (Leaf k x) =  f (Leaf k x)

ileafs :: IndexedTraversal' idx (Bin idx a) (Either Var a)
ileafs f (App k x y) = App k <$> ileafs f x <*> ileafs f y
ileafs _ (IVar k x) = pure (IVar k x)
ileafs f (Leaf k x) =  fmap setIndex (indexed f k (Right x))
  where
    setIndex (Right x') = Leaf k x'
    setIndex (Left x') = IVar k x'


type family Arity a where
    Arity (x -> y) = 1 + Arity y
    Arity a = 0
type FieldOf_ :: forall {k1}. Nat -> k1 -> Type
type family FieldOf_ (n :: Nat) (a :: k) where
    FieldOf_ 0 (x a) = a
    FieldOf_ n ((e :: k1 -> k) (b :: k1)) = FieldOf (n - 1) e

type family ArgCount a where
    ArgCount (x a) = 1 + ArgCount a
    ArgCount x = 0
type family FieldOf n a where
  FieldOf n a = FieldOf_ (ArgCount a - n - 1) a

newtype IsField c m a = IsField { unField :: m a}
  deriving (Functor, Applicative, Monad, Alternative, MonadState s, MonadWriter r, MonadOracle)
instance MonadTrans (IsField c) where
    lift = IsField

isField :: forall c m. Applicative m =>IsField c m ()
isField = pure ()
getInt :: forall n. KnownNat n => Int
getInt = fromInteger (natVal @n undefined)
getTypeable :: forall c. Typeable c => TypeRep
getTypeable = typeRep (undefined :: proxy c)

{-# NOINLINE myCount #-}
myCount :: IORef Int
myCount = unsafePerformIO $ newIORef (0::Int)

{-# INLINE incCount #-}
incCount :: a -> a
incCount a = unsafePerformIO (modifyIORef' myCount (+1)) `seq` a
getCount :: IO Int
getCount = readIORef myCount

-- myTest :: [Int] -> Bool
-- myTest ls 
--   | snd $ incCount (ls, False) = undefined
--   | otherwise = length ls > i ==> (ls !! 0::Int) /= 1+(ls !! i)
--   where
--     i =1
-- intTh :: [[Expr]]
-- intTh = [[val @Int 0], [value "+" ((+) @Int), value "*" ((*) @Int), value "abs" (abs @Int),val @Int 1, val @Int (-1)], [val @Int 2]]
-- ev :: Expr -> Expr -> Bool
-- ev a b 
--   | Just l <- evaluate @Int a
--   , Just r <- evaluate @Int b
--   = l == r
--   | otherwise = False

-- testS = theoryAndRepresentativesFromAtoms ev 8 intTh
