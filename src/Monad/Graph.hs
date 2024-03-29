{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Monad.Graph where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Lens
import Data.Generics.Labels ()
import GHC.Generics (Generic)
import Control.Monad.Morph
import Data.Ord (comparing)
import SmartShrink (HasIdx (theIdx), VarT, ShrinkT)
import Monad.Zipper (RecView (upBool, layerDownBool), orThrow, cursors, mapZipper, pullBool, MonadZipper, HasView, iwithinM, HasRec)
import Control.Monad.Writer
import Control.Zipper (leftmost, rightward)
import qualified Data.Map.Merge.Strict as MM
import Monad.Oracle (MonadOracle)
import Control.Applicative (Alternative)
import Monad.Critical (MonadCritical)
import PyF (fmt)
import Debug.Trace (traceM)
import Monad.Snapshot (MonadSnapshot)
import GHC.Stack (HasCallStack, callStack)
import Monad.Cut (MonadCut)
import Data.Utils

class (Ord k, Monad m) => MonadGraph k m | m -> k where
    getParentsMap :: m (M.Map k k)
    default getParentsMap :: (m ~ t n, MonadTrans t, MonadGraph k n) => m (M.Map k k)
    getParentsMap = lift getParentsMap
    getChildrenMap :: m (M.Map k (S.Set k))
    default getChildrenMap :: (m ~ t n, MonadTrans t, MonadGraph k n) => m (M.Map k (S.Set k))
    getChildrenMap = lift getChildrenMap
    getAritiesMap :: m (M.Map k Int)
    default getAritiesMap :: (m ~ t n, MonadTrans t, MonadGraph k n) => m (M.Map k Int)
    getAritiesMap = lift getAritiesMap
    getHidden :: m (S.Set k)
    default getHidden :: (m ~ t n, MonadTrans t, MonadGraph k n) => m (S.Set k)
    getHidden = lift getHidden
    {-# INLINE getParentsMap #-}
    {-# INLINE getChildrenMap #-}
    {-# INLINE getAritiesMap #-}
    {-# INLINE getHidden #-}



getChildren :: MonadGraph k m => k -> m (S.Set k)
getChildren k = getChildrenMap <&> (M.findWithDefault mempty k)
getParent :: (Ord k, MonadGraph k m) => k -> m (Maybe k)
getParent k = getParentsMap <&> (M.lookup k)
class MonadGraph k m => MonadGraphMut k m | m -> k where
    changeState :: (State (GraphState k) a) -> m a
    default changeState :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => State (GraphState k) a -> m a
    changeState = lift . changeState
    addChild :: k -> k -> m ()
    default addChild :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> k -> m ()
    addChild p c = lift (addChild p c)
    hideNodeUnsafe :: k -> m ()
    default hideNodeUnsafe :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> m ()
    hideNodeUnsafe = lift . hideNodeUnsafe

    deleteNode :: k -> m ()
    default deleteNode :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> m ()
    deleteNode = lift . deleteNode

    unhideNode :: k -> m ()
    default unhideNode :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> m ()
    unhideNode = lift . unhideNode

    markNodeAffected :: k -> m ()
    default markNodeAffected :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> m ()
    markNodeAffected = lift . markNodeAffected

    newlyHidden :: m (S.Set k)
    default newlyHidden :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => m (S.Set k)
    newlyHidden = lift newlyHidden
    resetNewHidden :: m ()
    default resetNewHidden :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => m ()
    resetNewHidden = lift resetNewHidden
    focusOn :: S.Set k -> m a -> m a
    default focusOn :: (m ~ t n, MFunctor t, MonadGraphMut k n) => S.Set k -> m a -> m a
    focusOn k m = hoist (focusOn k) m


    addDeps :: M.Map k (S.Set k) -> m ()
    default addDeps :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => M.Map k (S.Set k) -> m ()
    addDeps = lift . addDeps

    reduceArity :: Int -> k -> m ()
    default reduceArity :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => Int -> k -> m ()
    reduceArity i k = lift (reduceArity i k)
        

instance MonadCritical o m => MonadCritical o (GraphT k m)
instance MonadZipper o m => MonadZipper o (GraphT k m)
instance RecView o m => RecView o (GraphT k m)
instance MonadOracle m => MonadOracle (GraphT k m)
instance HasRec o m n => HasRec o (GraphT k m) (GraphT k n)
instance HasView m n i o idx => HasView (GraphT k m) (GraphT k n) i o idx where
    iwithinM l m  = GraphT $ StateT $ \i -> fmap (swizzle i) $ iwithinM l (fmap inj $ runStateT (unGraphT m) i)
      where
        -- swizzle f Nothing = (Nothing, f)
        swizzle _ (s,Last (Just r)) = (s, r)
        swizzle _ _ = error "weird things"
        inj (a,b) = (a, Last (Just b))

instance (Monoid r, MonadGraph k m) => MonadGraph k (WriterT r m)
instance (Monoid r, MonadGraphMut k m) => MonadGraphMut k (WriterT r m)
instance (MonadGraph k m) => MonadGraph k (StateT r m)
instance (MonadGraphMut k m) => MonadGraphMut k (StateT r m)
instance (MonadGraph k m) => MonadGraph k (VarT m)
instance (MonadGraphMut k m) => MonadGraphMut k (VarT m)
instance (MonadGraph k m) => MonadGraph k (ShrinkT r o m)
-- instance (MonadGraphMut k m) => MonadGraphMut k (ShrinkT r o m)

popChangedNodes :: MonadGraphMut k m => m (S.Set k)
popChangedNodes = do
   s <- newlyHidden
   resetNewHidden
   pure s

forgetNewlyHidden :: MonadGraphMut k m => k -> m ()
forgetNewlyHidden k = changeState $ #newHidden %= S.delete k

{-# INLINABLE isHidden #-}
{-# INLINABLE getArity #-}
isHidden :: MonadGraph k m => k -> m Bool
isHidden k = getHidden <&> (S.member k)
getArity :: MonadGraph k m => k -> m Int
getArity k = getAritiesMap <&> (M.findWithDefault 0 k)

forActiveReachable_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forActiveReachable_ k0 f = go k0
   where
      go k = do
        n <- getChildren k
        forM_ n $ \x -> do
           h <- isHidden x
           unless h $ go x >> f x
{-# INLINABLE forActiveReachable1_ #-}
{-# INLINABLE forActiveReachable_ #-}
forActiveReachable1_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forActiveReachable1_ k0 f = forActiveReachable_ k0 f >> f k0

forReachableAll_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forReachableAll_ k0 f = go k0
   where
      go k = do
        n <- getChildren k
        mapM_ (\x -> f x >> go x) n
{-# INLINABLE forReachableAll_ #-}
{-# INLINABLE forReachableAll1_ #-}
forReachableAll1_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forReachableAll1_ k f = f k >> forReachableAll_ k f

{-# INLINABLE forParentsAll1_ #-}
{-# INLINABLE forParentsAll_ #-}
forParentsAll1_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forParentsAll1_ k f = f k >> forParentsAll_ k f
forParentsAll_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forParentsAll_ k0 f = go k0
   where
     go k = getParent k >>= \case
        Nothing -> pure ()
        Just k' -> f k' >> go k'
parentsListAll1 :: (MonadGraph k m, Ord k) => k -> m [k]
parentsListAll1 k = do
   execWriterT $  forParentsAll1_ k $ \k' -> tell [k']
activeParents :: (MonadGraph k m, Ord k) => k -> m [k]
activeParents k = do
   execWriterT $  forParentsAll_ k $ \k' -> do
      p <- isHidden k'
      unless p (tell [k'])

data GraphState k = GraphState {
    parentMap :: M.Map k k,
    childMap :: M.Map k (S.Set k),
    arityMap :: M.Map k Int,
    hidden :: S.Set k,
    newHidden :: S.Set k
} deriving (Eq, Ord, Show, Generic)
newtype GraphT k m a = GraphT { unGraphT :: StateT (GraphState k) m a }
    deriving newtype (Functor, Applicative, Monad, MonadTrans, MFunctor, Alternative, MonadPlus, MonadSnapshot, MonadCut, MonadFail)
instance (Ord k, Monad m) => MonadGraph k (GraphT k m) where
    {-# INLINE getParentsMap #-}
    {-# INLINE getChildrenMap #-}
    {-# INLINE getAritiesMap #-}
    {-# INLINE getHidden #-}
    getParentsMap = GraphT (gets parentMap)
    getChildrenMap = GraphT (gets childMap)
    getAritiesMap = GraphT (gets arityMap)
    getHidden = GraphT (gets hidden)

instance (Ord k, Monad m, Show k) => MonadGraphMut k (GraphT k m) where
    changeState m = do
      s <- GraphT get
      let (a, s') = runState m s
      GraphT $ put s'
      pure a
       
    {-# INLINABLE addChild #-}
    addChild k k' = do
        getParent k' >>= \case
          Nothing -> do
            -- traceM $ "addChild1 " <> show k <> " " <> show k'
            GraphT $ modify $ \s ->
                          s { childMap = M.insertWith S.union k (S.singleton k') (childMap s)
                            , parentMap = M.insert k' k (parentMap s)
                            , arityMap = M.insert k' 1 (arityMap s) }
            forParentsAll_ k' $ \v -> GraphT (#arityMap . ix v += 1)
          Just oldParent -> do
            -- traceM $ "addChild2 " <> show k <> " " <> show k'
            ar <- getArity k'
            forParentsAll_ k' $ \v -> GraphT (#arityMap . ix v -= ar)
            GraphT $ do
              #childMap . ix oldParent . at k' .= Nothing
              #childMap . ix k . at k' .= Just ()
              #parentMap . at k' .= Just k
            forParentsAll_ k' $ \v -> GraphT (#arityMap . ix v += ar)
  
    {-# INLINE hideNodeUnsafe #-}
    hideNodeUnsafe :: Monad m => k -> GraphT k m ()
    hideNodeUnsafe k = do
        GraphT (#hidden . at k .= Just ())
    {-# INLINABLE deleteNode #-}
    deleteNode :: Monad m => k -> GraphT k m ()
    deleteNode k = do
        forParentsAll_ k $ \k' -> GraphT (#arityMap . ix k' -= 1)
        markNodeAffected k
        GraphT $ do 
          #hidden . at k .= Nothing
          #arityMap . at k .= Nothing
          #childMap . at k .= Nothing
          #childMap . each . at k .= Nothing
          #parentMap . at k .= Nothing
    {-# INLINABLE unhideNode #-}
    unhideNode :: Monad m => k -> GraphT k m ()
    unhideNode k = do
        GraphT (#hidden . at k .= Nothing)
    {-# INLINABLE markNodeAffected #-}
    markNodeAffected :: Monad m => k -> GraphT k m ()
    markNodeAffected k = GraphT (#newHidden . at k .= Just ())

    newlyHidden = GraphT (gets newHidden)
    resetNewHidden = GraphT (modify $ \s -> s { newHidden = S.empty })

    {-# INLINABLE focusOn #-}
    focusOn t m = do
        old <- GraphT (gets hidden)
        focusing <- GraphT (gets $ \s -> nodesOf s S.\\ t)
        GraphT $ modify $ \s -> s { hidden = focusing, newHidden = mempty }
        o <- m
        GraphT $ modify $ \s -> s { hidden = S.union (hidden s S.\\ focusing) old, newHidden = mempty }
        pure o
    {-# INLINABLE addDeps #-}
    addDeps deps0 = do
      oldDeps <- getChildrenMap
      let onlyRhs = mconcat (M.elems deps0) S.\\ S.fromList (M.keys deps0)
          deps = M.union deps0 (M.fromList [(k, S.empty) | k <- S.toList onlyRhs])
          newDeps = MM.merge MM.preserveMissing MM.dropMissing (MM.zipWithMatched $ \_ _ b -> b) deps oldDeps
          sizes = M.fromList [(k, 1+sum childSizes) | (k,vs) <- M.toList newDeps, let childSizes = map (sizes M.!) (S.toList vs)  ]
          parsMap = M.fromList [(k, p) | (p,cs) <- M.toList newDeps, k <- S.toList cs]
      -- pred <- GraphT get
      GraphT $ do
         modify $ \s -> s { childMap = M.unionWith (<>) newDeps (childMap s), parentMap = M.union parsMap (parentMap s), arityMap = MM.merge MM.preserveMissing MM.preserveMissing (MM.zipWithMatched $ \_ a b -> a + b - 1) sizes (arityMap s) }
      -- post <- GraphT get
      -- traceM ("addDeps " <> show deps <> ", newdeps " <> show newDeps <> show pred <> ", " <> show post)
      where notNull x = if S.null x then Nothing else Just x
    reduceArity i k = do GraphT $ #arityMap . ix k -= i

{-# INLINABLE hideNode #-}
hideNode :: MonadGraphMut k m => k -> m ()
hideNode k = do
  alreadyHidden <- isHidden k
  unless alreadyHidden $ do
      hideNodeUnsafe k
      markNodeAffected k
{-# INLINABLE nodesOf #-}
nodesOf :: Ord k => GraphState k -> S.Set k
nodesOf k = S.fromAscList $ M.keys $ arityMap k


-- hideNodesBelow :: MonadGraphMut k m => k -> m ()
-- hideNodesBelow k = forActiveReachable1_ k $ \k' -> hideNode k'
{-# INLINABLE deleteNodesBelow #-}
deleteNodesBelow :: (Show k, Num k, MonadGraphMut k m) => k -> m ()
deleteNodesBelow k0 = do
  a <- getArity k0
  aParent <- getParent k0
  childMap <- getChildrenMap
  r <- execWriterT $ forReachableAll1_ k0 (\x -> do
    s <- isHidden x
    -- when (s && x /= k0) (error ("deleteNodesBelow: node is hidden: " <> show x))
    tell (Endo (x:))
    )
  let reachable = k0:appEndo r []
      keyMap = M.fromList [(k, ()) | k <- reachable]
      keySet = S.fromList reachable
  changeState $ do
      #newHidden <>= keySet
      #hidden %= (S.\\ keySet)
      #childMap %= (M.\\ keyMap)
      #arityMap %= (M.\\ keyMap)
      #parentMap %= (M.\\ keyMap)
      #childMap . each %= (S.\\ keySet)
  case aParent of
    Nothing -> pure ()
    Just p -> forParentsAll1_ p $ \k' -> reduceArity a k'

{-# INLINABLE containsHidden #-}
containsHidden :: MonadGraph k m => m (S.Set k)
containsHidden = do
  hidden <- getHidden
  ls <- traverse parentsListAll1 (S.toList hidden)
  pure $ S.fromList $ concat ls
{-# INLINABLE largestNodeWith #-}
largestNodeWith :: (MonadGraph k m) => (Int -> k -> Bool) -> m (Maybe (Int,k))
largestNodeWith p = do
    m <- getAritiesMap
    h <- getHidden
    pure $ maximumByOf each (comparing fst) [ (v,k) | (k,v) <- M.toList m, p v k, not (S.member k h) ]
{-# INLINABLE nodeCount #-}
nodeCount :: MonadGraph k m => m Int
nodeCount = do
    n <- getAritiesMap
    h <- getHidden
    pure $ M.size n - S.size h

{-# INLINABLE rootsOf #-}
rootsOf :: MonadGraph k m => S.Set k -> m (S.Set k)
rootsOf ks = do
    o <- forM (S.toList ks) $ \k -> do
        ps <- parentsListAll1 k
        pure $ head $ filter (`S.member` ks) $ reverse ps
    pure $ S.fromList o
{-# INLINABLE getActiveRoots #-}
getActiveRoots :: MonadGraph k m => m (S.Set k)
getActiveRoots = do
    s <- getParentsMap
    n <- getActiveNodes
    let
      toRoot x = case M.lookup x s of
        Just x'
          | S.member x' n -> toRoot x'
        _ -> x
    pure (S.map toRoot n)

{-# INLINABLE getActiveNodes #-}
getActiveNodes :: MonadGraph k m => m (S.Set k)
getActiveNodes = do
    n <- getAritiesMap
    h <- getHidden
    pure $ S.fromAscList (M.keys n) S.\\ h
markAllCritical :: (Show k, MonadGraphMut k m) => m ()
markAllCritical = do
    nodes <- getActiveRoots
    traceM $ "markAllCritical " <> show nodes
    forM_ nodes $ hideNodeUnsafe

{-# INLINABLE pathFromRoot #-}
pathFromRoot :: MonadGraph k m => k -> m [k]
pathFromRoot k = fmap reverse $ execWriterT (forParentsAll1_ k $ \k' -> tell [k'])

runGraphT :: (Monad m) => GraphT Int m a -> m a
runGraphT = flip evalStateT (GraphState M.empty M.empty M.empty S.empty S.empty) . unGraphT

-- reparent :: MonadGraphMut k m => k -> k -> m ()
-- reparent f t =
--   setParent t =<< getParent f

{-# INLINABLE setParent #-}
setParent :: MonadGraphMut k m => k -> Maybe k -> m ()
setParent k p = do
    getParent k >>= \case
      Nothing -> pure ()
      Just old -> changeState $ #childMap . ix old . at k .= Nothing
    changeState $ do
        #parentMap . at k .= p
        case p of
          Just new -> #childMap . ix new . at k ?= ()
          _ -> pure ()


{-# INLINABLE navTo #-}
navTo :: forall o k m. (HasCallStack, RecView o m, MonadGraph k m, HasIdx o k, Show k) => Traversal' o o -> k -> m ()
navTo l t0 = do
   path <- pathFromRoot t0
   toPath (S.fromList path)
   cur <- cursors theIdx
   downPath (dropWhile (/= cur) path)
  where
   toPath path = do
      k' <- cursors theIdx
      if k' `S.member`  path
      then pure ()
      else orThrow upBool >> toPath path
   downPath (x:xs)
     | x == t0 = pure ()
     | (y:ys) <- xs  = downTo y *> downPath (y:ys)
   downPath _ =  error "illegal downPath"

   downTo :: k -> m ()
   downTo x = do
       orThrow (layerDownBool l)
       mapZipper leftmost
       let
         seek = do
           k <- cursors theIdx
           if k == x then pure ()
           else orThrow (pullBool rightward) *> seek
       seek

