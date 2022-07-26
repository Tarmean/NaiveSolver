{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Monad.Graph where
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Trans
import Control.Lens
import Data.Generics.Labels ()
import GHC.Generics (Generic)


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

getChildren :: MonadGraph k m => k -> m (S.Set k)
getChildren k = getChildrenMap <&> (M.findWithDefault mempty k)
getParent :: (Ord k, MonadGraph k m) => k -> m (Maybe k)
getParent k = getParentsMap <&> (M.lookup k)
class MonadGraph k m => MonadGraphMut k m | m -> k where
    addChild :: k -> k -> m ()
    default addChild :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> k -> m ()
    addChild p c = lift (addChild p c)
    hideNode :: k -> m ()
    default hideNode :: (m ~ t n, MonadTrans t, MonadGraphMut k n) => k -> m ()
    hideNode = lift . hideNode
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
           unless h $ f x >> go x

forReachable_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forReachable_ k0 f = go k0
   where
      go k = do
        n <- getChildren k
        mapM_ (\x -> f x >> go x) n
forReachable1_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forReachable1_ k f = f k >> forReachable_ k f

forParents1_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forParents1_ k f = f k >> forParents_ k f
forParents_ :: (MonadGraph k m, Ord k) => k -> (k -> m ()) -> m ()
forParents_ k0 f = go k0
   where
     go k = getParent k >>= \case
        Nothing -> pure ()
        Just k' -> f k' >> go k'

data GraphState k = GraphState {
    parentMap :: M.Map k k,
    childMap :: M.Map k (S.Set k),
    arityMap :: M.Map k Int,
    hidden :: S.Set k
} deriving (Eq, Ord, Show, Generic)
newtype GraphT k m a = GraphT { unGraphT :: StateT (GraphState k) m a }
    deriving (Functor, Applicative, Monad, MonadTrans)
instance (Ord k, Monad m) => MonadGraph k (GraphT k m) where
    getParentsMap = GraphT (gets parentMap)
    getChildrenMap = GraphT (gets childMap)
    getAritiesMap = GraphT (gets arityMap)
    getHidden = GraphT (gets hidden)

instance (Ord k, Monad m) => MonadGraphMut k (GraphT k m) where
    addChild k k' = do
        getParent k' >>= \case
          Nothing -> do
            GraphT $ modify $ \s ->
                          s { childMap = M.insertWith S.union k (S.singleton k') (childMap s)
                            , parentMap = M.insert k' k (parentMap s)
                            , arityMap = M.insert k' 1 (arityMap s) }
            forParents_ k' $ \v -> GraphT (#arityMap . ix v += 1)
          Just oldParent -> do
            ar <- getArity k'
            forParents_ k' $ \v -> GraphT (#arityMap . ix v -= ar)
            GraphT $ do
              #childMap . ix oldParent . at k' .= Nothing
              #childMap . ix k . at k' .= Just ()
              #parentMap . at k' .= Just k
            forParents_ k' $ \v -> GraphT (#arityMap . ix v += ar)
  
    hideNode :: Monad m => k -> GraphT k m ()
    hideNode k = do
        forParents_ k $ \k' -> GraphT (#arityMap . ix k' -= 1)
        GraphT (#hidden . at k .= Just ())
hideNodesBelow :: MonadGraphMut k m => k -> m ()
hideNodesBelow k = forReachable1_ k $ \k' -> hideNode k'

