{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
module Optics.Utils where
import Control.Lens
import Control.Monad.State

overM :: MonadState s m => Traversal' s a -> (a -> m a) -> m ()
overM l f = do
  s <- get
  s' <- traverseOf l f s
  put s'

-- overM_ :: (MonadState s m, Is k A_Fold) => Optic' k is s a -> (a -> m r) -> m ()
overM_ :: MonadState s m => Getting (Traversed r m) s a -> (a -> m r) -> m ()
overM_ l f = do
    s <- get
    traverseOf_ l f s

-- ioverM_ :: (MonadState s m, Is k A_Fold) => Optic' k '[i] s a -> (i -> a -> m r) -> m ()
ioverM_ :: MonadState s m => IndexedGetting i (Traversed r m) s a -> (i -> a -> m r) -> m ()
ioverM_ l f = do
    s <- get
    itraverseOf_ l f s

orDefault :: MonadState s m => (forall f. (Functor f) => (a -> f a) -> s -> f s) -> a -> m ()
orDefault l r = do
    b <- gets (has l)
    when (not b) (l .= r)


