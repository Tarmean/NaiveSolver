{-# LANGUAGE DataKinds #-}
module Optics.Utils where
import Optics
import Control.Monad.State
import Optics.State.Operators

overM_ :: (MonadState s m, Is k A_Fold) => Optic' k is s a -> (a -> m r) -> m ()
overM_ l f = do
    s <- get
    traverseOf_ l f s

ioverM_ :: (MonadState s m, Is k A_Fold) => Optic' k '[i] s a -> (i -> a -> m r) -> m ()
ioverM_ l f = do
    s <- get
    itraverseOf_ l f s

orDefault l r = do
    b <- gets (has l)
    when (not b) (l .= r)


