{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Monad.Oracle where
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State

class Monad m => MonadOracle m where
    checkpoint :: m ()
    default checkpoint :: (m ~ t n, MonadTrans t, MonadOracle n) => m ()
    checkpoint = lift checkpoint
instance MonadOracle m => MonadOracle (StateT s m)
instance (Monoid s, MonadOracle m) => MonadOracle (WriterT s m)
