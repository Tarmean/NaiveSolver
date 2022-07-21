{-# LANGUAGE UndecidableInstances #-}
module Monad.StateT2 where
import Control.Monad.State
import Control.Applicative

newtype StateT2 s m a = StateT2 { unStateT2 :: StateT s m a }
  deriving (Functor, Applicative, Monad, Alternative, MonadTrans)
instance MonadState s m => MonadState s (StateT2 v m) where
    get = StateT2 (lift get)
    put = StateT2 . lift . put
class Monad m => Has s m where
    getS :: m s
    putS :: s -> m ()
instance Monad m => Has s (StateT2 s m) where
    getS = StateT2 get
    putS = StateT2 . put
execStateT2 :: Monad m => StateT2 s m a -> s -> m s
execStateT2 = execStateT . unStateT2
