{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Monad.Cut where
import Control.Monad.Morph
import Control.Monad.State (StateT)
import Control.Monad.Trans.Writer (WriterT)
import Control.Monad.Cont (ContT)
import Monad.Amb
import Data.Functor.Identity
import Control.Monad (guard)
import Control.Applicative


class Monad m => MonadCut m where
   cut :: m a -> m a
   default cut :: (m ~ t n, MonadCut n, MFunctor t) => m a -> m a
   cut = hoist cut
instance MonadCut m => MonadCut (StateT s m)
instance MonadCut (AmbT r m) where
    cut (Amb k) = Amb $ \onSucc onFail -> k (\a _ -> onSucc a onFail) onFail


test :: [(Int,Int)]
test = ambToList $ do
   s <- pick [1..10]
   t <- cut $ do
       t <- pick [1..10]
       guard (s + t == 10)
       pure t
   pure (s,t)
    where pick = asum . fmap pure




instance (Monoid s, MonadCut m) => MonadCut (WriterT s m)
