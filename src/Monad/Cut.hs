{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Monad.Cut where
import Control.Monad.Morph
import Control.Monad.State (StateT)
import Control.Monad.Trans.Writer (WriterT)
import Control.Monad.Cont (ContT)
import Monad.Amb
import Control.Monad (guard)
import Control.Applicative
import Control.Monad.Trans.Control

import Data.IORef
import Debug.Trace
import GHC.IO (unsafePerformIO)

class (MonadFail m) => MonadCut m where
   cut :: m a -> m a
   default cut :: (m ~ t n, MonadCut n, MFunctor t) => m a -> m a
   cut = hoist cut
   {-# INLINE cut #-}


   ifte :: m a -> (a -> m b) -> m b -> m b
   default ifte :: (m ~ t n, MonadCut n, MonadTransControl t) => m a -> (a -> m b) -> m b -> m b
   ifte a f b = controlT $ \run -> ifte (run a) (\x -> run $  f =<< restoreT (pure x)) (run b)

instance MonadCut m => MonadCut (StateT s m)
instance MonadCut (AmbT r m) where
    {-# INLINE cut #-}
    cut (Amb k) = Amb $ \idx onSucc onFail -> 
       k idx (\idx' a _ -> onSucc idx' a onFail) onFail

    ifte :: AmbT r m a -> (a -> AmbT r m b) -> AmbT r m b -> AmbT r m b
    ifte (Amb k) f (Amb e) = Amb $ \idx onSucc onFail -> unsafePerformIO $ do
       ref <- newIORef False
       let markVisited = unsafePerformIO $ writeIORef ref True
       pure $ k idx (
            \idx' a e -> markVisited `seq` runAmb (f a) idx' onSucc e
         ) (
             \idx' -> if unsafePerformIO (readIORef ref) then onFail idx' else e idx' onSucc onFail
         )

test :: [(Int,Int)]
test = ambToList $ do
   s <- pick [1..10]
   t <- cut $ do
       t <- pick [1..10]
       guard (s + t == 10)
       pure t
   pure (s,t)



testIfThenElse :: [Int]
testIfThenElse = ambToList $ do
    ifte (ifte (pure 0) pure (pure 1) *> empty) pure (pure 10)

instance (Monoid s, MonadCut m) => MonadCut (WriterT s m)
