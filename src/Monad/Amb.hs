{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-| Basic non-determinism monad plus ability to register unwinding handlers. Useful for undoing changes to mutable state:

   x <- 1 <|> 2
   #count += x
   onFailure (#count -= x)
   ...

This works even if #count targets mutable memory. Operationally, both alternatives and unwinders are allocated on the heap most of the time, often forming a linked list of continuation pointers
- Marking the CPS functions as oneShot lets GHC optimize some of that away
- But on average this can still be much worse than a specific undo stack, like dancing links
- It's also more flexible, though, because we can use compound data-structures with sharing in unwinding handlers :)
- But we must be careful not to leak memory in unwinding handlers by laziness :/
 -}
module Monad.Amb where
import Control.Monad.State ( ap, MonadTrans (lift), MonadState (..) )
import Control.Applicative ( Alternative((<|>), empty), Applicative (liftA2) )
import Control.Monad.Primitive
import Control.Monad.Cont.Class
import Control.Monad
import GHC.Base (build)
import Data.Functor.Identity
import Monad.Snapshot (MonadSnapshot)
import qualified Data.Foldable as F

newtype AmbT r m a = Amb { runAmb :: Int -> (Int -> a -> (Int -> m r) -> m r) -> (Int -> m r) -> m r }
  deriving Functor
instance MonadFail (AmbT r m) where
   fail _ = empty
instance MonadSnapshot m => MonadSnapshot (AmbT r m)
   
pick :: (Foldable t, Alternative f) => t a -> f a
pick = F.asum . map pure . F.toList


-- peekAmb :: AmbT r m a -> m a

instance Monad (AmbT r m) where
  {-# INLINE (>>=) #-}
  Amb m >>= f = Amb $ \idx onSucc onFail -> m idx (\idx' a onFail' -> runAmb (f a) idx' onSucc onFail') onFail
instance Applicative (AmbT r m) where
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  pure a = Amb $ \idx k e -> k (idx+1) a e
  (<*>) = ap
instance Alternative (AmbT r m) where
  {-# INLINE (<|>) #-}
  {-# INLINE empty #-}
  empty = Amb $ \idx _ onFail -> onFail idx
  Amb m <|> Amb n = Amb $ \idx onSucc onFail -> m idx onSucc (\idx' -> n idx' onSucc onFail)
instance MonadPlus (AmbT r m) where
    {-# INLINE mplus #-}
    {-# INLINE mzero #-}
    mzero = empty
    mplus = (<|>)
instance MonadState s m => MonadState s (AmbT r m) where
  get = lift get
  put = lift . put
-- instance MonadEgg m => MonadEgg (AmbT r m) where
--   egg = lift egg

-- | Before backtracking, run the given action.
-- Used to undo mutation
onFailure :: (Applicative m) => m () -> AmbT r m ()
onFailure m = Amb $ \idx onSucc onFail -> onSucc idx () (\x -> m *> onFail x)
instance MonadTrans (AmbT r) where
  lift m = Amb $ \idx onSucc onFail -> m >>= \x -> onSucc idx x onFail
instance PrimMonad m => PrimMonad (AmbT r m) where
  type PrimState (AmbT r m) = PrimState m
  primitive = lift . primitive
instance (Alternative  m, Monad m) => MonadCont (AmbT r m) where
  callCC cont = Amb $ \idx onSucc onFail -> runAmb (cont $ \a -> Amb $ \idx' _onSucc' _onFail' -> onSucc idx' a (\_ -> empty)) idx onSucc onFail

-- withFuture_ :: ((a -> AmbT r m ()) -> AmbT r m a) -> AmbT r m a
-- withFuture_ f = Amb $ \idx onSucc onFail -> runAmb (f $ \a -> Amb $ \idx' next failed -> onSucc idx' a (next () failed)) idx (\a _ -> onSucc a onFail) onFail


gatherList :: Applicative m => AmbT [r] m r -> m [r]
gatherList (Amb k) = k 0 (\idx a b -> (a:) <$> (b idx)) (\_ -> pure [])
ambToList :: AmbT [r] Identity r -> [r]
ambToList = runIdentity . gatherList

withFuture :: ((a -> m r) -> m r) -> AmbT r m a
withFuture f = Amb $ \idx onSucc onFail -> f $ \a -> onSucc idx a onFail
-- withFuture' :: Applicative m => ((a -> AmbT m ()) -> AmbT m ()) -> AmbT m a
