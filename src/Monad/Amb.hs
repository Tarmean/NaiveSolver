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

data AmbT r m a = Amb { runAmb :: (a -> m r -> m r) -> m r -> m r }
  deriving Functor
instance MonadSnapshot m => MonadSnapshot (AmbT r m)
   
pick :: (Foldable t, Alternative f) => t a -> f a
pick = F.asum . map pure . F.toList

instance Monad (AmbT r m) where
  Amb m >>= f = Amb $ \onSucc onFail -> m (\a onFail' -> runAmb (f a) onSucc onFail') onFail
instance Applicative (AmbT r m) where
  pure a = Amb $ \k e -> k a e
  (<*>) = ap
instance Alternative (AmbT r m) where
  empty = Amb $ \_ onFail -> onFail
  Amb m <|> Amb n = Amb $ \onSucc onFail -> m onSucc (n onSucc onFail)
instance MonadPlus (AmbT r m) where
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
onFailure m = Amb $ \onSucc onFail -> onSucc () (m *> onFail)
instance MonadTrans (AmbT r) where
  lift m = Amb $ \onSucc onFail -> m >>= \x -> onSucc x onFail
instance PrimMonad m => PrimMonad (AmbT r m) where
  type PrimState (AmbT r m) = PrimState m
  primitive = lift . primitive
instance (Alternative  m, Monad m) => MonadCont (AmbT r m) where
  callCC cont = Amb $ \onSucc onFail -> runAmb (cont $ \a -> Amb $ \_onSucc' _onFail' -> onSucc a empty) onSucc onFail

withFuture_ :: ((a -> AmbT r m ()) -> AmbT r m a) -> AmbT r m a
withFuture_ f = Amb $ \onSucc onFail -> runAmb (f $ \a -> Amb $ \next failed -> onSucc a (next () failed)) (\a _ -> onSucc a onFail) onFail


gatherList :: Applicative m => AmbT [r] m r -> m [r]
gatherList (Amb k) = k (\a b -> (a:) <$> b) (pure [])
ambToList :: AmbT [r] Identity r -> [r]
ambToList = runIdentity . gatherList

withFuture :: ((a -> m r) -> m r) -> AmbT r m a
withFuture f = Amb $ \onSucc onFail -> f $ \a -> onSucc a onFail
-- withFuture' :: Applicative m => ((a -> AmbT m ()) -> AmbT m ()) -> AmbT m a
