{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Data.Mutable.Distributive where
import Control.Lens
import Control.Lens.Internal.Zoom
import Data.Functor.Compose
import Control.Monad (join)
import Control.Monad.Reader (ReaderT, MonadTrans (lift))
import Control.Applicative (Alternative)
import Control.Monad.Identity (IdentityT)
import Control.Monad.Trans.Writer (WriterT)
import Control.Monad.State (StateT)
import GHC.TypeLits
import Data.Monoid (Ap (..))
import Control.Monad.Primitive
import Data.Kind (Type)


type HasMonad m f = (JoinR m f, JoinL m f)

class JoinR m f | f -> m where
    joinR :: m (f a) -> f a
    default joinR :: (f ~ t m, MonadTrans t, Monad (t m), Monad m) => m (f a) -> f a
    joinR = join . lift
instance Monad m => JoinR m (Compose m f) where
   joinR =  Compose . join . fmap getCompose
instance  (Monad m) => JoinR m (IdentityT m)
instance  (Monad m) => JoinL m (IdentityT m)
instance  (Monoid e, Monad m) => JoinR m (WriterT e m)
instance  (Monoid e, Monad m) => JoinL m (WriterT e m)
instance  (Monad m) => JoinR m (StateT s m)
instance  (Monad m) => JoinL m (StateT s m)
instance  (Monad m) => JoinR m (ReaderT s m)
instance  (Monad m) => JoinL m (ReaderT s m)
instance (Functor m, JoinR m t) => JoinR m (Ap t) where
   joinR = Ap . joinR . fmap getAp
instance JoinL m  t=> JoinL m (Ap t) where
   joinL = Ap . joinL . getAp
instance JoinL m t => JoinL m (Const (t x)) where
   joinL (Const a) = Const a
instance (Functor m, JoinR m t) => JoinR m (Const (t x)) where
   joinR = Const . joinR . fmap getConst

class Dysfunctional a b | a -> b, b -> a where
instance (Dysfunctional a b) => Dysfunctional a b where
instance {-# OVERLAPPABLE #-} (
    Dysfunctional m t,
    TypeError ('Text "Missing Instance: JoinR " ':<>: 'ShowType m ':<>: 'Text " "  ':<>: 'ShowType t)
  ) => JoinR m t where
  joinR = undefined

mapML :: (JoinL m f, Functor f) => (a -> m b) -> f a -> f b
mapML f m = joinL $ fmap f m
mapMR :: (JoinR m f, Functor m) => (a1 -> f a2) -> m a1 -> f a2
mapMR f m = joinR $ fmap f m


class Functor f => JoinL m f | f -> m where
    joinL :: f (m a) -> f a
    default joinL :: (Monad (t m), Monad m, f ~ t m, MonadTrans t) => f (m a) -> f a
    joinL = join . fmap lift
instance (Monad m, Distributes m f) => JoinL m (Compose m f) where
   joinL =  Compose . join .  fmap distributes . getCompose

class Functor f => Distributes m f where
    distributes :: f (m a) -> m (f a)
    default distributes :: (Applicative m, Traversable f) => f (m a) -> m (f a)
    distributes = sequenceA
    {-# INLINE distributes #-}
traverseD :: Distributes m f => (a -> m b) -> f a -> m (f b)
traverseD f = distributes . (fmap f)

instance Applicative m => Distributes m ((,) w)
instance Applicative m => Distributes m Identity
instance Applicative m => Distributes m (Const w)

instance Monad m => Distributes m (Focusing m s) where
    distributes m = do
      (s,ma) <- unfocusing m
      a <- ma
      pure $ Focusing $ pure (s,a)
instance (Applicative m, Distributes m (k (s,w)), Functor (k (s,w))) => Distributes m (FocusingPlus w k s)  where
    distributes m = FocusingPlus <$> distributes (unfocusingPlus m)
instance (Applicative m, Distributes m (k (Err w s )), Functor (k (Err w s ))) => Distributes m (FocusingErr w k s)  where
    distributes m = FocusingErr <$> distributes (unfocusingErr m)
instance (Applicative m, Distributes m (k (w s)), Functor (k (w s))) => Distributes m (FocusingOn w k s)  where
    distributes m = FocusingOn <$> distributes (unfocusingOn m)
instance (Applicative m, Distributes m (k (May s)), Functor (k (May s))) => Distributes m (FocusingMay k s)  where
    distributes m = FocusingMay <$> distributes (unfocusingMay m)
instance (Applicative m, Distributes m (k (Freed f m s)), Functor (k (Freed f m s))) => Distributes m (FocusingFree f m k s)  where
    distributes m = FocusingFree <$> distributes (unfocusingFree m)
