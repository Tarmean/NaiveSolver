{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Mutable.Internal.MutZoom (BaseMonad, JoinZoom (joinZoom)) where
import Control.Lens.Internal.Zoom
import Control.Monad
import Data.Functor.Compose (Compose(..))
import Control.Lens (Zoomed)
import Data.Mutable.Distributive
import Control.Monad.State (StateT)
import Data.Kind (Type)
import Control.Monad.Trans.Writer (WriterT)
import Control.Monad.Reader (ReaderT)

type family BaseMonad (m :: Type -> Type) :: Type -> Type
type instance BaseMonad (StateT s m) = m
type instance BaseMonad (WriterT r m) = BaseMonad m
type instance BaseMonad (ReaderT r m) = BaseMonad m
type instance BaseMonad (Focusing m s) = m
type instance BaseMonad (FocusingWith w m s) = m
type instance BaseMonad (FocusingPlus w k s) = BaseMonad (k (s,w))
type instance BaseMonad (FocusingOn f k s) = BaseMonad (k (f s))
type instance BaseMonad (FocusingMay k s) = BaseMonad (k (May s))
type instance BaseMonad (FocusingErr e k s) = BaseMonad (k (Err e s))
type instance BaseMonad (FocusingFree f m k s) = BaseMonad (k (Freed f m s))

class (Monad (BaseMonad n)) => JoinZoom n where
    joinZoom :: BaseMonad n (n a) -> n a
instance Monad m => JoinZoom (Focusing m s) where
    joinZoom = Focusing . join . fmap unfocusing
instance Monad m => JoinZoom (FocusingWith w m s) where
    joinZoom = FocusingWith . join . fmap unfocusingWith

instance (JoinZoom (k (s,w))) => JoinZoom (FocusingPlus w k s) where
    joinZoom = FocusingPlus . joinZoom . fmap unfocusingPlus
instance (JoinZoom (k (f s))) => JoinZoom (FocusingOn f k s) where
    joinZoom = FocusingOn . joinZoom . fmap unfocusingOn

instance (JoinZoom (k (May s))) => JoinZoom (FocusingMay k s) where
    joinZoom = FocusingMay . joinZoom . fmap unfocusingMay
instance (JoinZoom (k (Err e s))) => JoinZoom (FocusingErr e k s) where
    joinZoom = FocusingErr . joinZoom . fmap unfocusingErr
instance (JoinZoom (k (Freed f m s)), Monad m) => JoinZoom (FocusingFree f m k s) where
    joinZoom = FocusingFree . joinZoom . fmap unfocusingFree

newtype AddLayerZ k m s a = AddLayerZ { runAddLayerZ :: m (k s a) }
  deriving Functor
instance (Applicative m, Applicative (k s)) => Applicative (AddLayerZ k m s) where
    pure = AddLayerZ . pure . pure
    AddLayerZ f <*> AddLayerZ x = AddLayerZ $ getCompose (Compose f <*> Compose x)
newtype AddLayer m a = AddLayer (m a)
  deriving (Functor, Applicative, Monad)
type instance Zoomed (AddLayer m) = AddLayerZ (Zoomed m) m
   
