{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Mutable.Internal.MutZoom (JoinZoom (joinZoom)) where
import Control.Lens.Internal.Zoom
import Control.Monad
import Data.Functor.Compose (Compose(..))
import Control.Lens (Zoomed)
import Data.Mutable.Distributive

class Monad m => JoinZoom m n | n -> m where
    joinZoom :: m n -> n
instance Monad m => JoinZoom m (Focusing m s t) where
    joinZoom = Focusing . join . fmap unfocusing
instance Monad m => JoinZoom m (FocusingWith w m s t) where
    joinZoom = FocusingWith . join . fmap unfocusingWith

instance (Monad m, JoinZoom m (k (s,w) a)) => JoinZoom m (FocusingPlus w k s a) where
    joinZoom = FocusingPlus . joinZoom . fmap unfocusingPlus
instance (JoinZoom m (k (f s) a), Monad m) => JoinZoom m (FocusingOn f k s a) where
    joinZoom = FocusingOn . joinZoom . fmap unfocusingOn

instance (JoinZoom m (k (May s) a), Monad m) => JoinZoom m (FocusingMay k s a) where
    joinZoom = FocusingMay . joinZoom . fmap unfocusingMay
instance (JoinZoom m (k (Err e s) a), Monad m) => JoinZoom m (FocusingErr e k s a) where
    joinZoom = FocusingErr . joinZoom . fmap unfocusingErr
instance (JoinZoom m (k (Freed f m s) a), Monad m) => JoinZoom m (FocusingFree f m k s a) where
    joinZoom = FocusingFree . joinZoom . fmap unfocusingFree

newtype AddLayerZ k m s a = AddLayerZ { runAddLayerZ :: m (k s a) }
  deriving Functor
instance (Applicative m, Applicative (k s)) => Applicative (AddLayerZ k m s) where
    pure = AddLayerZ . pure . pure
    AddLayerZ f <*> AddLayerZ x = AddLayerZ $ getCompose (Compose f <*> Compose x)
newtype AddLayer m a = AddLayer (m a)
  deriving (Functor, Applicative, Monad)
type instance Zoomed (AddLayer m) = AddLayerZ (Zoomed m) m
   
