{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Mutable.Distributive where
import Control.Lens
import Control.Lens.Internal.Zoom


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
