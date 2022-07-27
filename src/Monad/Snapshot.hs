{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Monad.Snapshot where
import Data.Kind (Type)
import Control.Monad.Trans
import GHC.TypeLits
import Control.Monad.State
import Control.Monad.Cont (ContT)


type family ChildSnapshot m where
  ChildSnapshot (t n) = Snapshot n
  ChildSnapshot m = TypeError ('Text "Cannot lift type" ':<>: 'ShowType m)
class Monad m => MonadSnapshot m where
   type family Snapshot m :: Type
   type Snapshot n = ChildSnapshot n
   snapshot :: m (Snapshot m)
   default snapshot :: (Snapshot (t n) ~ Snapshot n, m ~ t n, MonadTrans t, MonadSnapshot n) => m (Snapshot m)
   snapshot = lift snapshot
   restore :: Snapshot m -> m ()
   default restore :: (Snapshot (t n) ~ Snapshot n, m ~ t n, MonadTrans t, MonadSnapshot n) => Snapshot m -> m ()
   restore = lift . restore
instance MonadSnapshot (ContT r m) where
    type Snapshot (ContT r m) = ()
    snapshot = pure ()
    restore _ = pure ()


instance MonadSnapshot m => MonadSnapshot (StateT s m) where
    type Snapshot (StateT s m) = (s, Snapshot m)
    snapshot = do
       s <- get
       t <- lift snapshot
       pure (s,t)
    restore (s,t) = put s *> lift (restore t)
