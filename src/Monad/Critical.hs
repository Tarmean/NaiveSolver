{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Monad.Critical where


import Control.Monad.State
import qualified Data.Set as S
import Control.Monad.Morph
import Control.Monad.Writer (WriterT)
import Control.Monad.Reader (ReaderT)
import Data.Functor.Identity (Identity)
import Monad.Zipper
import Data.Monoid (Last(..))
import Monad.Oracle (MonadOracle)
import Control.Applicative (Alternative)
import Monad.Snapshot (MonadSnapshot)
import Monad.Cut (MonadCut)

newtype Critical k m a = Critical { unCritical :: StateT (S.Set k) m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans, MFunctor, Alternative, MonadPlus, MonadSnapshot, MonadCut, MonadFail)
evalCriticalT :: (Ord k, Monad m) => Critical k m a -> m a
evalCriticalT = flip evalStateT S.empty . unCritical
evalCritical :: (Ord k) => Critical k Identity a -> a
evalCritical = flip evalState S.empty . unCritical

instance MonadState s m => MonadState s (Critical k m) where

  get = lift get
  put = lift . put

class Monad m => MonadCritical k m | m -> k where
    {-# INLINE markCritical #-}
    {-# INLINE isCritical #-}
    markCritical :: k -> m ()
    default markCritical :: (MonadCritical k n, MonadTrans t, t n ~ m) => k -> m ()
    markCritical = lift . markCritical
    isCritical :: k -> m Bool
    default isCritical :: (MonadCritical k n, MonadTrans t, t n ~ m) => k -> m Bool
    isCritical = lift . isCritical
    getCriticals :: m (S.Set k)
    default getCriticals :: (MonadCritical k n, MonadTrans t, t n ~ m) => m (S.Set k)
    getCriticals = lift getCriticals

instance (Monad m, Ord k) => MonadCritical k (Critical k m) where
    {-# INLINE markCritical #-}
    {-# INLINE isCritical #-}
    markCritical k = Critical $ modify $ S.insert k
    isCritical k = Critical $ gets $ S.member k
    getCriticals = Critical get
instance MonadCritical k m => MonadCritical k (StateT s m)
instance (Monoid r, MonadCritical k m) => MonadCritical k (WriterT r m)
instance (MonadCritical k m) => MonadCritical k (ReaderT r m)


instance MonadZipper o m => MonadZipper o (Critical r m)
instance RecView o m => RecView o (Critical r m)
instance HasView m n o i idx => HasView (Critical r m) (Critical r n) o i idx where
    iwithinM l m  = Critical $ StateT $ \i -> fmap (swizzle i) $ iwithinM l (fmap inj $ runStateT (unCritical m) i)
      where
        swizzle _ (s,Last (Just r)) = (s, r)
        swizzle _ _ = error "weird things"
        inj (a,b) = (a, Last (Just b))
instance HasRec o m n => HasRec o (Critical r m) (Critical r n)
instance MonadOracle n => MonadOracle (Critical r n)
