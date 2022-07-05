{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
module Data.Mutable.Indexing where
import Data.Mutable.Lens
import Data.Functor.Compose
import Control.Lens
import qualified Data.Vector.Storable as IS
import Control.Monad.Primitive
import qualified Data.Vector.Generic.Mutable as V
import qualified Data.Vector.Unboxed as IU
import qualified Data.Vector as IB
import qualified Data.Primitive.PrimArray as A
import qualified Data.Vector.Hashtables as HT
import Data.Vector.Hashtables.Internal (DeleteEntry)
import Data.Hashable
import Data.Foldable (traverse_)



ixLens
    :: (Monad f, Traversable g)
    => (v -> ix -> f a)
    -> (v -> ix -> a -> f ())
    -> ix
    -> (a -> Compose f g a) -> v -> Compose f g ()
ixLens tRead tWrite = fid $ \i f m ->
    Compose $ do
      a <- tRead m i
      fa <- getCompose (f a)
      traverse (tWrite m i) fa
  where fid = id

class ValidateIdx v where
  validateIdx :: Index v -> v -> Bool
class IxM m v where
  tryIxM :: Applicative m => Index v -> LValTraversal m v (IxValue v)
  default tryIxM :: (ValidateIdx v, Applicative m) => Index v -> LValTraversal m v (IxValue v)
  tryIxM idx = (filtered (validateIdx idx) .$ uncheckedIxM idx)
  ixM :: Index v -> LValLens m v (IxValue v)
  uncheckedIxM :: Index v -> LValLens m v (IxValue v)
  uncheckedIxM = ixM
type instance Index (IS.MVector n a) = Int
type instance IxValue (IS.MVector n a) = a

instance (IS.Storable a) => ValidateIdx (IS.MVector n a) where
    validateIdx i a = i >= 0 && i < V.length a
instance (IS.Storable a, V.MVector IS.MVector a, PrimMonad m, n ~ PrimState m) => IxM m (IS.MVector n a) where
    ixM idx = ixLens V.read V.write idx
    uncheckedIxM idx = ixLens V.unsafeRead V.unsafeWrite idx

type instance Index (IU.MVector n a) = Int
type instance IxValue (IU.MVector n a) = a
instance (V.MVector IU.MVector a) => ValidateIdx (IU.MVector n a) where
    validateIdx i a = i >= 0 && i < V.length a
instance (V.MVector IU.MVector a, PrimMonad m, n ~ PrimState m) => IxM m (IU.MVector n a) where
    ixM idx = ixLens V.read V.write idx
    uncheckedIxM idx = ixLens V.unsafeRead V.unsafeWrite idx
type instance Index (IB.MVector n a) = Int
type instance IxValue (IB.MVector n a) = a
instance ValidateIdx (IB.MVector n a) where
    validateIdx i a = i >= 0 && i < V.length a
instance (V.MVector IB.MVector a, PrimMonad m, n ~ PrimState m) => IxM m (IB.MVector n a) where
    ixM idx = ixLens V.read V.write idx
    uncheckedIxM idx = ixLens V.unsafeRead V.unsafeWrite idx
type instance Index (A.MutablePrimArray n a) = Int
type instance IxValue (A.MutablePrimArray n a) = a
type instance IxValue (A.PrimArray a) = a
type instance Index (A.PrimArray a) = Int





type instance Index (HT.Dictionary s ks k vs v) = k
type instance IxValue (HT.Dictionary s ks k vs v) = v

instance (Hashable k, V.MVector vs v, V.MVector ks k, PrimMonad m, s ~ PrimState m) => IxM m (HT.Dictionary s ks k vs v) where
   tryIxM k f s = Compose $ do
       HT.lookup s k >>= \case
           Nothing -> pure (pure ())
           Just v -> do
              fv <- getCompose $ f v
              traverse (HT.insert s k) fv
   ixM k f s = Compose $ do
       HT.lookup s k >>= \case
           Nothing -> error "ixM: key not found"
           Just v -> do
              fv <- getCompose $ f v
              traverse (HT.insert s k) fv


class IxM m a => AtM m a where
    atM :: Index a -> MLens m a (Maybe (IxValue a))
instance (PrimMonad m, Eq k, Hashable k, s ~ PrimState m, DeleteEntry ks, V.MVector vs v, V.MVector ks k, DeleteEntry vs) => AtM m (HT.Dictionary s ks k vs v) where
    atM k f s = Compose $ do
        mo <- HT.lookup s k
        fa <- getCompose $ f mo
        let
          cont Nothing = HT.delete s k
          cont (Just o) = HT.insert s k o
        fu <- traverse cont fa
        pure $ s <$ fu
