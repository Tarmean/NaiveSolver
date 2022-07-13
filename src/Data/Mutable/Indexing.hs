{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
module Data.Mutable.Indexing where
import Data.Mutable.Lens
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
import Data.Mutable.Distributive



ixLens
    :: (JoinL m g, JoinR m g, Monad m)
    => (v -> ix -> m a)
    -> (v -> ix -> a -> m ())
    -> ix
    -> (a -> g a) -> v -> g ()
ixLens tRead tWrite i = mlens (`tWrite` i) (`tRead` i)

class ValidateIdx v where
  validateIdx :: Index v -> v -> Bool
class IxM m v where
  tryIxM :: (Applicative f, HasMonad m f) => Index v -> LValLensLike f v (IxValue v)
  default tryIxM :: (Applicative f, HasMonad m f, ValidateIdx v) => Index v -> LValLensLike f v (IxValue v)
  tryIxM idx = (filtered (validateIdx idx) .$ uncheckedIxM @m idx)
  ixM :: (HasMonad m f) => Index v -> LValLensLike f v (IxValue v)
  uncheckedIxM :: (HasMonad m f) => Index v -> LValLensLike f v (IxValue v)
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
   tryIxM k = maffine @m (\m -> HT.insert m k) (flip HT.lookup k)
   ixM k = mlens (\m -> HT.insert m k) (fmap unwrap . flip HT.lookup k)
     where
       unwrap (Just a) = a
       unwrap Nothing = error "ixM: key not found"

class IxM m a => AtM m a where
    atM :: HasMonad m f => Index a -> MLensLike' f a (Maybe (IxValue a))
instance (PrimMonad m, Eq k, Hashable k, s ~ PrimState m, DeleteEntry ks, V.MVector vs v, V.MVector ks k, DeleteEntry vs) => AtM m (HT.Dictionary s ks k vs v) where
    atM k = mlens setter (flip HT.lookup k)
      where
      setter t Nothing = t <$ HT.delete t k
      setter t (Just o) = t <$ HT.insert t k o
