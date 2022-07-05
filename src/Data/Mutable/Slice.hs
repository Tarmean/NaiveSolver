{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Data.Mutable.Slice where
import GHC.TypeLits ( KnownNat, Nat, natVal )
import Control.Lens ( Index, IxValue )
import Data.Proxy ( Proxy(..) )
import qualified Data.Vector.Primitive as IP
import qualified Data.Vector.Primitive.Mutable as IP
import qualified Data.Vector.Unboxed.Mutable as IU
import Data.Coerce ( coerce, Coercible )
import Data.Primitive ( sizeofMutableByteArray, sizeOf )
import Data.Mutable.Indexing

newtype Slice v s (xs :: [Nat]) a = Slice (v s a)
type family SliceIndex d where
  SliceIndex (Slice v s '[x] a) = Index (v s a)
  SliceIndex (Slice v s (_ ': xs) a) = Int

newtype VecOfSlices v s (xs :: [Nat]) a = VecOfSlices (v s a)
type instance Index (VecOfSlices v s xs a) = Int
type instance IxValue (VecOfSlices v s xs a) = Slice v s xs a


type instance Index (Slice v s xs a) = SliceIndex (Slice v s xs a)
type family RedIndex d where
  RedIndex (Slice v s '[d] a) = IxValue (v s a)
  RedIndex (Slice v s (_ ': xs) a) = Slice v s xs a
type instance IxValue (Slice v s xs a) = RedIndex (Slice v s xs a)
-- instance (SliceStride (l ': r), ValidateIdx (v s a), SliceStride r) => ValidateIdx (Slice v s (l ': r) a) where
    -- validateIdx i a = validateIdx (i * getStride @(l ': r)) a
-- instance (Functor m, IxM m (v s a)) => IxM m (Slice v s '[d] a) where
--    ixM i f (Slice v) = ixM i f v
-- instance (SliceStride (y ': xs), Functor m, IxM m (v s a), V.MVector v a) => IxM m (Slice v s (x ': y ': xs) a) where
--    ixM i f (Slice v) =  undefined $ f (Slice (V.slice l r v))
--      where
--        stride = getStride @(x ': y ':  xs)
--        l = i * stride
--        r = (i+1) * stride - 1
class SliceStride xs where
   getStrideI :: Int
instance SliceStride '[] where
   getStrideI = 1

getStride :: forall (xs :: [Nat]) a as. (xs ~ (a ': as), SliceStride as)=> Int
getStride = getStrideI @as
instance (KnownNat x, SliceStride xs) => SliceStride (x ': xs) where
  getStrideI = fromIntegral (natVal (Proxy :: Proxy x)) * getStrideI @xs

capPrim :: forall a s. (IP.Prim a) => IP.MVector s a -> Int
capPrim mv = case mv of { (IP.MVector _ _ mba) ->  sizeofMutableByteArray mba  `div` sizeOfT @a }
capUBPrim :: forall a s. (IP.Prim a, Coercible (IU.MVector s a) (IP.MVector s a)) => IU.MVector s a -> Int
capUBPrim = capPrim @a @s. coerce

sizeOfT :: forall a. IP.Prim a => Int
sizeOfT = sizeOf (undefined :: a)
