{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ImpredicativeTypes #-}
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
import qualified Data.Vector.Generic.Mutable as VGM
import Unsafe.Coerce (unsafeCoerce)

type family ValOf v (xs :: [Nat]) s a where
  ValOf _ '[] _ a  = a
  ValOf v (_ ': xs) s a = Slice v xs s a
data Slice v (xs :: [Nat]) s a where
    Slice :: !(v s a) -> Slice v xs s a


-- class IsSlice ls o where
-- instance IsSlice (Slice v (x ': y ': xs) s e) (Slice v (y ': xs) s e) where
-- instance IsSlice (Slice v '[x] s e) e where

-- unsafeSlice :: forall v s a o xs. (BaseVal o ~ a) => v s a -> Slice v xs s o
-- unsafeSlice = unsafeCoerce @(((ValOf v xs s a) ~ o, BaseVal o ~ a) => (v s a) -> Slice v xs s o) @((v s a) -> Slice v xs s o) Slice

type family SliceIndex d where
  SliceIndex (Slice v '[x] s  a) = Index (v s a)
  SliceIndex (Slice v (_ ': xs) s  a) = Int
class RowWidth (xs :: [Nat]) where
    width :: Int
instance RowWidth '[] where
    width = 1
instance (RowWidth xs, KnownNat x) => RowWidth (x ': xs) where
    width = fromIntegral (natVal (Proxy @x)) * width @xs

-- instance (VGM.MVector (Slice v (y ': xs)) (DropOne e)) => VGM.MVector (Slice v (x ': y ': xs)) e where
--   basicLength (Slice a) = VGM.basicLength (Slice a)
--   {-# INLINE basicLength #-}
--   basicUnsafeSlice l r (Slice a)  = Slice (VGM.slice (l * width @xs) (r * width @xs) a)
--   basicOverlaps (Slice l) (Slice r) = VGM.basicOverlaps l r
--   basicUnsafeNew len = unsafeSlice <$> VGM.basicUnsafeNew (len * width @xs)
--   basicInitialize (Slice l) = VGM.basicInitialize l
--   basicUnsafeRead (Slice l) idx  = undefined
--   basicUnsafeWrite = undefined
-- instance (RowWidth xs, BaseVal e ~ a, VGM.MVector v a) => VGM.MVector (Slice v '[]) e where
--   basicLength (Slice a) = VGM.basicLength a
--   {-# INLINE basicLength #-}
--   basicUnsafeSlice l r (Slice a)  = Slice (VGM.slice (l * width @xs) (r * width @xs) a)
--   basicOverlaps (Slice l) (Slice r) = VGM.basicOverlaps l r
--   basicUnsafeNew len = unsafeSlice <$> VGM.basicUnsafeNew (len * width @xs)
--   basicInitialize (Slice l) = VGM.basicInitialize l
--   basicUnsafeRead (Slice l) idx  = undefined
--   basicUnsafeWrite = undefined



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

-- hope you can swim
capSize :: forall a s. IP.Prim a => IP.MVector s a -> Int
capSize mv = case mv of { (IP.MVector _ _ mba) ->  sizeofMutableByteArray mba  `div` (sizeOfT @a) }
capPrim :: forall a s. (IP.Prim a) => IP.MVector s a -> Int
capPrim = capSize 
capUBPrim :: forall a s. (IP.Prim a, Coercible (IU.MVector s a) (IP.MVector s a)) => IU.MVector s a -> Int
capUBPrim = capPrim @a @s . coerce

sizeOfT :: forall a. IP.Prim a => Int
sizeOfT = sizeOf (undefined :: a)
