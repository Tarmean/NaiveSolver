{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Data.Growable where
import Control.Lens
import qualified Data.Vector.Generic.Mutable as V
import qualified Data.Vector.Generic as VN
import qualified Data.List as List
import qualified Data.Vector as IB
import Control.Monad.Primitive ( PrimMonad(PrimState) )
import Data.Coerce
import Data.Kind (Type)
import qualified Data.Vector.Unboxed.Mutable as IU
import qualified Data.Vector.Primitive.Mutable as IP
import qualified Data.Vector.Storable.Mutable as IS
import qualified Data.Primitive as Prim
import qualified Data.Vector.Mutable as IB
import qualified GHC.ForeignPtr as FP
import GHC.IO.Unsafe (unsafePerformIO)
import qualified Foreign as F

import Data.Mutable.Lens
import Data.Mutable.Indexing
import Data.Mutable.Each
import Control.Monad.State
import Data.Mutable.Slice
import Data.Mutable.QuickSort (quickSort)

type instance Index (Grow v s a) = Int
type instance IxValue (Grow v s a) = a

instance (Index (v n a) ~ Int, ValidateIdx (v n a)) => ValidateIdx (Grow v n a) where
  validateIdx i = validateIdx i . unGrow
instance (ValidateIdx (v n a), V.MVector v a, IxM m (v n a), Index (v n a) ~ Int, IxValue (v n a) ~ a, PrimMonad m, n ~ PrimState m) => IxM m (Grow v n a) where
    ixM i f (Grow m) = fmap coerce (ixM i f m)

newtype Grow v s (a :: Type) = Grow { unGrow :: v s a}


type family CoerceGrowable (a :: Type) :: Type where
  CoerceGrowable (Grow v s a) = v s a
  CoerceGrowable (a -> b) = CoerceGrowable a -> CoerceGrowable b
  CoerceGrowable c = c

coerceF :: Coercible a (CoerceGrowable a) => CoerceGrowable a -> a
coerceF = coerce

class Capacity v where
    getCapacity :: v -> Int
instance Capacity (IU.MVector s Int) where
    getCapacity =  capUBPrim
instance IP.Prim a => Capacity (IP.MVector s a) where
   getCapacity = capPrim
instance (F.Storable a) => Capacity (IS.MVector s a) where
   getCapacity v = storableVecBufSize v `div` F.sizeOf (undefined :: a)
instance Capacity (IB.MVector s a) where
   getCapacity (IB.MVector _ _ ma) = Prim.sizeofMutableArray ma

storableVecBufSize :: IS.MVector s a -> Int
storableVecBufSize (IS.MVector _ (FP.ForeignPtr _ (FP.MallocPtr buf _))) = Prim.sizeofMutableByteArray  (Prim.MutableByteArray buf)
storableVecBufSize (IS.MVector _ (FP.ForeignPtr _ (FP.PlainPtr buf))) = Prim.sizeofMutableByteArray  (Prim.MutableByteArray buf)
storableVecBufSize _ = undefined

ensureCap :: (Capacity (v (PrimState m) a), PrimMonad m, V.MVector v a) => Int -> Grow v (PrimState m) a -> m (Grow v (PrimState m) a)
ensureCap reserve (Grow v)
  | cap - reserve <= curSize = Grow . V.slice 0 curSize <$> V.unsafeGrow v cap'
  | otherwise = pure (Grow v)
  where
    cap = getCapacity v
    curSize = V.length v
    cap' = roundUpPower2 (max 1 cap)

    target = curSize + reserve
    -- using ~*1.5 via bitshifts might be better?
    roundUpPower2 c
      | c <= target = roundUpPower2 (c * 2)
      | otherwise = c
append :: (Capacity (v (PrimState m) a), PrimMonad m, V.MVector v a) => a -> Grow v (PrimState m) a -> m (Grow v (PrimState m) a)
append a m = do
    m <- unsafeGrowCap 1 m
    V.write m (V.length m - 1) a
    pure m

newtype Source a = Source a
appendVec :: (V.MVector v a, PrimMonad m, Capacity (v (PrimState m) a)) => Source (Grow v (PrimState m) a) -> Grow v (PrimState m) a -> m (Grow v (PrimState m) a)
appendVec (Source r) l = do
    let lLen = V.length l
        rLen = V.length r
        totalLen = lLen + rLen
    Grow l <- ensureCap rLen l
    let l' = V.unsafeSlice lLen totalLen l
    V.unsafeMove l' (unGrow r)
    pure $ Grow $ V.unsafeSlice 0 totalLen l

freeze :: (PrimMonad m, VN.Vector v a) => Grow (VN.Mutable v) (PrimState m) a -> m (v a)
freeze (Grow v) = VN.freeze v

fromList :: (PrimMonad f, VN.Vector v a) => [a] -> f (Grow (VN.Mutable v) (PrimState f) a)
fromList ls = fmap Grow $ VN.thaw $ VN.fromList ls
instance (PrimMonad m, s~PrimState m) => EachM m (Grow IB.MVector s a) where
  eachM f (Grow t) = eachM f t

type MonadGrow r m a = (ValidateIdx (r (PrimState m) a), IxM m (r (PrimState m) a), Index (r (PrimState m) a) ~ Int, IxValue (r (PrimState m) a) ~ a, MonadState (Grow r (PrimState m) a) m, PrimMonad m, V.MVector r a)
dedup :: (Eq a, MonadGrow r m a) => m ()
dedup = do
    l <- gets (V.length . unGrow)
    when (l >= 1) $ do
        s0 <- useP (ixM 0)
        go 0 s0 1 l
  where
    go :: (Eq a, MonadGrow r m a) => Int -> a -> Int -> Int -> m ()
    go frontier frontierVal candidate cap
      | candidate == cap = id %- capGrowable frontier
      | otherwise = do
        candidateVal <- useP (ixM candidate)
        if frontierVal == candidateVal
        then go frontier frontierVal (candidate+1) cap
        else do
          let frontier' = frontier+1
          mut (ixM frontier') .- candidateVal
          go (frontier+1) candidateVal (candidate+1) cap

capGrowable :: V.MVector v a => Int -> Grow v s a -> Grow v s a
capGrowable i (Grow v) = Grow $ V.unsafeSlice 0 (i+1) v

length :: V.MVector v a => Grow v s a -> Int
length (Grow v)= V.length v
clearGrowableVec :: V.MVector v a => Grow v s a -> Grow v s a
clearGrowableVec (Grow v) = Grow $ V.unsafeSlice 0 0 v

new :: (PrimMonad m, V.MVector v a) => Int -> m (Grow v (PrimState m) a)
new i = do
   v0 <- V.new i
   pure $ Grow $ V.unsafeSlice 0 0 v0

unsafeGrowCap :: (Capacity (v (PrimState m) a), PrimMonad m, V.MVector v a) => Int -> Grow v (PrimState m) a -> m (Grow v (PrimState m) a)
unsafeGrowCap i v = do
  v <- ensureCap i v
  pure $ V.unsafeSlice 0 (V.length v + i) v

instance V.MVector v a => V.MVector (Grow v) a where
  basicLength = coerceF V.basicLength
  basicUnsafeSlice = error "slicing isn't supported for growable vectors"
  basicOverlaps = coerceF V.basicOverlaps
  basicUnsafeNew i = coerceF <$> V.basicUnsafeNew i
  basicInitialize = fmap coerceF .  V.basicInitialize
  basicUnsafeReplicate a b = coerceF <$>  V.basicUnsafeReplicate a b
  basicUnsafeRead v i = V.basicUnsafeRead (unGrow v) i
  basicUnsafeWrite v i x = V.basicUnsafeWrite (unGrow v) i x
  basicClear v = V.basicClear (unGrow v)
  basicSet v a = V.basicSet (unGrow v) a
  basicUnsafeCopy l r = V.basicUnsafeCopy (unGrow l) (unGrow r)
  basicUnsafeMove l r = V.basicUnsafeMove (unGrow l) (unGrow r)
  basicUnsafeGrow l i = coerce <$> V.basicUnsafeGrow (unGrow l) i

-- prop> testDedup
-- +++ OK, passed 100 tests.
-- prop> testQuickSort
-- +++ OK, passed 100 tests.
-- prop> testAppendVec
-- +++ OK, passed 100 tests.

testDedup :: [Int] -> Bool
testDedup ls = unsafePerformIO $ do
    v <- fromList ls
    v <- execStateT dedup v
    o <- freeze v
    pure $ fmap head (List.group ls) == IB.toList o

testQuickSort :: [Int] -> Bool
testQuickSort ls0 = unsafePerformIO $ do
    v <- IB.thaw $ IB.fromList ls0
    v <- execStateT quickSort v
    o <- IB.freeze v
    pure $ IB.toList o == List.sort ls0

testAppendVec :: [Int] -> [Int] -> Bool
testAppendVec l0 r0 = unsafePerformIO $ do
    l <- fromList l0
    r <- fromList r0
    l <- appendVec (Source l) r
    o <- freeze l
    pure $ IB.toList o == l0 <> r0

