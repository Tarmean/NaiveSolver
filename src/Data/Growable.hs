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
import Prelude hiding (length)
import Data.Mutable.Distributive (HasMonad)
import Data.Foldable (traverse_)
import Data.List (unfoldr)
import Debug.Trace (traceM)
import GHC.Stack (HasCallStack)

type instance Index (Grow v s a) = Int
type instance IxValue (Grow v s a) = a

chunksOfM :: (Applicative f, V.MVector v a) => Int -> (v s a -> f ()) -> Grow v s a -> f ()
chunksOfM w f (Grow v) = traverse_ f theChunks
  where
    theChunks = unfoldr go v
    go x
      | V.null x = Nothing
      | otherwise = Just (V.splitAt w x)

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
instance (Capacity (IU.MVector s a), Capacity (IU.MVector s b)) => Capacity (IU.MVector s (a,b)) where
    getCapacity (IU.MV_2 _ a b) =  min (getCapacity a) (getCapacity b)
instance (Capacity (IU.MVector s a), Capacity (IU.MVector s b), Capacity (IU.MVector s c)) => Capacity (IU.MVector s (a,b,c)) where
    getCapacity (IU.MV_3 _ a b c) =  min (getCapacity a) (min (getCapacity b) (getCapacity c))
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
toState :: MonadState a m => (a -> m a) -> m ()
toState f = put =<< (f =<< get)
append :: (MonadState (Grow v (PrimState m) a) m, Capacity (v (PrimState m) a), PrimMonad m, V.MVector v a) => a -> m ()
append a = toState $ \m -> do
    m <- unsafeGrowCap 1 m
    V.write m (V.length m - 1) a
    pure m
appendSlice :: forall m v a. (MonadState (Grow (VN.Mutable v) (PrimState m) a) m, PrimMonad m, VN.Vector v a, Capacity (VN.Mutable v (PrimState m) a), Show (v a)) => v a -> m ()
appendSlice v = do
  v' <- VN.unsafeThaw v
  appendVec v'

getSlice :: ( PrimMonad m, V.MVector (VN.Mutable v) a, VN.Vector v a) => Int -> Int -> Grow (VN.Mutable v) (PrimState m) a -> m (v a)
getSlice l r (Grow v) = VN.freeze (V.slice l r v)

newtype Source a = Source a
appendVec :: (Show (v a), VN.Vector v a, MonadState (Grow (VN.Mutable v) (PrimState m) a) m, V.MVector (VN.Mutable v) a, PrimMonad m, Capacity (VN.Mutable v (PrimState m) a)) => VN.Mutable v (PrimState m) a -> m ()
appendVec r = do
    l <- get
    let lLen = V.length l
        rLen = V.length r
        totalLen = lLen + rLen
    Grow l <- ensureCap totalLen l
    let l' = V.unsafeSlice lLen rLen l
    V.copy l' r
    put $ Grow $ V.unsafeSlice 0 totalLen l


pop :: (PrimMonad m, MonadState (Grow (VN.Mutable v) (PrimState m) a) m, V.MVector (VN.Mutable v) a, VN.Vector v a, Capacity (VN.Mutable v (PrimState m) a)) => Int -> m (Maybe (v a))
pop i = do
    l <- gets length
    if l < i
    then pure Nothing
    else do
        sl <- usingP id (getSlice (l-1) i)
        id &-> pure . capGrowable (l-i)
        pure $ Just sl

freeze :: (PrimMonad m, VN.Vector v a) => Grow (VN.Mutable v) (PrimState m) a -> m (v a)
freeze (Grow v) = VN.freeze v

unsafeFreeze :: (PrimMonad m, VN.Vector v a) => Grow (VN.Mutable v) (PrimState m) a -> m (v a)
unsafeFreeze (Grow v) = VN.freeze v

fromList :: (PrimMonad f, VN.Vector v a) => [a] -> f (Grow (VN.Mutable v) (PrimState f) a)
fromList ls = fmap Grow $ VN.thaw $ VN.fromList ls
instance (PrimMonad m, s~PrimState m) => EachP m (Grow IB.MVector s a) where
  eachP f (Grow t) = eachP f t

type MonadGrow r m a = (ValidateIdx (r (PrimState m) a), IxM m (r (PrimState m) a), Index (r (PrimState m) a) ~ Int, IxValue (r (PrimState m) a) ~ a, MonadState (Grow r (PrimState m) a) m, PrimMonad m, V.MVector r a)
dedup :: (Eq a, MonadGrow r m a, Capacity (r (PrimState m) a)) => m ()
dedup = do
    l <- gets (V.length . unGrow)
    when (l >= 1) $ do
        s0 <- useP (ixM 0)
        go 0 s0 1 l
  where
    go :: (Eq a, MonadGrow r m a, Capacity (r (PrimState m) a)) => Int -> a -> Int -> Int -> m ()
    go frontier frontierVal candidate cap
      | candidate == cap = id &-> pure . capGrowable frontier
      | otherwise = do
        candidateVal <- useP (ixM candidate)
        if frontierVal == candidateVal
        then go frontier frontierVal (candidate+1) cap
        else do
          let frontier' = frontier+1
          mut (ixM frontier') &= candidateVal
          go (frontier+1) candidateVal (candidate+1) cap

capGrowable :: (HasCallStack, V.MVector v a, Capacity (v s a)) => Int -> Grow v s a -> Grow v s a
capGrowable i (Grow v) 
  | i+1 >= getCapacity v = error "Invalid capGrowable"
  | otherwise = Grow $ V.unsafeSlice 0 (i+1) v

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
-- +++ OK, passed 100 tests.
-- +++ OK, passed 100 tests.
-- <BLANKLINE>
-- GHC.ByteCode.Linker.lookupCE
-- During interactive linking, GHCi couldn't find the following symbol:
--   interactive_Ghci1_propEvaluation_closure
-- This may be due to you not asking GHCi to load extra object files,
-- archives or DLLs needed by your current session.  Restart GHCi, specifying
-- the missing library using the -L/path/to/object/dir and -lmissinglibname
-- flags, or simply by naming the relevant files on the GHCi command line.
-- Alternatively, this link failure might indicate a bug in GHCi.
-- If you suspect the latter, please report this as a GHC bug:
--   https://www.haskell.org/ghc/reportabug
-- +++ OK, passed 100 tests.
-- <BLANKLINE>
-- GHC.ByteCode.Linker.lookupCE
-- During interactive linking, GHCi couldn't find the following symbol:
--   interactive_Ghci1_propEvaluation_closure
-- This may be due to you not asking GHCi to load extra object files,
-- archives or DLLs needed by your current session.  Restart GHCi, specifying
-- the missing library using the -L/path/to/object/dir and -lmissinglibname
-- flags, or simply by naming the relevant files on the GHCi command line.
-- Alternatively, this link failure might indicate a bug in GHCi.
-- If you suspect the latter, please report this as a GHC bug:
--   https://www.haskell.org/ghc/reportabug
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
    l <- execStateT (appendSlice (VN.fromList r0)) l
    o <- freeze l
    pure $ IB.toList o == l0 <> r0

-- foo i = zoom (fmap getCompose $ mut (ixM i)) get
