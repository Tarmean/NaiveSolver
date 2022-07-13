{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Mutable.QuickSort where
import Data.Mutable.Indexing
import Control.Lens
import qualified Data.Vector.Generic.Mutable as V
import qualified Data.Vector.Generic as VI
import Control.Monad.State
import Control.Monad.Primitive
import Data.Mutable.Lens
import Data.Mutable.Distributive (JoinL)
import Control.Monad.ST (runST, ST)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.List as L
import qualified Data.Vector.Unboxed as VU

mergeProp :: [Int] -> [Int] -> Bool
mergeProp l r = VI.toList merged == map head (L.group (L.sort (l <> r)))
  where
    lz = VU.fromList $ L.sort l
    rz = VU.fromList $ L.sort r
    merged = mergeSortedDedup lz rz
mergeSortedDedup :: forall a v. (Show a, Show (v a), Ord a, VI.Vector v a) => v a -> v a -> v a
mergeSortedDedup l r = runST $ do
  v <- V.new total
  v' <- goBoth v 0 0 0
  v'' <- dedup v'
  VI.unsafeFreeze v''
 where
   total = VI.length l + VI.length r
   goBoth :: (Show a, Ord a, V.MVector (G.Mutable v) a) => G.Mutable v s a -> Int -> Int -> Int -> ST s (G.Mutable v s a)
   goBoth sink idxout idxl idxr
     | VI.length l == idxl = done sink idxout idxr r
     | VI.length r == idxr = done sink idxout idxl l
     | otherwise = go sink idxout (idxl+1) (idxr+1) (l VI.! idxl) (r VI.! idxr)

   done :: (Show a, Ord a, V.MVector (G.Mutable v) a) => G.Mutable v s a -> Int -> Int -> v a -> ST s (G.Mutable v s a)
   done sink idxout idx v 
     | leftover == 0 = pure $ V.take idxout sink
     | otherwise = do
       t <- G.unsafeThaw v
       V.copy (V.slice idxout leftover sink) (V.drop idx t)
       pure (V.take (idxout + leftover) sink)
      where leftover = VI.length v - idx
   goLeft :: (Show a, Ord a, V.MVector (G.Mutable v) a) => G.Mutable v s a -> Int -> Int -> Int -> a -> ST s (G.Mutable v s a)
   goLeft sink idxout idxl idxr b
      | VI.length l == idxl = do
        V.write sink idxout b
        done sink (idxout+1) idxr r
      | otherwise = go sink idxout (idxl+1) idxr (l VI.! idxl) b
   goRight :: (Show a, Ord a, V.MVector (G.Mutable v) a) => G.Mutable v s a -> Int -> Int -> Int -> a -> ST s (G.Mutable v s a)
   goRight sink idxout idxl idxr a
        | VI.length r == idxr = do
          V.write sink idxout a
          done sink (idxout+1) idxl l
        | otherwise = go sink idxout idxl (idxr+1) a (r VI.! idxr)

      
   go :: (Show a, Ord a, V.MVector (G.Mutable v) a) => G.Mutable v s a -> Int -> Int -> Int -> a -> a -> ST s (G.Mutable v s a)
   go sink idxout idxl idxr a b = case compare a b of
       EQ -> do
         V.write sink idxout a
         goBoth sink (idxout+1) idxl idxr
       LT -> do
         V.write sink idxout a
         goLeft sink (idxout +1) idxl idxr b
       GT -> do
         V.write sink idxout b
         goRight sink (idxout +1) idxl idxr a

dedup :: forall a v s m. (Show a, Ord a, V.MVector v a, s ~ PrimState m, PrimMonad m) => v s a -> m (v s a)
dedup v 
  | V.length v == 0 = pure v
  | otherwise = do
     x0 <- V.unsafeRead v 0
     go0 x0 1 1
  where
    go0 :: (Ord a, V.MVector v a, s ~ PrimState m, PrimMonad m) => a -> Int -> Int -> m (v s a)
    go0 x l r
      | r == V.length v = pure $ V.take l v
      | otherwise = do
        x' <- V.unsafeRead v r
        if x' > x
        then do
            V.unsafeWrite v l x'
            go0 x' (l+1) (r+1)
        else go0 x' l (r+1)
      


-- if we make a generic length function we can get rid of the vector constraints
quickSort :: (
    MonadState t f,
    IxM f t,
    V.MVector v a,
    t ~ v (PrimState f) a,
    Ord (IxValue t),
    Index t ~ Int
    ) => f ()
quickSort = do
    len <- gets V.length
    quickSort' 0 (len-1)

quickSort'
  :: (MonadState t f,
      IxM f t, Index t ~ Int, Ord (IxValue t)) => Index t -> Index t -> f ()
quickSort' i j
  | i >= j = pure ()
  | otherwise = do
      pivot <- useP (ixM j)
      let frontierL = i
      let frontierR = j-1
      n <- foldM (go pivot) frontierL [frontierL .. frontierR]
      swapM j n
      quickSort' i (n-1)
      quickSort' (n+1) j
  where
    go piv l r = do
      c <- useP (ixM r)
      if c <= piv
      then do
        swapM l r
        pure (l+1)
      else do
        pure l

swapM :: (MonadState v m, IxM m v) => Index v -> Index v -> m ()
swapM l r = do
  tl <- useP (ixM l)
  tr <- useP (ixM r)
  mut (ixM l) &= tr
  mut (ixM r) &= tl
