{-# LANGUAGE TypeFamilies #-}
module Data.Mutable.QuickSort where
import Data.Mutable.Indexing
import Control.Lens
import qualified Data.Vector.Generic.Mutable as V
import Control.Monad.State
import Control.Monad.Primitive
import Data.Mutable.Lens

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
  mut (ixM l) .- tr
  mut (ixM r) .- tl
