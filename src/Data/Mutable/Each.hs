{-# LANGUAGE TypeFamilies #-}
module Data.Mutable.Each where
import Data.Mutable.Lens
import Control.Lens
import Control.Monad.Primitive
import qualified Data.Vector as IB
import qualified Data.Vector.Generic.Mutable as V
import Data.Hashable
import Data.Mutable.Indexing ()
import qualified Data.Vector.Hashtables as HT
import Data.Mutable.Distributive
import qualified Data.Vector.Generic as GV
import Data.List (unfoldr)
import qualified Data.Vector.Generic.Mutable as GVM
import Data.Foldable (traverse_)
import qualified Data.Vector.Unboxed.Mutable as VU
import qualified Data.Vector.Storable.Mutable as VS

class EachP m a where
   eachP :: (Applicative f, HasMonad m f) => LValLensLike f a (IxValue a)
vecEachP :: (HasMonad m f, Monad m, GVM.MVector v a1, Monoid a2, Applicative f, s ~ (PrimState m)) => (v s a1 -> Int -> m t) -> (v s a1 -> Int -> a3 -> m a2) -> (t -> f a3) -> v s a1 -> f a2
vecEachP doRead doWrite f s = mjoin $ do
    let
      step i = do
          o <- doRead s i
          pure $ (doWrite s i) <$> (f o)
    fls <- traverse step [0..V.length s-1]
    pure $ flattenNested fls
instance (PrimMonad m, s~PrimState m) => EachP m (IB.MVector s a) where
  eachP = vecEachP V.read V.write
instance (V.MVector VU.MVector a, PrimMonad m, s~PrimState m) => EachP m (VU.MVector s a) where
  eachP = vecEachP V.read V.write
instance (V.MVector VS.MVector a, PrimMonad m, s~PrimState m) => EachP m (VS.MVector s a) where
  eachP = vecEachP V.read V.write
instance (V.MVector ks k, V.MVector vs v, Hashable k, Eq k, PrimMonad m, s~PrimState m) => EachP m (HT.Dictionary s ks k vs v) where
  eachP f s = mjoin $ do
    ls <- HT.toList s
    let step (k, v) = fmap (HT.insert s k) (f v)
    pure $ flattenNested  $ fmap step ls



class IEachP m s where
   ieachP :: (Applicative f, HasMonad m f) => (IxValue s -> WithIndex (Index s) f (IxValue s)) -> s -> f (())
vecIEachP :: (JoinR m f, JoinL m f, Monad m, GVM.MVector v a1, Monoid a2, Applicative f) => (v s a1 -> Int -> m t) -> (v s a1 -> Int -> a3 -> m a2) -> (t -> WithIndex Int f a3) -> v s a1 -> f a2
vecIEachP doread dowrite f s = mjoin $ do
    let
      step i = do
          o <- doread s i
          pure $ (dowrite s i) <$> (giveIndex i (f o))
    fls <- traverse step [0..V.length s-1]
    pure $ flattenNested fls
instance (V.MVector ks k, V.MVector vs v, Hashable k, Eq k, PrimMonad m, s~PrimState m) => IEachP m (HT.Dictionary s ks k vs v) where
    ieachP f s = mjoin $ do
        ls <- HT.toList s
        let step (k, v) = fmap (HT.insert s k) (giveIndex k (f v))
        pure $ flattenNested  $ fmap step ls
instance (PrimMonad m, s~PrimState m) => IEachP m (IB.MVector s a) where
  ieachP = vecIEachP V.read V.write
instance (GVM.MVector VU.MVector a, PrimMonad m, s~PrimState m) => IEachP m (VU.MVector s a) where
  ieachP = vecIEachP V.read V.write
instance (GVM.MVector VS.MVector a, PrimMonad m, s~PrimState m) => IEachP m (VS.MVector s a) where
  ieachP = vecIEachP V.read V.write


chunksOf :: (Monoid s, GV.Vector v a) => Int -> (v a -> s) -> v a -> s
chunksOf w f v = getConst $ traverse step theChunks
  where
    step = Const . f
    theChunks = unfoldr go v
    go x
      | GV.null x = Nothing
      | otherwise = Just (GV.splitAt w x)

