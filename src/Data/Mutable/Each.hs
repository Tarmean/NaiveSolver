{-# LANGUAGE TypeFamilies #-}
module Data.Mutable.Each where
import Data.Mutable.Lens
import Control.Lens
import Control.Monad.Primitive
import qualified Data.Vector as IB
import qualified Data.Vector.Generic.Mutable as V
import Data.Hashable
import Data.Mutable.Indexing ()
import Data.Functor.Compose
import Control.Applicative
import qualified Data.Vector.Hashtables as HT

class EachM m a where
   eachM :: LValTraversal m a (IxValue a)
instance (PrimMonad m, s~PrimState m) => EachM m (IB.MVector s a) where
  eachM f s = Compose $ do
    let
      step i = do
          o <- V.read s i
          fo <- getCompose $ f o
          traverse (V.write s i) fo
    foldl1 (liftA2 $ liftA2 (<>))  $ fmap step [0..V.length s-1]
instance (V.MVector ks k, V.MVector vs v, Hashable k, Eq k, PrimMonad m, s~PrimState m) => EachM m (HT.Dictionary s ks k vs v) where
  eachM f s = Compose $ do

    let
      step (k, v) = do
          fo <- getCompose $ f v
          traverse (HT.insert s k) fo
    ls <- HT.toList s
    foldl1 (liftA2 $ liftA2 (<>))  $ fmap step ls
