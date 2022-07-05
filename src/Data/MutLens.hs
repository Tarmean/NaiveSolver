{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DefaultSignatures #-}
module Data.MutLens where
-- import Control.Lens
import Control.Monad.State
import Data.Functor.Compose
import Control.Monad.Primitive as P
import qualified Data.Vector.Generic.Mutable as V
import qualified Data.Vector.Unboxed.Mutable as IU
import qualified Data.Vector as IB
import Data.Coerce (coerce, Coercible)
import Control.Monad.ST ( ST )
import Data.Hashable (Hashable)
import Data.Primitive (sizeofMutableByteArray, sizeOf)
import qualified Data.Vector.Primitive.Mutable as IP
import GHC.TypeLits ( KnownNat, Nat, natVal )
import Data.Proxy (Proxy (Proxy))
import Control.Applicative (Applicative(liftA2))
import Data.Functor.Const
import Data.Kind (Type)
import Data.Functor.Identity (Identity (..))
import qualified Data.Primitive.PrimArray as A
-- import qualified Data.Primitive.PrimArray.Utils as A
import Control.Lens as L hiding ((<~))
import qualified Data.Vector.Storable.Mutable as IS
import qualified Data.Vector.Internal.Check as V
import qualified Data.Primitive.MutVar as MV
import Data.Monoid
import qualified Data.HashTable.ST.Basic as HT
import qualified Data.HashTable.Class as HTC
import Control.Monad.Cont
-- import qualified Data.Vector.Unboxed as V
-- import qualified Data.Vector.Unboxed.Mutable as V

instance (MonadIO m, Applicative f, Monad (Compose m f)) => MonadIO (Compose m f) where
    liftIO m = Compose $ pure <$> liftIO m


-- breakLens :: ((a -> Cont s b) -> s -> Cont s t) -> s -> (a, b -> t)
-- breakLens f s = undefined (f _ s)
--   where
--     foo :: (a -> Cont s b)

newtype C m n a = C (m (n a))

type MLensLike' f m s a = Traversable f => (a -> Compose m f a) -> s -> Compose m f s
type MLensLike f m s t a b = Traversable f => (a -> Compose m f b) -> s -> Compose m f t
type MLens m s a = forall f. Traversable f => (a -> Compose m f a) -> s -> Compose m f s
type LValLens m s a = forall f. Traversable f => (a -> Compose m f a) -> s -> Compose m f ()
type LValLensLike f m s a = Traversable f => (a -> Compose m f a) -> s -> Compose m f ()
type LValTraversal m s a = forall f. (Monoid (f ()), Applicative f, Traversable f) => (a -> Compose m f a) -> s -> Compose m f ()
type LValTraversalLike f m s a = (Applicative f, Traversable f) => (a -> Compose m f a) -> s -> Compose m f ()

overMS :: (MonadState s m, Functor m) => MLensLike' (Const x) m s a -> (a -> m x) -> m  x
overMS f k = do
  s <- get
  fmap getConst $ getCompose $ f (Compose . fmap Const . k) s


data With s a = With s a
  deriving (Functor, Traversable, Foldable)
instance Monoid s => Applicative (With s) where
  pure = With mempty
  With l f <*> With r a = With (l <> r) (f a)

swapRefOfM :: (MonadState s m, Functor m) => MLensLike' (With a) m s a -> m a -> m a
swapRefOfM f k = do
  s <- get
  With x s' <- getCompose $ f (\old -> Compose $ With old <$> k) s
  put s'
  pure x
modifyRefOfM :: (MonadState s m, Functor m) => MLensLike' (With x) m s a -> (a -> m (a, x)) -> m  x
modifyRefOfM f k = do
  s <- get
  With x s' <- getCompose $ f (Compose . fmap (uncurry $ flip With) . k) s
  put s'
  pure x

($%%=) :: (MonadState s m, Functor m) => MLensLike' (With x) m s a -> (a -> m (a, x)) -> m x
($%%=) = modifyRefOfM

class ValidateIdx v where
  validateIdx :: Index v -> v -> Bool
class IxM m v where
  tryIxM :: Applicative m => Index v -> LValTraversal m v (IxValue v)
  default tryIxM :: (ValidateIdx v, Applicative m) => Index v -> LValTraversal m v (IxValue v)
  tryIxM = ifIdx validateIdx uncheckedIxM
  ixM :: Index v -> LValLens m v (IxValue v)
  uncheckedIxM :: Index v -> LValLens m v (IxValue v)
  uncheckedIxM = ixM
type instance Index (IS.MVector n a) = Int
type instance IxValue (IS.MVector n a) = a

ifIdx :: (Applicative m, Applicative f, Monoid (f ())) => (Index v -> v -> Bool) -> (Index v -> LValLensLike f m v (IxValue v)) ->  (Index v -> LValTraversalLike f m v (IxValue v))
ifIdx ifIdx l idx = filtered (ifIdx idx) .$ l idx

instance (IS.Storable a) => ValidateIdx (IS.MVector n a) where
    validateIdx i a = i >= 0 && i < V.length a
instance (IS.Storable a, V.MVector IS.MVector a, PrimMonad m, n ~ PrimState m) => IxM m (IS.MVector n a) where
    ixM = ixLens V.read V.write
    uncheckedIxM = ixLens V.unsafeRead V.unsafeWrite
type instance Index (IU.MVector n a) = Int
type instance IxValue (IU.MVector n a) = a
instance (V.MVector IU.MVector a) => ValidateIdx (IU.MVector n a) where
    validateIdx i a = i >= 0 && i < V.length a
instance (V.MVector IU.MVector a, PrimMonad m, n ~ PrimState m) => IxM m (IU.MVector n a) where
    ixM = ixLens V.read V.write
    uncheckedIxM = ixLens V.unsafeRead V.unsafeWrite
type instance Index (IB.MVector n a) = Int
type instance IxValue (IB.MVector n a) = a
instance ValidateIdx (IB.MVector n a) where
    validateIdx i a = i >= 0 && i < V.length a
instance (V.MVector IB.MVector a, PrimMonad m, n ~ PrimState m) => IxM m (IB.MVector n a) where
    ixM = ixLens V.read V.write
    uncheckedIxM = ixLens V.unsafeRead V.unsafeWrite
type instance Index (A.MutablePrimArray n a) = Int
type instance IxValue (A.MutablePrimArray n a) = a
type instance IxValue (A.PrimArray a) = a
type instance Index (A.PrimArray a) = Int

-- instance IP.Prim a => ValidateIdx (A.MutablePrimArray n a) where
--     validateIdx i a = i >= 0 && i < A.length a
-- instance (IP.Prim a, PrimMonad m, n ~ PrimState m) => IxM m (A.MutablePrimArray n a) where
--   ixM = ixLens A.readPrimArray A.writePrimArray
--   uncheckedIxM = ixLens A.readPrimArray A.writePrimArray
ixLens :: (Monad f, Traversable g) =>
    (v -> ix -> f a)
    -> (v -> ix -> a -> f ())
    -> ix
    -> (a -> Compose f g a)
    -> v -> Compose f g ()
ixLens read write = fid $ \i f m ->
    Compose $ do
      a <- read m i
      fa <- getCompose (f a)
      traverse (write m i) fa
  where fid = id
-- instance IP.Prim a => Ixed (A.PrimArray a) where
-- instance IP.Prim a => Ixed (A.PrimArray a) where
--   ix i f s = fmap (error "can't update") $ f $  A.indexPrimArray s i
(!) :: (Applicative m, IxM m s) => s -> Index s -> m (IxValue s)
(!) s i = viewM (uncheckedIxM i) s

(!.) :: (Ixed s) => s -> Index s -> IxValue s
(!.) s i = view (singular (ix i)) s

(<~) :: (Applicative m, IxM m s) => s -> Index s -> IxValue s -> m ()
(<~) s i a= setM (uncheckedIxM i) s (pure a)

-- The (a -> ...a) is probably fine, right? It hugely helps type inference for generic-lens
(.$) ::  (Functor f, Applicative m) => MLensLike (Const (f ())) m s t a a -> LValLensLike f m a x -> LValLensLike f m s x
(.$) l r f s = Compose $ fmap getConst $ getCompose $ l (\a -> Compose $ Const <$> getCompose (r f a)) s


nonM :: (Monad m) => m a -> MLens m (Maybe a) a
nonM m k Nothing = Just <$> Compose (getCompose . k =<< m)
nonM _ k (Just a) = Just <$> k a

previewM :: Applicative m => ((a -> Compose m (Const (First a)) b) -> s -> Compose m (Const (First a)) t)  -> s -> m (Maybe a)
previewM l s = getFirst <$> mkGetter l s (pure . First . Just)
viewM :: Applicative m => MLensLike (Const a) m s t a b -> s -> m a
viewM l s = mkGetter l s pure
viewsM :: Applicative m => MLensLike (Const o) m s t a a -> s -> (a -> m o) -> m o
viewsM = mkGetter

hasM :: Applicative m => ((a -> Compose m (Const Any) b) -> s -> Compose m (Const Any) t)  -> s -> m Bool
hasM l s = getAny <$> mkGetter l s (const $ pure (Any True))

mkGetter :: Functor m => ((a -> Compose m (Const x) b) -> s -> Compose m (Const x) t) -> s -> (a -> m x) -> m x
mkGetter l s f = fmap getConst $ getCompose $ l (Compose . fmap Const . f) s

-- | skip updating the original state when we only mutate nested lvalues
--
-- mapStateM (self $ #counters .$ ixM 1) (+1)
self :: (Functor f, Functor m) => LValLensLike f m s a -> MLensLike' f m s a
self l k s = s <$ l k s

mutateM :: MonadState s m => MLensLike' Identity m s a -> (a -> m a) -> m ()
mutateM l f = do
   s <- get
   s' <- overM l s f
   put s'
mapStateM :: MonadState s m => MLensLike' Identity m s a -> (a -> a) -> m ()
mapStateM l f = mutateM l (pure . f)


toListOfM :: (Applicative m) => MLensLike (Const [a]) m s t a a -> s -> m [a]
toListOfM = toApOfM
toApOfM ::
  (Applicative m, Applicative f) => MLensLike (Const (f a)) m s t a a -> s -> m (f a)
toApOfM f s = viewsM f s (pure . pure)

usingM :: (MonadState s m) => MLensLike (Const o) m s t a a -> (a -> m o) -> m o
usingM l f = do
  s <- get
  fmap getConst $ getCompose $ l (Compose . fmap Const . f) s
overM :: Applicative m => MLensLike Identity m s t a a -> s -> (a -> m a) -> m t
overM l s f = fmap runIdentity $ getCompose $  l (Compose . fmap Identity .  f) s

setM :: Applicative m => MLensLike Identity m s t a a -> s -> m a -> m t
setM l s a = overM l s (const a)

-- more polymorphic version of overM, often can wreak type inference
overM' :: Applicative m => MLensLike Identity m s t a b -> (a -> m b) -> s -> m t
overM' l f s = fmap runIdentity $ getCompose $ l (Compose . fmap Identity . f) s

infixr 9 .$

($%=) :: MonadState s m => MLensLike Identity m s s a b -> (a -> m b) -> m ()
($%=) l f = do
   s <- get
   s' <- overM' l f s
   put s'
($=) :: MonadState s m => MLensLike Identity m s s a b -> m b -> m ()
($=) l v = do
  l $%= const v
(?$=) :: MonadState s m => MLensLike Identity m s s a (Maybe b) -> m b -> m ()
(?$=) l v = do
  l $%= const (Just <$> v)

useM :: (MonadState s m, Functor m) => MLensLike (Const a) m s t a b -> m a
useM l = do
  s <- get
  viewM l s


infix 4 $=
infix 4 $%=
infix 4 ?$=
infix 4 $%%=

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
-- instance (SliceStride (l ': r), ValidateIdx (v s a)) => ValidateIdx (Slice v s (l ': r) a) where
--     validateIdx i a = validateIdx (i * getStride @(l ': r)) a
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




class RefM m r where
  refM :: LValLens m (r a) a
instance (PrimState m ~ s, PrimMonad m) => RefM m (MV.MutVar s) where
  refM f s = Compose $ do
    a <- MV.readMutVar s
    fo <- getCompose (f a)
    traverse (MV.writeMutVar s) fo


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
instance (Hashable k, Eq k, PrimMonad m, s~PrimState m) => EachM m (HT.HashTable s k a) where
  eachM f s = Compose $ do

    let
      step k v = do
          fo <- getCompose $ f v
          traverse (primToPrim . HT.insert s k) fo
    ls <- primToPrim $ HTC.toList s
    foldl1 (liftA2 $ liftA2 (<>))  $ fmap (uncurry step) ls
class IxM m a => AtM m a where
    atM :: Index a -> MLens m a (Maybe (IxValue a))

primST :: (PrimMonad m, PrimState m ~ s) => ST s a -> m a
primST = primToPrim

type instance Index (HT.HashTable s k a) = k
type instance IxValue (HT.HashTable s k a) = a

instance (PrimMonad m, Eq k, Hashable k, s ~ PrimState m) => IxM m (HT.HashTable s k v) where
    ixM k f s = Compose $ do
        mo <- primST $ HT.lookup s k
        case mo of
          Nothing -> error "Missing key"
          Just o -> do
            fa <- getCompose $ f o
            traverse (primST . HT.insert s k) fa
    tryIxM k f s = Compose $ do
        mo <- primST $ HT.lookup s k
        case mo of
          Nothing -> pure mempty
          Just o -> do
            fa <- getCompose $ f o
            traverse (primST . HT.insert s k) fa

-- toRefM :: LValLens m s a -> s -> m (m a, a -> m ())
-- toRefM lval s = getCompose $ lval _ s

instance (PrimMonad m, Eq k, Hashable k, s ~ PrimState m) => AtM m (HT.HashTable s k v) where
    atM k f s = Compose $ do
        mo <- primST $ HT.lookup s k
        fa <- getCompose $ f mo
        let
          cont Nothing = HT.delete s k
          cont (Just o) = HT.insert s k o
        fu <- traverse (primST . cont) fa
        pure $ s <$ fu

quickSort :: (
    Monad f,
    IxM f (v s a),
    Enum (Index (v s a)),
    Num (Index (v s a)),
    Ord (IxValue (v s a)),
    Ord (Index (v s a)),
    V.MVector v a,
    Index (v s a) ~ Int
    ) => v s a -> f ()
quickSort t = quickSort' 0 (V.length t-1) t

quickSort'
  :: (Monad f,
      IxM f t,
      Enum (Index t),
      Num (Index t),
      Ord (IxValue t),
      Ord (Index t)) => Index t -> Index t -> t -> f ()
quickSort' i j v
  | i >= j = pure ()
  | otherwise = do
      pivot <- v ! j
      let frontierL = i
      let frontierR = j-1
      n <- foldM (go pivot) frontierL [frontierL .. frontierR]
      swapM j n v
      quickSort' i (n-1) v
      quickSort' (n+1) j v
  where
    go piv l r = do
      c <- viewM (ixM r) v
      if c <= piv
      then do
        swapM l r v
        pure (l+1)
      else do
        pure l

swapM :: (Monad m, IxM m v) => Index v -> Index v -> v -> m ()
swapM l r v = do
  tl <- v ! l
  tr <- v ! r
  v <~ l $ tr
  v <~ r $ tl

