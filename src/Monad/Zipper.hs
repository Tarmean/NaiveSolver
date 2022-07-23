{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Monad.Zipper where

import Data.Kind (Type)
import Control.Monad.State
import Control.Monad.RWS
import Control.Applicative
import Control.Monad.Writer
import Control.Monad.Reader (ReaderT)
import Monad.StateT2 (StateT2)
import Control.Zipper
import qualified Control.Zipper.Internal as ZI
import Control.Lens
import Control.Monad.Morph (MFunctor(..))
import GHC.Stack (HasCallStack)



runZipperT :: ZipperT zip m a -> zip -> m (a, zip)
runZipperT (ZipperT m) o = runStateT m o
-- runZipperT :: Monad m => o -> ZipperT (Top :>> o) m a -> m (a, Top :>> o)
-- runZipperT o (ZipperT m) = runStateT m (zipper o)

evalZipperT :: Monad m => (o -> r) -> o -> ZipperT (Top :>> o) m a -> m a
evalZipperT f o (ZipperT m) = evalStateT m (zipper o)
extractZipperT :: (Monad m) => (o -> r) -> o -> ZipperT (Top :>> o) m a -> m o
extractZipperT k o (ZipperT m) = do
    z <- execStateT m (zipper o)
    pure $ rezips z
-- eachChild:: MonadZipper o m => m () -> m Any
-- eachChild m = execWriterT $ do
--     forM_ [minBound..maxBound] $ \c -> do
--         lift (stepBool c) >>= \case
--             True -> tell (Any True) *> lift m <* lift up
--             False -> return ()
-- postOrder :: MonadZipper o m => m () -> m ()
-- postOrder m = do
--     _ <- eachChild (postOrder m)
--     m

-- eachLeaf :: MonadZipper o m => m () -> m ()
-- eachLeaf m = do
--     o <- eachChild (eachLeaf m)
--     case o of
--         Any True -> pure ()
--         _ -> m

cursors :: MonadZipper a f => (a -> b) -> f b
cursors f = fmap f cursor
onlyIf :: MonadZipper o m => (o -> Bool) -> m () -> m ()
onlyIf p m = do
    o <- cursor
    when (p o) m

type family RecZipper m where
    RecZipper (Zipper h i o) = Zipper (Zipper h i o) i o
type family RecMonad (m :: Type -> Type) :: Type -> Type
type instance RecMonad (ZipperT zip m) = ZipperT (RecZipper zip) m

type family TopZip a where
    TopZip (SomeZipper a o) = Zipped a o
    TopZip (Zipper a _ b) = Zipped a b
data SomeZipper r o where
    SomeZipper :: (Zipped h o ~ Zipped r o, Zipping h o) => ZipCount r (Zipper h Int o) o -> Zipper h Int o -> SomeZipper r o
data ZipCount r h o where 
    ZNil :: Zipping a o => ZipCount (Zipper a Int o) (Zipper a Int o) o
    ZSucc :: (Zipping h' o, h ~ Zipper h' Int o) => ZipCount r h' o -> ZipCount r h o
type instance Zipped (SomeZipper r o) a = Zipped r a
class ReZipping h where
    rezips ::  h -> TopZip h
instance Zipping t a => ReZipping (Zipper t i a) where
    rezips = rezip
instance (zip ~ (Zipper p i o), Zipping p o) => ReZipping (SomeZipper zip o) where
    rezips sz = rezip (toTop sz)

class (RecView o n) => HasRec o m n | m -> n, m -> o, n -> o where
    recursive :: n a -> m a
    default recursive :: (MFunctor t, m ~ t w, HasRec o w v, n ~ t v) => n a -> m a
    recursive = hoist recursive
instance HasRec o m n => HasRec o (StateT s m) (StateT s n)
instance (Monoid s, HasRec o m n) => HasRec o (WriterT s m) (WriterT s n)
instance RecView o n => RecView o (StateT s n)
instance (Monoid s, RecView o n) => RecView o (WriterT s n)

instance (Zipping h o, Monad m) => HasRec o (ZipperT (Zipper h Int o) m) (ZipperT (SomeZipper (Zipper h Int o) o) m) where
    recursive m = ZipperT $ do
        z <- get
        let x = SomeZipper ZNil z
        (a, z') <- lift $ runZipperT m x
        put (toTop z')
        pure a

toTop :: SomeZipper r o -> r
toTop (SomeZipper x0 y0) = go x0 y0
  where 
    go :: ZipCount r h o -> h -> r
    go zc z = case zc of
       ZNil -> z
       ZSucc (ZSucc zc') -> go (ZSucc zc') (upward z)-- (upward z)
       ZSucc ZNil -> upward z 

-- instance Mo
    

class MonadZipper o m => RecView o m where
    down :: Lens' o o -> m ()
    default down :: (m ~ t n, MonadTrans t, RecView o n) => Lens' o o -> m ()
    down l = lift (down l)
    layerDownBool :: Traversal' o o -> m Bool
    default layerDownBool :: (m ~ t n, MonadTrans t, RecView o n) => Traversal' o o -> m Bool
    layerDownBool l = lift (layerDownBool l)
    upBool :: m Bool
    default upBool :: (m ~ t n, MonadTrans t, RecView o n) => m Bool
    upBool = lift upBool
instance (Monad m) => RecView o (ZipperT (SomeZipper h o) m) where
    down l = ZipperT $ do
        SomeZipper zc z <- get
        put $ SomeZipper (ZSucc zc) (z & downward l)
    layerDownBool l = ZipperT $ do
        SomeZipper zc z <- get
        case z & within l of
          Nothing -> pure False
          Just t -> do
            put $ SomeZipper (ZSucc zc) t
            pure True
    upBool = ZipperT $ do
        SomeZipper zc z <- get
        case zc of
           ZNil -> pure False
           ZSucc ZNil -> do
               put $ SomeZipper ZNil (upward z)
               pure True
           ZSucc (ZSucc zc') -> do
               put $ SomeZipper (ZSucc zc') (upward z)
               pure True

unsafeUp :: HasCallStack => (RecView o m) => m ()
unsafeUp = upBool >>= \case
   True -> pure ()
   False -> error "unsafe up"
up :: (Alternative m, RecView o m) => m ()
up = upBool >>= \case
   True -> pure ()
   False -> empty
block :: (RecView o m) => Traversal' o o -> m () -> m ()
block p tr = layerDownBool p >>= \case
   True -> tr *> unsafeUp
   False -> pure ()
layerDown :: (Alternative m, RecView o m) => Traversal' o o -> m ()
layerDown p = layerDownBool p >>= \case
   True -> pure ()
   False -> empty

class (MonadZipper o m, MonadZipper i n) => HasView m n o i idxI | m idxI i -> n, n -> m, n -> idxI where
    idownwardM :: IndexedLens' idxI o i -> n a -> m a
    iwithinM :: Monoid t => IndexedTraversal' idxI o i -> n t -> m t
instance (zip2~ (Zipper zip idxI i), Ord idxI, Ord idxO, Monad m, zip ~ Zipper h idxO o) => HasView (ZipperT zip m) (ZipperT zip2  m) o i idxI where
    idownwardM l n = do
        s <- ZipperT get
        let s' = idownward l s
        (a, s'') <- lift (runZipperT n s')
        ZipperT $ put (upward s'')
        pure a
    iwithinM l n = do
        s <- ZipperT get
        let ms' = iwithin l s
        case ms' of
          Just s' -> do
            (a, s'') <- lift (runZipperT n s')
            ZipperT $ put (upward s'')
            pure a
          Nothing -> pure mempty



class MonadZipper o m => MonadOut o r m | m -> r, m -> o where
   getOut :: m r
   default getOut :: (m ~ t n, MonadTrans t, Monad (t n), MonadOut o r n) => m r
   getOut = lift getOut
   -- default readCursor :: (m ~ t n, MonadTrans t, Monad (t n), MonadOut o r n) => m r
   withZipper' :: (forall z i. r ~ Zipped z o => Zipper z i o -> (x, Zipper z i o)) -> m x
   default withZipper' :: (m ~ t n, MonadTrans t, Monad (t n), MonadOut o r n) => (forall z i. r ~ Zipped z o => Zipper z i o -> (x, Zipper z i o)) -> m x
   withZipper' f = lift (withZipper' f)
instance MonadOut o r m => MonadOut o r (StateT s m)
instance (Monoid s, MonadOut o r m) => MonadOut o r (WriterT s m)
instance (zip ~  Zipper h i o, MonadZipper o (ZipperT zip m), ReZipping zip, Monad m, r ~ Zipped h o) => MonadOut o r (ZipperT (Zipper h i o) m) where
   getOut = ZipperT (gets (rezips))
   withZipper' f = ZipperT $ do
       s <- get
       let (x,s') = f s
       put s'
       pure x
instance (Monad m, TopZip (SomeZipper h o) ~ r, ReZipping (SomeZipper h o)) => MonadOut o r (ZipperT (SomeZipper h o) m) where
   getOut = ZipperT (gets rezips)
   withZipper' f = ZipperT $ do
       SomeZipper z s <- get
       let (x,s') = f s
       put (SomeZipper z s')
       pure x

-- data family Mark t :: Type
class (Monad m) => MonadZipper o m | m -> o where
   cursor :: m o
   default cursor :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m o
   cursor = lift cursor

   stepBool :: (o -> Maybe o) -> m Bool
   default stepBool :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => (o -> Maybe o) -> m Bool
   stepBool = lift . stepBool

   setCursor :: o -> m ()
   default setCursor :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => o -> m ()
   setCursor = lift . setCursor

   withZipper :: MonadZipper o m => (forall h i. Zipper h i o -> (x, Zipper h i o)) -> m x
   default withZipper :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => (forall h i. Zipper h i o -> (x, Zipper h i o)) -> m x
   withZipper f = lift (withZipper f)

pullBool :: (MonadZipper o m) => (forall h i. Zipper h i o -> Maybe (Zipper h i o)) -> m Bool
pullBool f = do
   b <- withZipper (\x -> case f x of
        Nothing -> (False, x)
        Just x' -> (True, x'))
   pure b
pullIf :: (MonadZipper o m) => (forall h i. Zipper h i o -> Maybe (Zipper h i o)) -> m a -> m a -> m a
pullIf f m1 m2 = do
   b <- pullBool f
   if b then m1 else m2
nextTooth :: MonadZipper o m => (forall h i. Zipper h i o -> Maybe (Zipper h i o)) -> m () -> m ()
nextTooth f m = pullIf f m (pure ())
pull :: (MonadZipper o m, Alternative m) => (forall h i. Zipper h i o -> Maybe (Zipper h i o)) -> m ()
pull l = pullIf l (pure ()) empty
left :: (MonadZipper o m, Alternative m) => m ()
left = pull leftward
right :: (MonadZipper o m, Alternative m) => m ()
right = pull rightward

   -- mapZipper :: MonadZipper o m => (forall h i. Zipper h i o -> Zipper h i o) -> m ()
   -- upBool :: m Bool
   -- default upBool :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m Bool
   -- upBool = lift upBool
   -- remember :: m ()
   -- default remember :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m ()
   -- remember = lift remember
   -- recall :: m ()
   -- default recall :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m ()
   -- recall = lift recall

instance (Monoid r, MonadZipper o m) => MonadZipper o (WriterT r m)
instance (MonadZipper o m) => MonadZipper o (StateT r m)
instance (MonadZipper o m) => MonadZipper o (ReaderT r m)
instance (MonadZipper o m) => MonadZipper o (StateT2 r m)

newtype ZipperT zip m a = ZipperT { unZipperT :: StateT zip m a }
  deriving (Alternative, MonadPlus, Applicative, Functor, Monad, MonadReader r, MonadWriter w, MonadFail)
instance MonadTrans (ZipperT zip) where
   lift m = ZipperT (lift m)


instance (MonadState s m) => MonadState s (ZipperT zip m) where
   get = lift get
   put = lift . put

type family ZipCursor (zip :: Type) :: Type where
    ZipCursor (Zipper _ _ a) = a

instance (Monad m) => MonadZipper a (ZipperT (Zipper h i a)  m) where
    cursor = ZipperT (use focus)
    setCursor s = ZipperT $ focus .= s
    -- remember = ZipperT $ modify (second zMark)
    -- recall = ZipperT $ modify (second zRet)
    stepBool p = ZipperT $ do
       s <- use focus
       case p s of
          Nothing -> pure False
          Just s' -> True <$ (focus .= s')
    withZipper f = do
        s <- ZipperT get
        let (o, s') = f s
        ZipperT (put s')
        pure o
instance (Monad m) => MonadZipper a (ZipperT (SomeZipper r a) m) where
    cursor = ZipperT $ do
      SomeZipper _ z <- get
      pure (z ^. focus)
    setCursor s = ZipperT $ do
        SomeZipper c  z <- get
        put $ SomeZipper c (z & focus .~ s)
    stepBool p = do
       s <- cursor
       case p s of
          Nothing -> pure False
          Just s' -> True <$ setCursor s'
    withZipper f = do
        SomeZipper c s <- ZipperT get
        let (o, s') = f s
        ZipperT (put $ SomeZipper c s')
        pure o

readZipper :: MonadZipper o m => (forall h i. Zipper h i o -> x) -> m x
readZipper f = withZipper (\s -> (f s, s))
readZipper' :: MonadOut o r m => (forall h i. r ~ Zipped h o => Zipper h i o -> x) -> m x
readZipper' f = withZipper' (\s -> (f s, s))
mapZipper :: MonadZipper o m => (forall i h. Zipper h i o -> Zipper h i o) -> m ()
mapZipper f = withZipper (\x -> ((), f x))
    -- withZipper f = ZipperT $ do
    -- setZipper = ZipperT . put
mapNeighborhood :: forall o m. MonadZipper o m => (o -> o) -> m ()
mapNeighborhood f = mapZipper (mapLevel f)
  where
mapLevel :: forall o h i. (o -> o) -> Zipper h i o -> (Zipper h i o)
mapLevel f z0 = go (leftmost z0)
 where
  pos = tooth z0
  go :: Zipper h i o -> (Zipper h i o)
  go z = case rightward z' of
     Just z'' -> go z''
     Nothing -> tugTo pos z'
     where z' = z & focus %~ f
tryBool :: (Alternative m, Monad m) => m Bool -> m ()
tryBool m = m >>= \case
    True -> pure ()
    False -> empty
