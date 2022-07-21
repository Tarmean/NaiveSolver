{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
module Monad.Zipper where

import Data.Kind (Type)
import Data.Monoid (Any(..))
import Control.Monad.State
import Control.Monad.RWS
import Control.Applicative
import GHC.Stack
import Control.Monad.Writer
import Control.Monad.Reader (ReaderT)
import Monad.StateT2 (StateT2)



data family Dir t :: Type
data Zipper o = Zipper { path :: [OrMark (ZipperStep o)], current :: o }
toRoot :: Walkable o => Zipper o -> o
toRoot (Zipper xs0 o0) = go xs0 o0
  where
    go [] a = a
    go (Mark:xs) a = go xs a
    go (NoMark x:xs) !a = go xs (zApp x a)
runZipperT :: Monad m => o -> ZipperT o m a -> m (a, Zipper o)
runZipperT o (ZipperT m) = runStateT m (Zipper [] o)
evalZipperT :: Monad m => o -> ZipperT o m a -> m a
evalZipperT o (ZipperT m) = evalStateT m (Zipper [] o)
extractZipperT :: (Walkable o, Monad m) => o -> ZipperT o m a -> m o
extractZipperT o (ZipperT m) = fmap toRoot $ execStateT m (Zipper [] o)

unCons ::  (o -> Maybe (ZipperStep o, o)) -> Zipper o -> Maybe (Zipper o)
unCons f (Zipper xs o) = case f o of
  Nothing -> Nothing
  Just (x, o') -> Just $ Zipper (NoMark x:xs) o'

eachChild :: MonadZipper o m => m () -> m Any
eachChild m = execWriterT $ do
    forM_ [minBound..maxBound] $ \c -> do
        lift (stepBool c) >>= \case
            True -> tell (Any True) *> lift m <* lift up
            False -> return ()
postOrder :: MonadZipper o m => m () -> m ()
postOrder m = do
    _ <- eachChild (postOrder m)
    m

eachLeaf :: MonadZipper o m => m () -> m ()
eachLeaf m = do
    o <- eachChild (eachLeaf m)
    case o of
        Any True -> m
        _ -> pure ()

doWhen :: MonadZipper o m => (o -> Bool) -> m () -> m ()
doWhen p m = do
    o <- cursor
    when (p o) m


-- data family Mark t :: Type
class (Walkable o, Monad m) => MonadZipper o m | m -> o where
   cursor :: m o
   default cursor :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m o
   cursor = lift cursor
   setCursor :: o -> m ()
   default setCursor :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => o -> m ()
   setCursor = lift . setCursor
   stepBool :: Dir o -> m Bool
   default stepBool :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => Dir o -> m Bool
   stepBool = lift . stepBool
   upBool :: m Bool
   default upBool :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m Bool
   upBool = lift upBool
   remember :: m ()
   default remember :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m ()
   remember = lift remember
   recall :: m ()
   default recall :: (MonadTrans t, m ~ t n, MonadZipper o n, Monad (t n)) => m ()
   recall = lift recall
instance (Monoid r, MonadZipper o m) => MonadZipper o (WriterT r m)
instance (MonadZipper o m) => MonadZipper o (StateT r m)
instance (MonadZipper o m) => MonadZipper o (ReaderT r m)
instance (MonadZipper o m) => MonadZipper o (StateT2 r m)
class (Enum (Dir o), Bounded (Dir o)) => Walkable o where
    data ZipperStep o :: Type
    zGo :: Dir o -> Zipper o -> Maybe (Zipper o)
    zApp :: ZipperStep o -> o -> o
    -- zMark :: Zipper o -> Zipper o
    -- zRet :: Zipper o -> Maybe (Zipper o)

newtype ZipperT o m a = ZipperT { unZipperT :: StateT (Zipper o) m a }
  deriving (Alternative, MonadPlus, Applicative, Functor, Monad, MonadReader r, MonadWriter w, MonadTrans, MonadFail)

data ZipperChain o r where
    ZipperNil :: ZipperChain r r
    ZipperCons :: (a -> b) -> ZipperChain b r -> ZipperChain a r

appChain :: ZipperChain a r -> a -> r
appChain ZipperNil a = a
appChain (ZipperCons f xs) a = appChain xs (f a)

instance (Walkable o, MonadState s m) => MonadState s (ZipperT o m) where
   get = lift get
   put = lift . put

instance (Walkable o, Monad m) => MonadZipper o (ZipperT o m) where
    cursor = ZipperT (gets current)
    remember = ZipperT $ modify zMark
    upBool = ZipperT $ do
       s <- get
       case path s of
         (NoMark x:xs) ->  True <$ put (Zipper xs (zApp x (current s)))
         (Mark:_) -> error "Up into mark"
         _ -> pure False
    setCursor s = ZipperT $ modify (\(Zipper m _) -> (Zipper m s))
    recall = ZipperT $ modify zRet
    stepBool p = ZipperT $ do
       s <- get
       case zGo p s of
         Nothing -> pure False
         Just s' -> do
            put s'
            pure True
tryBool :: (Alternative m, Monad m) => m Bool -> m ()
tryBool m = m >>= \case
    True -> pure ()
    False -> empty

step :: (Alternative m, MonadZipper o m) => Dir o -> m ()
step = tryBool . stepBool
up :: (MonadZipper o m) => m ()
up = forceBool upBool
-- forceUp :: (Alternative m, MonadZipper o m) => m ()
-- forceUp = forceBool upBool

forceBool :: (HasCallStack, Monad m) => m Bool -> m ()
forceBool m = do
   m >>= \case
         False -> error "failed step"
         True -> pure ()

zMark :: Zipper a -> Zipper a
zMark (Zipper ms o) = Zipper (Mark : ms) o
zRet :: Zipper a -> Zipper a
zRet (Zipper ms o) = Zipper (dropWhile notMark ms) o
  where
    notMark Mark = False
    notMark _ = True
-- newtype Mu f = Mu { unMu :: f (Mu f) }
data OrMark a = Mark | NoMark a
    deriving (Eq, Ord, Show, Functor)
    
-- instance Functor f => Walkable (Mu (OrMark f)) where
    -- zGo p (Mu (Mark a)) = Just (Mu (Mark a))

