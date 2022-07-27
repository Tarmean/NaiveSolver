{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
module ShrinkLoop where
import Monad.Graph
import Monad.Oracle
import Control.Applicative
import Monad.Zipper (RecView, MonadZipper (cursor, setCursor))
import Control.Lens
import SmartShrink (HasIdx (theIdx), depsMap)
import Control.Monad (when)
import Debug.Trace (traceM)
import qualified Data.Set as S
import Monad.Snapshot (MonadSnapshot(..))



newtype GenAction m = GenAction {unAction :: Int -> m (Maybe (Int, m ())) }

instance (Monad m) => Semigroup (GenAction m) where
  (<>) l r = GenAction $ \i -> do
        a <- unAction l i
        b <- unAction r i
        case (a,b) of
           (Nothing, x) -> pure x
           (x, Nothing) -> pure x
           (Just (ai,_), Just (bi,_)) 
             | ai >= bi -> pure a
             | otherwise -> pure b
instance (Monad m) => Monoid (GenAction m) where
   mempty = GenAction $ \_ -> pure Nothing

doShrink :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m) => GenAction m -> m Bool
doShrink g = do
    fullSize <- nodeCount
    branchCheckpoint (quotaShrink fullSize g) (pure ()) (has_conflict g)

has_conflict :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m) => GenAction m -> m ()
has_conflict g = do
    fullSize <- nodeCount
    if fullSize > 1 then do
        o <- branchCheckpoint (quotaShrink (fullSize `div` 2) g) (has_conflict g) (has_conflict g)
        when (not o) markAllCritical
    else markAllCritical

branchCheckpoint :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m) => m Bool -> m () -> m () -> m Bool
branchCheckpoint m onSuccess onFail = do
    affected <- popChangedNodes
    -- traceM ("prev affected " <> show affected)

    p <- snapshot
    m >>= \case
      True -> do
        affected <- popChangedNodes
        -- traceM ("affected " <> show affected)
        if S.null affected
        then pure False
        else do
            (checkpoint >> onSuccess) <|> (restore p >> popChangedNodes >> focusOn affected onFail)
            pure True
      False -> pure False

quotaShrink :: (Show k, MonadGraphMut k m) => Int -> GenAction m -> m Bool
quotaShrink quota0 g = loop False quota0
  where
      loop acc quota
        | quota <= 0 = pure acc
        | otherwise = do
            ma <- unAction g quota
            case ma of
                Nothing -> pure acc
                Just (quota', m) -> m >> loop True quota'

replaceNode :: (HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k) => (o -> m o) -> Traversal' o o -> GenAction m
replaceNode genReplacement l = GenAction $ \sizeLimit -> do
  hidden <- containsHidden
  sl <- largestNodeWith (\v k -> v <= sizeLimit && not (S.member k hidden))
  case sl of
    Just (s, k) | s > 1 -> 
      let
        rep = do
          navTo l k
          o <- cursor
          o' <- genReplacement o
          setCursor o'
          newDeps <- depsMap l
          addDeps newDeps
          getParent k >>= \case
            Nothing -> pure ()
            Just p -> addChild p (theIdx o')
          hideNodesBelow k
      in pure $ Just (sizeLimit-s+1, rep)
    _ -> pure Nothing
