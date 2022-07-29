{-# LANGUAGE QuasiQuotes #-}
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
import Control.Monad.State
import qualified Data.List as L
import Data.Ord (comparing)
import Data.Maybe (isNothing, isJust)
import PyF (fmt)
import Monad.Cut
import Monad.Amb (pick)



newtype GenAction m = GenAction { getAction :: Int -> m Int }
unAction :: (MonadCut m, Alternative m) => GenAction m -> Int -> m (Maybe Int)
unAction m i = cut (fmap Just (getAction m i) <|> pure Nothing)

instance (Alternative m) => Semigroup (GenAction m) where
  (<>) l r = GenAction $ \i -> do
        getAction l i <|> getAction r i

instance (Alternative m) => Monoid (GenAction m) where
   mempty = GenAction $ \_ -> empty

doShrink :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> m Bool
doShrink g = do
    fullSize <- nodeCount
    branchCheckpoint (quotaShrink fullSize g) (pure ()) (has_conflict g)

has_conflict :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> m ()
has_conflict g = do
    fullSize <- nodeCount
    if fullSize > 1 then do
        o <- branchCheckpoint (quotaShrink (fullSize `div` 2) g) (has_conflict g) (has_conflict g)
        when (not o) markAllCritical
    else markAllCritical

data ShrinkResult k = FullyShrunk (S.Set k) | NoShrinksLeft | ShrinksLeft (S.Set k)
partialShrink :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => Int -> GenAction m -> m (ShrinkResult k)
partialShrink size g = do
    _ <- popChangedNodes
    p <- snapshot
    (quotaShrink size g) >>= \case
      True -> do
        affected <- popChangedNodes
        if S.null affected
        then pure NoShrinksLeft
        else (checkpoint >> pure (FullyShrunk affected)) <|> (restore p >> popChangedNodes >> pure (ShrinksLeft affected))
      False -> pure (NoShrinksLeft)

data SearchState k = SearchState {
    blocked :: [S.Set k],
    stepSize :: Int,
    history :: [Int]
    } deriving (Eq, Ord, Show)
peekBestBlocked :: (Monad m, Eq k) => StateT (SearchState k) m (Maybe (S.Set k))
peekBestBlocked = do
    s <- get
    case blocked s of
      [] -> pure Nothing
      xs -> do
        let x = L.maximumBy (comparing S.size) xs
        pure (Just x)
getStepSize :: (MonadGraph k m, Eq k) => StateT (SearchState k) m Int
getStepSize = do
   g <- getActiveNodes
   s <- gets stepSize
   pure $ min (S.size g) s
takeBlocked :: (Monad m, Eq k) => S.Set k -> StateT (SearchState k) m ()
takeBlocked x = do
    s <- get
    put $ s { blocked = L.filter (/= x) (blocked s) }
addBlocked  :: (Monad m, Eq k) => S.Set k -> StateT (SearchState k) m ()
addBlocked x = modify $ \s -> s { blocked =  x:blocked s}
performNextAction :: (MonadGraphMut k m, Show k, MonadSnapshot m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> StateT (SearchState k) m Bool
performNextAction gen = do
     bb <- peekBestBlocked
     ss <- getStepSize
     sss <- gets stepSize
     active <- getActiveNodes
     pending <- gets blocked
     traceM [fmt|performing iteration, active: {show active}, blocks: {show pending}, stepsize: {ss}|]
     case bb of
       Just s' | ss < sss && S.size s' > 2*ss -> do
           traceM [fmt|unblocking {show s'}|]
           takeBlocked s'
           unblockAction gen s'
           pure True
       _ -> do
            let step = S.size active `div` 2
            r <- lift $ partialShrink step gen
            case r of
              ShrinksLeft ls -> do
                modify (\s -> s { stepSize = max 1 (stepSize s `div` 2) })
                traceM [fmt|stepping with size {step}, crit region: {show ls}|]
                mapM_ hideNodeUnsafe ls
                addBlocked ls
                pure True
              NoShrinksLeft -> do
                traceM [fmt|no shrink left with stepsize {ss}|]
                case bb of
                   Just s' -> do
                       traceM [fmt|unblocking {show s'}|]
                       takeBlocked s'
                       unblockAction gen s'
                       pure True
                   Nothing -> pure False
                -- traceM [fmt|stepping with size {step}, no shrink|] >> pure (isJust bb)
              _ -> modify (\s -> s { stepSize = stepSize s * 2 }) >> pure True
smartLoop :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> m ()
smartLoop gen = flip evalStateT (SearchState [] 8 []) $ do
    let
      loop = performNextAction gen >>= \case
        True -> loop
        _ -> pure ()
    loop
    crits <- getHidden
    active <- getActiveNodes
    traceM [fmt|active {show active}, criticals {show crits}|]

unblockAction :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> S.Set k -> StateT (SearchState k) m  ()
unblockAction g s = do
    mapM_ unhideNode s
    (r, left) <- focusOn s $ do
        step <- fmap (`div` 2) nodeCount
        r <- lift $ partialShrink step g
        left <- getActiveNodes
        pure (r,left)
    case r of
      ShrinksLeft ls -> do
        mapM_ hideNodeUnsafe ls
        traceM ("hit " <> show ls <> ", restoring" <> show (left S.\\ ls))
        addBlocked ls
      NoShrinksLeft -> do
        traceM ("no shrinks left for " ++ show s)
        mapM_ hideNodeUnsafe s
      FullyShrunk notIt -> do
        let critRegion = s S.\\ notIt
        mapM_ hideNodeUnsafe critRegion
        traceM [fmt|fully shrunk {show notIt} out of {show s}, remainder {show critRegion}|]
        addBlocked critRegion


branchCheckpoint :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m) => m Bool -> m () -> m () -> m Bool
branchCheckpoint m onSuccess onFail = do
    _ <- popChangedNodes
    p <- snapshot
    m >>= \case
      True -> do
        affected <- popChangedNodes
        if S.null affected
        then pure False
        else do
            (checkpoint >> onSuccess) <|> (restore p >> popChangedNodes >> focusOn affected onFail)
            pure True
      False -> pure False

quotaShrink :: (Show k, MonadGraphMut k m, MonadCut m, Alternative m) => Int -> GenAction m -> m Bool
quotaShrink quota0 g = loop False quota0
  where
      loop acc quota
        | quota <= 0 = pure acc
        | otherwise = do
            ma <- unAction g quota
            case ma of
                Nothing -> pure acc
                Just quota' -> loop True quota'


replaceNode :: (HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m) => (o -> m o) -> Traversal' o o -> GenAction m
replaceNode genReplacement l = GenAction $ \sizeLimit -> do
  hidden <- containsHidden
  sl <- largestNodeWith (\v k -> v <= sizeLimit && not (S.member k hidden))
  case sl of
    Just (s, k) | s > 1 -> do
      navTo l k
      o <- cursor
      o' <- genReplacement o
      replaceValue l k o'
      pure $ sizeLimit-s+1
    _ -> empty

hoistNode :: (HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => Traversal' o o -> GenAction m
hoistNode l = GenAction $ \limit -> cut $ do
    hs <- getHidden
    h <- pick hs
    navTo l h
    ps <- activeParents h
    p <- pick ps
    prevSize <- S.size <$> getActiveNodes
    v <- cursor
    replaceValue l p v
    postSize <- S.size <$> getActiveNodes
    guard (postSize - prevSize <= limit)
    pure (limit + postSize - prevSize)

replaceValue ::(HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k) => Traversal' o o -> k -> o -> m ()
replaceValue l k v = do
    navTo l k
    setCursor v
    newDeps <- depsMap l
    addDeps newDeps
    getParent k >>= \case
      Nothing -> pure ()
      Just p -> addChild p (theIdx v)
    deleteNodesBelow k

