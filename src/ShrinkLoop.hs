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
-- import Debug.Trace (traceM)
import qualified Data.Set as S
import Monad.Snapshot (MonadSnapshot(..))
import Control.Monad.State
import qualified Data.List as L
import Data.Ord (comparing)
import Data.Maybe (isNothing, isJust)
import PyF (fmt)
import Monad.Cut
import Monad.Amb (pick)
import Monad.Critical
import qualified Data.Map.Strict as M
import Data.Monoid (Any(..))
import Control.Monad.Writer (execWriterT, MonadWriter (tell))


traceM :: Monad m => String -> m ()
traceM _ = pure ()

newtype GenAction m = GenAction { getAction :: Int -> m Int }
{-# INLINABLE unAction #-}
unAction :: (MonadCut m, Alternative m) => GenAction m -> Int -> m (Maybe Int)
unAction m i = cut (fmap Just (getAction m i) <|> pure Nothing)

instance (MonadPlus m, MonadCut m) => Semigroup (GenAction m) where
  {-# INLINABLE (<>) #-}
  (<>) l r = GenAction $ \i -> --forI i (i - 2) ||| forI i (i `div` 2) ||| getAction l i ||| getAction r i
    -- where
       (getAction l i) <|> (getAction r i)
      -- forI i i' = (mfilter ((>i)) $ getAction l i) ||| (mfilter ((>i)) $ getAction r i)

instance (MonadCut m, MonadPlus m) => Monoid (GenAction m) where
   mempty = GenAction $ \_ -> mzero

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
{-# INLINABLE partialShrink #-}
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
{-# INLINABLE performNextAction #-}
performNextAction :: (MonadGraphMut k m, Show k, MonadSnapshot m, MonadOracle m, Alternative m, MonadCut m, MonadCritical k m) => GenAction m -> StateT (SearchState k) m Bool
performNextAction gen = do
     bb <- peekBestBlocked
     active <- getActiveNodes
     case bb of
       Just s' | S.size s' > S.size active -> do
           traceM [fmt|unblocking {show s'}|]
           takeBlocked s'
           unblockAction gen s'
           pure True
       _ -> do
         let
           stepFor step cont = do
            r <- lift $ partialShrink step gen
            case r of
              ShrinksLeft ls -> do
                mapM_ hideNodeUnsafe ls
                addBlocked ls
                pure True
              NoShrinksLeft -> do
                case bb of
                   Just s' -> do
                       traceM [fmt|unblocking {show s'}|]
                       takeBlocked s'
                       unblockAction gen s'
                       pure True
                   Nothing -> do
                      cont
                -- traceM [fmt|stepping with size {step}, no shrink|] >> pure (isJust bb)
              _ -> pure True
         let step = S.size active - (S.size active `div` 2)
         stepFor step (stepFor (S.size active*2) (pure False))
{-# INLINABLE smartLoop #-}
smartLoop :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m, MonadCritical k m) => GenAction m -> m ()
smartLoop gen = flip evalStateT (SearchState [] 8 []) $ do
    let
      loop = performNextAction gen >>= \case
        True -> loop
        _ -> pure ()
    loop
    hidden <- getHidden
    crits <- getCriticals
    active <- getActiveNodes
    traceM [fmt|active {show active}, hidden {show hidden}, criticals {show crits}|]

{-# INLINABLE unblockAction #-}
unblockAction :: (MonadCritical k m, Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> S.Set k -> StateT (SearchState k) m  ()
unblockAction g s = do
    mapM_ unhideNode s
    (r, left, theQuota) <- focusOn s $ do
        step <- fmap (\x -> x - x`div` 2) nodeCount
        r <- lift $ partialShrink step g
        left <- getActiveNodes
        pure (r,left, step)
    case r of
      ShrinksLeft ls -> do
        mapM_ hideNodeUnsafe ls
        -- traceM ("hit " <> show ls <> ", restoring" <> show (left S.\\ ls))
        addBlocked ls
      NoShrinksLeft -> do
        traceM [fmt|no shrinks left for {show s} with quota {theQuota}|]
        leafRegion s
      FullyShrunk notIt -> do
        let critRegion = left S.\\ notIt
        -- mapM_ hideNodeUnsafe critRegion
        traceM [fmt|fully shrunk {show notIt} out of {show s}, remainder {show critRegion}|]
        unblockAction g critRegion
        -- addBlocked critRegion
{-# INLINABLE leafRegion #-}
leafRegion :: (MonadGraphMut a m, MonadCritical a m, Show a) => S.Set a -> m ()
leafRegion s = do
    sizes <- getAritiesMap
    let ls = [(k, sizes M.! k) | k <- S.toList s]
    -- mapM_ hideNodeUnsafe s
    o <- rootsOf s
    traceM [fmt|leaf region {show ls}, roots {show o}|]
    mapM_ markCritical o

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

{-# INLINABLE quotaShrink #-}
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


{-# INLINABLE replaceNode #-}
replaceNode :: (MonadCritical k m, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => (o -> m o) -> Traversal' o o -> GenAction m
replaceNode genReplacement l = GenAction $ \sizeLimit -> cut $ do
  hidden <- containsHidden
  hasCritical <- containingCritical
  traceM "largestNode"
  sl <- largestNodeWith (\v k -> v <= sizeLimit && not (S.member k hidden) && not (S.member k hasCritical))
  traceM "largestNode found"
  case sl of
    Just (s, k) | s > 1 -> do
      navTo l k
      o <- cursor
      o' <- cut (genReplacement o)
      replaceValue l k o'
      pure $ sizeLimit-s+1
    _ -> empty

{-# INLINABLE guardDeleteable #-}
guardDeleteable :: (Alternative m, MonadGraphMut k m, Show k, MonadCritical k m) => S.Set k -> m ()
guardDeleteable ks = do
    hasHidden <- containsHidden
    guard $ S.null (S.intersection ks hasHidden)
    hasCrit <- containingCritical
    guard $ S.null (S.intersection ks hasCrit)

{-# INLINABLE hoistNode #-}
hoistNode :: (MonadCritical k m, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => Traversal' o o -> GenAction m
hoistNode l = GenAction $ \limit -> cut $ do
    parent <- pick =<< getActiveNodes
    guard . not =<< isCritical parent
    siblings <- getChildren parent
    [kain] <- filterM containsCritical (S.toList siblings)

    leftover <- leftoverSize limit parent kain

    guardDeleteable (S.delete kain siblings)

    traceM [fmt|HOISTING {show kain} into {show parent}|]
    replaceWithKey l parent kain
    pure leftover
{-# INLINABLE hoistInCrit #-}
hoistInCrit :: (MonadCritical k m, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => Traversal' o o -> GenAction m
hoistInCrit l = GenAction $ \limit -> cut $ do
    parent <- pick =<< getCriticals
    guard . not =<< isHidden parent

    siblings <- getChildren parent
    kain <- pick siblings


    leftover <- leftoverSize limit parent kain

    guardDeleteable (S.delete kain siblings)

    traceM [fmt|HOISTING CRIT {show kain} into {show parent}, siblings {show (S.delete kain siblings)}|]
    markCritical kain
    replaceWithKey l parent kain
    forgetNewlyHidden parent
    pure leftover

{-# INLINABLE leftoverSize #-}
leftoverSize :: (Alternative m, MonadGraph k m) => Int -> k -> k -> m Int
leftoverSize limit parent kain = do
    parentSize <- getArity parent
    childSize <- getArity kain
    let leftover = limit - parentSize + childSize
    guard (leftover >= 0)
    pure leftover

{-# INLINABLE containsCritical #-}
containsCritical :: (MonadGraph k m, MonadCritical k m) => k -> m Bool
containsCritical k = fmap getAny $ execWriterT $ do
  forReachableAll1_ k $ \s -> 
     isCritical s >>= \case
        True -> tell (Any True)
        _ -> tell (Any False)
{-# INLINABLE containingCritical #-}
containingCritical :: (MonadGraph k m, MonadCritical k m) => m (S.Set k)
containingCritical = do
  crits <- getCriticals
  o <- mapM parentsListAll1 (S.toList crits)
  pure (S.fromList $ concat o)
    


{-# INLINABLE replaceWithKey #-}
replaceWithKey :: (MonadZipper o m, MonadGraph k m, RecView o m, HasIdx o k, MonadGraphMut k m) => Traversal' o o -> k -> k -> m ()
replaceWithKey l parent kain = do
    setAt l parent =<< getAt l kain
    setParent kain =<< getParent parent
    deleteNodesBelow parent
{-# INLINABLE getAt #-}
getAt :: (MonadZipper o m, MonadGraph k m, RecView o m, HasIdx o k) => Traversal' o o -> k -> m o
getAt l n = do
    navTo l n
    cursor
{-# INLINABLE setAt #-}
setAt :: (MonadZipper o m, MonadGraph k m, RecView o m, HasIdx o k) => Traversal' o o -> k -> o -> m ()
setAt l n v = do
    navTo l n
    setCursor v

{-# INLINABLE replaceValue #-}
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