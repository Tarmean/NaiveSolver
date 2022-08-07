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
import GHC.Stack
import Data.Utils


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

-- doShrink :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> m Bool
-- doShrink g = do
--     fullSize <- nodeCount
--     branchCheckpoint (quotaShrink fullSize g) (pure ()) (has_conflict g)

-- has_conflict :: (Num k, Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> m ()
-- has_conflict g = do
--     fullSize <- nodeCount
--     if fullSize > 1 then do
--         o <- branchCheckpoint (quotaShrink (fullSize `div` 2) g) (has_conflict g) (has_conflict g)
--         when (not o) markAllCritical
--     else markAllCritical

data ShrinkResult k = FullyShrunk (S.Set k) | NoShrinksLeft | ShrinkFailed (S.Set k)
{-# INLINABLE partialShrink #-}
partialShrink :: (Num k, Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => Int -> GenAction m -> m (ShrinkResult k)
partialShrink size g = do
    _ <- popChangedNodes
    p <- snapshot
    (quotaShrink size g) >>= \case
      True -> do
        affected <- popChangedNodes
        -- traceM [fmt|partialShrink: affected nodes: {show (compact affected)}|]
        if S.null affected
        then pure NoShrinksLeft
        else (checkpoint >> pure (FullyShrunk affected)) <|> (restore p >> popChangedNodes >> pure (ShrinkFailed affected))
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
performNextAction :: (Num k, MonadGraphMut k m, Show k, MonadSnapshot m, MonadOracle m, Alternative m, MonadCut m, MonadCritical k m) => GenAction m -> StateT (SearchState k) m Bool
performNextAction gen = do
     bb <- peekBestBlocked
     active <- getActiveNodes
     case bb of
       Just s'  -> do
           -- traceM [fmt|unblocking {show s'}|]
           takeBlocked s'
           unblockAction gen s'
           pure True
       _ -> traceM "no blocekd left" *> pure False
       -- _ -> do
         -- let
         --   stepFor step cont = do
         --    r <- lift $ partialShrink step gen
         --    case r of
         --      ShrinkFailed ls -> do
         --        mapM_ hideNodeUnsafe ls
         --        addBlocked ls
         --        pure True
         --      NoShrinksLeft -> do
         --        case bb of
         --           Just s' -> do
         --               -- traceM [fmt|unblocking {show s'}|]
         --               takeBlocked s'
         --               unblockAction gen s'
         --               pure True
         --           Nothing -> do
         --              cont
                -- traceM [fmt|stepping with size {step}, no shrink|] >> pure (isJust bb)
              -- _ -> pure True
         -- let step = S.size active *5
         -- stepFor step (pure False)
{-# INLINABLE smartLoop #-}
smartLoop :: (Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m, MonadCritical k m, Num k) => GenAction m -> m ()
smartLoop gen = flip evalStateT (SearchState [] 8 []) $ do
    s <- getActiveNodes
    tryDelete gen s
    let
      loop = performNextAction gen >>= \case
        True -> loop
        _ -> pure ()
    loop
    hidden <- getHidden
    crits <- getCriticals
    active <- getActiveNodes
    traceM [fmt|active {show $ compact (active S.\\ crits)}, hidden {show $ compact (hidden S.\\ crits)}, criticals {show $ compact crits}|]

{-# INLINABLE tryDelete #-}
tryDelete :: (Num k, MonadCritical k m, Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m) => GenAction m -> S.Set k -> StateT (SearchState k) m  ()
tryDelete g s
  | S.size s == 1 = leafRegion s
tryDelete g s = do
    -- traceM [fmt|tryDelete: block {show s}|]
    mapM_ unhideNode s
    (r, left, theQuota) <- focusOn s $ do
        let step = S.size s - S.size s `div` 2
        r <- lift $ partialShrink (step*2) g
        left <- getActiveNodes
        pure (r,left, step)
    case r of
      ShrinkFailed ls -> do
        let critRegion = left S.\\ ls
        -- when (not $ null critRegion) (error [fmt|illegal crit region {show left} {show ls}|])
        -- traceM ("try delete hit " <> show ls <> ", restoring" <> show (left S.\\ ls))
        mapM_ hideNodeUnsafe ls
        addBlocked ls
      NoShrinksLeft -> do
        -- traceM [fmt|no shrinks left for {show s} with quota {theQuota}|]
        pure ()
      FullyShrunk notIt -> do
        let critRegion = left S.\\ notIt
        when (not $ S.null critRegion) $ do
            -- traceM [fmt|fully shrunk {show notIt} out of {show s}, remainder {show critRegion}|]
            tryDelete g critRegion
        -- addBlocked critRegion
{-# INLINABLE unblockAction #-}
unblockAction :: (MonadCritical k m, Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m, MonadCut m, Num k) => GenAction m -> S.Set k -> StateT (SearchState k) m  ()
unblockAction g s = do
    -- traceM [fmt|unblock action: block {show s}|]
    mapM_ unhideNode s
    (r, left, theQuota) <- focusOn s $ do
        let quota = S.size s - S.size s `div` 2
        r <- lift $ partialShrink quota g
        left <- getActiveNodes
        pure (r,left, quota)
    case r of
      ShrinkFailed ls -> do
        traceM [fmt|shrink failed {show(compact ls)}|]
        mapM_ hideNodeUnsafe ls
        addBlocked ls
        let rhs = (left S.\\ ls)
        when (not $ S.null rhs) $ tryDelete g rhs
      NoShrinksLeft -> do
        -- traceM [fmt|no shrinks left for {show s} with quota {theQuota}|]
        leafRegion s
      FullyShrunk notIt -> do
        let critRegion = left S.\\ notIt
        -- mapM_ hideNodeUnsafe critRegion
        -- traceM [fmt|fully shrunk {show (compact notIt)} out of {show (compact s)}, remainder {show (compact critRegion)}|]
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

branchCheckpoint :: (Num k, Show k, MonadSnapshot m, MonadGraphMut k m, MonadOracle m, Alternative m) => m Bool -> m () -> m () -> m Bool
branchCheckpoint m onSuccess onFail = do
    _ <- popChangedNodes
    p <- snapshot
    m >>= \case
      True -> do
        affected <- popChangedNodes
        traceM [fmt|try remove {show (compact affected)}|]
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
                Just quota' -> pure True


{-# INLINABLE replaceNode #-}
replaceNode :: (Num k, MonadCritical k m, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => (o -> m o) -> Traversal' o o -> GenAction m
replaceNode genReplacement l = GenAction $ \sizeLimit -> cut $ do
  hidden <- containsHidden
  hasCritical <- containingCritical
  sl <- largestNodeWith (\v k -> v <= sizeLimit && not (S.member k hidden) && not (S.member k hasCritical))
  case sl of
    Just (s, k) | s > 1 -> orFail $ do
      traceM [fmt|hole for {show k}, reduction {show s}|]
      orFail $ navTo l k
      o <- orFail cursor
      o' <- orFail (genReplacement o)
      orFail $ replaceValue l k o'
      orFail $ pure $ sizeLimit-s+1
    _ -> empty
orFail :: (HasCallStack, Alternative m) => m a -> m a
orFail a = a <|> pure (error ("orFail failed"))
{-# INLINABLE guardDeleteable #-}
guardDeleteable :: (Alternative m, MonadGraphMut k m, Show k, MonadCritical k m) => S.Set k -> m ()
guardDeleteable ks = do
    -- hasHidden <- containsHidden
    -- guard $ S.null (S.intersection ks hasHidden)
    hasCrit <- containingCritical
    guard $ S.null (S.intersection ks hasCrit)

{-# INLINABLE hoistNode #-}
hoistNode :: (Num k, MonadCritical k m, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => Traversal' o o -> GenAction m
hoistNode l = GenAction $ \limit -> cut $ do
    parent <- pick =<< getActiveNodes
    guard . not =<< isCritical parent
    siblings <- getChildren parent
    [kain] <- filterM containsCritical (S.toList siblings)
    guard . not =<<  isHidden kain

    leftover <- leftoverSize limit parent kain

    guardDeleteable (S.delete kain siblings)

    traceM [fmt|HOISTING {show kain} into {show parent}|]
    replaceWithKey l parent kain
    pure leftover
{-# INLINABLE hoistInCrit #-}
hoistInCrit :: (Num k, MonadCritical k m, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k, Alternative m, MonadCut m) => Traversal' o o -> GenAction m
hoistInCrit l = GenAction $ \limit -> cut $ do
    active <- getActiveNodes
    parent <- pick =<< getCriticals
    -- guard . not =<< isHidden parent

    siblings <- getChildren parent
    kain <- pick siblings
    kainHidden <- isHidden kain
    guard (not kainHidden)


    parentSize <- getArity parent
    childSize <- getArity kain
    let leftover = limit - parentSize + childSize
    
    -- leftover <- leftoverSize limit parent kain

    guardDeleteable (S.delete kain siblings)

    alreadyHidden <- filterM isHidden (S.toList $ S.delete kain siblings)
    mapM_ markNodeAffected (S.delete kain siblings S.\\ S.fromList alreadyHidden)

    traceM [fmt|HOISTING CRIT {show kain} into {show parent}, siblings {show (S.delete kain siblings)}, already hidden {show alreadyHidden}|]
    markCritical kain
    replaceWithKey l parent kain
    mapM_ forgetNewlyHidden alreadyHidden
    forgetNewlyHidden kain
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
replaceWithKey :: (Num k, Show k, MonadZipper o m, MonadGraph k m, RecView o m, HasIdx o k, MonadGraphMut k m) => Traversal' o o -> k -> k -> m ()
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
replaceValue ::(Num k, HasIdx o k, RecView o m, MonadGraphMut k m, RecView o m, Show k) => Traversal' o o -> k -> o -> m ()
replaceValue l k v = do
    navTo l k
    setCursor v
    newDeps <- depsMap l
    addDeps newDeps
    getParent k >>= \case
      Nothing -> pure ()
      Just p -> addChild p (theIdx v)
    deleteNodesBelow k
