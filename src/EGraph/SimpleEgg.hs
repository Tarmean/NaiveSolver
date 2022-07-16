{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module EGraph.SimpleEgg where
import EGraph.PlanTypes
import qualified Data.Vector.Unboxed as VU
import EGraph.Storage
    ( mkApp,
      newClass,
      mkEGraph,
      toFixpoint,
      runRebuild,
      RebuildT,
      UpdatedEGraph(new_data),
      addApp, showNew )
import Control.Monad.ST
import EGraph.Plan
import EGraph.ByteCodeVM (allMatches)
import qualified Data.IntMap.Strict as M
import Control.Monad.Primitive (PrimMonad)
import Control.Monad (forM_, replicateM)
-- import Debug.Trace


traceM _ = pure ()
trace _ a = a

    
appRule :: [Pat] -> ([Int] -> RebuildT (ST s) ()) -> RebuildT (ST s) ()
appRule pats cont = forM_ progs $ \prog -> do
   allMatches prog (cont . VU.toList)
  where progs = compilePats pats
runRules :: (forall s. RebuildT (ST s) ()) -> UpdatedEGraph -> UpdatedEGraph
runRules mo !egg 
  | trace "runRules" False = undefined
  | otherwise = update
  where
    (update, ()) = runRebuild egg (mo *> toFixpoint)



emptyEgg :: UpdatedEGraph
emptyEgg = mkEGraph (M.fromList [(1,2)])


mkList :: (PrimMonad m) => Int -> RebuildT m ()
mkList i = do
  cs <- replicateM i newClass
  _ <- go (head cs) (tail cs)
  toFixpoint
  where
    go _ [] = pure ()
    go acc (x:xs) = do
        acc' <- mkApp 1 [acc, x]
        go acc' xs

batchTest :: IO ()
batchTest = do
  i <- readIO =<< getLine
  go (fst $ runRebuild emptyEgg $ mkList i)
  where
    go e = do
       putStrLn $ showNew e
       if M.null (new_data e)
         then pure ()
         else go (eggUp e)
interactiveTest :: IO ()
interactiveTest = do
  i <- readIO =<< getLine
  go (fst $ runRebuild emptyEgg $ mkList i)
  where
    go e = do
       putStrLn $ showNew e
       c <- getChar
       if c == '\n'
       then go (eggUp e)
       else putStrLn (show c)

myTest :: (PrimMonad m) => RebuildT m ()
myTest = mkList 6

egg1 :: UpdatedEGraph
egg1 = fst $ runRebuild emptyEgg myTest

testPat :: [Pat]
testPat = [pap 0 1 [ppap 1 [1,2], 3]]
eggUp :: UpdatedEGraph -> UpdatedEGraph
eggUp = runRules $ do
  appRule [pap 0 1 [1,2]]  $ \[cid,v0,v1] -> do
    traceM $ "rule assoc "  <> show (cid,v0,v1)
    addApp cid 1 [v1,v0]
    pure ()
  appRule testPat  $ \[cid,v0,v1,v2] -> do
    traceM $ "rule commutative "  <> show (cid,v0,v1,v2)
    rhs <- mkApp 1 [v1,v2]
    addApp cid 1 [v0, rhs]
    pure ()


