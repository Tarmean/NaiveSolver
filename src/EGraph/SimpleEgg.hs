module EGraph.SimpleEgg where
import EGraph.PlanTypes
import qualified Data.Vector.Unboxed as VU
import EGraph.Storage
import Control.Monad.ST
import EGraph.Plan
import EGraph.ByteCodeVM (allMatches)
import qualified Data.IntMap.Strict as M
import Control.Monad.Primitive (PrimMonad)



appRule :: [Pat] -> (forall s. [Int] -> RebuildT (ST s) ()) -> EGraph -> UpdatedEGraph
appRule p cont egg = update
  where
    prog = compilePats p
    mo = allMatches prog (cont . VU.toList)
    (update, ()) = runRebuild egg (mo *> toFixpoint)



emptyEgg :: EGraph
emptyEgg = mkEGraph (M.fromList [(1,2)])



myTest :: (PrimMonad m) => RebuildT m ()
myTest = do
  c1 <- newClass
  c2 <- newClass
  c3 <- newClass
  c1_2 <- mkApp 1 [c1, c2]
  _ <- mkApp 1 [c1_2, c3]
  toFixpoint

egg1 :: UpdatedEGraph
egg1 = fst $ runRebuild emptyEgg myTest

testPat :: [Pat]
testPat = [pap 1 [ppap 1 [0,1], 2]]
eggUp :: EGraph -> UpdatedEGraph
eggUp = appRule testPat  $ \[v0,v1,v2] -> do
    rhs <- mkApp 1 [v1,v2]
    _ <- mkApp 1 [v0, rhs]
    pure ()
