module EGraph.Plan where
import EGraph.PlanTypes
import EGraph.Types (Elem'(..), Var)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.State
import EGraph.PlanAssembly (assemble)
import EGraph.PlanSequence (greedyMatching)
import Data.Foldable (traverse_)

test1 :: Pat
test1 = pap 1 [ppap 2 [2], ppap 3 [2]]

compilePat :: Pat -> Program
compilePat pat = compilePats [pat]

compilePats :: [Pat] -> Program
compilePats pats = assemble env steps
  where
    (steps, env) = greedyMatching (patsToGraph pats)


patsToGraph :: [Pat] -> PGraph
patsToGraph p = PGraph $ M.fromList [(v,k) | (k,v) <- M.toList $ execState (traverse_ patToCtx p) mempty]

patToCtx :: MonadState (M.Map (Either VarId (Elem' ExprNodeId)) ExprNodeId) m => Pat -> m ExprNodeId
patToCtx (Pat p0) = (go p0)
  where
    go (Elem h ls) = do
       ls' <- traverse go' ls
       toId (Right (Elem h ls'))
    go' (P (Pat p)) = go p
    go' (V v) =  toId (Left v)
    toId :: (MonadState (M.Map k ExprNodeId) m, Ord k) => k -> m ExprNodeId
    toId v = do
      m <- get
      case m M.!? v of
        Just o -> pure o
        Nothing -> do
          let o = EId $ M.size m
          put (M.insert v o m)
          pure o
ctxFreeVars :: (Ord a1, Ord a2) => [(Either a2 (Elem' a1), a1)] -> M.Map a1 (S.Set a2)
ctxFreeVars m = out
  where
    out = M.fromList [(i, step ev) | (ev, i) <- m]
    step (Left v) = S.singleton v
    step (Right (Elem _ ts)) = mconcat (map (out M.!) ts)
