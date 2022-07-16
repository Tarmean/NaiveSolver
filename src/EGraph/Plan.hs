module EGraph.Plan where
import EGraph.PlanTypes
import EGraph.Types (Elem'(..), Var, ONSymbol(..))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.State
import EGraph.PlanAssembly (assemble)
import EGraph.PlanSequence (greedyMatching)
import Data.Foldable (traverse_)
import Control.Lens
import qualified Data.List as L
import Control.Arrow (second)

test1 :: Pat
test1 = ppap 1 [ppap 2 [2], ppap 3 [2]]

-- compilePat :: Pat -> Program Symbol
-- compilePat pat = compilePats id [pat]

compilePats :: [Pat] -> [Program ONSymbol]
compilePats pats = do
    sym <- theSyms
    let (steps, env) = greedyMatching (calcJoinCost pgraph sym) pgraph
    pure (assemble env steps sym)
  where
    pgraph = patsToGraph pats
    theSyms = mappingsFor pgraph

calcJoinCost :: PGraph -> M.Map ExprNodeId ONSymbol -> M.Map ExprNodeId Double
calcJoinCost _ joins = M.map single joins
  where
    single (OSymbol _) = -8.0
    single (ONSymbol _) = -9.5
    single (NSymbol _) = 0

mappingsFor :: PGraph -> [M.Map ExprNodeId ONSymbol]
mappingsFor pg = [o | (l,m,r) <- splitsOf exprs, let o = toLookup l m r ]
  where
    exprs = [(k,fSymbol r) | (k,Right r) <- M.toList (definitions pg)]
    toLookup :: [(ExprNodeId, Symbol)] -> (ExprNodeId, Symbol) -> [(ExprNodeId, Symbol)] -> M.Map ExprNodeId ONSymbol
    toLookup l m r = M.fromList $ w OSymbol l <> w NSymbol [m] <> w ONSymbol r
      where w k = fmap (second (\(Symbol s) -> k s))
splitsOf :: [a] -> [([a], a, [a])]
splitsOf = go []
  where
    go acc (x:xs) = (acc, x, xs) : go (x:acc) xs
    go _ [] = []


patsToGraph :: [Pat] -> PGraph
patsToGraph p = PGraph (M.fromList [(v,k) | (k,v) <- M.toList defs]) (M.map (mapKeys M.!) outMap)
  where
    (defs, outMap) = execState (traverse_ patToCtx p) mempty
    mapKeys = M.fromList (zip (L.sort $ M.elems outMap) [0..])

patToCtx :: MonadState (M.Map (Either VarId (Elem' ExprNodeId)) ExprNodeId, M.Map ExprNodeId VarId) m => Pat -> m ExprNodeId
patToCtx p0 = go' p0
  where
    go (PMatch minto h ls) = do
       ls' <- traverse go' ls
       outid <- case minto of
         Nothing -> toId (Right (Elem h ls'))
         Just v -> go' (PV v)
       setId outid (Elem h ls')
       pure outid
       
    go' (PApp p) = go p
    go' (PV v) = do
      out <- toId (Left v)
      _2 . at out ?= v
      pure out
    setId :: (MonadState (M.Map (Either VarId (Elem' ExprNodeId)) ExprNodeId, M.Map ExprNodeId VarId) m) => ExprNodeId -> Elem' ExprNodeId -> m ()
    setId outid val = do
        o <- use (_1 . at (Right val))
        case o of
          Nothing -> (_1 . at (Right val)) ?= outid
          Just id'
            | id' /= outid -> error ("mismatched variables in pattern: " <> show (outid,id') <> " for " <> show val)
            | otherwise -> pure ()

    toId :: (MonadState (M.Map k ExprNodeId, M.Map ExprNodeId VarId) m, Ord k) => k -> m ExprNodeId
    toId v = do
      m <- use (_1 . at v)
      case m of
        Just o -> pure o
        Nothing -> do
          o <- use (_1 . to M.size . to EId)
          _1 . at v ?= o
          pure o
ctxFreeVars :: (Ord a1, Ord a2) => [(Either a2 (Elem' a1), a1)] -> M.Map a1 (S.Set a2)
ctxFreeVars m = out
  where
    out = M.fromList [(i, step ev) | (ev, i) <- m]
    step (Left v) = S.singleton v
    step (Right (Elem _ ts)) = mconcat (map (out M.!) ts)
