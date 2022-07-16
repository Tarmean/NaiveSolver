{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-| EGraph.PlanStep gives possible joins, this module greedily picks the next one until done.
    This is quite a bit like the QuickSI subgraph isomorphism algorithm!
    The output requires some assembly, which is done in EGraph.PlanAssembly
 -}
module EGraph.PlanSequence where
import EGraph.PlanStep
import qualified Data.Set as S
import EGraph.Types ( Elem'(argIds) )
import qualified Data.Map as M
import Data.List (maximumBy)
import Data.Ord (comparing)
import EGraph.Pending (mkPending)
import EGraph.PlanTypes
import Data.Maybe (fromMaybe)

greedyMatching :: M.Map ExprNodeId Double -> PGraph -> ([PlanStep], MatchEnv)
greedyMatching joinCost pgraph = go mempty (makeMatchEnv pgraph)
  where
    go acc env = case collectSteps env of
      [] -> (reverse acc, env)
      candidates -> let ((pid, stats), env') = maximumBy (comparing rate1) candidates in go (PlanStep stats pid (elemOf pid) : acc) env'
    elemOf pid 
      | Right out <- pgraph.definitions M.! pid = out
      | otherwise = undefined
    rate1 ((pid, stats), env) = rateStats pelem stats (joinCost M.!? pid)
      where 
        pelem = case env.patGraph.definitions M.! pid of
          Left _ -> error "collectSteps cannot yield leaf notes"
          Right e -> e

makeMatchEnv :: PGraph -> MatchEnv
makeMatchEnv pgraph = MEnv innerNodes mempty pending pgraph
  where
    innerNodes = S.fromList [pid | (pid, Right _) <- M.toList pgraph.definitions]
    pending = mkPending $ M.fromList [(pid, S.fromList expr.argIds) | (pid, Right expr) <- M.toList pgraph.definitions]


rateStats :: PElem -> Stats -> Maybe Double -> Double
rateStats expr stats joinCost = rateIndex + rateLocalFilters + rateExistentialJoins + rateBranchingFactor + fromMaybe 0 joinCost
  where
    argCount = length expr.argIds

    indexCount = S.size stats.preKnown
    prefixCount = countInfix stats.preKnown
    -- how much local filtering is leftover if we only use the natural sorting as 'index'
    naiveIndex = indexCount - prefixCount

    countFilters = length stats.allowsChecks
    countExistential = S.size stats.allowsDiscovers

    unknownVars = argCount - indexCount

    rateIndex = scale R{rmin = 1, rmax=3,score=7} prefixCount
    rateLocalFilters = scale R{rmin = 0, rmax=4,score=4} (naiveIndex + countFilters)
    rateExistentialJoins = scale R{rmin = 0, rmax=2,score=2} countExistential
    rateBranchingFactor = scale R{rmin=1, rmax=4, score= -8} unknownVars

data Range = R { rmin :: Double, rmax :: Double, score :: Double }
scale :: Integral a => Range -> a -> Double
scale r v 
  | fromIntegral v <= r.rmin = 0
  | fromIntegral v >= r.rmax = r.score
  | otherwise = (fromIntegral v - r.rmin) / (r.rmax - r.rmin) * r.score


