{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-| EGraph.PlanStep gives possible joins, this module greedily picks the next one until done.
    This is quite a bit like the QuickSI subgraph isomorphism algorithm!
    The output requires some assembly, which is done in EGraph.PlanAssembly
 -}
module EGraph.PlanSequence (greedyMatching) where
import EGraph.PlanStep
    ( Stats(preKnown, allowsDiscovers, allowsChecks),
      MatchEnv(MEnv, patGraph),
      collectSteps )
import EGraph.MatchTypes
    ( PGraph(definitions), PElem, ExprNodeId, ArgPos )
import qualified Data.Set as S
import EGraph.Types ( Elem'(argIds) )
import qualified Data.Map as M
import Data.List (maximumBy)
import Data.Ord (comparing)
import EGraph.Pending (mkPending)

greedyMatching :: PGraph -> (M.Map ExprNodeId Stats, MatchEnv)
greedyMatching pgraph = go mempty (makeMatchEnv pgraph)
  where
    go acc env = case collectSteps env of
      [] -> (acc, env)
      candidates -> let ((pid, stats), env') = maximumBy (comparing rate1) candidates in go (M.insert pid stats acc) env'
    rate1 ((pid, stats), env) = rateStats pelem stats
      where 
        pelem = case env.patGraph.definitions M.! pid of
          Left _ -> error "collectSteps cannot yield leaf notes"
          Right e -> e

makeMatchEnv :: PGraph -> MatchEnv
makeMatchEnv pgraph = MEnv innerNodes mempty pending pgraph
  where
    innerNodes = S.fromList [pid | (pid, Right _) <- M.toList pgraph.definitions]
    pending = mkPending $ M.fromList [(pid, S.fromList expr.argIds) | (pid, Right expr) <- M.toList pgraph.definitions]


rateStats :: PElem -> Stats -> Double
rateStats expr stats = rateIndex + rateLocalFilters + rateExistentialJoins + rateBranchingFactor
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
    rateBranchingFactor = scale R{rmin=2, rmax=4, score= -4} unknownVars

data Range = R { rmin :: Double, rmax :: Double, score :: Double }
scale :: Integral a => Range -> a -> Double
scale r v 
  | fromIntegral v <= r.rmin = 0
  | fromIntegral v >= r.rmax = r.score
  | otherwise = (fromIntegral v - r.rmin) / (r.rmax - r.rmin) * r.score

countInfix :: S.Set ArgPos -> Int
countInfix s = go 0
  where
   go idx
     | S.member idx s = go (idx+1)
     | otherwise = idx
