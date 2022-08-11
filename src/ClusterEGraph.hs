{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
-- | Visualize and cluster EGraphs
-- Theoretically useful to find mostly independent
-- sub-problems, but the dependency footprint is so large
-- that it is a 10* increase in compile time
module ClusterEGraph where
-- import Overeasy.EGraph
-- import Overeasy.Assoc


-- import Data.Graph.Analysis as A
import qualified IntLike.Map as ILM
import qualified Data.Foldable as F
-- import Data.GraphViz.Printing (renderDot)
-- import Data.GraphViz (defaultParams, quickParams, printDotGraph, preview, runGraphvizCanvas', GraphvizCanvas (Xlib, Gtk), GraphvizParams (..), blankParams)
-- import Data.GraphViz.Attributes (Labellable(..))
-- import Data.GraphViz.Attributes.Complete (Label(..), EscString(..), RecordFields(..), RecordField(..), PortName(..))
import Data.Text.Lazy (Text, pack)
import Data.Utils (pshow)
import Prettyprinter (Pretty)
import qualified Data.Text.Lazy.IO as T
import IntLike.Map (IntLikeMap)
import GHC.Stack
import Data.Maybe (fromMaybe)
import Data.Coerce (Coercible)
import Control.Concurrent (forkIO)
import System.Random
import Data.Utils (zipFoldableWith)
import Overeasy.Assoc (assocPartialLookupByKey)

class DecideIfEdgeLife f d where
    decideIfEdgeLife :: d -> f d -> f Bool


-- data BiGraph d f = EClass d EClassId | ENode ENodeId (f EClassId)
-- deriving instance (Eq d, Eq (f EClassId)) => Eq (BiGraph d f)
-- deriving instance (Ord d, Ord (f EClassId)) => Ord (BiGraph d f)
-- deriving instance (Show d, Show (f EClassId)) => Show (BiGraph d f)

-- mkParams :: (DecideIfEdgeLife f d, Traversable f) => EGraph d f -> ImportParams (BiGraph d f) String
-- mkParams eg = ImpParams dp rel dp  True
--   where
--     dp = eClasses <> eNodes
--     rel = eNodeEdges <> eClassEdges


--     eClasses = [EClass (eciData cd) c | (c, cd) <- ILM.toList (egClassMap eg)]
--     eNodes = [ENode c cd | (c, cd) <- assocToList (egNodeAssoc eg)]

--     eClassMap = ILM.fromList [(c, EClass d c) | EClass d c <- eClasses]
--     eNodeMap = ILM.fromList [(c, ENode c d) | ENode c d <- eNodes]

--     eNodeEdges = [ (ENode c1 f, yoink c2 eClassMap, show i) | ENode c1 f <- eNodes, (i, (True, c2)) <- zip [(1::Int)..] (F.toList $ zipFoldableWith (,) (decideIfEdgeLife (dataFor (nodeCls c1)) (fmap dataFor f)) f)]
--     eClassEdges = [(yoink c eClassMap, yoink n eNodeMap, "") | (n, c) <- ILM.toList (egHashCons eg)]
--     dataFor c = case (ILM.lookup c eClassMap) of
--         Just (EClass d _) -> d
--         _ -> error $ "dataFor: " ++ show c
--     nodeCls n = ILM.partialLookup n (egHashCons eg)

-- mkParamsClassOnly :: (DecideIfEdgeLife f d, Traversable f) => EGraph d f -> ImportParams (BiGraph d f) String
-- mkParamsClassOnly eg = ImpParams dp rel dp  True
--   where
--     dp = eClasses
--     rel = eClassEdges


--     eClasses = [EClass (eciData cd) c | (c, cd) <- ILM.toList (egClassMap eg)]
--     eNodes = assocToList (egNodeAssoc eg)

--     eClassMap = ILM.fromList [(c, EClass d c) | EClass d c <- eClasses]

--     nodeEdgesFor c1 =  [ c2 | let f = assocPartialLookupByKey c1 (egNodeAssoc eg), (i, (True, c2)) <- zip [(1::Int)..] (F.toList $ zipFoldableWith (,) (decideIfEdgeLife (dataFor (nodeCls c1)) (fmap dataFor f)) f)]
--     eClassEdges = [(yoink c eClassMap, yoink c2 eClassMap, "") | (n, c) <- ILM.toList (egHashCons eg), c2 <- nodeEdgesFor n]
--     dataFor c = case (ILM.lookup c eClassMap) of
--         Just (EClass d _) -> d
--         _ -> error $ "dataFor: " ++ show c
--     nodeCls n = ILM.partialLookup n (egHashCons eg)


-- yoink :: (Show s, Coercible s Int, HasCallStack) => s -> IntLikeMap s a -> a
-- yoink s m = fromMaybe (error $ "yoink: " ++ show s) (ILM.lookup s m)

-- mkImport :: (Traversable f, DecideIfEdgeLife f d, Ord (f EClassId), Ord d, Foldable f) => EGraph d f -> GraphData (BiGraph d f) String
-- mkImport = importData . mkParamsClassOnly


-- clusterGraph :: (Eq d, Eq a) => GraphData a d -> IO (GraphData (GenCluster a) d)
-- clusterGraph g = do
--    std <- initStdGen
--    pure $ updateGraph (chineseWhispers std) g

-- instance (Pretty (f EClassId), Pretty ENodeId, Pretty EClassId , Pretty d) => Labellable (BiGraph d f) where
--   toLabelValue (EClass d c) = StrLabel $ pack $ pshow c <> "[" <> pshow d <> "]"
--   toLabelValue (ENode c d) = StrLabel $ pack $ pshow c <> ": " <> pshow d

-- printGraph :: (Labellable l, Labellable el) => GraphData l el -> Text
-- printGraph eg = printDotGraph  (graphviz  quickParams eg)
-- printGraphCluster :: (Labellable nl) => GraphData (GenCluster nl) el -> Text
-- printGraphCluster eg = printDotGraph  (graphvizClusters  clusterParams eg)

-- -- clusterParams :: GraphvizParams Node nl el Int nl
-- clusterParams = blankParams { globalAttributes = [], fmtCluster = const [], fmtNode = const [], fmtEdge = const [] }


-- egPrint :: (Traversable f, DecideIfEdgeLife f d, Pretty d, Ord d, Ord (f EClassId), Pretty (f EClassId), Foldable f, Pretty ENodeId, Pretty EClassId) => String -> EGraph d f -> IO ()
-- egPrint s eg = T.writeFile s $ printGraph (mkImport eg)
-- -- egPrint :: (Traversable f, DecideIfEdgeLife f d, Pretty d, Ord d, Ord (f EClassId), Pretty (f EClassId), Foldable f, Pretty ENodeId, Pretty EClassId) => String -> EGraph d f -> IO ()
-- -- egPrint s eg = T.writeFile s =<< printGraphCluster <$> clusterGraph (mkImport eg)

-- egPreview :: (Traversable f, DecideIfEdgeLife f d, Pretty d, Ord d, Ord (f EClassId), Pretty (f EClassId), Foldable f, Pretty ENodeId, Pretty EClassId) => EGraph d f -> IO ()
-- egPreview eg =  () <$ (forkIO  $ runGraphvizCanvas'(graphviz quickParams (mkImport eg)) Gtk)
