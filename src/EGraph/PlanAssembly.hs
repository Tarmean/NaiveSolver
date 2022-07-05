{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-| Takes plans from EGraph.PlanSequence and generates VM operations
 -}
module EGraph.PlanAssembly where
import EGraph.Types (Symbol)
import GHC.Generics (Generic)
import qualified Data.Set as S
import Control.Monad.State
import EGraph.PlanStep
import EGraph.PlanSequence
import qualified Data.Map as M
import EGraph.Types
import Control.Monad.Trans.Writer
import qualified Data.Sequence as Seq
import EGraph.PlanTypes

import Data.Generics.Labels ()
import Control.Lens
import Optics.Utils
assemble :: MatchEnv -> [PlanStep] -> Program
assemble env ps = Program out st.varUniq st.nodeUniq
  where
    (out, st) = runState (execWriterT (mapM_ doAssembly ps)) (AssemblyState mempty mempty env.patGraph firstOccs becomeGround 0 0)
    firstOccs = M.fromListWith (<>) [ (node, [(pos, learned)])  | (learned, ArgOf node pos) <- M.toList env.knownClass]
    becomeGround = M.fromListWith (<>) [ (node, S.singleton learned)  | (learned, CongruenceLookup node) <- M.toList env.knownClass ]



data AssemblyState = AssemblyState
  { regMap :: M.Map ExprNodeId Reg
  , isLoaded :: S.Set ExprNodeId
  , pgraph :: PGraph
  , firstOccs :: M.Map ExprNodeId [(ArgPos, ExprNodeId)]
  , becomeGround :: M.Map ExprNodeId (S.Set ExprNodeId)
  , varUniq :: Int
  , nodeUniq :: Int
  }
  deriving (Eq, Ord, Show, Generic)


type M = WriterT (Seq.Seq VM) (State AssemblyState)

newReg :: ExprNodeId -> M Reg
newReg eid = do
    out <- use (#pgraph . #definitions . at eid) >>= \case
       Nothing -> error "Invalid pgraph"
       Just (Left _) -> fmap Output (#varUniq <%= succ)
       Just (Right _) -> fmap Temporary (#nodeUniq <%= succ)
    #regMap %= M.insert eid out
    pure out

regFor :: ExprNodeId -> M Reg
regFor pid = do
    use (#regMap . at pid) >>= \case
        Just reg -> return reg
        Nothing -> do
            reg <- newReg pid
            #regMap %= M.insert pid reg
            return reg
tell1 :: VM -> M ()
tell1 = tell . Seq.singleton
loadWith :: ExprNodeId -> VM -> M ()
loadWith nid vm = do
   tell1 vm
   #isLoaded %= S.insert nid
doAssembly :: PlanStep -> M ()
doAssembly pstep = do
   -- store all values we haven't seen before into output
   overM_ (#firstOccs . at pstep.node . non mempty . each) $ \(argPos, node) -> do
     reg <- regFor node
     loadWith node (CopyValue argPos reg)
   -- do all filtering that didn't happen via joins
   forM_ pstep.stats.allowsChecks \case
     ArgOf node argPos -> do
         -- duplicate variable in this subexpression, e.g. second arg in ?a+?a
         reg <- regFor node
         tell1 (GuardEq argPos reg)
     CongruenceLookup node -> do
         -- newly ground subexpression that also occurs locally in variable
         expr <- exprFor node
         ensureChildrenCongruenceLoaded expr
         reg <- regFor node
         argRegs <- traverse regFor expr.argIds
         tell1 (HashLookup expr.fSymbol argRegs (CheckEqual reg))
   -- new ground subexpression whose class we don't know yet
   overM_ (#becomeGround . at pstep.node . non mempty . folded) $ \nid -> do
     node <- exprFor nid
     loadCongruence nid node

markLoaded :: ExprNodeId -> M ()
markLoaded n = #isLoaded %= S.insert n

ensureChildrenCongruenceLoaded :: PElem -> M ()
ensureChildrenCongruenceLoaded node = forChildrenOf node loadCongruence
loadCongruence :: ExprNodeId -> PElem -> M ()
loadCongruence pid node = do
    isLoaded <- gets (has $ #isLoaded . ix pid)
    when (not isLoaded) $ do
        ensureChildrenCongruenceLoaded node
        outReg <- regFor pid
        argRegs <- traverse regFor node.argIds
        loadWith pid (HashLookup node.fSymbol argRegs (StoreInto outReg))
forChildrenOf :: PElem -> (ExprNodeId -> PElem -> M ()) -> M ()
forChildrenOf node f = do
        forM_ node.argIds $ \child -> do
            overM_ (#pgraph . #definitions . at child) \case
              Just (Right expr) -> f child expr
              _ -> pure ()


exprFor :: ExprNodeId -> M PElem
exprFor pid = do
    use (#pgraph . #definitions . at pid) >>= \case
        Nothing -> error "Invalid pgraph"
        Just (Right e) -> return e
        Just (Left _) -> error "Trying to get an expression for a node that is not an expression"
    
