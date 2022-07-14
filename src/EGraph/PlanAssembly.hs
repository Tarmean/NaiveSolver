{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-| Takes plans from EGraph.PlanSequence and generates VM operations
 -}
module EGraph.PlanAssembly where
import EGraph.Types (Symbol)
import GHC.Generics (Generic)
import qualified Data.Set as S
import Control.Monad.State.Strict
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
import GHC.Stack (HasCallStack)
import Debug.Trace (traceM)

assemble :: MatchEnv -> [PlanStep] -> Program
assemble env ps = Program out st.nodeUniq st.varUniq
  where
    (out, st) = runState (execWriterT (mapM_ doAssembly ps)) (AssemblyState mempty mempty env.patGraph firstOccs becomeGround 0 0)

    firstOccs = M.fromListWith (<>) [ (node, [(pos, learned)])  | (learned, ArgOf _ node pos) <- M.toList env.knownClass]
    becomeGround = M.fromListWith (<>) [ (node, S.singleton learned)  | (learned, CongruenceLookup _ node) <- M.toList env.knownClass ]
assembleDebug :: MatchEnv -> [PlanStep] -> (M.Map ExprNodeId [(ArgPos, ExprNodeId)],M.Map ExprNodeId (S.Set ExprNodeId))
assembleDebug env ps = (firstOccs, becomeGround)
  where

    firstOccs = M.fromListWith (<>) [ (node, [(pos, learned)])  | (learned, ArgOf _ node pos) <- M.toList env.knownClass]
    becomeGround = M.fromListWith (<>) [ (node, S.singleton learned)  | (learned, CongruenceLookup _ node) <- M.toList env.knownClass ]



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
       Just (Left (VarId l)) -> do
           #varUniq %= max l
           pure $ Output l
       Just (Right _) -> fmap Temporary (#nodeUniq <<%= succ)
    #regMap %= M.insert eid out
    pure out

maybeNewRegFor :: ExprNodeId -> M (Reg, Bool)
maybeNewRegFor pid = do
    use (#regMap . at pid) >>= \case
        Just reg -> return (reg, False)
        Nothing -> do
            reg <- newReg pid
            #regMap %= M.insert pid reg
            return (reg, True)
regFor :: ExprNodeId -> M Reg
regFor pid = fst <$> maybeNewRegFor pid
tell1 :: VM -> M ()
tell1 = tell . Seq.singleton
loadWith :: ExprNodeId -> VM -> M ()
loadWith nid vm = do
   tell1 vm
   #isLoaded %= S.insert nid
tellJoin :: PlanStep -> M ()
tellJoin p = do
   hasParent <- gets $ has (#isLoaded . ix p.node)
   if hasParent
   then do
      parReg <- regFor p.node
      prefix <- prefixRegs p.stats.preKnown p.expr.argIds
      tell1 Join {join_class = parReg, join_symbol = p.expr.fSymbol, prefix = prefix}
   else do
      prefix <- prefixRegs p.stats.preKnown p.expr.argIds
      tell1 Startup {join_symbol = p.expr.fSymbol, prefix = prefix}

prefixRegs :: S.Set ArgPos -> [ExprNodeId] -> M [Reg]
prefixRegs known args = do
    let count = countInfix known
    traverse regFor (take count args)
    
    
doAssembly :: PlanStep -> M ()
doAssembly pstep = do
   tellJoin pstep
   -- store all values we haven't seen before into output
   overM_ (#firstOccs . at pstep.node . non mempty . each) $ \(argPos, node) -> do
     -- traceM $ "First occurence of " <> show node <> " at " <> show argPos <> "  -- " <> show pstep
     reg <- regFor node
     loadWith node (CopyValue argPos reg)
   -- do all filtering that didn't happen via joins
   forM_ pstep.stats.allowsChecks \case
     ArgOf self _ argPos -> do
         -- duplicate variable in this subexpression, e.g. second arg in ?a+?a
         reg <- regFor self
         tell1 (GuardEq argPos reg)
     CongruenceLookup self n -> do
         -- newly ground subexpression that also occurs locally in variable
         (reg, isNew) <- maybeNewRegFor self
         sink <- if isNew
             then error $ "Congruence lookup " <> show self <> " on unloaded reg for " <> show n
             else pure $ CheckEqual reg
         expr <- exprFor self
         ensureChildrenCongruenceLoaded expr
         argRegs <- traverse regFor expr.argIds
         tell1 (HashLookup expr.fSymbol argRegs sink)
   -- new ground subexpression whose class we don't know yet
     FreeJoin -> pure ()
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


exprFor :: HasCallStack => ExprNodeId -> M PElem
exprFor pid = do
    use (#pgraph . #definitions . at pid) >>= \case
        Nothing -> error "Invalid pgraph"
        Just (Right e) -> return e
        Just (Left l) -> error ("Trying to get an expression for a node that is not an expression" <> show pid <> ", output: " <> show l)
