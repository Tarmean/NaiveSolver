{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module EGraph.ByteCodeVM where

import Data.Generics.Labels ()
import Control.Lens

import Data.Maybe (fromJust)
import qualified Data.Vector.Unboxed.Mutable as VU
import qualified Data.Sequence as Seq
import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString as BS
import GHC.Word
import GHC.Generics
import Control.Monad.State
import EGraph.PlanAssembly
import EGraph.Class
import Control.Monad.Primitive
import EGraph.PlanTypes
import qualified Data.Vector.Unboxed as V
import Monad.Amb
import Control.Applicative


data NaiveVMState s = NVM { outVec :: VU.MVector s Int, tempVec :: VU.MVector s Int, curMatch :: Match }
  deriving (Generic)
type EvalM m a = AmbT () (StateT (NaiveVMState (PrimState m)) m) a

allMatches :: (MonadEgg m, PrimMonad m) => Program -> (V.Vector Int -> m ()) -> m ()
allMatches (prog :: Program) k = do
    outVec <- VU.new prog.outCount
    tempVec <- VU.new prog.tempCount
    let emptyState = NVM outVec  tempVec V.empty
    flip evalStateT emptyState $ runAmb (mapM_ eval prog.ops) (\_ _ -> use #outVec >>= \v -> lift (V.freeze v >>= k)) (pure ())

writeReg :: (PrimMonad m, MonadEgg m) => Int -> Reg -> EvalM m ()
writeReg val (Temporary regId) = #tempVec $= \v -> VU.write v regId val
writeReg val (Output regId) = #outVec $= \v -> VU.write v regId val

-- Invariants:
-- - Registers are only written once
-- - Registers aren't read before they are written
-- - The current match isn't read after the next Join call
-- It might be nicer to split joins and the non-control-flow ops
eval :: (PrimMonad m, MonadEgg m) => VM -> EvalM m ()
eval (CopyValue pos reg) = do
    val <- readCur pos
    writeReg val reg
eval (GuardEq pos reg) = do
    new <- readCur pos
    old <- readReg reg
    guard (old == new)
eval (Join classReg symbol prefixRegs) = do
    classId <- readReg classReg
    prefix <- loadRegs prefixRegs
    withFuture $ \cont -> do
        forMatches classId symbol prefix $ \match -> do
            #curMatch .= match
            cont ()
eval (Startup symbol prefixRegs) = do
    prefix <- loadRegs prefixRegs
    withFuture $ \cont -> do
        forClasses $ \classId -> do
            forMatches classId symbol prefix $ \match -> do
                #curMatch .= match
                cont ()
eval (HashLookup sym regs out)= do
    args <- V.fromList <$> traverse readReg regs
    val <- lift $ resolve sym args
    case val of
      Nothing -> empty
      Just new ->
        case out of
          StoreInto reg -> writeReg new reg
          CheckEqual reg -> do
              old <- readReg reg
              when (old /= new) empty
          Ignore -> pure ()
loadRegs :: (MonadEgg m, PrimMonad m) => [Reg] -> EvalM m (V.Vector Int)
loadRegs ls = V.fromList <$> traverse readReg ls

($=) :: MonadState s m => Lens' s a -> (a -> m ()) -> m ()
($=) l f = do
  v <- use l
  f v

readReg :: (PrimMonad m, MonadEgg m) => Reg -> EvalM m Int
readReg (Temporary regId) = use #tempVec >>= \v -> VU.read v regId
readReg (Output regId) = use #outVec >>= \v -> VU.read v regId
readCur :: (PrimMonad m, MonadEgg m) => Int -> EvalM m Int
readCur pos = do
  cur <- use #curMatch
  pure $ fromJust $ cur ^? ix pos


data ProgramBuilder = Program { vmCode :: BB.Builder, tempOffset :: Int }




-- emitVM :: VM -> BuilderM ()
-- emitVM (CopyValue pos into)  = pure ()



