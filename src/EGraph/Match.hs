{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
module EGraph.Match where


import EGraph.PlanTypes
import EGraph.PlanSequence ( greedyMatching )
import EGraph.PlanAssembly (assemble)
import EGraph.Pure
import Control.Monad.State
import EGraph.ByteCodeVM (allMatches)
import Control.Applicative
import EGraph.Class (MonadEgg (..))
import Control.Monad.Primitive (PrimMonad (..))


printResults :: Program -> PureEggT IO ()
printResults p = allMatches p $ \m -> lift (print m)

compilePattern :: PGraph -> Program
compilePattern pgraph = assemble env steps
  where (steps, env) = greedyMatching pgraph

newtype PureEggT m a = PureEggT { runPureEggT :: StateT EGraph m a }
  deriving newtype (Monad, MonadTrans, Functor, Applicative, Alternative, MonadPlus)
instance PrimMonad m => PrimMonad (PureEggT m) where
  type PrimState (PureEggT m) = PrimState m
  primitive = lift . primitive
instance MonadState s m => MonadState s (PureEggT m) where
  get = lift get
  put = lift . put
instance Monad m => MonadEgg (PureEggT m) where
  forMatches cid sym pre k = pure ()
  forClasses k = pure ()
  resolve = undefined

