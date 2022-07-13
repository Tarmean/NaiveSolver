{-# OPTIONS_GHC -Wno-missing-methods #-}
module EGraph.PlanTypes (module EGraph.PlanTypes, Symbol(..)) where
import GHC.Generics
import EGraph.Types
import qualified Data.Set as S
import qualified Data.Map as M
import EGraph.Pending
import qualified Data.Sequence as Seq

type ArgPos = Int
newtype ExprNodeId = EId Int
  deriving (Eq, Ord, Show, Generic)
type PElem = Elem' ExprNodeId

data VOP = V VarId | P Pat
  deriving Show
newtype Pat = Pat (Elem' VOP)
  deriving Show
instance Num VOP where
    fromInteger a = V (VarId $ fromInteger a)
pap :: Int -> [VOP] -> Pat
pap n args = (Pat $ Elem (Symbol n) args)
ppap :: Int -> [VOP] -> VOP
ppap n args = P (pap n args)



newtype VarId = VarId Int
 deriving (Eq, Ord, Show)

data Program = Program {ops :: Seq.Seq VM, tempCount :: Int, outCount :: Int }
  deriving (Eq, Ord, Show, Generic)
data PGraph = PGraph {
    definitions :: M.Map ExprNodeId (Either VarId PElem)
    -- freeVars :: M.Map ExprNodeId (S.Set ExprNodeId)
 }
  deriving (Eq, Ord, Show, Generic)


data PlanStep = PlanStep { stats :: Stats, node :: ExprNodeId, expr :: PElem }
  deriving (Eq, Ord, Show, Generic)

-- | A VM instruction.
-- The VM has
--   - A number of registers
--   - A current cursor to a specific DB row
data VM
  = CopyValue ArgPos Reg -- ^ Copy from the active row to a register
  | HashLookup Symbol [Reg] RegOut -- ^ Use the congruence closure hash-map to retrieve a value
  | GuardEq ArgPos Reg -- ^ We already know what this arg should be, filter!
  | Join { join_class :: Reg, join_symbol :: Symbol, prefix :: [Reg] } -- ^ Join a new table, this acts as a nested loop
  | Startup { join_symbol :: Symbol, prefix :: [Reg] } -- ^ Like Join, but we don't know the equality class the table is in so also loop over all classes
  deriving (Eq, Ord, Show, Generic)

data RegOut
    = StoreInto Reg  -- ^ We need this value later, store it
    | CheckEqual Reg -- ^ We already know this value, but if comparison with
                     -- the already stored version fails the partial solution is inconsistent and
                     -- we can skip forward
    | Ignore -- ^ We don't actually need this value, just had to ensure the lookup succeeds
  deriving (Eq, Ord, Show, Generic)

data Reg = Temporary Int | Output Int
  deriving (Eq, Ord, Show, Generic)


data MatchEnv = MEnv {
    possiblyInconsistent :: S.Set ExprNodeId,
    knownClass :: M.Map ExprNodeId DiscoverKind,
    nonGroundNodes :: Pending ExprNodeId,
    patGraph :: PGraph
} deriving (Eq, Ord, Show, Generic)

-- | We know the class of a node, but *how* did we find out?
data DiscoverKind = ArgOf { self :: ExprNodeId, parent :: ExprNodeId, pos :: ArgPos } | CongruenceLookup { self :: ExprNodeId, unblockedBy :: ExprNodeId } | FreeJoin
  deriving (Eq, Ord, Show, Generic)

countInfix :: S.Set ArgPos -> Int
countInfix s = go 0
  where
   go idx
     | S.member idx s = go (idx+1)
     | otherwise = idx
data Stats = Stats {
    preKnown :: S.Set ArgPos,
    allowsDiscovers :: S.Set ExprNodeId,
    allowsChecks :: S.Set DiscoverKind,
    learned :: Int
} deriving (Eq, Ord, Show, Generic)
instance Semigroup Stats where
    Stats a b c d <> Stats a' b' c' d' = Stats (a <> a') (b <> b') (c <> c')  (d + d')
instance Monoid Stats where
    mempty = Stats mempty mempty mempty 0
