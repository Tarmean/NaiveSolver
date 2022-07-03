{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-| Takes plans from EGraph.PlanSequence and generates VM operations
 -}
module EGraph.PlanAssembly where
import EGraph.MatchTypes (ArgPos)
import EGraph.Types (Symbol)
import GHC.Generics (Generic)

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
