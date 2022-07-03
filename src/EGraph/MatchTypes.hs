module EGraph.MatchTypes where
import qualified Data.Map as M
import qualified Data.Set as S
import EGraph.Types (Elem'(..))
import GHC.Generics (Generic)

newtype Symbol = Symbol Int
  deriving (Eq, Ord, Show, Generic)
type ArgPos = Int


newtype ExprNodeId = EId Int
  deriving (Eq, Ord, Show, Generic)
-- data Matcher = KnownClassAt ArgPos ExprNodeId | EqShallow ArgPos ExprNodeId | KnownClass ElemId
--   deriving (Eq, Ord, Show)
data MatchArgs = MArgs {
   -- | How much of the prefix is known
   -- long prefix => efficiently matchable without index if the data is sorted
   matchedPrefix :: Int,
   -- | Known args, used to quickly filter with an index
   knownArgs :: M.Map ArgPos ExprNodeId,
   -- | Unknown args, we should store them if they are needed later
   learnedArgs :: M.Map ArgPos ExprNodeId,
   -- | Unknown args, but they become known by other arguments in the same match
   --   - lowers branching factor :)
   --   - linear scan through all candidate matches :(
   filterable :: M.Map ArgPos ExprNodeId
}
  deriving (Eq, Ord, Show, Generic)
data MatchGuards = MGuard {
    -- | The last of the variable of some inner node are discovered by this match
    -- =>we can use the congruence closure mechanism to retrieve its class
    newlyResolvable :: [ExprNodeId],
    -- | Some (unknown) argument is repeated `a+a`
    -- => useless for indexing but great for filtering
    -- theoretically we could add an index for positional repetition
    argRepeated :: [S.Set ArgPos]
    }
  deriving (Eq, Ord, Show, Generic)
data MatchFilter = F {
    hasSymb :: Symbol,
    argMatch :: MatchArgs,
    matchGuards :: MatchGuards,
    matches :: ExprNodeId,
    classKnown :: Bool
  }
  deriving (Eq, Ord, Show, Generic)
  
type PElem = Elem' ExprNodeId
newtype VarId = VarId Int
 deriving (Eq, Ord, Show)
type Pos = Int
data PGraph = PGraph {
    definitions :: M.Map ExprNodeId (Either VarId PElem),
    freeVars :: M.Map ExprNodeId (S.Set ExprNodeId)
 }
  deriving (Eq, Ord, Show, Generic)
