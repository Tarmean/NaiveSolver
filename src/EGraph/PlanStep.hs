{-|
Generate the next matching candidates, given some partially known pattern
For each candidate, produce a new state and stats like:
    - How many variables are already known (matchable using index)
    - How many other subexpressions become ground, so we can validate them with hash joins?
    - Are there locally known variables? We can't use the index but can filter while linearly scanning, e.g.: 
        - a+a has lower branching factor than a+b
        - a+f(a) means we can validate f(a) with a hash lookup, this is better
          than just an existential join because the second argument of `+` must
          be consistent with the result
    - How many new variables would we learn

This is essentially greedy SQL query planning, i.e. not very good. But
it must be sufficient, we don't have table statistics to work with most of
the time
-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
module EGraph.PlanStep (collectSteps, MatchEnv(..), DiscoverKind(..), Stats(..)) where
import EGraph.MatchTypes
    ( PGraph(definitions), PElem, ExprNodeId, ArgPos )

import Control.Monad.State
    ( forM_, gets, MonadState(state), StateT(runStateT) )
import Control.Applicative ( asum )

import Optics ( has, to, (%), non, use, At(at), Zoom(zoom) )
import Optics.State.Operators ( (%=), (?=) )

import qualified Data.Set as S
import qualified Data.Map as M

import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import EGraph.Types (Elem'(..))
import EGraph.Pending ( Pending, markKnown )
import Control.Monad.Trans.Writer ( WriterT(runWriterT), tell )
{-
 [NOTE: Pattern Matching]
 Given a rule `a + (b * a) => (b+1) * a` we must match the pattern `a + (b * a)`.

Every node in the pattern must be matched to an equality class.
   For any sub-pattern x, we will write |x| for  equality class we match x to.
A matching is consistent if, for any sub-expression such as (b * a),
     `lookup_egraph(|b| * |a|) == |b * a|`. 

A silly but trivial correct e-matching algorithm would be to
- generate all substitutions of variables=>equality classes
- filter down to consistent substitutions

It has runtime of O(|eclasses|^|variables|). The problem is NP-hard (it can be seen as subgraph isomorphism or datalog matching) but we can do much better in praxis.

The big idea is:
- Start with some partial matching, i.e. some known variables
- Given some sub-expression with known class but some unknown arguments, iterate through all instantiations which extends our partial matching
- Validate consistency as soon as possible
 
The 'extends our partial matching' phrasing hides a subtlety. There are four kinds of variables:

- We know the variable and can use it to speed up matching, e.g. using an index or the natural sorting if we know some prefix
- We don't know the variable at all and must record it
- We learn the variable while matching the curent sub-expression
  - because the variable occurs multiple times, `a+a`: check the second variable for equality directly after the match
  - because some sub-expression becomes resolvable, `a+b` but `a == f(b)`: check a's consistency after the match
-}


collectSteps :: MatchEnv -> [((ExprNodeId, Stats), MatchEnv)]
collectSteps env = runStateT (runWriterT step) env
  where
    step = do
         c <- candidates
         processElem c
         pure c

data MatchEnv = MEnv {
    possiblyInconsistent :: S.Set ExprNodeId,
    knownClass :: M.Map ExprNodeId DiscoverKind,
    nonGroundNodes :: Pending ExprNodeId,
    patGraph :: PGraph
} deriving (Eq, Ord, Show, Generic)

-- | We know the class of a node, but *how* did we find out?
data DiscoverKind = ArgOf { parent :: ExprNodeId, pos :: ArgPos } | CongruenceLookup { unblockedBy :: ExprNodeId }
  deriving (Eq, Ord, Show, Generic)

data Stats = Stats { preKnown :: S.Set ArgPos, allowsDiscovers :: S.Set ExprNodeId, allowsChecks :: [DiscoverKind], learned :: Int }
  deriving (Eq, Ord, Show, Generic)
instance Semigroup Stats where
    Stats a b c d <> Stats a' b' c' d' = Stats (a <> a') (b <> b') (c <> c')  (d + d')
instance Monoid Stats where
    mempty = Stats mempty mempty mempty 0
type M = WriterT Stats (StateT MatchEnv [])

amb :: [a] -> M a
amb ls = asum $ map pure ls

candidates :: M ExprNodeId
candidates = do
    os <- use #possiblyInconsistent
    o <- amb (S.toList os)
    #possiblyInconsistent %= S.delete o
    pure o

tellPreKnown :: HasCallStack => PElem -> M ()
tellPreKnown p = do
     known <- use #knownClass
     let knownArgs = S.fromList [idx | (idx, arg) <- zip [0..] p.argIds, M.member arg known]
     tell $ mempty { preKnown = knownArgs }

getElem :: HasCallStack => ExprNodeId -> M PElem
getElem i =
    use (#patGraph % #definitions % at i % non (error "getElem: no such element") % to unwrap)
     where
       unwrap (Left _) = error "Expected inner node, found leaf"
       unwrap (Right o) = o
markArgKnown :: ExprNodeId -> DiscoverKind -> M ()
markArgKnown node potentialReason = do
    known <- gets $ has (#knownClass % at node)
    if known
    then tellCheck potentialReason
    else do
      tellReason node potentialReason
      tell mempty { learned = 1 }

tellCheck :: DiscoverKind -> M ()
tellCheck discover = tell mempty { allowsChecks = [discover] }
tellReason :: ExprNodeId -> DiscoverKind -> M ()
tellReason node reason = #knownClass % at node ?= reason

-- | Which nodes become ground after learning the classes of nodes in `written`?
-- Being ground means no unknowns, so we can use the congruence closure hash-table to retrieve their class
newGroundNodes :: [ExprNodeId] -> M (S.Set ExprNodeId)
newGroundNodes written = zoom #nonGroundNodes $ state (markKnown written)
processElem :: ExprNodeId -> M ()
processElem pid = do
   p <- getElem pid
   tellPreKnown p
   forM_ (zip [0..] p.argIds) $ \(idx, arg) -> markArgKnown arg (ArgOf pid idx)
   newGround <- newGroundNodes (pid : p.argIds)
   forM_ newGround $ \ground -> markArgKnown ground (CongruenceLookup pid)
   tell mempty { allowsDiscovers = newGround }
   #possiblyInconsistent %= (S.\\ newGround)


