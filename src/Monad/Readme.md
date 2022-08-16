Monad transformers used for the shrinking DSL.


Oracle: Coroutine communication with the oracle
Snapshot: Save and restore state when backtracking
Amb: Backtracking search with cut, can register callback to run on backtrack
Graph: Track graph information about the current term
Zipper: Cursor api to walk through arbitrary terms. Some variants, e.g. one with down and up for self-recursive types
Critical: Remember identifiers which cannot be removed by shrinking
Levels: Breadth first search, taken from 'algebras for weighted search'
ConcreteBreadthFirst: Less efficient api of Levels
