# NaiveSolver


Contains code for E-Graph propagation and a counterexample-shrinking DSL.


In `src/BFSChoiceTree`, there is a decision tree which propagates approximations.
The approximations are E-Graphs. An example problem is given in `src/EPropTest`.

Some standard shrinking combinators are given in `src/ShrinkLoop`.
In `scripts/shrink_list.py` the core BlockXPlain algorithm is isolated and specialized for lists.
