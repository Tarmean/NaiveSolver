EGraph implementation that is reasonably performant but currently does not support propagation. We use a fork of the Overeasy library instead, which supports propagation but not pattern matching. Both together would make a halfway decent implementation.

This implementation is interesting because it performs seminaive evaluation, performing *much* better if few classes are modified since the previous run. This works by having two copies of each table. We rewrite query into a series of querywhich uses different combinations of old and new tables, with the condition that at least one new table is in each query.


We also use hashtable lookups in queries to speed things up, but someone working on the Egg egraph library discovered this technique independently. (actually two people working on egg discovered it independently)
