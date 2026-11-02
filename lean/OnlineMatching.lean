import OnlineMatching.Theorems
import OnlineMatching.Invariance.Warmup
import OnlineMatching.Invariance.IntegerScaling
import OnlineMatching.Invariance.IntegerSolver
import OnlineMatching.Invariance.IntegerMemo

/-!
# Online matching under random edge arrivals

* `OnlineMatching.Basic`: Bellman models, offline matchings, permutations.
* `OnlineMatching.Reference`: the reference Bellman recurrence on labeled
  observed graphs, and its optimality against every online strategy.
* `OnlineMatching.Invariance`: permutation invariance, list invariance,
  compression of unseen labels, labeling counts and memoization; together they
  prove that the memoized solver equals the reference value for every
  relabeling oracle.
* `OnlineMatching.Final`: the color-refinement oracle and the solver run by
  the executable.
* `OnlineMatching.Theorems`: the main theorems.
-/
