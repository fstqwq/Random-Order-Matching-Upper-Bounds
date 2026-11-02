import OnlineMatching

/-!
# Axiom audit

Run `lake env lean Audit.lean`. Each `#print axioms` lists the axioms used by a
theorem.
-/

/-! ## Main theorems -/

#print axioms OnlineMatching.reference_optimal
#print axioms OnlineMatching.reference_randomized
#print axioms OnlineMatching.memoized_eq_reference
#print axioms OnlineMatching.Final.opt_eq_reference
#print axioms OnlineMatching.Final.opt_correct
#print axioms OnlineMatching.Final.opt_randomized

/-! ## Reference recurrence -/

#print axioms OnlineMatching.value_correct
#print axioms OnlineMatching.ImplementationGraph.reference_ratio_optimal
#print axioms OnlineMatching.Experiment.experiment_ratio_optimal
#print axioms OnlineMatching.Randomized.experiment_ratio_optimal

/-! ## Invariance and memoization -/

#print axioms OnlineMatching.Symmetry.value_map
#print axioms OnlineMatching.CanonicalState.value_canonical
#print axioms OnlineMatching.CollapsedBellman.value_succ_compressed
#print axioms OnlineMatching.CountingEndToEnd.count_fits_eq_compatibleCount
#print axioms OnlineMatching.Uncached.ratio_reference
#print axioms OnlineMatching.AvailableOrder.solve_perm
#print axioms OnlineMatching.Memo.correct_memo
#print axioms OnlineMatching.Memoized.ratio_eq

/-! ## Division-free integer recurrence and cache prewarming -/

#print axioms OnlineMatching.IntegerSolver.term_scaled
#print axioms OnlineMatching.IntegerSolver.solve_scaled
#print axioms OnlineMatching.IntegerSolver.ratio_reference
#print axioms OnlineMatching.Memo.warmup_then_root

#eval OnlineMatching.IntegerSolver.ratio OnlineMatching.RefinedOrder.oracle 2 [(0,1)]
#eval OnlineMatching.IntegerSolver.ratio OnlineMatching.RefinedOrder.oracle 4 [(0,3),(1,2),(1,3),(2,3)]
#print axioms OnlineMatching.IntegerSolver.ratio_eq_final
#print axioms OnlineMatching.IntegerSolver.sumNat_perm

/-! ## Memoized integer recurrence (the C++ solver) -/

#print axioms OnlineMatching.IntegerMemo.solve_correct
#print axioms OnlineMatching.IntegerMemo.warmup_root_correct
#print axioms OnlineMatching.IntegerMemo.warmup_root_ratio
#print axioms OnlineMatching.IntegerMemo.publish_solve
#print axioms OnlineMatching.IntegerMemo.two_level_hit
#print axioms OnlineMatching.IntegerMemo.copy_hit
#print axioms OnlineMatching.IntegerMemo.oracle_independent
#print axioms OnlineMatching.IntegerMemo.normalized_reference
#print axioms OnlineMatching.IntegerMemo.stateKey_injective
#print axioms OnlineMatching.IntegerMemo.child_fuel

/-! ## Small examples

Maximum matchings checked by the kernel, and reference ratios of a single edge
and of the four-vertex graph `G4` (expected `1` and `3/4`).
-/

example : OnlineMatching.Offline.matching [(0, 3), (1, 2), (1, 3), (2, 3)] 2 [0, 1, 2, 3] = 2 := by
  decide

example : OnlineMatching.Offline.matching
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5)]
    3 [0, 1, 2, 3, 4, 5] = 3 := by
  decide

#eval OnlineMatching.ImplementationGraph.referenceRatio 2 [(0, 1)]
#eval OnlineMatching.ImplementationGraph.referenceRatio 4 [(0, 3), (1, 2), (1, 3), (2, 3)]
