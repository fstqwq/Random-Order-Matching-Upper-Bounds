import OnlineMatching.Reference.Experiment
import OnlineMatching.Final

/-!
# Main theorems

1. `reference_optimal`, `reference_randomized`: the reference Bellman value
   `referenceRatio` bounds the ratio of every deterministic strategy and of every
   randomized strategy with rational action probabilities.
2. `memoized_eq_reference`: for every relabeling oracle, the memoized solver
   equals `referenceRatio`.
3. `Final.opt_correct`, `Final.opt_randomized`: the value printed by the
   executable bounds the ratio of every strategy.
-/

namespace OnlineMatching

open ImplementationGraph

theorem reference_optimal (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hne : edges ≠ []) :
    ∀ strategy, Experiment.experimentExpectation n edges strategy /
      (denominator n edges : Rat) ≤ referenceRatio n edges :=
  (Experiment.experiment_ratio_optimal n edges hn hs hb hne).1

theorem reference_randomized (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hne : edges ≠ []) :
    ∀ strategy, Randomized.Valid strategy → Randomized.experimentExpectation n edges strategy /
      (denominator n edges : Rat) ≤ referenceRatio n edges :=
  (Randomized.experiment_ratio_optimal n edges hn hs hb hne).1

theorem memoized_eq_reference (oracle : Solver.Oracle) (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    Memoized.ratio oracle n edges = referenceRatio n edges := by
  rw [Memoized.ratio_eq]
  exact Uncached.ratio_reference oracle n edges hn hs hb

theorem Final.opt_correct (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hne : edges ≠ []) :
    ∀ strategy, Experiment.experimentExpectation n edges strategy /
      (denominator n edges : Rat) ≤ Final.opt n edges := by
  rw [Final.opt_eq_reference n edges hn hs hb]
  exact reference_optimal n edges hn hs hb hne

theorem Final.opt_randomized (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hne : edges ≠ []) :
    ∀ strategy, Randomized.Valid strategy → Randomized.experimentExpectation n edges strategy /
      (denominator n edges : Rat) ≤ Final.opt n edges := by
  rw [Final.opt_eq_reference n edges hn hs hb]
  exact reference_randomized n edges hn hs hb hne

end OnlineMatching
