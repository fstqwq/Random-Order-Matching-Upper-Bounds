# Lean 4 formalization of the fixed-graph upper bound

The executable `opt` computes the fixed-graph upper bound on the competitive ratio of online matching under random edge arrivals in exact rational arithmetic. Lean proves that its output bounds the ratio of every online strategy (with expectation defined as the finite average over all $n!$ vertex labelings and all $m!$ arrival orders), and that the division-free integer recurrence implemented by [`../cpp`](../cpp/README.md) computes the same value.

## Build and run

```bash
lake build
.lake/build/bin/opt < ../graphs/general/4.in
lake env lean Audit.lean
```

Input: `n m` followed by `m` zero-based edges of a nonempty simple graph. Output: the optimal ratio $V^\star(G)/\mathrm{OPT}(G)$ as a reduced fraction.

## Proof structure

The main theorems are in [Theorems.lean](OnlineMatching/Theorems.lean).

**1. Reference recurrence** ([Reference/](OnlineMatching/Reference)). A state $(H,U)$ consists of the labeled subgraph $H$ of edges observed so far and the set $U\subseteq[n]$ of currently unmatched labels, without isomorphism reduction. Each next edge $e\notin E(H)$ has conditional probability $p(e\mid H)=C(H+e)/((m-|E(H)|)C(H))$, where $C(H)$ is the number of compatible labelings $\pi$. `reference_optimal` and `reference_randomized` prove that `referenceRatio` bounds the ratio of every deterministic strategy and of every randomized strategy with rational action probabilities.

**2. Invariance and memoization** ([Invariance/](OnlineMatching/Invariance)). The Bellman value is invariant under any permutation of the observed labels and under reordering the edge history or the unmatched list. Unseen labels are interchangeable, so a state only records its observed labels. The compatible-labeling count $C(H)$ is computed by a degree-pruned depth-first search (`count_fits`), and a hash-map cache memoizes the recurrence. `memoized_eq_reference` proves that the resulting solver equals `referenceRatio` for every relabeling oracle; the oracle need not produce canonical forms.

**3. Lean solver** ([Final.lean](OnlineMatching/Final.lean)). The executable instantiates the relabeling oracle with color refinement, branching on non-singleton cells and pruning twin vertices. `Final.opt_correct` and `Final.opt_randomized` state that the fraction printed by `opt` bounds the ratio of every online strategy.

**4. Integer recurrence** ([IntegerSolver.lean](OnlineMatching/Invariance/IntegerSolver.lean), [IntegerMemo.lean](OnlineMatching/Invariance/IntegerMemo.lean)). Multiplying the recurrence by $(m-|E(H)|)!\,C(H)$ gives a natural-number recurrence; `IntegerSolver.ratio_reference` proves that it yields `referenceRatio`. `IntegerMemo.solve_correct` proves that its memoized version returns the uncached value from every sound cache, and `warmup_root_ratio` extends this to arbitrary cache prewarming followed by the root call. `oracle_independent` and `normalized_reference` show that the value does not depend on the relabeling chosen at each step, and `sumNat_perm` that it does not depend on the order of summation. See [the C++ README](../cpp/README.md#correspondence-with-lean) for the correspondence with `solver.cpp`.

Shared definitions (Bellman models, offline matchings, permutations) are in [Basic.lean](OnlineMatching/Basic.lean); [Main.lean](Main.lean) is the command-line entry point.

## Axioms

All theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound` (verified by `Audit.lean`), with no `sorry`, `native_decide` or `implemented_by`.
