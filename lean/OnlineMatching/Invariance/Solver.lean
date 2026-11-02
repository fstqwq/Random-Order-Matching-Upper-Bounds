import OnlineMatching.Invariance.Compression
import OnlineMatching.Invariance.Counting

/-!
# Relabeled solver

For any relabeling oracle, `Uncached.solve` relabels each child state, prunes
by the resource bound and uses the counts above. `Uncached.ratio_reference`
proves that it equals `referenceRatio`, and `AvailableOrder.solve_perm` shows
that the order of the unmatched list does not matter.
-/

/-! ## Relabeled recurrence -/

namespace OnlineMatching.Solver

open ImplementationGraph CanonicalState

abbrev Oracle := (k : Nat) → (g : Graph Nat) → CanonicalResult k g

structure State where
  seen : Nat
  observed : List Offline.Edge
  available : List Nat

structure Valid (n : Nat) (s : State) : Prop where
  seen : s.seen ≤ n
  nodup : s.observed.Nodup
  sorted : ∀ e ∈ s.observed, e.1 < e.2
  bounds : ∀ e ∈ s.observed, e.1 < s.seen ∧ e.2 < s.seen
  free : ∀ v ∈ s.available, v < s.seen
  freeNodup : s.available.Nodup

def expand (n : Nat) (s : State) : ImplementationGraph.State :=
  ⟨s.observed, Implementation.expand n s.seen s.available⟩

def normalize (oracle : Oracle) (s : State) : State :=
  let r := oracle s.seen (CanonicalState.graph s.observed)
  ⟨s.seen, CanonicalState.edges s.seen r.canonical, s.available.map r.permutation.forward⟩

def reveal (s : State) (e : Offline.Edge) (added : Nat) : State :=
  ⟨s.seen + added, e :: s.observed, Implementation.revealList s.available s.seen added⟩

def remove (s : State) (e : Offline.Edge) : State :=
  { s with available := Offline.remove s.available e }

def weight (n : Nat) (original : List Offline.Edge) (s : State)
    (e : Offline.Edge) (multiplicity : Nat) : Rat :=
  ((multiplicity * Anonymous.compatibleCount n original (e :: s.observed) : Nat) : Rat) /
    (((original.length - s.observed.length) *
      Anonymous.compatibleCount n original s.observed : Nat) : Rat)

def branch (oracle : Oracle) (continuation : State → Rat) (s : State)
    (e : Offline.Edge) (added : Nat) : Rat :=
  let child := reveal s e added
  let reject := continuation (normalize oracle child)
  if decide (Offline.legal child.available e) then
    max reject (1 + continuation (normalize oracle (remove child e)))
  else reject

def solve (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Nat → State → Rat
  | 0, _ => 0
  | fuel+1, s =>
    if s.observed.length < original.length then
      total (Transitions.remainingEdges (Transitions.freshPairs s.seen) s.observed)
        (fun e => weight n original s e 1 * branch oracle (solve oracle n original fuel) s e 0) +
      (if s.seen < n then total (List.range s.seen)
        (fun u => weight n original s (u,s.seen) (n-s.seen) *
          branch oracle (solve oracle n original fuel) s (u,s.seen) 1) else 0) +
      (if s.seen+1 < n then
        weight n original s (s.seen,s.seen+1) ((n-s.seen)*(n-s.seen-1)/2) *
          branch oracle (solve oracle n original fuel) s (s.seen,s.seen+1) 2 else 0)
    else 0

theorem normalize_valid (oracle : Oracle) (n : Nat) (s : State) (h : Valid n s) :
    Valid n (normalize oracle s) := by
  let r := oracle s.seen (CanonicalState.graph s.observed)
  refine ⟨h.seen, edges_nodup _ _, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact ((mem_edges s.seen r.canonical e).mp he).1
  · intro e he
    obtain ⟨h1,h2,_⟩ := (mem_edges s.seen r.canonical e).mp he
    change e.1 < s.seen ∧ e.2 < s.seen
    exact ⟨by omega,h2⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact (r.permutation.finite (Nat.le_refl s.seen)).forward_lt u (h.free u hu)
  · exact List.Pairwise.map _ (fun _ _ hne he =>
      hne (r.permutation.toPermutation.injective he)) h.freeNodup

theorem reveal_valid (n : Nat) (s : State) (e : Offline.Edge) (added : Nat)
    (h : Valid n s) (hk : s.seen+added ≤ n) (hs : e.1 < e.2)
    (hb : e.1 < s.seen+added ∧ e.2 < s.seen+added) (hf : e ∉ s.observed) :
    Valid n (reveal s e added) := by
  refine ⟨hk, List.nodup_cons.mpr ⟨hf,h.nodup⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hs
    · exact h.sorted a ha
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb
    · obtain ⟨h1,h2⟩ := h.bounds a ha
      exact ⟨by simp only [reveal]; omega, by simp only [reveal]; omega⟩
  · exact Implementation.reveal_bound s.seen added s.available h.free
  · exact Implementation.revealList_nodup s.available s.seen added h.freeNodup h.free

theorem remove_valid (n : Nat) (s : State) (e : Offline.Edge) (h : Valid n s) :
    Valid n (remove s e) :=
  ⟨h.seen,h.nodup,h.sorted,h.bounds,
    Implementation.remove_bound s.seen s.available e h.free,
    (h.freeNodup.erase e.1).erase e.2⟩

theorem normalize_value (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : State) (fuel : Nat) (h : Valid n s)
    (hn : original.Nodup) (ho : ∀ e ∈ original, e.1 < e.2)
    (hb : ∀ e ∈ original, e.1 < n ∧ e.2 < n) :
    value (referenceModel n original) fuel (expand n (normalize oracle s)) =
      value (referenceModel n original) fuel (expand n s) :=
  value_canonical original s.observed s.available
    (oracle s.seen (CanonicalState.graph s.observed)) h.seen fuel hn ho hb
    h.nodup h.sorted h.bounds

theorem weight_reference (n : Nat) (original : List Offline.Edge) (s : State)
    (e : Offline.Edge) (mult : Nat) (h : Valid n s)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (he : e.1 < e.2) (hf : e ∉ s.observed) :
    weight n original s e mult =
      (mult : Rat) * (referenceModel n original).probability (expand n s) e := by
  change weight n original s e mult = (mult : Rat) *
    (referenceModel n original).probability ⟨s.observed, Implementation.expand n s.seen s.available⟩ e
  rw [reference_weight_formula n original s.observed _ e hn ho hb h.nodup
    (fun a ha => Nat.le_of_lt (h.sorted a ha)) (Nat.le_of_lt he) hf]
  simp only [weight, Rat.natCast_mul, Rat.div_def, Rat.mul_assoc]

theorem branch_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : State) (e : Offline.Edge) (added fuel : Nat) (continuation : State → Rat)
    (hc : ∀ t, Valid n t → continuation t = value (referenceModel n original) fuel (expand n t))
    (h : Valid n s) (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hk : s.seen+added ≤ n) (he : e.1 < e.2)
    (heb : e.1 < s.seen+added ∧ e.2 < s.seen+added) (hf : e ∉ s.observed) :
    branch oracle continuation s e added =
      CollapsedBellman.branch (value (referenceModel n original) fuel) (expand n s) e := by
  have hr := reveal_valid n s e added h hk he heb hf
  have ha := remove_valid n (reveal s e added) e hr
  have hrej := (hc _ (normalize_valid oracle n _ hr)).trans
    (normalize_value oracle n original _ fuel hr hn ho hb)
  have hacc := (hc _ (normalize_valid oracle n _ ha)).trans
    (normalize_value oracle n original _ fuel ha hn ho hb)
  have hreveal : expand n (reveal s e added) = ImplementationGraph.reject (expand n s) e := by
    simp only [expand, reveal, ImplementationGraph.reject]
    rw [Implementation.expand_reveal n s.seen added s.available hk]
  have hremove : expand n (remove (reveal s e added) e) =
      ImplementationGraph.accept (expand n s) e := by
    simp only [expand, reveal, remove, ImplementationGraph.accept]
    rw [Implementation.reveal_accept n s.seen added s.available e hk heb]
  rw [hreveal] at hrej
  rw [hremove] at hacc
  have hlegal : decide (Offline.legal (reveal s e added).available e) =
      decide (Offline.legal (expand n s).free e) := by
    change decide (Offline.legal (Implementation.revealList s.available s.seen added) e) =
      decide (Offline.legal (Implementation.expand n s.seen s.available) e)
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      Implementation.reveal_legal n s.seen added s.available e hk heb
  simp only [branch, hrej, hacc, hlegal, CollapsedBellman.branch]

/-- The finite-fuel three-loop recursion with canonicalized children computes
exactly the full labeled reference value, using the canonicalizer through its
adjacency relabeling contract. -/
theorem solve_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : State) (h : Valid n s)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    solve oracle n original fuel s = value (referenceModel n original) fuel (expand n s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [solve]
    by_cases ht : s.observed.length < original.length
    · rw [ite_eq_left ht]
      change _ = value (referenceModel n original) (fuel+1)
        ⟨s.observed,Implementation.expand n s.seen s.available⟩
      rw [CollapsedBellman.value_succ_compressed n s.seen original s.observed s.available fuel
        hn ho hb h.nodup (fun e he => Nat.le_of_lt (h.sorted e he)) h.bounds h.free h.seen ht]
      congr 1
      · congr 1
        · apply total_congr
          intro e he
          have hem := List.mem_filter.mp he
          have hep := (Transitions.mem_freshPairs s.seen e.1 e.2).mp hem.1
          have hef : e ∉ s.observed := by simpa only [decide_eq_true_eq] using hem.2
          have heb : e.1 < s.seen+0 ∧ e.2 < s.seen+0 := ⟨by omega, by omega⟩
          rw [weight_reference n original s e 1 h hn ho hb hep.1 hef,
            branch_reference oracle n original s e 0 fuel _ ih h hn ho hb
              (by simpa using h.seen) hep.1 heb hef, Rat.natCast_ofNat, Rat.one_mul]
          rfl
        · by_cases hk : s.seen < n
          · rw [ite_eq_left hk, ite_eq_left hk]
            apply total_congr
            intro u hu
            have hu' := List.mem_range.mp hu
            have hef : (u,s.seen) ∉ s.observed := by
              intro he
              have := (h.bounds _ he).2
              omega
            rw [weight_reference n original s (u,s.seen) (n-s.seen) h hn ho hb hu' hef,
              branch_reference oracle n original s (u,s.seen) 1 fuel _ ih h hn ho hb
                (by omega) hu' ⟨by omega,by omega⟩ hef]
            rfl
          · simp only [ite_eq_right hk]
      · by_cases hk : s.seen+1 < n
        · rw [ite_eq_left hk, ite_eq_left hk]
          have hef : (s.seen,s.seen+1) ∉ s.observed := by
            intro he
            have := (h.bounds _ he).1
            omega
          rw [weight_reference n original s (s.seen,s.seen+1)
              ((n-s.seen)*(n-s.seen-1)/2) h hn ho hb (by omega) hef,
            branch_reference oracle n original s (s.seen,s.seen+1) 2 fuel _ ih h hn ho hb
              (by omega) (by omega) ⟨by omega,by omega⟩ hef]
          rfl
        · simp only [ite_eq_right hk]
    · rw [ite_eq_right ht]
      exact (CollapsedBellman.value_succ_terminal n original (expand n s) fuel ht).symm

def initial : State := ⟨0,[],[]⟩

theorem initial_valid (n : Nat) : Valid n initial := by
  refine ⟨Nat.zero_le n, by simp [initial], ?_, ?_, ?_, ?_⟩ <;> simp [initial]

def ratio (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Rat :=
  solve oracle n original original.length initial / (denominator n original : Rat)

/-- The compressed recurrence and the concrete reference entrypoint report
exactly the same rational number. -/
theorem ratio_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    ratio oracle n original = referenceRatio n original := by
  unfold ratio referenceRatio
  rw [solve_reference oracle n original original.length initial (initial_valid n) hn ho hb]
  simp only [referenceModel, graph_pruning_correct]
  congr 1
  congr 1
  simp [expand, initial, ImplementationGraph.initial, Implementation.expand, List.range_eq_range']

end OnlineMatching.Solver

/-! ## Resource pruning -/

namespace OnlineMatching.Solver

open ImplementationGraph

/-- The resource bound, with unseen vertices implicit. -/
def capacity (n : Nat) (original : List Offline.Edge) (s : State) : Nat :=
  min (original.length - s.observed.length) ((s.available.length + n - s.seen) / 2)

theorem capacity_reference (n : Nat) (original : List Offline.Edge) (s : State)
    (h : Valid n s) : (capacity n original s : Rat) =
      ImplementationGraph.upper original.length (expand n s) := by
  exact congrArg (fun k : Nat => (k : Rat))
    (Implementation.compressed_upper_eq n s.seen (original.length-s.observed.length)
      s.available h.seen)

theorem reject_le_capacity (n : Nat) (original : List Offline.Edge) (s : State)
    (e : Offline.Edge) (fuel : Nat) (h : Valid n s) :
    value (referenceModel n original) fuel (ImplementationGraph.reject (expand n s) e) ≤
      (capacity n original s : Rat) := by
  rw [capacity_reference n original s h]
  apply Rat.le_trans (value_le_budget (referenceModel n original)
    (ImplementationGraph.upper original.length)
    (graph_budget (hiddenLabels n) (labelledHost original) original.length) fuel _)
  apply Rat.natCast_le_natCast.mpr
  change Implementation.resource (original.length-(e::s.observed).length)
      (Implementation.expand n s.seen s.available).length ≤
    Implementation.resource (original.length-s.observed.length)
      (Implementation.expand n s.seen s.available).length
  have heq : original.length-(e::s.observed).length = original.length-s.observed.length-1 := by
    simp only [List.length_cons]
    omega
  rw [heq]
  exact Implementation.resource_reject _ _

/-- Evaluate rejection only while the current best is below the resource bound. -/
def prunedBranch (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (continuation : State → Rat) (s : State) (e : Offline.Edge) (added : Nat) : Rat :=
  let child := reveal s e added
  let best := if decide (Offline.legal child.available e) then
    1 + continuation (normalize oracle (remove child e)) else 0
  if best < (capacity n original s : Rat) then
    max best (continuation (normalize oracle child))
  else best

theorem prunedBranch_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : State) (e : Offline.Edge) (added fuel : Nat) (continuation : State → Rat)
    (hc : ∀ t, Valid n t → continuation t = value (referenceModel n original) fuel (expand n t))
    (h : Valid n s) (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hk : s.seen+added ≤ n) (he : e.1 < e.2)
    (heb : e.1 < s.seen+added ∧ e.2 < s.seen+added) (hf : e ∉ s.observed) :
    prunedBranch oracle n original continuation s e added =
      CollapsedBellman.branch (value (referenceModel n original) fuel) (expand n s) e := by
  have hv := reveal_valid n s e added h hk he heb hf
  have hrej := (hc _ (normalize_valid oracle n _ hv)).trans
    (normalize_value oracle n original _ fuel hv hn ho hb)
  have heq : expand n (reveal s e added) = ImplementationGraph.reject (expand n s) e := by
    simp only [expand, reveal, ImplementationGraph.reject]
    rw [Implementation.expand_reveal n s.seen added s.available hk]
  rw [heq] at hrej
  have hr : continuation (normalize oracle (reveal s e added)) ≤
      (capacity n original s : Rat) := by
    rw [hrej]
    exact reject_le_capacity n original s e fuel h
  have hr0 : 0 ≤ continuation (normalize oracle (reveal s e added)) := by
    rw [hrej]
    exact value_nonnegative _ _ _
  have heqbranch : prunedBranch oracle n original continuation s e added =
      branch oracle continuation s e added := by
    simp only [prunedBranch, branch]
    rw [skip_reject _ _ _ hr]
    cases hl : decide (Offline.legal (reveal s e added).available e)
    · simp only [Bool.false_eq_true, ite_false]
      rw [Rat.max_def, ite_eq_left hr0]
    · simp only [ite_true]
      rw [Rat.max_def, Rat.max_def]
      split <;> split <;> grind
  rw [heqbranch]
  exact branch_reference oracle n original s e added fuel continuation hc h hn ho hb hk he heb hf

end OnlineMatching.Solver

/-! ## Weights from counts -/

namespace OnlineMatching.SolverCounting
open Solver CanonicalState CanonicalCounting

/-- The transition weight equals the quotient of degree-pruned counts,
with the child relabeled. -/
theorem weight_eq_counts (n : Nat) (original : List Offline.Edge) (s : Solver.State)
    (e : Offline.Edge) (mult childK : Nat)
    (r : CanonicalResult childK (graph (e::s.observed)))
    (order childOrder : List Nat) (h : Solver.Valid n s)
    (ho : order.Perm (List.range s.seen)) (hco : childOrder.Perm (List.range childK))
    (hk : s.seen ≤ childK) (hcn : childK ≤ n)
    (hes : e.1 < e.2) (heb : e.1 < childK ∧ e.2 < childK) (hef : e ∉ s.observed) :
    Solver.weight n original s e mult =
      ((mult * countFits n childK original (edges childK r.canonical) childOrder : Nat) : Rat) /
        (((original.length-s.observed.length) *
          countFits n s.seen original s.observed order : Nat) : Rat) := by
  have hcs : ∀ a ∈ e::s.observed, a.1 < a.2 := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hes
    · exact h.sorted a ha
  have hcb : ∀ a ∈ e::s.observed, a.1 < childK ∧ a.2 < childK := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact heb
    · obtain ⟨h1,h2⟩ := h.bounds a ha
      exact ⟨by omega,by omega⟩
  rw [countFits_canonical n childK original (e::s.observed) r childOrder childOrder
    hco hco hcn (List.nodup_cons.mpr ⟨hef,h.nodup⟩) hcs hcb,
    countFits_eq n childK original (e::s.observed) childOrder hco hcn
      (fun a ha => Nat.ne_of_lt (hcs a ha)) hcb,
    countFits_eq n s.seen original s.observed order ho h.seen
      (fun a ha => Nat.ne_of_lt (h.sorted a ha)) h.bounds]
  rfl

/-- Skip transitions with zero compatible labelings. -/
def dfsTerm (n : Nat) (original : List Offline.Edge) (s : Solver.State)
    (e : Offline.Edge) (mult childK : Nat)
    (r : CanonicalResult childK (graph (e::s.observed)))
    (order childOrder : List Nat) (branchValue : Rat) : Rat :=
  let fits := countFits n childK original (edges childK r.canonical) childOrder
  if fits = 0 then 0 else
    (((mult * fits : Nat) : Rat) /
      (((original.length-s.observed.length) *
        countFits n s.seen original s.observed order : Nat) : Rat)) * branchValue

/-- Skipping a zero-fit canonical child changes no transition contribution.
No nonzero probability or assumed count identity is needed. -/
theorem dfsTerm_eq_weight (n : Nat) (original : List Offline.Edge) (s : Solver.State)
    (e : Offline.Edge) (mult childK : Nat)
    (r : CanonicalResult childK (graph (e::s.observed)))
    (order childOrder : List Nat) (branchValue : Rat) (h : Solver.Valid n s)
    (ho : order.Perm (List.range s.seen)) (hco : childOrder.Perm (List.range childK))
    (hk : s.seen ≤ childK) (hcn : childK ≤ n)
    (hes : e.1 < e.2) (heb : e.1 < childK ∧ e.2 < childK) (hef : e ∉ s.observed) :
    dfsTerm n original s e mult childK r order childOrder branchValue =
      Solver.weight n original s e mult * branchValue := by
  rw [weight_eq_counts n original s e mult childK r order childOrder h ho hco hk hcn hes heb hef]
  unfold dfsTerm
  dsimp only
  split
  next hz => simp only [hz, Nat.mul_zero, Rat.natCast_ofNat, Rat.div_def, Rat.zero_mul]
  next _ => rfl

end OnlineMatching.SolverCounting

/-! ## Uncached solver -/

namespace OnlineMatching.Uncached

open Solver CanonicalState

/-- The same lexicographic selection rule as count_fits: most neighbors already
placed, then largest degree, then smallest vertex label. -/
def prefer (k : Nat) (g : Graph Nat) (placed : List Nat) (a b : Nat) : Bool :=
  let pa := (placed.filter (fun v => g a v)).length
  let pb := (placed.filter (fun v => g b v)).length
  let da := ((List.range k).filter (fun v => g a v)).length
  let db := ((List.range k).filter (fun v => g b v)).length
  decide (pa < pb ∨ (pa = pb ∧ (da < db ∨ (da = db ∧ b < a))))

def countOrder (k : Nat) (g : Graph Nat) : List Nat :=
  Ordering.orderBy (prefer k g) k (List.range k) []

theorem countOrder_perm (k : Nat) (g : Graph Nat) :
    (countOrder k g).Perm (List.range k) :=
  Ordering.orderBy_perm (prefer k g) k (List.range k) [] (by simp)

/-- A transition uses the canonical child's actual degree-pruned DFS count,
its exact factorial completion factor, and skips the child when that count is zero. -/
def term (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (continuation : Solver.State → Rat) (s : Solver.State) (e : Offline.Edge)
    (added mult : Nat) : Rat :=
  let r := oracle (s.seen+added) (graph (e::s.observed))
  SolverCounting.dfsTerm n original s e mult (s.seen+added) r
    (countOrder s.seen (graph s.observed)) (countOrder (s.seen+added) r.canonical)
    (prunedBranch oracle n original continuation s e added)

theorem term_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : Solver.State) (e : Offline.Edge) (added mult fuel : Nat)
    (continuation : Solver.State → Rat)
    (hc : ∀ t, Solver.Valid n t → continuation t =
      value (ImplementationGraph.referenceModel n original) fuel (Solver.expand n t))
    (h : Solver.Valid n s) (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hk : s.seen+added ≤ n) (he : e.1 < e.2)
    (heb : e.1 < s.seen+added ∧ e.2 < s.seen+added) (hf : e ∉ s.observed) :
    term oracle n original continuation s e added mult =
      (mult : Rat) * (ImplementationGraph.referenceModel n original).probability (Solver.expand n s) e *
        CollapsedBellman.branch (value (ImplementationGraph.referenceModel n original) fuel)
          (Solver.expand n s) e := by
  unfold term
  rw [SolverCounting.dfsTerm_eq_weight n original s e mult (s.seen+added) _ _ _ _ h
    (countOrder_perm _ _) (countOrder_perm _ _) (by omega) hk he heb hf,
    weight_reference n original s e mult h hn ho hb he hf,
    prunedBranch_reference oracle n original s e added fuel continuation hc h hn ho hb hk he heb hf]

/-- The solver with exact counts and rational weights. Each child adds an edge,
so the original edge count supplies enough recursion fuel. -/
def solve (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Nat → Solver.State → Rat
  | 0, _ => 0
  | fuel+1, s =>
    if capacity n original s = 0 then 0 else
      total (Transitions.remainingEdges (Transitions.freshPairs s.seen) s.observed)
        (fun e => term oracle n original (solve oracle n original fuel) s e 0 1) +
      (if s.seen < n then total (List.range s.seen)
        (fun u => term oracle n original (solve oracle n original fuel)
          s (u,s.seen) 1 (n-s.seen)) else 0) +
      (if s.seen+1 < n then term oracle n original (solve oracle n original fuel)
        s (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2) else 0)

open ImplementationGraph

theorem solve_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : Solver.State) (h : Valid n s)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    solve oracle n original fuel s = value (referenceModel n original) fuel (Solver.expand n s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [solve]
    by_cases hz : capacity n original s = 0
    · rw [ite_eq_left hz]
      have hu := value_le_budget (referenceModel n original)
        (ImplementationGraph.upper original.length)
        (graph_budget (hiddenLabels n) (labelledHost original) original.length) (fuel+1) (Solver.expand n s)
      have hlo := value_nonnegative (referenceModel n original) (fuel+1) (Solver.expand n s)
      rw [← capacity_reference n original s h, hz, Rat.natCast_ofNat] at hu
      exact (Rat.le_antisymm hu hlo).symm
    · rw [ite_eq_right hz]
      have ht : s.observed.length < original.length := by
        unfold capacity at hz
        omega
      change _ = value (referenceModel n original) (fuel+1)
        ⟨s.observed,Implementation.expand n s.seen s.available⟩
      rw [CollapsedBellman.value_succ_compressed n s.seen original s.observed s.available fuel
        hn ho hb h.nodup (fun e he => Nat.le_of_lt (h.sorted e he)) h.bounds h.free h.seen ht]
      congr 1
      · congr 1
        · apply total_congr
          intro e he
          have hem := List.mem_filter.mp he
          have hep := (Transitions.mem_freshPairs s.seen e.1 e.2).mp hem.1
          have hef : e ∉ s.observed := by simpa only [decide_eq_true_eq] using hem.2
          have heb : e.1 < s.seen+0 ∧ e.2 < s.seen+0 := ⟨by omega, by omega⟩
          rw [term_reference oracle n original s e 0 1 fuel _ ih h hn ho hb
              (by simpa using h.seen) hep.1 heb hef, Rat.natCast_ofNat, Rat.one_mul]
          rfl
        · by_cases hk : s.seen < n
          · rw [ite_eq_left hk, ite_eq_left hk]
            apply total_congr
            intro u hu
            have hu' := List.mem_range.mp hu
            have hef : (u,s.seen) ∉ s.observed := by
              intro he
              have := (h.bounds _ he).2
              omega
            rw [term_reference oracle n original s (u,s.seen) 1 (n-s.seen) fuel _ ih h hn ho hb
                (by omega) hu' ⟨by omega,by omega⟩ hef]
            rfl
          · simp only [ite_eq_right hk]
      · by_cases hk : s.seen+1 < n
        · rw [ite_eq_left hk, ite_eq_left hk]
          have hef : (s.seen,s.seen+1) ∉ s.observed := by
            intro he
            have := (h.bounds _ he).1
            omega
          rw [term_reference oracle n original s (s.seen,s.seen+1) 2
              ((n-s.seen)*(n-s.seen-1)/2) fuel _ ih h hn ho hb
              (by omega) (by omega) ⟨by omega,by omega⟩ hef]
          rfl
        · simp only [ite_eq_right hk]

def ratio (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Rat :=
  solve oracle n original original.length Solver.initial / (denominator n original : Rat)

/-- The counting-based, pruned solver equals the reference recurrence. -/
theorem ratio_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    ratio oracle n original = referenceRatio n original := by
  rw [← Solver.ratio_reference oracle n original hn ho hb]
  unfold ratio Solver.ratio
  rw [solve_reference oracle n original original.length Solver.initial (initial_valid n) hn ho hb,
    Solver.solve_reference oracle n original original.length Solver.initial (initial_valid n) hn ho hb]

end OnlineMatching.Uncached

/-! ## Order of unmatched labels -/

namespace OnlineMatching.AvailableOrder
open Solver

/-- The solver value depends on the available list only up to permutation,
for arbitrary inputs. -/
theorem solve_perm (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel k : Nat) (observed : List Offline.Edge) (a b : List Nat)
    (h : a.Perm b) :
    Uncached.solve oracle n original fuel ⟨k,observed,a⟩ =
    Uncached.solve oracle n original fuel ⟨k,observed,b⟩ := by
  induction fuel generalizing k observed a b with
  | zero => rfl
  | succ fuel ih =>
    have cap : capacity n original ⟨k,observed,a⟩ = capacity n original ⟨k,observed,b⟩ := by
      simp only [capacity, h.length_eq]
    have termEq : ∀ e added mult,
        Uncached.term oracle n original (Uncached.solve oracle n original fuel)
          ⟨k,observed,a⟩ e added mult =
        Uncached.term oracle n original (Uncached.solve oracle n original fuel)
          ⟨k,observed,b⟩ e added mult := by
      intro e added mult
      have hp := h.append_right (List.range' k added)
      have legal : Offline.legal (a ++ List.range' k added) e =
          Offline.legal (b ++ List.range' k added) e := by
        simp only [Offline.legal, hp.mem_iff]
      have rej := ih (k+added)
        (CanonicalState.edges (k+added) (oracle (k+added) (CanonicalState.graph (e::observed))).canonical)
        _ _ (hp.map (oracle (k+added) (CanonicalState.graph (e::observed))).permutation.forward)
      have acc := ih (k+added)
        (CanonicalState.edges (k+added) (oracle (k+added) (CanonicalState.graph (e::observed))).canonical)
        _ _ (((hp.erase e.1).erase e.2).map
          (oracle (k+added) (CanonicalState.graph (e::observed))).permutation.forward)
      simp only [Uncached.term, SolverCounting.dfsTerm, prunedBranch,
        reveal, remove, normalize, Implementation.revealList, Offline.remove] at *
      simp only [legal, acc, rej, cap]
      rfl
    simp only [Uncached.solve, cap]
    simp only [termEq]

end OnlineMatching.AvailableOrder
