import OnlineMatching.Invariance.IntegerScaling
import OnlineMatching.Invariance.Solver
import OnlineMatching.Reference.Experiment
import OnlineMatching.Final

/-!
# Division-free integer recurrence

Multiplying the Bellman value by $(m-|E(H)|)!\,C(H)$ yields the natural-number
recurrence `IntegerSolver.solve`. `IntegerSolver.ratio_reference` proves that
dividing the root value by $m!\,n!\,\mathrm{OPT}(G)$ recovers `referenceRatio`.
-/

namespace OnlineMatching.IntegerSolver
open Solver

def sumNat {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | x::xs, f => f x + sumNat xs f

theorem cast_sum {α : Type} (xs : List α) (f : α → Nat) :
    (sumNat xs f : Rat) = total xs (fun x => (f x : Rat)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumNat, total, Rat.natCast_add, ih]

/-- Exact integer summation is invariant under reordering of the terms. -/
theorem sumNat_perm {α : Type} {xs ys : List α} (h : xs.Perm ys) (f : α → Nat) :
    sumNat xs f = sumNat ys f := by
  apply Rat.natCast_inj.mp
  rw [cast_sum, cast_sum]
  exact total_perm h (fun x => (f x : Rat))

theorem cast_max (a b : Nat) : ((max a b : Nat) : Rat) = max (a : Rat) (b : Rat) := by
  by_cases h : a ≤ b
  · have hr := Rat.natCast_le_natCast.mpr h
    simp only [Nat.max_def, Rat.max_def, h, hr, ite_true]
  · have hr : ¬ (a : Rat) ≤ (b : Rat) := fun hh => h (Rat.natCast_le_natCast.mp hh)
    simp only [Nat.max_def, Rat.max_def, h, hr, ite_false]

def scale (n : Nat) (original : List Offline.Edge) (s : State) : Nat :=
  Counting.factorial (original.length-s.observed.length) *
    Anonymous.compatibleCount n original s.observed

def term (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (continuation : State → Nat) (s : State) (e : Offline.Edge) (added mult : Nat) : Nat :=
  let fits := Anonymous.compatibleCount n original (e::s.observed)
  if fits = 0 then 0 else
    let child := reveal s e added
    let z := Counting.factorial (original.length-s.observed.length-1)*fits
    let reject := continuation (normalize oracle child)
    mult * (if decide (Offline.legal child.available e) then
      max reject (z + continuation (normalize oracle (remove child e))) else reject)

/-- The natural-number, division-free Bellman recurrence. -/
def solve (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Nat → State → Nat
  | 0, _ => 0
  | fuel+1, s =>
    if capacity n original s = 0 then 0 else
      sumNat (Transitions.remainingEdges (Transitions.freshPairs s.seen) s.observed)
        (fun e => term oracle n original (solve oracle n original fuel) s e 0 1) +
      (if s.seen < n then sumNat (List.range s.seen)
        (fun u => term oracle n original (solve oracle n original fuel) s (u,s.seen) 1 (n-s.seen)) else 0) +
      (if s.seen+1 < n then term oracle n original (solve oracle n original fuel) s
        (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2) else 0)

theorem normalize_length (oracle : Oracle) (n : Nat) (s : State) (h : Valid n s) :
    (normalize oracle s).observed.length = s.observed.length := by
  have hp := CanonicalState.canonical_edges_perm s.observed
    (oracle s.seen (CanonicalState.graph s.observed)) h.nodup h.sorted h.bounds
  simpa [normalize, Symmetry.history] using hp.length_eq.symm

theorem normalize_count (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : State) (h : Valid n s) :
    Anonymous.compatibleCount n original (normalize oracle s).observed =
      Anonymous.compatibleCount n original s.observed :=
  CanonicalCounting.compatibleCount_canonical n s.seen original s.observed
    (oracle s.seen (CanonicalState.graph s.observed)) h.seen h.nodup h.sorted h.bounds

theorem normalize_scale (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : State) (h : Valid n s) : scale n original (normalize oracle s) = scale n original s := by
  unfold scale
  rw [normalize_length oracle n s h, normalize_count oracle n original s h]

theorem term_scaled (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (s : State) (e : Offline.Edge) (added mult : Nat)
    (fi : State → Nat) (fr : State → Rat)
    (ih : ∀ t, Valid n t → 0 < Anonymous.compatibleCount n original t.observed →
      (fi t : Rat) = (scale n original t : Rat)*fr t)
    (h : Valid n s) (hp : 0 < Anonymous.compatibleCount n original s.observed)
    (ht : s.observed.length < original.length)
    (hk : s.seen+added ≤ n) (hes : e.1 < e.2)
    (heb : e.1 < s.seen+added ∧ e.2 < s.seen+added) (hef : e ∉ s.observed) :
    (term oracle n original fi s e added mult : Rat) =
      (scale n original s : Rat) * (weight n original s e mult * branch oracle fr s e added) := by
  have hc := reveal_valid n s e added h hk hes heb hef
  have ha := remove_valid n (reveal s e added) e hc
  by_cases hz : Anonymous.compatibleCount n original (e::s.observed) = 0
  · simp [term, weight, hz, Rat.div_def]
  · have hpos : 0 < Anonymous.compatibleCount n original (e::s.observed) := by omega
    have hcr : 0 < Anonymous.compatibleCount n original (normalize oracle (reveal s e added)).observed := by
      rw [normalize_count oracle n original _ hc]; exact hpos
    have hca : 0 < Anonymous.compatibleCount n original (normalize oracle (remove (reveal s e added) e)).observed := by
      rw [normalize_count oracle n original _ ha]; exact hpos
    have hr := ih _ (normalize_valid oracle n _ hc) hcr
    have har := ih _ (normalize_valid oracle n _ ha) hca
    let z := Counting.factorial (original.length-s.observed.length-1) *
      Anonymous.compatibleCount n original (e::s.observed)
    have hzrej : scale n original (normalize oracle (reveal s e added)) = z := by
      rw [normalize_scale oracle n original _ hc]
      simp only [scale, reveal, List.length_cons]
      congr 2 <;> omega
    have hzacc : scale n original (normalize oracle (remove (reveal s e added) e)) = z := by
      rw [normalize_scale oracle n original _ ha]
      simp only [scale, remove, reveal, List.length_cons]
      congr 2 <;> omega
    rw [hzrej] at hr
    rw [hzacc] at har
    have hbranch : (term oracle n original fi s e added mult : Rat) =
        (mult : Rat) * ((z : Rat) * branch oracle fr s e added) := by
      simp only [term, hz, ite_false, Rat.natCast_mul, branch]
      split
      · rw [cast_max, Rat.natCast_add, hr, har]
        exact congrArg ((mult : Rat) * ·)
          (IntegerScaling.scaled_accept_reject (z : Rat) _ _ Rat.natCast_nonneg)
      · rw [hr]
    rw [hbranch]
    have he : original.length-s.observed.length = (original.length-s.observed.length-1)+1 := by omega
    have hf : Counting.factorial (original.length-s.observed.length) =
        (original.length-s.observed.length)*Counting.factorial (original.length-s.observed.length-1) := by
      calc
        _ = Counting.factorial ((original.length-s.observed.length-1)+1) := congrArg _ he
        _ = _ := by rw [Counting.factorial, ← he]
    have hd : (((original.length-s.observed.length) *
        Anonymous.compatibleCount n original s.observed : Nat) : Rat) ≠ 0 := by
      have hh : 0 < (original.length-s.observed.length)*Anonymous.compatibleCount n original s.observed := Nat.mul_pos (by omega) hp
      exact Rat.ne_of_gt (Rat.natCast_pos.mpr hh)
    have cancel := @Rat.div_mul_cancel
      (((mult * Anonymous.compatibleCount n original (e::s.observed) : Nat) : Rat))
      ((((original.length-s.observed.length)*Anonymous.compatibleCount n original s.observed : Nat) : Rat)) hd
    simp only [scale, hf, weight, z, Rat.natCast_mul] at *
    grind

theorem sum_scaled {α : Type} (xs : List α) (fi : α → Nat) (fr : α → Rat) (c : Rat)
    (h : ∀ x ∈ xs, (fi x : Rat) = c*fr x) : (sumNat xs fi : Rat) = c*total xs fr := by
  rw [cast_sum]
  calc
    _ = total xs (fun x => fr x*c) := total_congr xs _ _ (fun x hx => by rw [h x hx, Rat.mul_comm])
    _ = total xs fr*c := total_mul xs fr c
    _ = _ := Rat.mul_comm _ _

/-- `IntegerSolver.solve` equals the rational Bellman value multiplied by $(m-|E(H)|)!\,C(H)$. -/
theorem solve_scaled (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : State) (h : Valid n s)
    (hp : 0 < Anonymous.compatibleCount n original s.observed)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    (solve oracle n original fuel s : Rat) =
      (scale n original s : Rat)*Solver.solve oracle n original fuel s := by
  induction fuel generalizing s with
  | zero => simp only [solve, Solver.solve, Rat.natCast_ofNat, Rat.mul_zero]
  | succ fuel ih =>
    by_cases hz : capacity n original s = 0
    · have hv : Solver.solve oracle n original (fuel+1) s = 0 := by
        rw [Solver.solve_reference oracle n original (fuel+1) s h hn ho hb,
          ← Uncached.solve_reference oracle n original (fuel+1) s h hn ho hb]
        simp only [Uncached.solve, hz, ite_true]
      simp only [solve, hz, ite_true, Rat.natCast_ofNat, hv, Rat.mul_zero]
    · have ht : s.observed.length < original.length := by unfold capacity at hz; omega
      rw [solve, ite_eq_right hz, Solver.solve, ite_eq_left ht]
      simp only [Rat.natCast_add, Rat.mul_add]
      congr 1
      · congr 1
        · apply sum_scaled
          intro e he
          have hem := List.mem_filter.mp he
          have hep := (Transitions.mem_freshPairs s.seen e.1 e.2).mp hem.1
          have hef : e ∉ s.observed := by simpa only [decide_eq_true_eq] using hem.2
          exact term_scaled oracle n original s e 0 1 _ _ ih h hp ht
            (by simpa using h.seen) hep.1 ⟨by omega,by omega⟩ hef
        · by_cases hk : s.seen < n
          · rw [ite_eq_left hk, ite_eq_left hk]
            apply sum_scaled
            intro u hu
            have hu' := List.mem_range.mp hu
            have hef : (u,s.seen) ∉ s.observed := by
              intro he; have := (h.bounds _ he).2; omega
            exact term_scaled oracle n original s (u,s.seen) 1 (n-s.seen) _ _ ih h hp ht
              (by omega) hu' ⟨by omega,by omega⟩ hef
          · simp only [ite_eq_right hk, Rat.natCast_ofNat, Rat.mul_zero]
      · by_cases hk : s.seen+1 < n
        · rw [ite_eq_left hk, ite_eq_left hk]
          have hef : (s.seen,s.seen+1) ∉ s.observed := by
            intro he; have := (h.bounds _ he).1; omega
          exact term_scaled oracle n original s (s.seen,s.seen+1) 2
            ((n-s.seen)*(n-s.seen-1)/2) _ _ ih h hp ht (by omega) (by omega) ⟨by omega,by omega⟩ hef
        · simp only [ite_eq_right hk, Rat.natCast_ofNat, Rat.mul_zero]

theorem initial_count (n : Nat) (original : List Offline.Edge) :
    Anonymous.compatibleCount n original Solver.initial.observed = Counting.factorial n := by
  change ((Anonymous.labels n).filter (fun _ => true)).length = Counting.factorial n
  rw [List.filter_eq_self.mpr (by intro x hx; rfl)]
  exact Counting.completions_length n (List.range n) (by simp)

def ratio (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Rat :=
  (solve oracle n original original.length Solver.initial : Rat) /
    ((Counting.factorial original.length * Counting.factorial n *
      ImplementationGraph.denominator n original : Nat) : Rat)

/-- The C++ final normalization reports the same value as the reference solver. -/
theorem ratio_reference (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    ratio oracle n original = ImplementationGraph.referenceRatio n original := by
  have hp : 0 < Anonymous.compatibleCount n original Solver.initial.observed := by
    rw [initial_count]; exact Experiment.factorial_positive n
  have hs : scale n original Solver.initial = Counting.factorial original.length * Counting.factorial n := by
    unfold scale
    rw [initial_count]
    simp [Solver.initial]
  have h := solve_scaled oracle n original original.length Solver.initial (initial_valid n) hp hn ho hb
  have hspos : 0 < scale n original Solver.initial := by
    rw [hs]; exact Nat.mul_pos (Experiment.factorial_positive _) (Experiment.factorial_positive _)
  have hsne : (scale n original Solver.initial : Rat) ≠ 0 :=
    Rat.ne_of_gt (Rat.natCast_pos.mpr hspos)
  unfold ratio
  rw [← hs, Rat.natCast_mul,
    IntegerScaling.final_normalization _ _ _ _ hsne h]
  exact Solver.ratio_reference oracle n original hn ho hb

theorem ratio_eq_final (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    ratio oracle n original = Final.opt n original :=
  (ratio_reference oracle n original hn ho hb).trans (Final.opt_eq_reference n original hn ho hb).symm

end OnlineMatching.IntegerSolver
