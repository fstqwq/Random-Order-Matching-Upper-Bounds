import OnlineMatching.Invariance.IntegerSolver
import OnlineMatching.Invariance.Warmup

/-!
# Memoized integer recurrence

Memoized evaluation of `IntegerSolver.solve` in the `Memo` state monad, together
with soundness lemmas for cache prewarming, two-level cache hits, and oracle
independence.
-/
namespace OnlineMatching.IntegerMemo
open Solver Memo

def key (fuel : Nat) (s : State) : Key :=
  (3, fuel, s.seen, s.observed, s.available)

def spec (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Key → Value
  | (_, fuel, k, observed, available) =>
    (IntegerSolver.solve oracle n original fuel ⟨k, observed, available⟩, 0)

def sum (xs : List α) (f : α → Work Nat) : Work Nat :=
  match xs with
  | [] => pure 0
  | x :: xs => do
    let a ← f x
    let b ← sum xs f
    pure (a+b)

theorem sum_correct (sp : Key → Value) (xs : List α) (f : α → Work Nat)
    (g : α → Nat) (h : ∀ x ∈ xs, Correct sp (f x) (g x)) :
    Correct sp (sum xs f) (IntegerSolver.sumNat xs g) := by
  induction xs with
  | nil => exact correct_pure _ _
  | cons x xs ih =>
    apply correct_bind _ _ _ _ _ (h x (by simp))
    apply correct_bind _ _ _ _ _ (ih (fun y hy => h y (by simp [hy])))
    exact correct_pure _ _

def term (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (recur : State → Work Nat) (s : State) (e : Offline.Edge) (added mult : Nat) : Work Nat := do
  let fits := Anonymous.compatibleCount n original (e::s.observed)
  if fits = 0 then pure 0 else
    let child := reveal s e added
    let z := Counting.factorial (original.length-s.observed.length-1)*fits
    let reject ← recur (normalize oracle child)
    if decide (Offline.legal child.available e) then
      let accept ← recur (normalize oracle (remove child e))
      pure (mult * max reject (z+accept))
    else pure (mult*reject)

theorem term_correct (sp : Key → Value) (oracle : Oracle) (n : Nat)
    (original : List Offline.Edge) (recur : State → Work Nat) (f : State → Nat)
    (h : ∀ s, Correct sp (recur s) (f s)) (s : State) (e : Offline.Edge) (added mult : Nat) :
    Correct sp (term oracle n original recur s e added mult)
      (IntegerSolver.term oracle n original f s e added mult) := by
  unfold term IntegerSolver.term
  dsimp only
  split
  · exact correct_pure _ _
  · apply correct_bind _ _ _ _ _ (h _)
    split
    · apply correct_bind _ _ _ _ _ (h _)
      exact correct_pure _ _
    · exact correct_pure _ _

def solve (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Nat → State → Work Nat
  | fuel, s => memoNat (key fuel s) (defer fun _ =>
    match fuel with
    | 0 => pure 0
    | fuel+1 =>
      if capacity n original s = 0 then pure 0 else do
        let oldOld ← sum (Transitions.remainingEdges (Transitions.freshPairs s.seen) s.observed)
          (fun e => term oracle n original (solve oracle n original fuel) s e 0 1)
        let oldNew ← (if s.seen < n then sum (List.range s.seen)
          (fun u => term oracle n original (solve oracle n original fuel) s (u,s.seen) 1 (n-s.seen))
          else pure 0)
        let newNew ← (if s.seen+1 < n then term oracle n original (solve oracle n original fuel) s
          (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2) else pure 0)
        pure (oldOld+oldNew+newNew))

/-- Every memoized integer call returns the uncached value and preserves cache soundness. -/
theorem solve_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : State) :
    Correct (spec oracle n original) (solve oracle n original fuel s)
      (IntegerSolver.solve oracle n original fuel s) := by
  induction fuel generalizing s with
  | zero =>
    rw [solve]
    apply correct_memoNat _ _ _ _ rfl
    exact correct_pure _ _
  | succ fuel ih =>
    rw [solve]
    apply correct_memoNat _ _ _ _ rfl
    change Correct _ (if capacity n original s = 0 then _ else _) _
    rw [IntegerSolver.solve]
    split
    · exact correct_pure _ _
    · apply correct_bind _ _ _ _ _ (sum_correct _ _ _ _ (fun e _ => term_correct _ _ _ _ _ _ ih s e 0 1))
      have hOld : Correct (spec oracle n original)
          (if s.seen < n then sum (List.range s.seen)
            (fun u => term oracle n original (solve oracle n original fuel) s (u,s.seen) 1 (n-s.seen)) else pure 0)
          (if s.seen < n then IntegerSolver.sumNat (List.range s.seen)
            (fun u => IntegerSolver.term oracle n original (IntegerSolver.solve oracle n original fuel) s (u,s.seen) 1 (n-s.seen)) else 0) := by
        split
        · exact sum_correct _ _ _ _ (fun u _ => term_correct _ _ _ _ _ _ ih s (u,s.seen) 1 (n-s.seen))
        · exact correct_pure _ _
      have hNew : Correct (spec oracle n original)
          (if s.seen+1 < n then term oracle n original (solve oracle n original fuel) s
            (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2) else pure 0)
          (if s.seen+1 < n then IntegerSolver.term oracle n original (IntegerSolver.solve oracle n original fuel) s
            (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2) else 0) := by
        split
        · exact term_correct _ _ _ _ _ _ ih s (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2)
        · exact correct_pure _ _
      apply correct_bind _ _ _ _ _ hOld
      apply correct_bind _ _ _ _ _ hNew
      exact correct_pure _ _

def warmup (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (jobs : List (Nat × State)) : Work Unit :=
  match jobs with
  | [] => pure ()
  | (fuel,s)::jobs => do
    let _ ← solve oracle n original fuel s
    warmup oracle n original jobs

theorem warmup_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (jobs : List (Nat × State)) : Correct (spec oracle n original) (warmup oracle n original jobs) () := by
  induction jobs with
  | nil => exact correct_pure _ _
  | cons job jobs ih =>
    exact correct_bind _ _ _ _ _ (solve_correct oracle n original job.1 job.2) ih

/-- Any list of prewarming calls, including repeated or incomplete-coverage jobs,
    followed by the root call, returns the proved integer recurrence. -/
theorem warmup_root_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (jobs : List (Nat × State)) :
    Correct (spec oracle n original)
      (do warmup oracle n original jobs; solve oracle n original original.length initial)
      (IntegerSolver.solve oracle n original original.length initial) :=
  correct_bind _ _ _ _ _ (warmup_correct oracle n original jobs)
    (solve_correct oracle n original original.length initial)

/-- Both levels may miss, evict, or contain different subsets of correct entries. -/
theorem two_level_hit (sp : Key → Value) (localCache shared : Cache)
    (hl : Sound sp localCache) (hs : Sound sp shared) (k : Key) (v : Value)
    (h : localCache[k]? = some v ∨ shared[k]? = some v) : v = sp k := by
  rcases h with h | h
  · exact hl k v h
  · exact hs k v h

/-- Publishing a completed memoized call is safe, including duplicate insertion. -/
theorem publish_solve (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : State) (c : Cache) (hc : Sound (spec oracle n original) c) :
    Sound (spec oracle n original)
      (((solve oracle n original fuel s).run c).2.insert (key fuel s)
        (((solve oracle n original fuel s).run c).1,0)) := by
  have h := solve_correct oracle n original fuel s c hc
  apply sound_insert _ _ h.2
  exact congrArg (fun a => (a, (0 : Rat))) h.1

/-- Successful prewarming and root evaluation give the reference ratio. -/
theorem warmup_root_ratio (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (jobs : List (Nat × State)) (c : Cache) (hc : Sound (spec oracle n original) c)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    (((do warmup oracle n original jobs; solve oracle n original original.length initial).run c).1 : Rat) /
      ((Counting.factorial original.length * Counting.factorial n *
        ImplementationGraph.denominator n original : Nat) : Rat) =
      ImplementationGraph.referenceRatio n original := by
  rw [(warmup_root_correct oracle n original jobs c hc).1]
  exact IntegerSolver.ratio_reference oracle n original hn ho hb

/-- The specification does not depend on which legal labeling oracle is chosen. -/
theorem oracle_independent (o₁ o₂ : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : State) (h : Valid n s)
    (hp : 0 < Anonymous.compatibleCount n original s.observed)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    IntegerSolver.solve o₁ n original fuel s = IntegerSolver.solve o₂ n original fuel s := by
  apply Rat.natCast_inj.mp
  rw [IntegerSolver.solve_scaled o₁ n original fuel s h hp hn ho hb,
      IntegerSolver.solve_scaled o₂ n original fuel s h hp hn ho hb,
      Solver.solve_reference o₁ n original fuel s h hn ho hb,
      Solver.solve_reference o₂ n original fuel s h hn ho hb]

/-- Applying any legal normalization preserves the scaled reference value. -/
theorem normalized_reference (o : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : State) (h : Valid n s)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) :
    (IntegerSolver.scale n original (normalize o s) : Rat) *
      value (ImplementationGraph.referenceModel n original) fuel (expand n (normalize o s)) =
    (IntegerSolver.scale n original s : Rat) *
      value (ImplementationGraph.referenceModel n original) fuel (expand n s) := by
  rw [IntegerSolver.normalize_scale o n original s h]
  apply congrArg ((IntegerSolver.scale n original s : Rat) * ·)
  exact CanonicalState.value_canonical original s.observed s.available
    (o s.seen (CanonicalState.graph s.observed)) h.seen fuel hn ho hb h.nodup h.sorted h.bounds

/-- Fuel need not occupy bits in a C++ key: the observed graph determines it. -/
def stateKey (original : List Offline.Edge) (s : State) : Key :=
  key (original.length-s.observed.length) s

theorem stateKey_injective (original : List Offline.Edge) : Function.Injective (stateKey original) := by
  intro s t h
  cases s; cases t
  simp only [stateKey, key, Prod.mk.injEq] at h
  rcases h with ⟨_, _, hk, he, ha⟩
  subst_vars
  rfl

theorem child_fuel (m t : Nat) (h : t < m) : m-(t+1)+1 = m-t := by omega

/-- A sound shared hit can be copied to a private cache without changing its meaning. -/
theorem copy_hit (sp : Key → Value) (privateCache shared : Cache)
    (hp : Sound sp privateCache) (hs : Sound sp shared) (k : Key) (v : Value)
    (hit : shared[k]? = some v) : Sound sp (privateCache.insert k v) :=
  sound_insert sp privateCache hp k v (hs k v hit)

end OnlineMatching.IntegerMemo
