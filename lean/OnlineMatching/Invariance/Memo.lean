import Std.Data.HashMap.Lemmas
import OnlineMatching.Invariance.Solver

/-!
# Memoization

`Memo` is a state monad with a hash-map cache whose entries equal the uncached
function. `Memoized.ratio` memoizes the relabeled solver with sorted cache
keys and one relabeling shared by the accept and reject children, as in
`opt.py`; `Memoized.ratio_eq` proves it equal to `Uncached.ratio` for
every oracle.
-/

/-! ## Verified memoization -/

namespace OnlineMatching.Memo

abbrev Key := Nat × Nat × Nat × List (Nat × Nat) × List Nat
abbrev Value := Nat × Rat
abbrev Cache := Std.HashMap Key Value

structure Work (α : Type) where
  run : Cache → α × Cache

instance : Monad Work where
  pure a := ⟨fun c => (a,c)⟩
  bind p f := ⟨fun c => let (a,c') := p.run c; (f a).run c'⟩

def defer (f : Unit → Work α) : Work α := ⟨fun c => (f ()).run c⟩

/-- Every stored entry equals the uncached function at that exact key. -/
def Sound (spec : Key → Value) (c : Cache) : Prop :=
  ∀ k v, c[k]? = some v → v = spec k

def Correct (spec : Key → Value) (p : Work α) (a : α) : Prop :=
  ∀ c, Sound spec c → (p.run c).1 = a ∧ Sound spec (p.run c).2

theorem sound_empty (spec : Key → Value) : Sound spec (∅ : Cache) := by
  intro k v h
  simp at h

theorem sound_insert (spec : Key → Value) (c : Cache) (hc : Sound spec c)
    (k : Key) (v : Value) (hv : v = spec k) : Sound spec (c.insert k v) := by
  intro q w h
  rw [Std.HashMap.getElem?_insert] at h
  by_cases hk : k = q
  · subst q
    simp only [BEq.rfl, ite_true, Option.some.injEq] at h
    exact h ▸ hv
  · simp only [beq_iff_eq, hk, ite_false] at h
    exact hc q w h

theorem correct_pure (spec : Key → Value) (a : α) :
    Correct spec (pure a) a := fun _ hc => ⟨rfl,hc⟩

theorem correct_bind (spec : Key → Value) (p : Work α) (f : α → Work β)
    (a : α) (b : β) (hp : Correct spec p a) (hf : Correct spec (f a) b) :
    Correct spec (p >>= f) b := by
  intro c hc
  have h := hp c hc
  change ((f (p.run c).1).run (p.run c).2).1 = b ∧
    Sound spec ((f (p.run c).1).run (p.run c).2).2
  rw [h.1]
  exact hf _ h.2

def memo (key : Key) (body : Work Value) : Work Value := ⟨fun c =>
  match c[key]? with
  | some v => (v,c)
  | none => let (v,c') := body.run c; (v,c'.insert key v)⟩

theorem correct_memo (spec : Key → Value) (key : Key) (body : Work Value)
    (h : Correct spec body (spec key)) : Correct spec (memo key body) (spec key) := by
  intro c hc
  cases hl : c[key]? with
  | some v =>
    simp only [memo, hl]
    exact ⟨hc key v hl,hc⟩
  | none =>
    simp only [memo, hl]
    have hb := h c hc
    exact ⟨hb.1,sound_insert spec _ hb.2 key _ hb.1⟩

def sum (xs : List α) (f : α → Work Rat) : Work Rat :=
  match xs with
  | [] => pure 0
  | x::rest => do
      let a ← f x
      let b ← sum rest f
      pure (a+b)

theorem correct_sum (spec : Key → Value) (xs : List α) (f : α → Work Rat)
    (g : α → Rat) (h : ∀ x ∈ xs, Correct spec (f x) (g x)) :
    Correct spec (sum xs f) (total xs g) := by
  induction xs with
  | nil => exact correct_pure _ _
  | cons x xs ih =>
    apply correct_bind _ _ _ _ _ (h x (by simp))
    apply correct_bind _ _ _ _ _ (ih (fun y hy => h y (by simp [hy])))
    exact correct_pure _ _

def memoNat (key : Key) (body : Work Nat) : Work Nat := do
  let v ← memo key (do let a ← body; pure (a,0))
  pure v.1

def memoRat (key : Key) (body : Work Rat) : Work Rat := do
  let v ← memo key (do let a ← body; pure (0,a))
  pure v.2

theorem correct_memoNat (spec : Key → Value) (key : Key) (body : Work Nat)
    (a : Nat) (hk : spec key = (a,0)) (h : Correct spec body a) :
    Correct spec (memoNat key body) a := by
  apply correct_bind _ _ _ (spec key) _
  · apply correct_memo
    rw [hk]
    apply correct_bind _ _ _ _ _ h
    exact correct_pure _ _
  · rw [hk]
    exact correct_pure _ _

theorem correct_memoRat (spec : Key → Value) (key : Key) (body : Work Rat)
    (a : Rat) (hk : spec key = (0,a)) (h : Correct spec body a) :
    Correct spec (memoRat key body) a := by
  apply correct_bind _ _ _ (spec key) _
  · apply correct_memo
    rw [hk]
    apply correct_bind _ _ _ _ _ h
    exact correct_pure _ _
  · rw [hk]
    exact correct_pure _ _

def maximum (xs : List α) (f : α → Work Nat) : Work Nat :=
  match xs with
  | [] => pure 0
  | x::rest => do
      let a ← f x
      let b ← maximum rest f
      pure (max a b)

theorem correct_maximum (spec : Key → Value) (xs : List α) (f : α → Work Nat)
    (g : α → Nat) (h : ∀ x ∈ xs, Correct spec (f x) (g x)) :
    Correct spec (maximum xs f) ((xs.map g).foldr max 0) := by
  induction xs with
  | nil => exact correct_pure _ _
  | cons x xs ih =>
    apply correct_bind _ _ _ _ _ (h x (by simp))
    apply correct_bind _ _ _ _ _ (ih (fun y hy => h y (by simp [hy])))
    exact correct_pure _ _

end OnlineMatching.Memo

/-! ## Memoized solver -/

namespace OnlineMatching.Memoized

/- Available vertices are sorted in cache keys, and the accept and reject
children share the relabelling of their common observed graph. -/

open Memo Solver CanonicalState

def spec (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Key → Value
  | (0,fuel,k,observed,available) =>
      (0,Uncached.solve oracle n original fuel ⟨k,observed,available⟩)
  | (1,_,k,observed,order) =>
      (CanonicalCounting.countFits n k original observed order,0)
  | (2,fuel,_,_,available) => (Offline.matching original fuel available,0)
  | _ => (0,0)

def count (n : Nat) (original : List Offline.Edge) (k : Nat)
    (observed : List Offline.Edge) (order : List Nat) : Work Nat :=
  memoNat (1,0,k,observed,order) (defer fun _ =>
    pure (CanonicalCounting.countFits n k original observed order))

theorem count_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (k : Nat) (observed : List Offline.Edge) (order : List Nat) :
    Correct (spec oracle n original) (count n original k observed order)
      (CanonicalCounting.countFits n k original observed order) := by
  apply correct_memoNat _ _ _ _ rfl
  exact correct_pure _ _

def branch (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (recur : Solver.State → Work Rat) (s : Solver.State) (e : Offline.Edge)
    (added : Nat) : Work Rat := do
  let child := reveal s e added
  let acceptAction : Work Rat := if decide (Offline.legal child.available e) then do
      let accepted ← recur (normalize oracle (remove child e))
      pure (1+accepted)
    else pure 0
  let best ← acceptAction
  if best < (capacity n original s : Rat) then
    let rejected ← recur (normalize oracle child)
    pure (max best rejected)
  else pure best

theorem branch_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (recur : Solver.State → Work Rat) (f : Solver.State → Rat)
    (h : ∀ s, Correct (spec oracle n original) (recur s) (f s))
    (s : Solver.State) (e : Offline.Edge) (added : Nat) :
    Correct (spec oracle n original) (branch oracle n original recur s e added)
      (prunedBranch oracle n original f s e added) := by
  unfold branch prunedBranch
  dsimp only
  apply correct_bind _ _ _
    (if decide (Offline.legal (reveal s e added).available e) then
      1+f (normalize oracle (remove (reveal s e added) e)) else 0)
  · split
    · apply correct_bind _ _ _ _ _ (h _)
      exact correct_pure _ _
    · exact correct_pure _ _
  · generalize (if decide (Offline.legal (reveal s e added).available e) then
      1+f (normalize oracle (remove (reveal s e added) e)) else 0) = best
    split
    · apply correct_bind _ _ _ _ _ (h _)
      exact correct_pure _ _
    · exact correct_pure _ _

def branchWith (n : Nat) (original : List Offline.Edge)
    (recur : Solver.State → Work Rat) (s : Solver.State) (e : Offline.Edge)
    (added : Nat) (r : CanonicalResult (s.seen+added) (graph (e::s.observed))) : Work Rat := do
    let child := reveal s e added
    let observed := edges (s.seen+added) r.canonical
    let acceptAction : Work Rat := if decide (Offline.legal child.available e) then do
        let accepted ← recur ⟨s.seen+added, observed,
          (Offline.remove child.available e).map r.permutation.forward⟩
        pure (1+accepted)
      else pure 0
    let accepted ← acceptAction
    if accepted < (capacity n original s : Rat) then do
        let rejected ← recur ⟨s.seen+added, observed,
          child.available.map r.permutation.forward⟩
        pure (max accepted rejected)
      else pure accepted

def term (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (recur : Solver.State → Work Rat) (s : Solver.State) (e : Offline.Edge)
    (added mult : Nat) : Work Rat := do
  let r := oracle (s.seen+added) (graph (e::s.observed))
  let fits ← count n original (s.seen+added) (edges (s.seen+added) r.canonical)
    (Uncached.countOrder (s.seen+added) r.canonical)
  if fits = 0 then pure 0 else
    let parent ← count n original s.seen s.observed
      (Uncached.countOrder s.seen (graph s.observed))
    let best ← branchWith n original recur s e added r
    pure (((mult*fits : Nat) : Rat) /
      (((original.length-s.observed.length)*parent : Nat) : Rat) * best)

theorem term_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (recur : Solver.State → Work Rat) (f : Solver.State → Rat)
    (h : ∀ s, Correct (spec oracle n original) (recur s) (f s))
    (s : Solver.State) (e : Offline.Edge) (added mult : Nat) :
    Correct (spec oracle n original) (term oracle n original recur s e added mult)
      (Uncached.term oracle n original f s e added mult) := by
  unfold term Uncached.term SolverCounting.dfsTerm
  dsimp only
  apply correct_bind _ _ _ _ _ (count_correct oracle n original _ _ _)
  split
  · exact correct_pure _ _
  · apply correct_bind _ _ _ _ _ (count_correct oracle n original _ _ _)
    apply correct_bind _ _ _ _ _ (branch_correct oracle n original recur f h s e added)
    exact correct_pure _ _

def solve (oracle : Oracle) (n : Nat) (original : List Offline.Edge) :
    Nat → Solver.State → Work Rat
  | fuel, s => memoRat (0,fuel,s.seen,s.observed,s.available.mergeSort (· ≤ ·)) (defer fun _ =>
      match fuel with
      | 0 => pure 0
      | fuel+1 =>
          if capacity n original s = 0 then pure 0 else do
            let a ← Memo.sum (Transitions.remainingEdges (Transitions.freshPairs s.seen) s.observed)
              (fun e => term oracle n original (solve oracle n original fuel) s e 0 1)
            let oldNewAction : Work Rat := if s.seen < n then
                Memo.sum (List.range s.seen) (fun u =>
                  term oracle n original (solve oracle n original fuel) s (u,s.seen) 1 (n-s.seen))
              else pure 0
            let b ← oldNewAction
            let newNewAction : Work Rat := if s.seen+1 < n then
                term oracle n original (solve oracle n original fuel)
                  s (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2)
              else pure 0
            let c ← newNewAction
            pure (a+b+c))

theorem solve_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (s : Solver.State) :
    Correct (spec oracle n original) (solve oracle n original fuel s)
      (Uncached.solve oracle n original fuel s) := by
  induction fuel generalizing s with
  | zero =>
    apply correct_memoRat _ _ _ _ (by
      exact congrArg (fun x : Rat => (0,x))
        (AvailableOrder.solve_perm oracle n original _ s.seen s.observed _ s.available
          (List.mergeSort_perm s.available (· ≤ ·))))
    exact correct_pure _ _
  | succ fuel ih =>
    rw [solve]
    apply correct_memoRat _ _ _ _ (by
      exact congrArg (fun x : Rat => (0,x))
        (AvailableOrder.solve_perm oracle n original _ s.seen s.observed _ s.available
          (List.mergeSort_perm s.available (· ≤ ·))))
    change Correct _ (if capacity n original s = 0 then pure 0 else _) _
    rw [Uncached.solve]
    split
    · exact correct_pure _ _
    · apply correct_bind
      · apply correct_sum
        intro e _
        exact term_correct oracle n original _ _ ih s e 0 1
      · apply correct_bind _ _ _
          (if s.seen < n then total (List.range s.seen) (fun u =>
            Uncached.term oracle n original (Uncached.solve oracle n original fuel)
              s (u,s.seen) 1 (n-s.seen)) else 0)
        · split
          · apply correct_sum
            intro u _
            exact term_correct oracle n original _ _ ih s (u,s.seen) 1 (n-s.seen)
          · exact correct_pure _ _
        · apply correct_bind _ _ _
            (if s.seen+1 < n then
              Uncached.term oracle n original (Uncached.solve oracle n original fuel)
                s (s.seen,s.seen+1) 2 ((n-s.seen)*(n-s.seen-1)/2) else 0)
          · split
            · exact term_correct oracle n original _ _ ih s (s.seen,s.seen+1) 2 _
            · exact correct_pure _ _
          · exact correct_pure _ _

def matching (original : List Offline.Edge) : Nat → List Nat → Work Nat
  | fuel, free => memoNat (2,fuel,0,[],free) (defer fun _ =>
      match fuel with
      | 0 => pure 0
      | fuel+1 => Memo.maximum (original.filter fun e => decide (Offline.legal free e))
          (fun e => do
            let r ← matching original fuel (Offline.remove free e)
            pure (1+r)))

theorem maximum_fold (xs : List Nat) : xs.foldr max 0 = Offline.maximum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Offline.maximum,ih]

theorem matching_correct (oracle : Oracle) (n : Nat) (original : List Offline.Edge)
    (fuel : Nat) (free : List Nat) :
    Correct (spec oracle n original) (matching original fuel free)
      (Offline.matching original fuel free) := by
  induction fuel generalizing free with
  | zero =>
    apply correct_memoNat _ _ _ _ rfl
    exact correct_pure _ _
  | succ fuel ih =>
    rw [matching]
    apply correct_memoNat _ _ _ _ rfl
    change Correct _ (Memo.maximum _ _) _
    rw [Offline.matching, ← maximum_fold]
    apply correct_maximum
    intro e _
    apply correct_bind _ _ _ _ _ (ih _)
    exact correct_pure _ _

def computation (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Work Rat := do
  let numerator ← solve oracle n original original.length Solver.initial
  let denominator ← matching original (n/2) (List.range n)
  pure (numerator / (denominator : Rat))

def ratio (oracle : Oracle) (n : Nat) (original : List Offline.Edge) : Rat :=
  ((computation oracle n original).run ∅).1

/-- The hash-table computation returns exactly the uncached result, for
arbitrary inputs. -/
theorem ratio_eq (oracle : Oracle) (n : Nat) (original : List Offline.Edge) :
    ratio oracle n original = Uncached.ratio oracle n original := by
  have h : Correct (spec oracle n original) (computation oracle n original)
      (Uncached.ratio oracle n original) := by
    apply correct_bind _ _ _ _ _ (solve_correct oracle n original _ _)
    apply correct_bind _ _ _ _ _ (matching_correct oracle n original _ _)
    exact correct_pure _ _
  exact (h ∅ (sound_empty _)).1

end OnlineMatching.Memoized
