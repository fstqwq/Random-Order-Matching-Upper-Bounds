import Std

/-!
# Basic definitions

Finite Bellman models and their optimality against strategy trees, offline
maximum matchings, vertex permutations, and list utilities.
-/

/-! ## Bellman models -/

namespace OnlineMatching

def total {α : Type} : List α → (α → Rat) → Rat
  | [], _ => 0
  | x :: xs, f => f x + total xs f

theorem total_congr {α : Type} (xs : List α) (f g : α → Rat)
    (h : ∀ x ∈ xs, f x = g x) : total xs f = total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [total]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem total_mono {α : Type} (xs : List α) (f g : α → Rat)
    (h : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [total]
    exact Rat.le_trans (Rat.add_le_add_right.mpr hx) (Rat.add_le_add_left.mpr ht)

structure Model (S O : Type) where
  observations : S → List O
  probability : S → O → Rat
  nonnegative : ∀ s o, o ∈ observations s → 0 ≤ probability s o
  legal : S → O → Bool
  reject : S → O → S
  accept : S → O → S

def Strategy (O : Type) : Nat → Type
  | 0 => Unit
  | k + 1 => O → Bool × Strategy O k

def value {S O : Type} (M : Model S O) : Nat → S → Rat
  | 0, _ => 0
  | k + 1, s => total (M.observations s) fun o =>
      M.probability s o *
        (if M.legal s o then
          max (value M k (M.reject s o)) (1 + value M k (M.accept s o))
        else value M k (M.reject s o))

def eval {S O : Type} (M : Model S O) : (k : Nat) → S → Strategy O k → Rat
  | 0, _, _ => 0
  | k + 1, s, p => total (M.observations s) fun o =>
      M.probability s o *
        (if (p o).1 && M.legal s o then
          1 + eval M k (M.accept s o) (p o).2
        else eval M k (M.reject s o) (p o).2)

theorem le_max_left (a b : Rat) : a ≤ max a b := by
  rw [Rat.max_def]; split <;> grind

theorem le_max_right (a b : Rat) : b ≤ max a b := by
  rw [Rat.max_def]; split <;> grind

theorem eval_le_value {S O : Type} (M : Model S O) (k : Nat) (s : S)
    (p : Strategy O k) : eval M k s p ≤ value M k s := by
  induction k generalizing s with
  | zero => exact Rat.le_refl
  | succ k ih =>
    apply total_mono
    intro o ho
    apply Rat.mul_le_mul_of_nonneg_left _ (M.nonnegative s o ho)
    cases hl : M.legal s o <;> cases hp : (p o).1
    · simpa [hl, hp] using ih (M.reject s o) (p o).2
    · simpa [hl, hp] using ih (M.reject s o) (p o).2
    · simpa [hl, hp] using Rat.le_trans (ih (M.reject s o) (p o).2)
        (le_max_left (value M k (M.reject s o)) (1 + value M k (M.accept s o)))
    · simpa [hl, hp] using Rat.le_trans
        (Rat.add_le_add_left.mpr (ih (M.accept s o) (p o).2))
        (le_max_right (value M k (M.reject s o)) (1 + value M k (M.accept s o)))

def best {S O : Type} (M : Model S O) : (k : Nat) → S → Strategy O k
  | 0, _ => ()
  | k + 1, s => fun o =>
      if M.legal s o && decide (value M k (M.reject s o) ≤ 1 + value M k (M.accept s o))
      then (true, best M k (M.accept s o))
      else (false, best M k (M.reject s o))

theorem best_attains {S O : Type} (M : Model S O) (k : Nat) (s : S) :
    eval M k s (best M k s) = value M k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    apply total_congr
    intro o _
    cases hl : M.legal s o
    · simp [best, hl, ih]
    · by_cases h : value M k (M.reject s o) ≤ 1 + value M k (M.accept s o)
      · simp [best, hl, h, ih, Rat.max_def]
      · simp [best, hl, h, ih, Rat.max_def]

/-- Optimality against the full observation-history strategy tree. -/
theorem value_correct {S O : Type} (M : Model S O) (k : Nat) (s : S) :
    (∀ p, eval M k s p ≤ value M k s) ∧
    (∃ p, eval M k s p = value M k s) :=
  ⟨eval_le_value M k s, ⟨best M k s, best_attains M k s⟩⟩

/-- The local `if best < upper` rule for rational values. -/
theorem skip_reject (accept reject upper : Rat) (h : reject ≤ upper) :
    (if accept < upper then max accept reject else accept) = max accept reject := by
  split
  · rfl
  · rw [Rat.max_def]
    split <;> grind

theorem max_le (a b c : Rat) (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  rw [Rat.max_def]; split <;> assumption

theorem total_mul (xs : List α) (f : α → Rat) (c : Rat) :
    total xs (fun x => f x * c) = total xs f * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Rat.add_mul]

theorem value_nonnegative {S O : Type} (M : Model S O) (k : Nat) (s : S) :
    0 ≤ value M k s := by
  induction k generalizing s with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have hz : total (M.observations s) (fun _ => (0 : Rat)) = 0 := by
      induction M.observations s with
      | nil => rfl
      | cons x xs h => simp [total, h, Rat.zero_add]
    rw [← hz]
    apply total_mono
    intro o ho
    apply Rat.mul_nonneg (M.nonnegative s o ho)
    cases hl : M.legal s o
    · simpa [hl] using ih (M.reject s o)
    · simpa [hl] using Rat.le_trans (ih (M.reject s o))
        (le_max_left (value M k (M.reject s o)) (1 + value M k (M.accept s o)))

/-- A resource bound decreases by at least one when an edge is accepted.
These are local, checkable transition conditions, not an assumption about the DP's value. -/
structure Budget {S O : Type} (M : Model S O) (upper : S → Rat) : Prop where
  nonnegative : ∀ s, 0 ≤ upper s
  probability_sum : ∀ s, total (M.observations s) (M.probability s) ≤ 1
  reject : ∀ s o, o ∈ M.observations s → upper (M.reject s o) ≤ upper s
  accept : ∀ s o, o ∈ M.observations s → M.legal s o = true →
    1 + upper (M.accept s o) ≤ upper s

theorem value_le_budget {S O : Type} (M : Model S O) (upper : S → Rat)
    (b : Budget M upper) (k : Nat) (s : S) : value M k s ≤ upper s := by
  induction k generalizing s with
  | zero => exact b.nonnegative s
  | succ k ih =>
    calc
      value M (k + 1) s ≤ total (M.observations s) (fun o => M.probability s o * upper s) := by
        apply total_mono
        intro o ho
        apply Rat.mul_le_mul_of_nonneg_left _ (M.nonnegative s o ho)
        have hr := Rat.le_trans (ih (M.reject s o)) (b.reject s o ho)
        cases hl : M.legal s o
        · simpa [hl] using hr
        · simp only [↓reduceIte]
          apply max_le _ _ _ hr
          exact Rat.le_trans (Rat.add_le_add_left.mpr (ih (M.accept s o))) (b.accept s o ho hl)
      _ = total (M.observations s) (M.probability s) * upper s := total_mul _ _ _
      _ ≤ 1 * upper s := Rat.mul_le_mul_of_nonneg_right (b.probability_sum s) (b.nonnegative s)
      _ = upper s := Rat.one_mul _

def prunedValue {S O : Type} (M : Model S O) (upper : S → Rat) : Nat → S → Rat
  | 0, _ => 0
  | k + 1, s =>
      if upper s = 0 then 0 else
      total (M.observations s) fun o =>
        let best := if M.legal s o then 1 + prunedValue M upper k (M.accept s o) else 0
        M.probability s o *
          (if best < upper s then max best (prunedValue M upper k (M.reject s o)) else best)

/-- Resource pruning preserves the Bellman value. -/
theorem prunedValue_eq_value {S O : Type} (M : Model S O) (upper : S → Rat)
    (b : Budget M upper) (k : Nat) (s : S) : prunedValue M upper k s = value M k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [prunedValue]
    split
    · rename_i h
      have hi := value_le_budget M upper b (k + 1) s
      have lo := value_nonnegative M (k + 1) s
      rw [h] at hi
      exact (Rat.le_antisymm hi lo).symm
    · apply total_congr
      intro o ho
      simp only [ih]
      have hr := Rat.le_trans (value_le_budget M upper b k (M.reject s o)) (b.reject s o ho)
      rw [skip_reject _ _ _ hr]
      cases hl : M.legal s o
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Rat.max_def, ite_eq_left (value_nonnegative M k (M.reject s o))]
      · simp only [↓reduceIte]
        congr 1
        rw [Rat.max_def, Rat.max_def]
        split <;> split <;> grind

end OnlineMatching

/-! ## Offline maximum matching -/

namespace OnlineMatching.Offline

abbrev Edge := Nat × Nat

def legal (free : List Nat) (e : Edge) : Prop :=
  e.1 ∈ free ∧ e.2 ∈ free ∧ e.1 ≠ e.2

instance (free : List Nat) (e : Edge) : Decidable (legal free e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def remove (free : List Nat) (e : Edge) : List Nat :=
  (free.erase e.1).erase e.2

/-- A matching is constructed only from host edges with unused distinct endpoints. -/
inductive Fits (edges : List Edge) : List Nat → List Edge → Prop
  | nil (free) : Fits edges free []
  | cons {free e rest} : e ∈ edges → legal free e →
      Fits edges (remove free e) rest → Fits edges free (e :: rest)

def maximum : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maximum xs)

theorem le_maximum (xs : List Nat) (x : Nat) (h : x ∈ xs) : x ≤ maximum xs := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maximum_attains (xs : List Nat) : maximum xs = 0 ∨ maximum xs ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    by_cases h : x ≤ maximum xs
    · rw [maximum, Nat.max_eq_right h]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr (List.mem_cons_of_mem _ ih)
    · rw [maximum, Nat.max_eq_left (by omega)]
      exact Or.inr (by simp)

def matching (edges : List Edge) : Nat → List Nat → Nat
  | 0, _ => 0
  | k + 1, free => maximum ((edges.filter (fun e => decide (legal free e))).map
      (fun e => 1 + matching edges k (remove free e)))

theorem fits_le_matching (edges : List Edge) (k : Nat) (free : List Nat)
    (chosen : List Edge) (h : Fits edges free chosen) (hk : chosen.length ≤ k) :
    chosen.length ≤ matching edges k free := by
  induction k generalizing free chosen with
  | zero => simp only [matching]; omega
  | succ k ih =>
    cases h with
    | nil => exact Nat.zero_le _
    | cons he hl ht =>
      simp only [List.length_cons] at hk ⊢
      have hc := ih _ _ ht (by omega)
      rw [Nat.add_comm]
      apply Nat.le_trans (Nat.add_le_add_left hc 1)
      apply le_maximum
      apply List.mem_map.mpr
      exact ⟨_, List.mem_filter.mpr ⟨he, by simpa⟩, rfl⟩

theorem matching_attains (edges : List Edge) (k : Nat) (free : List Nat) :
    ∃ chosen, Fits edges free chosen ∧ chosen.length = matching edges k free := by
  induction k generalizing free with
  | zero => exact ⟨[], Fits.nil free, rfl⟩
  | succ k ih =>
    rcases maximum_attains ((edges.filter (fun e => decide (legal free e))).map
      (fun e => 1 + matching edges k (remove free e))) with hz | hm
    · exact ⟨[], Fits.nil free, hz.symm⟩
    · obtain ⟨e, he, hv⟩ := List.mem_map.mp hm
      obtain ⟨he, hl⟩ := List.mem_filter.mp he
      obtain ⟨chosen, hc, hn⟩ := ih (remove free e)
      refine ⟨e :: chosen, Fits.cons he (by simpa using hl) hc, ?_⟩
      simp only [List.length_cons, hn]
      simpa [matching, Nat.add_comm] using hv

theorem remove_length (free : List Nat) (e : Edge) (h : legal free e) :
    (remove free e).length + 2 = free.length := by
  have hmem : e.2 ∈ free.erase e.1 := by
    exact (List.mem_erase_of_ne (Ne.symm h.2.2)).mpr h.2.1
  have ha := List.length_erase_of_mem h.1
  have hb := List.length_erase_of_mem hmem
  have hpos := List.length_pos_of_mem hmem
  unfold remove
  omega

theorem fits_size (edges : List Edge) (free : List Nat) (chosen : List Edge)
    (h : Fits edges free chosen) : 2 * chosen.length ≤ free.length := by
  induction h with
  | nil => simp
  | @cons free e rest he hl ht ih =>
    have hs := remove_length free e hl
    simp only [List.length_cons]
    omega

/-- In particular, fuel `free.length / 2` suffices for the unbounded recursion. -/
theorem matching_correct (edges : List Edge) (free : List Nat) :
    (∀ chosen, Fits edges free chosen →
      chosen.length ≤ matching edges (free.length / 2) free) ∧
    (∃ chosen, Fits edges free chosen ∧
      chosen.length = matching edges (free.length / 2) free) := by
  constructor
  · intro chosen h
    apply fits_le_matching edges _ free chosen h
    have := fits_size edges free chosen h
    omega
  · exact matching_attains edges _ free

end OnlineMatching.Offline

/-! ## Permutations and relabeled graphs -/

namespace OnlineMatching

/-- A permutation with both inverse laws. -/
structure Permutation (V : Type) where
  forward : V → V
  backward : V → V
  left_inverse : ∀ v, backward (forward v) = v
  right_inverse : ∀ v, forward (backward v) = v

theorem Permutation.injective {V : Type} (p : Permutation V)
    {u v : V} (h : p.forward u = p.forward v) : u = v := by
  have := congrArg p.backward h
  simpa [p.left_inverse] using this

abbrev Graph (V : Type) := V → V → Bool

def renameGraph {V : Type} (p : Permutation V) (g : Graph V) : Graph V :=
  fun u v => g (p.backward u) (p.backward v)

theorem total_map {A B : Type} (xs : List A) (f : A → B) (g : B → Rat) :
    total (xs.map f) g = total xs (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, ih]

end OnlineMatching

/-! ## Finite sums -/

namespace OnlineMatching

theorem total_append (xs ys : List α) (f : α → Rat) :
    total (xs ++ ys) f = total xs f + total ys f := by
  induction xs with
  | nil => simp [total, Rat.zero_add]
  | cons x xs ih => simp [total, ih, Rat.add_assoc]

theorem total_flatMap (xs : List α) (fibers : α → List β) (f : β → Rat) :
    total (xs.flatMap fibers) f = total xs (fun x => total (fibers x) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, total_append, total, ih]

theorem total_perm {xs ys : List α} (h : xs.Perm ys) (f : α → Rat) :
    total xs f = total ys f := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [total, ih]
  | swap a b xs => simp [total, Rat.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end OnlineMatching

/-! ## Selection order -/

namespace OnlineMatching.Ordering

/-- Scanning candidates always selects an input candidate, independently of ties. -/
def best (prefer : Nat → Nat → Bool) : Nat → List Nat → Nat
  | a, [] => a
  | a, b :: rest => best prefer (if prefer a b then b else a) rest

theorem best_mem (prefer : Nat → Nat → Bool) (a : Nat) (rest : List Nat) :
    best prefer a rest ∈ a :: rest := by
  induction rest generalizing a with
  | nil => simp [best]
  | cons b rest ih =>
    simp only [best]
    cases h : prefer a b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ht := ih a
      simp only [List.mem_cons] at ht ⊢
      grind
    · simp only [↓reduceIte]
      have ht := ih b
      simp only [List.mem_cons] at ht ⊢
      grind

/-- The score may depend on every previously placed vertex, as in `count_fits`.
Erasing the selected candidate is the list counterpart of setting its placed bit. -/
def orderBy (prefer : List Nat → Nat → Nat → Bool) :
    Nat → List Nat → List Nat → List Nat
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, a :: rest, placed =>
      let chosen := best (prefer placed) a rest
      chosen :: orderBy prefer fuel ((a :: rest).erase chosen) (chosen :: placed)

theorem orderBy_perm (prefer : List Nat → Nat → Nat → Bool)
    (fuel : Nat) (remaining placed : List Nat) (h : remaining.length = fuel) :
    (orderBy prefer fuel remaining placed).Perm remaining := by
  induction fuel generalizing remaining placed with
  | zero =>
    have he : remaining = [] := by simpa using h
    simp [he, orderBy]
  | succ fuel ih =>
    cases remaining with
    | nil => simp at h
    | cons a rest =>
      have hm := best_mem (prefer placed) a rest
      have hl := List.length_erase_of_mem hm
      have ht := ih ((a :: rest).erase (best (prefer placed) a rest))
        (best (prefer placed) a rest :: placed) (by omega)
      simp only [orderBy]
      exact ht.cons _ |>.trans (List.perm_cons_erase hm).symm

end OnlineMatching.Ordering
