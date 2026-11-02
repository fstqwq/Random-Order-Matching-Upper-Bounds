import OnlineMatching.Basic

/-!
# Hidden labelings and transition probabilities

The hidden graph is a uniformly random relabeling of the input graph, and its
edges arrive in uniformly random order. This file enumerates the hidden
labelings and computes the probability of each next observed edge.
-/

/-! ## Enumerating labelings -/

namespace OnlineMatching.Counting

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

/-- Enumerate images of the remaining isolated labels, choosing each host vertex once. -/
def completions {A : Type} [DecidableEq A] : Nat → List A → List (List A)
  | 0, _ => [[]]
  | k+1, free => free.flatMap (fun w => (completions k (free.erase w)).map (w :: ·))

theorem sum_map_constant {A : Type} (xs : List A) (f : A → Nat)
    (c : Nat) (h : ∀ a ∈ xs, f a = c) : (xs.map f).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h a (by simp), ih (fun a ha => h a (by simp [ha]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem completions_length {A : Type} [DecidableEq A] (k : Nat) (free : List A) (hlen : free.length = k) :
    (completions k free).length = factorial k := by
  induction k generalizing free with
  | zero => simp [completions, factorial]
  | succ k ih =>
    rw [completions, List.length_flatMap]
    have h : ∀ w ∈ free, ((completions k (free.erase w)).map (w :: ·)).length = factorial k := by
      intro w hw
      rw [List.length_map]
      apply ih
      rw [List.length_erase_of_mem hw, hlen]
      omega
    rw [sum_map_constant _ _ _ h, hlen, factorial]

theorem completions_spec {A : Type} [DecidableEq A] (k : Nat) (free result : List A) (hlen : free.length = k) :
    result ∈ completions k free ↔ result.Perm free := by
  induction k generalizing free result with
  | zero =>
    have he : free = [] := by simpa using hlen
    subst free
    simp [completions]
  | succ k ih =>
    cases result with
    | nil =>
      simp only [completions, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨w, hw, xs, hxs, he⟩; cases he
      · intro h
        have := h.length_eq
        simp at this
        omega
    | cons w rest =>
      rw [List.cons_perm_iff_perm_erase]
      constructor
      · intro hm
        obtain ⟨v, hv, hrest⟩ := List.mem_flatMap.mp hm
        obtain ⟨xs, hxs, he⟩ := List.mem_map.mp hrest
        cases he
        refine ⟨hv, (ih _ _ ?_).mp hxs⟩
        rw [List.length_erase_of_mem hv, hlen]
        omega
      · rintro ⟨hw, hrest⟩
        apply List.mem_flatMap.mpr
        refine ⟨w, hw, List.mem_map.mpr ⟨rest, ?_, rfl⟩⟩
        apply (ih _ _ ?_).mpr hrest
        rw [List.length_erase_of_mem hw, hlen]
        omega

end OnlineMatching.Counting

/-! ## Transition probabilities -/

namespace OnlineMatching.Transitions

/-- Explicit unordered choices of two fresh labels, enumerated once by u < v. -/
def freshPairs : Nat → List (Nat × Nat)
  | 0 => []
  | s + 1 => freshPairs s ++ (List.range s).map (fun u => (u, s))

theorem freshPairs_length (s : Nat) :
    2 * (freshPairs s).length = s * (s - 1) := by
  induction s with
  | zero => simp [freshPairs]
  | succ s ih =>
    simp only [freshPairs, List.length_append, List.length_map, List.length_range]
    cases s with
    | zero => simp [freshPairs]
    | succ k =>
      simp only [Nat.succ_sub_one, Nat.succ_mul, Nat.mul_succ] at ih ⊢
      omega

theorem freshPairs_length_div (s : Nat) :
    (freshPairs s).length = s * (s - 1) / 2 := by
  have := freshPairs_length s
  omega

theorem mem_freshPairs (s u v : Nat) :
    (u, v) ∈ freshPairs s ↔ u < v ∧ v < s := by
  induction s with
  | zero => simp [freshPairs]
  | succ s ih =>
    simp only [freshPairs, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq]
    rw [ih]
    constructor
    · rintro (h | ⟨a, ha, hu, hv⟩)
      · omega
      · omega
    · intro h
      by_cases hv : v = s
      · right; exact ⟨u, by omega, rfl, hv.symm⟩
      · left; omega

theorem freshPairs_nodup (s : Nat) : (freshPairs s).Nodup := by
  induction s with
  | zero => simp [freshPairs]
  | succ s ih =>
    rw [freshPairs, List.nodup_append]
    refine ⟨ih, ?_, ?_⟩
    · exact List.Pairwise.map (fun u => (u,s))
        (fun a b hne he => hne (Prod.mk.inj he).1) List.nodup_range
    · intro a ha b hb he
      have hv := (mem_freshPairs s a.1 a.2).mp ha
      obtain ⟨u, _, hu⟩ := List.mem_map.mp hb
      have he' := congrArg Prod.snd (he.trans hu.symm)
      simp only at he'
      omega

/-- Outcomes after a compatible hidden labeling is selected, followed by one
remaining edge. Both lists are explicit; no transition probability is assumed. -/
def outcomes (labels : List L) (remaining : L → List E) : List (L × E) :=
  labels.flatMap fun l => (remaining l).map fun e => (l,e)

theorem outcomes_length (labels : List L) (remaining : L → List E) (r : Nat)
    (hr : ∀ l ∈ labels, (remaining l).length = r) :
    (outcomes labels remaining).length = labels.length * r := by
  induction labels with
  | nil => simp [outcomes]
  | cons l ls ih =>
    simp only [outcomes, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons]
    rw [hr l (by simp), show (ls.flatMap fun l => (remaining l).map fun e => (l,e)).length = ls.length*r from
      ih (fun x hx => hr x (by simp [hx]))]
    simp [Nat.add_mul, Nat.add_comm]

/-- Probability of an event in the uniform finite outcome space. -/
def probability (xs : List A) (event : A → Bool) : Rat :=
  ((xs.filter event).length : Rat) / (xs.length : Rat)

theorem total_const (xs : List A) (c : Rat) :
    total xs (fun _ => c) = (xs.length : Rat) * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Rat.natCast_add, Rat.add_mul, Rat.add_comm]

/-- For a fixed edge, each compatible hidden labeling contributes either one
outcome (if it contains that edge) or none. No duplicate edges are allowed. -/
theorem edge_fiber_count [DecidableEq E] (labels : List L)
    (remaining : L → List E) (edge : E)
    (hn : ∀ l ∈ labels, (remaining l).Nodup) :
    ((outcomes labels remaining).filter (fun p => p.2 == edge)).length =
      (labels.filter (fun l => decide (edge ∈ remaining l))).length := by
  simp only [← List.countP_eq_length_filter]
  induction labels with
  | nil => simp [outcomes]
  | cons l ls ih =>
    simp only [outcomes, List.flatMap_cons, List.countP_append, List.countP_map,
      Function.comp_def, List.countP_cons]
    rw [← List.count_eq_countP, (hn l (by simp)).count]
    rw [show List.countP (fun p => p.2 == edge)
        (ls.flatMap fun l => (remaining l).map fun e => (l,e)) =
        List.countP (fun l => decide (edge ∈ remaining l)) ls from
      ih (fun x hx => hn x (by simp [hx]))]
    simp only [decide_eq_true_eq]
    omega

/-- The full-labeled next-edge probability C(H+e)/(r*C(H)), derived from
uniform elementary outcomes. `labels` is the current compatible-labeling list;
the filtered list on the right is precisely compatibility after observing e. -/
theorem next_edge_probability [DecidableEq E] (labels : List L)
    (remaining : L → List E) (edge : E) (r : Nat)
    (hn : ∀ l ∈ labels, (remaining l).Nodup)
    (hr : ∀ l ∈ labels, (remaining l).length = r) :
    probability (outcomes labels remaining) (fun p => p.2 == edge) =
      ((labels.filter (fun l => decide (edge ∈ remaining l))).length : Rat) /
        ((r * labels.length : Nat) : Rat) := by
  unfold probability
  rw [edge_fiber_count labels remaining edge hn, outcomes_length labels remaining r hr,
    Nat.mul_comm labels.length r]

theorem filter_partition_length (xs : List A) (p : A → Bool) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

/-- Removing the t distinct already observed edges leaves m-t edges in every
compatible simple labeled host, independent of its hidden labeling. -/
theorem remaining_length [DecidableEq E] (host observed : List E)
    (hh : host.Nodup) (ho : observed.Nodup)
    (hsub : ∀ e ∈ observed, e ∈ host) :
    (host.filter (fun e => decide (e ∉ observed))).length =
      host.length - observed.length := by
  have hn : (host.filter (fun e => decide (e ∈ observed))).Nodup :=
    hh.sublist List.filter_sublist
  have hp : (host.filter (fun e => decide (e ∈ observed))).Perm observed := by
    apply List.perm_iff_count.mpr
    intro e
    rw [hn.count, ho.count]
    have he : (e ∈ host ∧ e ∈ observed) ↔ e ∈ observed :=
      ⟨fun h => h.2, fun h => ⟨hsub e h, h⟩⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    simp only [he]
  have hlen := hp.length_eq
  have part := filter_partition_length host (fun e => decide (e ∈ observed))
  have hfun : (fun e : E => !(decide (e ∈ observed))) =
      (fun e => decide (e ∉ observed)) := by funext e; simp
  rw [hfun] at part
  omega

def compatible [DecidableEq E] (observed : List E) (host : List E) : Bool :=
  observed.all fun e => decide (e ∈ host)

theorem compatible_iff [DecidableEq E] (observed host : List E) :
    compatible observed host = true ↔ ∀ e ∈ observed, e ∈ host := by
  simp [compatible, List.all_eq_true]

def compatibleLabels [DecidableEq E] (labels : List L) (host : L → List E)
    (observed : List E) : List L :=
  labels.filter fun l => compatible observed (host l)

def remainingEdges [DecidableEq E] (host observed : List E) : List E :=
  host.filter fun e => decide (e ∉ observed)

/-- Concrete transition experiment on the set of compatible labeled hosts. -/
def graphOutcomes [DecidableEq E] (labels : List L) (host : L → List E)
    (observed : List E) : List (L × E) :=
  outcomes (compatibleLabels labels host observed) (fun l => remainingEdges (host l) observed)

theorem compatible_remaining_length [DecidableEq E] (labels : List L)
    (host : L → List E) (observed : List E) (m : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (l : L) (hl : l ∈ compatibleLabels labels host observed) :
    (remainingEdges (host l) observed).length = m - observed.length := by
  have hl' := List.mem_filter.mp hl
  unfold remainingEdges
  rw [remaining_length (host l) observed (hh l hl'.1) ho
      ((compatible_iff observed (host l)).mp hl'.2), hm l hl'.1]

theorem graph_next_edge_probability [DecidableEq E] (labels : List L)
    (host : L → List E) (observed : List E) (m : Nat) (edge : E)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (fresh : edge ∉ observed) :
    probability (graphOutcomes labels host observed) (fun p => p.2 == edge) =
      ((compatibleLabels labels host (edge :: observed)).length : Rat) /
        (((m - observed.length) * (compatibleLabels labels host observed).length : Nat) : Rat) := by
  unfold graphOutcomes
  have hn : ∀ l ∈ compatibleLabels labels host observed,
      (remainingEdges (host l) observed).Nodup := by
    intro l hl
    exact (hh l (List.mem_filter.mp hl).1).sublist List.filter_sublist
  rw [next_edge_probability (compatibleLabels labels host observed)
    (fun l => remainingEdges (host l) observed) edge (m - observed.length) hn
    (compatible_remaining_length labels host observed m hh hm ho)]
  have heq : (compatibleLabels labels host observed).filter
      (fun l => decide (edge ∈ remainingEdges (host l) observed)) =
      compatibleLabels labels host (edge :: observed) := by
    simp only [compatibleLabels, remainingEdges, List.filter_filter]
    congr 1
    funext l
    simp [compatible, List.mem_filter, fresh]
  rw [heq]

theorem total_add (xs : List A) (f g : A → Rat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp [total, Rat.zero_add]
  | cons x xs ih => simp [total, ih]; grind

theorem total_indicator [DecidableEq E] (es : List E) (edge : E) :
    total es (fun e => if e == edge then 1 else 0) = (es.count edge : Rat) := by
  induction es with
  | nil => simp [total]
  | cons e es ih =>
    simp only [total, List.count_cons, Rat.natCast_add]
    rw [ih]
    cases h : e == edge <;> simp [Rat.add_comm]

/-- Counting all distinct edge fibres counts every elementary outcome exactly once. -/
theorem fiber_mass_count [DecidableEq E] (xs : List A) (classify : A → E)
    (catalog : List E) (hn : catalog.Nodup)
    (hc : ∀ x ∈ xs, classify x ∈ catalog) :
    total catalog (fun e => ((xs.filter (fun x => classify x == e)).length : Rat)) =
      (xs.length : Rat) := by
  induction xs with
  | nil => simp [total_const]
  | cons x xs ih =>
    have he : total catalog (fun e => (((x :: xs).filter (fun y => classify y == e)).length : Rat)) =
        total catalog (fun e => ((xs.filter (fun y => classify y == e)).length : Rat) +
          if e == classify x then 1 else 0) := by
      apply total_congr
      intro e _
      by_cases h : classify x = e
      · simp [h, Rat.natCast_add, Rat.add_comm]
      · have h' : e ≠ classify x := Ne.symm h
        simp [h, h', Rat.add_zero]
    rw [he, total_add, ih (fun y hy => hc y (by simp [hy])), total_indicator,
      hn.count, ite_eq_left (hc x (by simp))]
    simp [Rat.natCast_add]

theorem classified_mass_one [DecidableEq E] (xs : List A) (classify : A → E)
    (catalog : List E) (hn : catalog.Nodup)
    (hc : ∀ x ∈ xs, classify x ∈ catalog) (hx : xs ≠ []) :
    total catalog (fun e => probability xs (fun x => classify x == e)) = 1 := by
  simp only [probability, Rat.div_def]
  rw [total_mul, fiber_mass_count xs classify catalog hn hc]
  apply Rat.mul_inv_cancel
  simpa using Nat.ne_of_gt (List.length_pos_iff.mpr hx)

theorem probability_nonnegative (xs : List A) (event : A → Bool) :
    0 ≤ probability xs event := by
  by_cases hx : xs = []
  · simp [hx, probability, Rat.div_def]
  · unfold probability
    rw [Rat.div_def]
    apply Rat.mul_nonneg Rat.natCast_nonneg
    exact Rat.le_of_lt (Rat.inv_pos.mpr
      (Rat.natCast_pos.mpr (List.length_pos_iff.mpr hx)))

/-- An involution of the finite hidden-labeling universe preserves counting. -/
theorem involution_preserves_list [DecidableEq L] (labels : List L) (f : L → L)
    (hn : labels.Nodup) (hi : ∀ l, f (f l) = l)
    (hc : ∀ l ∈ labels, f l ∈ labels) : (labels.map f).Perm labels := by
  have hm : (labels.map f).Nodup :=
    List.Pairwise.map f (fun a b hne he => hne (by
      have := congrArg f he
      simpa [hi] using this)) hn
  apply List.perm_iff_count.mpr
  intro l
  rw [hm.count, hn.count]
  have he : l ∈ labels.map f ↔ l ∈ labels := by
    constructor
    · intro h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      exact hc x hx
    · intro h
      exact List.mem_map.mpr ⟨f l, hc l h, hi l⟩
  simp only [he]

/-- Explicit transport suffices for equal compatible-labeling counts; equality
of those counts is concluded here, rather than assumed. -/
theorem involution_event_counts [DecidableEq L] (labels : List L) (f : L → L)
    (hn : labels.Nodup) (hi : ∀ l, f (f l) = l)
    (hc : ∀ l ∈ labels, f l ∈ labels)
    (p q : L → Bool) (hpq : ∀ l ∈ labels, q (f l) = p l) :
    (labels.filter p).length = (labels.filter q).length := by
  have h := ((involution_preserves_list labels f hn hi hc).filter q).length_eq
  rw [List.filter_map, List.length_map] at h
  have he : labels.filter (q ∘ f) = labels.filter p :=
    List.filter_congr hpq
  simpa [he] using h

def swapLabels (x y v : Nat) : Nat := if v = x then y else if v = y then x else v

theorem swapLabels_involution (x y v : Nat) :
    swapLabels x y (swapLabels x y v) = v := by
  simp only [swapLabels]
  split <;> split <;> grind

theorem swapLabels_seen (k x y v : Nat) (hx : k ≤ x) (hy : k ≤ y) (hv : v < k) :
    swapLabels x y v = v := by
  have h1 : v ≠ x := by omega
  have h2 : v ≠ y := by omega
  simp [swapLabels, h1, h2]

/-- The actual permutation exchanging two still-unseen labels. -/
def unseenSwap (x y : Nat) : Permutation Nat where
  forward := swapLabels x y
  backward := swapLabels x y
  left_inverse := swapLabels_involution x y
  right_inverse := swapLabels_involution x y

end OnlineMatching.Transitions

/-! ## Edge orders with a given prefix -/

namespace OnlineMatching.Prefix

variable {E : Type} [DecidableEq E]

omit [DecidableEq E] in
private theorem branches_nodup (xs : List E) (f : E → List (List E))
    (hx : xs.Nodup) (hf : ∀ x ∈ xs, (f x).Nodup) :
    (xs.flatMap (fun x => (f x).map (x :: ·))).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hx
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, ih htail (fun x hx => hf x (by simp [hx])), ?_⟩
    · exact List.Pairwise.map _ (fun _ _ hne he => hne (List.cons.inj he).2)
        (hf x (by simp))
    · intro a ha b hb heq
      obtain ⟨as, has, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp hb
      have hxy : x = y := (List.cons.inj heq).1
      exact hnot (hxy ▸ hy)

theorem completions_nodup (k : Nat) (free : List E) (hn : free.Nodup) :
    (Counting.completions k free).Nodup := by
  induction k generalizing free with
  | zero => simp [Counting.completions]
  | succ k ih =>
    apply branches_nodup _ _ hn
    intro x _
    exact ih _ (List.erase_sublist.nodup hn)

end OnlineMatching.Prefix
