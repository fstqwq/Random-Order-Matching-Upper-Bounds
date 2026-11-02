import OnlineMatching.Reference.Transitions

/-!
# Reference Bellman recurrence

A state is the labeled graph of observed edges together with the unmatched
labels. `ImplementationGraph.referenceModel` is the Bellman model on these
states, with no isomorphism reduction, and `ImplementationGraph.referenceRatio`
is its optimal value divided by the maximum matching size.
-/

/-! ## Resource bound and revealed labels -/

namespace OnlineMatching.Implementation

/-- The resource bound used by `solve`: unseen vertices are counted as free. -/
def resource (remaining free : Nat) : Nat := min remaining (free / 2)

theorem resource_reject (remaining free : Nat) :
    resource (remaining - 1) free ≤ resource remaining free := by
  unfold resource
  omega

theorem resource_accept (remaining free free' : Nat)
    (hr : 0 < remaining) (hf : free' + 2 = free) :
    1 + resource (remaining - 1) free' ≤ resource remaining free := by
  unfold resource
  omega

/-- Newly observed labels are exactly `seen, ..., seen+added-1`. -/
def revealList (available : List Nat) (seen added : Nat) : List Nat :=
  available ++ List.range' seen added

def expand (n seen : Nat) (available : List Nat) : List Nat :=
  available ++ List.range' seen (n - seen)

theorem revealList_nodup (available : List Nat) (seen added : Nat)
    (hn : available.Nodup) (hr : ∀ v ∈ available, v < seen) :
    (revealList available seen added).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hn, List.nodup_range', ?_⟩
  intro u hu v hv heq
  have hlt := hr u hu
  obtain ⟨i, hi, hv⟩ := List.mem_range'.mp hv
  simp only [Nat.one_mul] at hv
  omega

/-- Making fresh vertices explicit preserves the complete list of free labels. -/
theorem expand_reveal (n seen added : Nat) (available : List Nat)
    (h : seen + added ≤ n) :
    expand n (seen + added) (revealList available seen added) =
      expand n seen available := by
  simp only [expand, revealList, List.append_assoc]
  have hr : List.range' seen added ++ List.range' (seen + added) (n - (seen + added)) =
      List.range' seen (n - seen) := by
    have ha := List.range'_append (s := seen) (m := added)
      (n := n - (seen + added)) (step := 1)
    have he : added + (n - (seen + added)) = n - seen := by omega
    simpa only [Nat.one_mul, he] using ha
  rw [hr]

theorem expand_length (n seen : Nat) (available : List Nat) :
    (expand n seen available).length = available.length + (n - seen) := by
  simp [expand]

theorem compressed_upper_eq (n seen remaining : Nat) (available : List Nat)
    (h : seen ≤ n) :
    resource remaining (available.length + n - seen) =
      resource remaining (expand n seen available).length := by
  simp only [expand_length]
  congr 1
  omega

/-- A nonempty valid edge list has a nonzero matching denominator. -/
theorem matching_positive (edges : List Offline.Edge) (free : List Nat)
    (e : Offline.Edge) (he : e ∈ edges) (hl : Offline.legal free e) :
    0 < Offline.matching edges (free.length / 2) free := by
  have hs : Offline.Fits edges free [e] :=
    Offline.Fits.cons he hl (Offline.Fits.nil _)
  have hm := (Offline.matching_correct edges free).1 [e] hs
  simp only [List.length_singleton] at hm
  omega

theorem mem_rename (p : Permutation Nat) (free : List Nat) (v : Nat) :
    p.forward v ∈ free.map p.forward ↔ v ∈ free := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    have : w = v := p.injective he
    simpa [this] using hw
  · intro h
    exact List.mem_map.mpr ⟨v, h, rfl⟩

theorem legal_rename (p : Permutation Nat) (free : List Nat) (e : Offline.Edge) :
    Offline.legal (free.map p.forward) (p.forward e.1, p.forward e.2) ↔
      Offline.legal free e := by
  simp only [Offline.legal, mem_rename]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun he => h3 (congrArg p.forward he)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun he => h3 (p.injective he)⟩

theorem rename_erase (p : Permutation Nat) (free : List Nat) (v : Nat) :
    (free.erase v).map p.forward = (free.map p.forward).erase (p.forward v) := by
  induction free with
  | nil => simp
  | cons a free ih =>
    by_cases h : a = v
    · subst a
      simp
    · have hp : p.forward a ≠ p.forward v := fun he => h (p.injective he)
      simp [h, hp, ih]

theorem remove_rename (p : Permutation Nat) (free : List Nat) (e : Offline.Edge) :
    (Offline.remove free e).map p.forward =
      Offline.remove (free.map p.forward) (p.forward e.1, p.forward e.2) := by
  simp [Offline.remove, rename_erase]

end OnlineMatching.Implementation

/-! ## Reference model -/

namespace OnlineMatching.ImplementationGraph

open Implementation Transitions

theorem dedup_nodup [DecidableEq A] (xs : List A) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · simp [List.mem_eraseDups, List.mem_filter]
    · exact dedup_nodup (xs.filter fun b => !b == a)
termination_by xs.length
decreasing_by
  have := List.length_filter_le (fun b => !b == a) xs
  simp only [List.length_cons]
  omega

/-- Unlike elementary outcomes, these public states do not expose the hidden labeling. -/
structure State where
  observed : List Offline.Edge
  free : List Nat

def possible (labels : List L) (host : L → List Offline.Edge) (s : State) :
    List Offline.Edge :=
  ((graphOutcomes labels host s.observed).map Prod.snd).eraseDups

def nextWeight (labels : List L) (host : L → List Offline.Edge) (s : State)
    (e : Offline.Edge) : Rat :=
  probability (graphOutcomes labels host s.observed) (fun p => p.2 == e)

theorem possible_mass (labels : List L) (host : L → List Offline.Edge) (s : State) :
    total (possible labels host s) (nextWeight labels host s) ≤ 1 := by
  by_cases hx : graphOutcomes labels host s.observed = []
  · simp [possible, hx, total]
    decide
  · have hn : (possible labels host s).Nodup := dedup_nodup _
    have hc : ∀ x ∈ graphOutcomes labels host s.observed,
        x.2 ∈ possible labels host s := by
      intro x hx
      simp only [possible, List.mem_eraseDups]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hm := classified_mass_one (graphOutcomes labels host s.observed)
      Prod.snd (possible labels host s) hn hc hx
    change total (possible labels host s)
      (fun e => probability (graphOutcomes labels host s.observed) (fun p => p.2 == e)) ≤ 1
    rw [hm]
    exact Rat.le_refl

def reject (s : State) (e : Offline.Edge) : State := ⟨e :: s.observed, s.free⟩
def accept (s : State) (e : Offline.Edge) : State :=
  ⟨e :: s.observed, Offline.remove s.free e⟩

/-- An entirely concrete finite conditional-edge model. The observation is the edge,
not the hidden labeling; labels are summed out in `nextWeight`. -/
def model (labels : List L) (host : L → List Offline.Edge) (m : Nat) :
    Model State Offline.Edge where
  observations s := if s.observed.length < m then possible labels host s else []
  probability := nextWeight labels host
  nonnegative _s _e _ := probability_nonnegative _ _
  legal s e := decide (Offline.legal s.free e)
  reject := reject
  accept := accept

def upper (m : Nat) (s : State) : Rat :=
  (resource (m - s.observed.length) s.free.length : Rat)

/-- The actual conditional distribution supplies the mass inequality, so this
budget theorem has no probability-normalization or Bellman-value hypotheses. -/
theorem graph_budget (labels : List L) (host : L → List Offline.Edge) (m : Nat) :
    Budget (model labels host m) (upper m) := by
  constructor
  · intro s
    exact Rat.natCast_nonneg
  · intro s
    simp only [model]
    split
    · exact possible_mass labels host s
    · change (0 : Rat) ≤ 1
      decide
  · intro s e he
    change (resource (m - (e :: s.observed).length) s.free.length : Rat) ≤
      (resource (m - s.observed.length) s.free.length : Rat)
    apply Rat.natCast_le_natCast.mpr
    have heq : m - (e :: s.observed).length = m - s.observed.length - 1 := by
      simp only [List.length_cons]
      omega
    rw [heq]
    exact resource_reject _ _
  · intro s e he hl
    have hr : s.observed.length < m := by
      simp only [model] at he
      split at he
      · assumption
      · simp at he
    have hf : Offline.legal s.free e := by simpa [model] using hl
    have h := resource_accept (m - s.observed.length) s.free.length
      (Offline.remove s.free e).length (by omega) (Offline.remove_length s.free e hf)
    have heq : m - (e :: s.observed).length = m - s.observed.length - 1 := by
      simp only [List.length_cons]
      omega
    have hc := Rat.natCast_le_natCast.mpr h
    simpa only [model, upper, accept, heq, Rat.natCast_add, Rat.natCast_ofNat] using hc

theorem graph_pruning_correct (labels : List L) (host : L → List Offline.Edge)
    (m fuel : Nat) (s : State) :
    prunedValue (model labels host m) (upper m) fuel s =
      value (model labels host m) fuel s :=
  prunedValue_eq_value _ _ (graph_budget labels host m) fuel s

/-- Optimality of the pruned recursion against public edge-history strategies. -/
theorem graph_optimality (labels : List L) (host : L → List Offline.Edge)
    (m fuel : Nat) (s : State) :
    (∀ p, eval (model labels host m) fuel s p ≤
      prunedValue (model labels host m) (upper m) fuel s) ∧
    (∃ p, eval (model labels host m) fuel s p =
      prunedValue (model labels host m) (upper m) fuel s) := by
  rw [graph_pruning_correct]
  exact value_correct _ _ _

/-- Every enumerated public observation is a fresh edge and leaves a nonempty
compatible-labeling set. This is proved from the explicit outcome enumeration. -/
theorem possible_reachable (labels : List L) (host : L → List Offline.Edge)
    (s : State) (e : Offline.Edge) (he : e ∈ possible labels host s) :
    e ∉ s.observed ∧ compatibleLabels labels host (e :: s.observed) ≠ [] := by
  simp only [possible, List.mem_eraseDups, List.mem_map] at he
  obtain ⟨p, hp, hpedge⟩ := he
  simp only [graphOutcomes, outcomes, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨l, hl, edge, hedge, hp⟩ := hp
  subst p
  simp only at hpedge
  subst e
  have hl' := List.mem_filter.mp hl
  have hedge' := List.mem_filter.mp hedge
  have hfresh : edge ∉ s.observed := by simpa using hedge'.2
  refine ⟨hfresh, ?_⟩
  have hchild : l ∈ compatibleLabels labels host (edge :: s.observed) := by
    apply List.mem_filter.mpr
    refine ⟨hl'.1, ?_⟩
    apply (compatible_iff _ _).mpr
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hedge'.1
    · exact (compatible_iff _ _).mp hl'.2 f hf
  intro hempty
  rw [hempty] at hchild
  simp at hchild

/-- All full hidden vertex relabelings, represented as image lists. -/
def hiddenLabels (n : Nat) : List (List Nat) :=
  Counting.completions n (List.range n)

theorem hiddenLabels_spec (n : Nat) (p : List Nat) :
    p ∈ hiddenLabels n ↔ p.Perm (List.range n) :=
  Counting.completions_spec n (List.range n) p (by simp)

def labelAt (p : List Nat) (v : Nat) : Nat := p[v]?.getD 0

def labelledHost (edges : List Offline.Edge) (p : List Nat) : List Offline.Edge :=
  edges.map fun e =>
    let u := labelAt p e.1
    let v := labelAt p e.2
    (min u v, max u v)

def initial (n : Nat) : State := ⟨[], List.range n⟩

def referenceModel (n : Nat) (edges : List Offline.Edge) : Model State Offline.Edge :=
  model (hiddenLabels n) (labelledHost edges) edges.length

def denominator (n : Nat) (edges : List Offline.Edge) : Nat :=
  Offline.matching edges (n / 2) (List.range n)

/-- The reference ratio for a vertex count and edge list. -/
def referenceRatio (n : Nat) (edges : List Offline.Edge) : Rat :=
  prunedValue (referenceModel n edges) (upper edges.length) edges.length (initial n) /
    (denominator n edges : Rat)

def strategyRatio (n : Nat) (edges : List Offline.Edge)
    (strategy : Strategy Offline.Edge edges.length) : Rat :=
  eval (referenceModel n edges) edges.length (initial n) strategy /
    (denominator n edges : Rat)

theorem denominator_positive (n : Nat) (edges : List Offline.Edge)
    (e : Offline.Edge) (he : e ∈ edges)
    (hu : e.1 < n) (hv : e.2 < n) (hne : e.1 ≠ e.2) :
    0 < denominator n edges := by
  have h := matching_positive edges (List.range n) e he
    ⟨List.mem_range.mpr hu, List.mem_range.mpr hv, hne⟩
  simpa [denominator] using h

/-- Exact optimality of the concrete reference ratio for the public edge-history
model, with only the nonempty valid-edge condition needed for the denominator. -/
theorem reference_ratio_optimal (n : Nat) (edges : List Offline.Edge)
    (e : Offline.Edge) (he : e ∈ edges)
    (hu : e.1 < n) (hv : e.2 < n) (hne : e.1 ≠ e.2) :
    (∀ strategy, strategyRatio n edges strategy ≤ referenceRatio n edges) ∧
    (∃ strategy, strategyRatio n edges strategy = referenceRatio n edges) := by
  have hd : 0 < (denominator n edges : Rat) :=
    Rat.natCast_pos.mpr (denominator_positive n edges e he hu hv hne)
  have hi : 0 ≤ (denominator n edges : Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  obtain ⟨hb, strategy, hs⟩ := graph_optimality
    (hiddenLabels n) (labelledHost edges) edges.length edges.length (initial n)
  constructor
  · intro strategy
    unfold strategyRatio referenceRatio
    simp only [Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right (hb strategy) hi
  · exact ⟨strategy, congrArg (fun x => x / (denominator n edges : Rat)) hs⟩

end OnlineMatching.ImplementationGraph

/-! ## Counts for unseen endpoints -/

namespace OnlineMatching.Anonymous
open Transitions

abbrev labels (n : Nat) := Counting.completions n (List.range n)

def swapLabelling (x y : Nat) (ls : List Nat) := ls.map (swapLabels x y)

theorem swapLabelling_involution (x y : Nat) (ls : List Nat) :
    swapLabelling x y (swapLabelling x y ls) = ls := by
  simp [swapLabelling, List.map_map, Function.comp_def, swapLabels_involution]

theorem swap_range (n x y : Nat) (hx : x < n) (hy : y < n) :
    ((List.range n).map (swapLabels x y)).Perm (List.range n) := by
  apply involution_preserves_list _ _ List.nodup_range (swapLabels_involution x y)
  intro v hv
  simp only [List.mem_range] at hv ⊢
  unfold swapLabels
  split <;> (try split) <;> omega

theorem swapLabelling_mem (n x y : Nat) (hx : x < n) (hy : y < n)
    (ls : List Nat) (hl : ls ∈ labels n) : swapLabelling x y ls ∈ labels n := by
  apply (Counting.completions_spec n (List.range n) _ (by simp)).mpr
  have hp := (Counting.completions_spec n (List.range n) ls (by simp)).mp hl
  exact (hp.map (swapLabels x y)).trans (swap_range n x y hx hy)

theorem swapLabels_eq_iff (x y a b : Nat) :
    swapLabels x y a = swapLabels x y b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (swapLabels x y) h
    simpa [swapLabels_involution] using this
  · exact congrArg _

/-- A relabeled undirected host edge, with the hidden bijection given by its
list of images. Option-valued indexing keeps this total without default labels. -/
def edgePresent (original : List (Nat × Nat)) (ls : List Nat) (u v : Nat) : Bool :=
  original.any fun (a,b) =>
    ((ls[a]? == some u) && (ls[b]? == some v)) ||
    ((ls[a]? == some v) && (ls[b]? == some u))

def historyCompatible (original : List (Nat × Nat)) (ls : List Nat)
    (history : List (Nat × Nat)) : Bool :=
  history.all fun (u,v) => edgePresent original ls u v

def compatibleCount (n : Nat) (original history : List (Nat × Nat)) : Nat :=
  ((labels n).filter (fun ls => historyCompatible original ls history)).length

theorem mapped_lookup (ls : List Nat) (x y a u : Nat) :
    ((swapLabelling x y ls)[a]? == some (swapLabels x y u)) = (ls[a]? == some u) := by
  simp only [swapLabelling, List.getElem?_map]
  cases ls[a]? with
  | none => rfl
  | some w =>
    apply Bool.eq_iff_iff.mpr
    simp [swapLabels_eq_iff]

theorem edgePresent_swap (original : List (Nat × Nat)) (ls : List Nat) (x y u v : Nat) :
    edgePresent original (swapLabelling x y ls) (swapLabels x y u) (swapLabels x y v) =
      edgePresent original ls u v := by
  unfold edgePresent
  congr 1
  funext e
  rcases e with ⟨a,b⟩
  simp only [mapped_lookup]

theorem historyCompatible_swap (_n k x y : Nat) (original history : List (Nat × Nat))
    (ls : List Nat) (hx : k ≤ x) (hy : k ≤ y)
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    historyCompatible original (swapLabelling x y ls) history =
      historyCompatible original ls history := by
  unfold historyCompatible
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro h e he
  · have hh := h e he
    have hv := edgePresent_swap original ls x y e.1 e.2
    rw [swapLabels_seen k x y e.1 hx hy (hs e he).1,
      swapLabels_seen k x y e.2 hx hy (hs e he).2] at hv
    rw [hv] at hh
    exact hh
  · have hh := h e he
    have hv := edgePresent_swap original ls x y e.1 e.2
    rw [swapLabels_seen k x y e.1 hx hy (hs e he).1,
      swapLabels_seen k x y e.2 hx hy (hs e he).2] at hv
    rw [hv]
    exact hh

/-- The old-new observation has the same compatible-bijection count for every
choice of the still-unseen endpoint. This is proved on the complete permutation
universe, by swapping those two labels. -/
theorem old_new_counts_equal (n k u x y : Nat) (original history : List (Nat × Nat))
    (hu : u < k) (hx : k ≤ x) (hy : k ≤ y) (hxn : x < n) (hyn : y < n)
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    compatibleCount n original ((u,x) :: history) =
      compatibleCount n original ((u,y) :: history) := by
  apply involution_event_counts (labels n) (swapLabelling x y)
    (Prefix.completions_nodup n _ List.nodup_range)
    (swapLabelling_involution x y) (swapLabelling_mem n x y hxn hyn)
  intro ls _
  have he := edgePresent_swap original ls x y u x
  rw [swapLabels_seen k x y u hx hy hu] at he
  have hxy : swapLabels x y x = y := by simp [swapLabels]
  rw [hxy] at he
  have hh := historyCompatible_swap n k x y original history ls hx hy hs
  simp only [historyCompatible, List.all_cons] at hh ⊢
  rw [he, hh]

theorem child_counts_swap (n k x y u v : Nat) (original history : List (Nat × Nat))
    (hx : k ≤ x) (hy : k ≤ y) (hxn : x < n) (hyn : y < n)
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    compatibleCount n original ((u,v) :: history) =
      compatibleCount n original ((swapLabels x y u, swapLabels x y v) :: history) := by
  apply involution_event_counts (labels n) (swapLabelling x y)
    (Prefix.completions_nodup n _ List.nodup_range)
    (swapLabelling_involution x y) (swapLabelling_mem n x y hxn hyn)
  intro ls _
  have he := edgePresent_swap original ls x y u v
  have hh := historyCompatible_swap n k x y original history ls hx hy hs
  simp only [historyCompatible, List.all_cons] at hh ⊢
  rw [he, hh]

/-- All unordered pairs of unseen labels have equal child-compatible counts. -/
theorem new_new_counts_equal (n k x y a b : Nat) (original history : List (Nat × Nat))
    (hx : k ≤ x) (hy : k ≤ y) (ha : k ≤ a) (hb : k ≤ b)
    (hxn : x < n) (hyn : y < n) (han : a < n) (hbn : b < n)
    (hxy : x ≠ y) (hab : a ≠ b)
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    compatibleCount n original ((x,y) :: history) =
      compatibleCount n original ((a,b) :: history) := by
  let z := swapLabels x a y
  have hxa : swapLabels x a x = a := by simp [swapLabels]
  have haz : a ≠ z := by
    intro he
    have h := (swapLabels_eq_iff x a x y).mp (hxa.trans he)
    exact hxy h
  have hz : k ≤ z := by
    unfold z swapLabels
    split <;> (try split) <;> omega
  have hzn : z < n := by
    unfold z swapLabels
    split <;> (try split) <;> omega
  have h1 := child_counts_swap n k x a x y original history hx ha hxn han hs
  rw [hxa] at h1
  have h2 := child_counts_swap n k z b a z original history hz hb hzn hbn hs
  have hza : swapLabels z b a = a := by simp [swapLabels, haz, hab]
  have hzb : swapLabels z b z = b := by simp [swapLabels]
  rw [hza, hzb] at h2
  exact h1.trans h2

end OnlineMatching.Anonymous

/-! ## Labeled input graph -/

namespace OnlineMatching.ImplementationGraph

theorem labelAt_lookup (p : List Nat) (v u : Nat) (hv : v < p.length) :
    labelAt p v = u ↔ p[v]? = some u := by
  simp [labelAt, List.getElem?_eq_getElem hv]

theorem sorted_pair_eq (a b u v : Nat) (huv : u ≤ v) :
    (min a b, max a b) = (u,v) ↔ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  simp only [Prod.mk.injEq]
  omega

/-- The total sorted-edge representation and option-valued adjacency test agree
on valid input endpoints. This connects the reference model to anonymous counts. -/
theorem labelledHost_edgePresent (edges : List Offline.Edge) (p : List Nat)
    (u v : Nat) (huv : u ≤ v)
    (hend : ∀ e ∈ edges, e.1 < p.length ∧ e.2 < p.length) :
    (u,v) ∈ labelledHost edges p ↔ Anonymous.edgePresent edges p u v = true := by
  simp only [labelledHost, List.mem_map, Anonymous.edgePresent, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hpair⟩
    obtain ⟨ha, hb⟩ := hend e he
    refine ⟨e, he, ?_⟩
    rcases (sorted_pair_eq _ _ u v huv).mp hpair with h | h
    · have h1 := (labelAt_lookup p e.1 u ha).mp h.1
      have h2 := (labelAt_lookup p e.2 v hb).mp h.2
      simp [h1, h2]
    · have h1 := (labelAt_lookup p e.1 v ha).mp h.1
      have h2 := (labelAt_lookup p e.2 u hb).mp h.2
      simp [h1, h2]
  · rintro ⟨e, he, htest⟩
    obtain ⟨ha, hb⟩ := hend e he
    refine ⟨e, he, (sorted_pair_eq _ _ u v huv).mpr ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at htest
    rcases htest with h | h
    · exact Or.inl ⟨(labelAt_lookup p e.1 u ha).mpr h.1,
        (labelAt_lookup p e.2 v hb).mpr h.2⟩
    · exact Or.inr ⟨(labelAt_lookup p e.1 v ha).mpr h.1,
        (labelAt_lookup p e.2 u hb).mpr h.2⟩

theorem labelledHost_compatible (edges history : List Offline.Edge) (p : List Nat)
    (horder : ∀ e ∈ history, e.1 ≤ e.2)
    (hend : ∀ e ∈ edges, e.1 < p.length ∧ e.2 < p.length) :
    Transitions.compatible history (labelledHost edges p) =
      Anonymous.historyCompatible edges p history := by
  apply Bool.eq_iff_iff.mpr
  simp only [Transitions.compatible_iff, Anonymous.historyCompatible, List.all_eq_true]
  constructor
  · intro h e he
    exact (labelledHost_edgePresent edges p e.1 e.2 (horder e he) hend).mp (h e he)
  · intro h e he
    exact (labelledHost_edgePresent edges p e.1 e.2 (horder e he) hend).mpr (h e he)

/-- Concrete compatible host-label counts in the reference and anonymous models
coincide; no counting equality is supplied as a hypothesis. -/
theorem labelledHost_count (n : Nat) (edges history : List Offline.Edge)
    (horder : ∀ e ∈ history, e.1 ≤ e.2)
    (hend : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    (Transitions.compatibleLabels (hiddenLabels n) (labelledHost edges) history).length =
      Anonymous.compatibleCount n edges history := by
  unfold Transitions.compatibleLabels Anonymous.compatibleCount
  congr 1
  apply List.filter_congr
  intro p hp
  have hlen : p.length = n := by
    have hperm := (hiddenLabels_spec n p).mp hp
    simpa using hperm.length_eq
  exact labelledHost_compatible edges history p horder (by simpa [hlen] using hend)

theorem labelAt_injective (p : List Nat) (hn : p.Nodup) (a b : Nat)
    (ha : a < p.length) (hb : b < p.length)
    (he : labelAt p a = labelAt p b) : a = b := by
  have h1 := (labelAt_lookup p a (labelAt p a) ha).mp rfl
  have h2 := (labelAt_lookup p b (labelAt p b) hb).mp rfl
  rw [he] at h1
  exact hn.eq_of_getElem?_eq ha (h1.trans h2.symm)

theorem sorted_pair_same (a b c d : Nat) :
    (min a b, max a b) = (min c d, max c d) →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [Prod.mk.injEq]
  omega

theorem labelledHost_nodup (n : Nat) (edges : List Offline.Edge) (p : List Nat)
    (hn : edges.Nodup) (hp : p ∈ hiddenLabels n)
    (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    (labelledHost edges p).Nodup := by
  have hperm := (hiddenLabels_spec n p).mp hp
  have hpn : p.Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hlen : p.length = n := by simpa using hperm.length_eq
  unfold labelledHost
  change (edges.map _).Pairwise (fun a b => a ≠ b)
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_ hn
  intro a b ha hbb hab he
  obtain ⟨ha1, ha2⟩ := hb a ha
  obtain ⟨hb1, hb2⟩ := hb b hbb
  have hsa := hs a ha
  have hsb := hs b hbb
  rcases sorted_pair_same _ _ _ _ he with h | h
  · have h1 := labelAt_injective p hpn a.1 b.1 (by omega) (by omega) h.1
    have h2 := labelAt_injective p hpn a.2 b.2 (by omega) (by omega) h.2
    exact hab (Prod.ext h1 h2)
  · have h1 := labelAt_injective p hpn a.1 b.2 (by omega) (by omega) h.1
    have h2 := labelAt_injective p hpn a.2 b.1 (by omega) (by omega) h.2
    omega

theorem labelledHost_length (edges : List Offline.Edge) (p : List Nat) :
    (labelledHost edges p).length = edges.length := by simp [labelledHost]

/-- Actual weights of the reference implementation are the concrete compatible
permutation counts used by the anonymous-edge multiplicity theorems. -/
theorem reference_weight_formula (n : Nat) (edges history : List Offline.Edge)
    (free : List Nat) (e : Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ a ∈ edges, a.1 < a.2)
    (hb : ∀ a ∈ edges, a.1 < n ∧ a.2 < n)
    (hhn : history.Nodup) (hhs : ∀ a ∈ history, a.1 ≤ a.2)
    (hes : e.1 ≤ e.2) (hef : e ∉ history) :
    (referenceModel n edges).probability ⟨history, free⟩ e =
      (Anonymous.compatibleCount n edges (e :: history) : Rat) /
        (((edges.length - history.length) *
          Anonymous.compatibleCount n edges history : Nat) : Rat) := by
  change Transitions.probability
    (Transitions.graphOutcomes (hiddenLabels n) (labelledHost edges) history)
    (fun p => p.2 == e) = _
  rw [Transitions.graph_next_edge_probability (hiddenLabels n) (labelledHost edges)
    history edges.length e
    (fun p hp => labelledHost_nodup n edges p hn hp hs hb)
    (fun p _ => labelledHost_length edges p) hhn hef]
  rw [labelledHost_count n edges history hhs hb]
  rw [labelledHost_count n edges (e :: history) (by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hes
    · exact hhs a ha) hb]

/-- Grouping all old-new labeled observations gives the actual multiplicity
`n-k` in the reference model, including its conditional probabilities. -/
theorem reference_old_new_probability (n k u : Nat)
    (edges history : List Offline.Edge) (free : List Nat)
    (hn : edges.Nodup) (hs : ∀ a ∈ edges, a.1 < a.2)
    (hb : ∀ a ∈ edges, a.1 < n ∧ a.2 < n)
    (hhn : history.Nodup) (hhs : ∀ a ∈ history, a.1 ≤ a.2)
    (hseen : ∀ a ∈ history, a.1 < k ∧ a.2 < k) (hu : u < k) (hk : k < n) :
    total (List.range' k (n-k))
      (fun x => (referenceModel n edges).probability ⟨history, free⟩ (u,x)) =
      ((n-k : Nat) : Rat) *
        (referenceModel n edges).probability ⟨history, free⟩ (u,k) := by
  have hf (x : Nat) (hx : k ≤ x) : (u,x) ∉ history := by
    intro he
    have hh := (hseen _ he).2
    omega
  have heq : total (List.range' k (n-k))
      (fun x => (referenceModel n edges).probability ⟨history, free⟩ (u,x)) =
      total (List.range' k (n-k))
        (fun _ => (referenceModel n edges).probability ⟨history, free⟩ (u,k)) := by
    apply total_congr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
    simp only [Nat.one_mul]
    rw [reference_weight_formula n edges history free _ hn hs hb hhn hhs (by omega) (hf _ (by omega)),
        reference_weight_formula n edges history free _ hn hs hb hhn hhs (by omega) (hf _ (by omega)),
        Anonymous.old_new_counts_equal n k u (k+i) k edges history hu
          (by omega) (by omega) (by omega) hk hseen]
  rw [heq, Transitions.total_const, List.length_range']

/-- Grouping all new-new labeled observations gives the binomial multiplicity
in the actual reference probability distribution. -/
theorem reference_new_new_probability (n k : Nat)
    (edges history : List Offline.Edge) (free : List Nat)
    (hn : edges.Nodup) (hs : ∀ a ∈ edges, a.1 < a.2)
    (hb : ∀ a ∈ edges, a.1 < n ∧ a.2 < n)
    (hhn : history.Nodup) (hhs : ∀ a ∈ history, a.1 ≤ a.2)
    (hseen : ∀ a ∈ history, a.1 < k ∧ a.2 < k) (hk : k+1 < n) :
    total (Transitions.freshPairs (n-k))
      (fun p => (referenceModel n edges).probability ⟨history, free⟩ (k+p.1,k+p.2)) =
      (((n-k)*(n-k-1)/2 : Nat) : Rat) *
        (referenceModel n edges).probability ⟨history, free⟩ (k,k+1) := by
  have hf (x y : Nat) (hx : k ≤ x) : (x,y) ∉ history := by
    intro he
    have hh := (hseen _ he).1
    omega
  have heq : total (Transitions.freshPairs (n-k))
      (fun p => (referenceModel n edges).probability ⟨history, free⟩ (k+p.1,k+p.2)) =
      total (Transitions.freshPairs (n-k))
        (fun _ => (referenceModel n edges).probability ⟨history, free⟩ (k,k+1)) := by
    apply total_congr
    intro p hp
    have hp' := (Transitions.mem_freshPairs (n-k) p.1 p.2).mp hp
    rw [reference_weight_formula n edges history free _ hn hs hb hhn hhs (by omega) (hf _ _ (by omega)),
        reference_weight_formula n edges history free _ hn hs hb hhn hhs (by omega) (hf _ _ (by omega)),
        Anonymous.new_new_counts_equal n k (k+p.1) (k+p.2) k (k+1) edges history
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) hk (by omega) (by omega) hseen]
  rw [heq, Transitions.total_const, Transitions.freshPairs_length_div]

end OnlineMatching.ImplementationGraph
