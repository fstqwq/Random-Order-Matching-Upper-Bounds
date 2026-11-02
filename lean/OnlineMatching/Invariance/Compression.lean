import OnlineMatching.Invariance.Symmetry

/-!
# Compressed states

Unseen labels are interchangeable. Next edges are grouped by how many unseen
endpoints they have, and a state is represented by its observed labels only.
-/

/-! ## Edge classes -/

namespace OnlineMatching.EdgeClasses
open Transitions

abbrev oldNew (n k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap (fun u => (List.range' k (n-k)).map (fun x => (u,x)))

abbrev newNew (n k : Nat) : List (Nat × Nat) :=
  (freshPairs (n-k)).map (fun p => (k+p.1,k+p.2))

theorem mem_oldNew (n k u v : Nat) (hk : k ≤ n) :
    (u,v) ∈ oldNew n k ↔ u < k ∧ k ≤ v ∧ v < n := by
  simp [oldNew, List.mem_flatMap, List.mem_map, Nat.add_sub_of_le hk]

theorem mem_newNew (n k u v : Nat) (hk : k ≤ n) :
    (u,v) ∈ newNew n k ↔ k ≤ u ∧ u < v ∧ v < n := by
  constructor
  · intro h
    obtain ⟨p,hp,hp'⟩ := List.mem_map.mp h
    have he := (mem_freshPairs _ _ _).mp hp
    have hu := congrArg Prod.fst hp'
    have hv := congrArg Prod.snd hp'
    simp only at hu hv
    omega
  · intro h
    apply List.mem_map.mpr
    refine ⟨(u-k,v-k), (mem_freshPairs _ _ _).mpr ⟨by omega,by omega⟩, ?_⟩
    simp only [Prod.mk.injEq]
    omega

private theorem product_nodup (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup) :
    (xs.flatMap (fun u => ys.map (fun v => (u,v)))).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, ht⟩ := List.nodup_cons.mp hx
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨List.Pairwise.map _ (fun _ _ hne he => hne (congrArg Prod.snd he)) hy,
      ih ht, ?_⟩
    intro a ha b hb he
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy',hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    have he' : x = y := congrArg Prod.fst he
    exact hnot (he' ▸ hy')

theorem oldNew_nodup (n k : Nat) : (oldNew n k).Nodup :=
  product_nodup _ _ List.nodup_range List.nodup_range'

theorem newNew_nodup (n k : Nat) : (newNew n k).Nodup := by
  apply List.Pairwise.map _ _ (freshPairs_nodup _)
  intro a b hne he
  have ha := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  simp only at ha hb
  apply hne
  apply Prod.ext <;> omega

theorem classes_nodup (n k : Nat) (hk : k ≤ n) :
    (freshPairs k ++ oldNew n k ++ newNew n k).Nodup := by
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨freshPairs_nodup k, oldNew_nodup n k, ?_⟩, newNew_nodup n k, ?_⟩
  · intro a ha b hb he
    have h1 := (mem_freshPairs k a.1 a.2).mp ha
    have h2 := (mem_oldNew n k b.1 b.2 hk).mp hb
    have := congrArg Prod.snd he
    omega
  · intro a ha b hb he
    have h2 := (mem_newNew n k b.1 b.2 hk).mp hb
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    rcases List.mem_append.mp ha with ha | ha
    · have h1 := (mem_freshPairs k a.1 a.2).mp ha
      omega
    · have h1 := (mem_oldNew n k a.1 a.2 hk).mp ha
      omega

/-- Every possible sorted edge occurs in exactly one concrete endpoint class. -/
theorem freshPairs_partition (n k : Nat) (hk : k ≤ n) :
    (freshPairs n).Perm (freshPairs k ++ oldNew n k ++ newNew n k) := by
  apply (List.perm_ext_iff_of_nodup (freshPairs_nodup n) (classes_nodup n k hk)).mpr
  intro e
  rcases e with ⟨u,v⟩
  simp only [List.mem_append, mem_freshPairs, mem_oldNew n k u v hk,
    mem_newNew n k u v hk]
  omega

end OnlineMatching.EdgeClasses

namespace OnlineMatching.EdgeClasses
open Transitions

theorem oldNew_not_observed (n k : Nat) (hk : k ≤ n) (history : List (Nat × Nat))
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) (e : Nat × Nat)
    (he : e ∈ oldNew n k) : e ∉ history := by
  intro h
  have h1 := (mem_oldNew n k e.1 e.2 hk).mp he
  have h2 := hs e h
  omega

theorem newNew_not_observed (n k : Nat) (hk : k ≤ n) (history : List (Nat × Nat))
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) (e : Nat × Nat)
    (he : e ∈ newNew n k) : e ∉ history := by
  intro h
  have h1 := (mem_newNew n k e.1 e.2 hk).mp he
  have h2 := hs e h
  omega

/-- Already observed edges can occur only in the old-old class. -/
theorem remaining_partition (n k : Nat) (hk : k ≤ n) (history : List (Nat × Nat))
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    (remainingEdges (freshPairs n) history).Perm
      (remainingEdges (freshPairs k) history ++ oldNew n k ++ newNew n k) := by
  have h := (freshPairs_partition n k hk).filter (fun e => decide (e ∉ history))
  have ho : (oldNew n k).filter (fun e => decide (e ∉ history)) = oldNew n k := by
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (oldNew_not_observed n k hk history hs e he)
  have hn : (newNew n k).filter (fun e => decide (e ∉ history)) = newNew n k := by
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (newNew_not_observed n k hk history hs e he)
  simpa only [remainingEdges, List.filter_append, ho, hn] using h

theorem total_remaining_partition (n k : Nat) (hk : k ≤ n) (history : List (Nat × Nat))
    (hs : ∀ e ∈ history, e.1 < k ∧ e.2 < k) (f : (Nat × Nat) → Rat) :
    total (remainingEdges (freshPairs n) history) f =
      total (remainingEdges (freshPairs k) history) f +
      total (List.range k) (fun u => total (List.range' k (n-k)) (fun x => f (u,x))) +
      total (freshPairs (n-k)) (fun p => f (k+p.1,k+p.2)) := by
  rw [total_perm (remaining_partition n k hk history hs), total_append, total_append,
    total_flatMap, total_map]
  congr 2
  apply total_congr
  intro u hu
  exact total_map _ _ _

end OnlineMatching.EdgeClasses

/-! ## Sums over all label pairs -/

namespace OnlineMatching.FullEdges
open ImplementationGraph Transitions

theorem nextWeight_zero_of_not_possible (labels : List L)
    (host : L → List Offline.Edge) (s : State) (e : Offline.Edge)
    (he : e ∉ possible labels host s) : nextWeight labels host s e = 0 := by
  have hf : (graphOutcomes labels host s.observed).filter (fun p => p.2 == e) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    intro ht
    have hpe : p.2 = e := by simpa using ht
    apply he
    simp only [possible, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨p, hp, hpe⟩
  simp [nextWeight, probability, hf, Rat.div_def, Rat.zero_mul]

theorem labelAt_lt (n : Nat) (p : List Nat) (hp : p ∈ hiddenLabels n)
    (a : Nat) (ha : a < n) : labelAt p a < n := by
  have hperm := (hiddenLabels_spec n p).mp hp
  have hlen : p.length = n := by simpa using hperm.length_eq
  have ha' : a < p.length := by omega
  have hm : p[a] ∈ p := List.getElem_mem ha'
  have ht := List.mem_range.mp (hperm.mem_iff.mp hm)
  simpa only [labelAt, List.getElem?_eq_getElem ha', Option.getD_some] using ht

theorem labelledHost_mem_freshPairs (n : Nat) (original : List Offline.Edge)
    (p : List Nat) (hp : p ∈ hiddenLabels n)
    (hn : ∀ a ∈ original, a.1 ≠ a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (e : Offline.Edge) (he : e ∈ labelledHost original p) : e ∈ freshPairs n := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  have hperm := (hiddenLabels_spec n p).mp hp
  have hlen : p.length = n := by simpa using hperm.length_eq
  have hpn := hperm.nodup_iff.mpr List.nodup_range
  have h1 := labelAt_lt n p hp a.1 (hb a ha).1
  have h2 := labelAt_lt n p hp a.2 (hb a ha).2
  have hne : labelAt p a.1 ≠ labelAt p a.2 := by
    intro heq
    exact hn a ha (labelAt_injective p hpn _ _ (by have := (hb a ha).1; omega)
      (by have := (hb a ha).2; omega) heq)
  apply (mem_freshPairs _ _ _).mpr
  omega

theorem possible_subset_remaining (n : Nat) (original : List Offline.Edge)
    (s : State) (hn : ∀ a ∈ original, a.1 ≠ a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (e : Offline.Edge) (he : e ∈ possible (hiddenLabels n) (labelledHost original) s) :
    e ∈ remainingEdges (freshPairs n) s.observed := by
  have hef := (possible_reachable _ _ s e he).1
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true hef⟩
  simp only [possible, List.mem_eraseDups, List.mem_map] at he
  obtain ⟨p,hp,hpe⟩ := he
  simp only [graphOutcomes, outcomes, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨ls,hls,a,ha,hp⟩ := hp
  subst p
  simp only at hpe
  subst e
  exact labelledHost_mem_freshPairs n original ls (List.mem_filter.mp hls).1 hn hb a
    (List.mem_filter.mp ha).1

private theorem total_filter_zero (xs : List A) (p : A → Bool) (f : A → Rat)
    (hz : ∀ x ∈ xs, p x = false → f x = 0) : total (xs.filter p) f = total xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht := ih (fun a ha => hz a (by simp [ha]))
    cases hp : p x
    · simp [hp, total, ht, hz x (by simp) hp, Rat.zero_add]
    · simp [hp, total, ht]

/-- Impossible sorted pairs have zero weight, so the reference Bellman sum can
be taken over all fresh pairs instead of its enumerated positive support. -/
theorem total_possible_eq_remaining (n : Nat) (original : List Offline.Edge)
    (s : State) (hn : ∀ a ∈ original, a.1 ≠ a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n) (f : Offline.Edge → Rat) :
    total (possible (hiddenLabels n) (labelledHost original) s)
        (fun e => nextWeight (hiddenLabels n) (labelledHost original) s e * f e) =
      total (remainingEdges (freshPairs n) s.observed)
        (fun e => nextWeight (hiddenLabels n) (labelledHost original) s e * f e) := by
  let ps := possible (hiddenLabels n) (labelledHost original) s
  let all := remainingEdges (freshPairs n) s.observed
  have ha : all.Nodup := (freshPairs_nodup n).sublist List.filter_sublist
  have hp : ps.Nodup := dedup_nodup _
  have hperm : ps.Perm (all.filter (fun e => decide (e ∈ ps))) := by
    apply (List.perm_ext_iff_of_nodup hp (ha.sublist List.filter_sublist)).mpr
    intro e
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun he => ⟨possible_subset_remaining n original s hn hb e he, he⟩,
      fun he => he.2⟩
  rw [total_perm hperm]
  apply total_filter_zero
  intro e _ he
  have hnot : e ∉ ps := by simpa using he
  rw [nextWeight_zero_of_not_possible _ _ _ e hnot, Rat.zero_mul]

/-- The positive-support sum is exactly the three explicit endpoint loops,
including zero weights for impossible observations. -/
theorem total_possible_three_classes (n k : Nat) (original : List Offline.Edge)
    (s : State) (hn : ∀ a ∈ original, a.1 ≠ a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hk : k ≤ n) (hs : ∀ a ∈ s.observed, a.1 < k ∧ a.2 < k)
    (f : Offline.Edge → Rat) :
    total (possible (hiddenLabels n) (labelledHost original) s)
        (fun e => nextWeight (hiddenLabels n) (labelledHost original) s e * f e) =
      total (remainingEdges (freshPairs k) s.observed)
        (fun e => nextWeight (hiddenLabels n) (labelledHost original) s e * f e) +
      total (List.range k) (fun u => total (List.range' k (n-k))
        (fun x => nextWeight (hiddenLabels n) (labelledHost original) s (u,x) * f (u,x))) +
      total (freshPairs (n-k))
        (fun p => nextWeight (hiddenLabels n) (labelledHost original) s
          (k+p.1,k+p.2) * f (k+p.1,k+p.2)) := by
  rw [total_possible_eq_remaining n original s hn hb f]
  exact EdgeClasses.total_remaining_partition n k hk s.observed hs _

end OnlineMatching.FullEdges

/-! ## Fresh-label transport -/

namespace OnlineMatching.Compression

open Transitions

def compose (p q : Permutation Nat) : Permutation Nat where
  forward v := p.forward (q.forward v)
  backward v := q.backward (p.backward v)
  left_inverse v := by simp [p.left_inverse, q.left_inverse]
  right_inverse v := by simp [p.right_inverse, q.right_inverse]

theorem fixed_backward (p : Permutation Nat) (k : Nat)
    (hf : ∀ v, v < k → p.forward v = v) (v : Nat) (hv : v < k) :
    p.backward v = v := by
  have h := congrArg p.backward (hf v hv)
  simpa [p.left_inverse] using h.symm

theorem fixed_range (p : Permutation Nat) (k : Nat)
    (hf : ∀ v, v < k → p.forward v = v) (v : Nat) :
    p.backward v < k ↔ v < k := by
  constructor
  · intro h
    have he := hf (p.backward v) h
    rw [p.right_inverse] at he
    omega
  · intro h
    rw [fixed_backward p k hf v h]
    exact h

theorem swap_bound (n x y v : Nat) (hx : x < n) (hy : y < n) :
    swapLabels x y v < n ↔ v < n := by
  unfold swapLabels
  split <;> (try split) <;> omega

/-- An explicit permutation relating a representative fresh edge to an actual
labeled edge. It fixes the complete old observation, not just its edge count. -/
structure FreshTransport (n k u v a b : Nat) where
  permutation : Permutation Nat
  first : permutation.forward u = a
  second : permutation.forward v = b
  fixes : ∀ w, w < k → permutation.forward w = w
  bound : ∀ w, permutation.forward w < n ↔ w < n

def oldNew (n k u x : Nat) (hu : u < k) (hx : k ≤ x) (hxn : x < n) :
    FreshTransport n k u k u x where
  permutation := unseenSwap k x
  first := swapLabels_seen k k x u (by omega) hx hu
  second := by simp [unseenSwap, swapLabels]
  fixes w hw := swapLabels_seen k k x w (by omega) hx hw
  bound w := swap_bound n k x w (by omega) hxn

def newNew (n k x y : Nat) (hx : k ≤ x) (hy : k ≤ y)
    (hxn : x < n) (hyn : y < n) (hxy : x ≠ y) (hk : k + 1 < n) :
    FreshTransport n k k (k+1) x y := by
  let z := swapLabels k x (k+1)
  have hzx : z ≠ x := by
    intro h
    have h' : swapLabels k x (k+1) = swapLabels k x k := by
      simpa [z, swapLabels] using h
    have hi := congrArg (swapLabels k x) h'
    simp only [swapLabels_involution] at hi
    omega
  have hz : k ≤ z := by
    unfold z swapLabels
    split <;> (try split) <;> omega
  have hzn : z < n := (swap_bound n k x (k+1) (by omega) hxn).mpr hk
  refine ⟨compose (unseenSwap z y) (unseenSwap k x), ?_, ?_, ?_, ?_⟩
  · change swapLabels z y (swapLabels k x k) = x
    simp [swapLabels, Ne.symm hzx, hxy]
  · change swapLabels z y z = y
    simp [swapLabels]
  · intro w hw
    change swapLabels z y (swapLabels k x w) = w
    rw [swapLabels_seen k k x w (by omega) hx hw,
      swapLabels_seen k z y w hz hy hw]
  · intro w
    change swapLabels z y (swapLabels k x w) < n ↔ w < n
    rw [swap_bound n z y _ hzn hyn, swap_bound n k x w (by omega) hxn]

end OnlineMatching.Compression

/-! ## Equal child values -/

namespace OnlineMatching.Compression

open Implementation ImplementationGraph

def FreshTransport.finite {n k u v a b : Nat} (T : FreshTransport n k u v a b) :
    Symmetry.FinitePermutation n where
  toPermutation := T.permutation
  forward_lt w hw := (T.bound w).mpr hw
  backward_lt w hw := by
    have h := T.bound (T.permutation.backward w)
    rw [T.permutation.right_inverse] at h
    exact h.mp hw

theorem transport_forward_old {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (w : Nat) : T.permutation.forward w < k ↔ w < k := by
  constructor
  · intro h
    have he := T.fixes (T.permutation.forward w) h
    have hw := T.permutation.injective he
    omega
  · intro h
    rw [T.fixes w h]
    exact h

theorem transport_backward_old {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (w : Nat) : T.permutation.backward w < k ↔ w < k :=
  fixed_range T.permutation k T.fixes w

theorem fresh_map_perm {n k u v a b : Nat} (T : FreshTransport n k u v a b) :
    ((List.range' k (n-k)).map T.permutation.forward).Perm (List.range' k (n-k)) := by
  have hr (w : Nat) : w ∈ List.range' k (n-k) ↔ k ≤ w ∧ w < n := by
    simp only [List.mem_range']
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [Nat.one_mul]
      omega
    · rintro ⟨hw, hn⟩
      exact ⟨w-k, by omega, by simp; omega⟩
  have hn : ((List.range' k (n-k)).map T.permutation.forward).Nodup :=
    List.Pairwise.map _ (fun _ _ hne he => hne (T.permutation.injective he)) List.nodup_range'
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range').mpr
  intro w
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    obtain ⟨hzk, hzn⟩ := (hr z).mp hz
    apply (hr _).mpr
    have h := transport_forward_old T z
    exact ⟨by omega, (T.bound z).mpr hzn⟩
  · intro h
    obtain ⟨hwk, hwn⟩ := (hr w).mp h
    apply List.mem_map.mpr
    refine ⟨T.permutation.backward w, (hr _).mpr ?_, T.permutation.right_inverse w⟩
    have h := transport_backward_old T w
    exact ⟨by omega, T.finite.backward_lt w hwn⟩

theorem expanded_map_perm {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (available : List Nat) (ha : ∀ w ∈ available, w < k) :
    ((expand n k available).map T.permutation.forward).Perm (expand n k available) := by
  have hmap : available.map T.permutation.forward = available := by
    exact (List.map_congr_left (fun w hw => T.fixes w (ha w hw))).trans (List.map_id available)
  simp only [expand, List.map_append, hmap]
  exact (fresh_map_perm T).append_left available

theorem seen_history_fixed {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (history : List Offline.Edge)
    (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hb : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    Symmetry.history T.permutation.forward history = history := by
  unfold Symmetry.history
  apply (List.map_congr_left ?_).trans (List.map_id history)
  intro e he
  obtain ⟨h1,h2⟩ := hb e he
  simp only [Symmetry.edge, T.fixes e.1 h1, T.fixes e.2 h2,
    Nat.min_eq_left (hs e he), Nat.max_eq_right (hs e he)]
  rfl

theorem child_history_mapped {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (history : List Offline.Edge)
    (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hb : ∀ e ∈ history, e.1 < k ∧ e.2 < k) (hab : a ≤ b) :
    Symmetry.history T.permutation.forward ((u,v) :: history) = (a,b) :: history := by
  change Symmetry.edge T.permutation.forward (u,v) ::
    Symmetry.history T.permutation.forward history = _
  rw [seen_history_fixed T history hs hb]
  simp [Symmetry.edge, T.first, T.second, Nat.min_eq_left hab, Nat.max_eq_right hab]

theorem reject_free_mapped {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (available : List Nat) (ha : ∀ w ∈ available, w < k) :
    ((expand n k available).map T.permutation.forward).Perm (expand n k available) :=
  expanded_map_perm T available ha

theorem accept_free_mapped {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (available : List Nat) (ha : ∀ w ∈ available, w < k) :
    ((Offline.remove (expand n k available) (u,v)).map T.permutation.forward).Perm
      (Offline.remove (expand n k available) (a,b)) := by
  rw [remove_rename, T.first, T.second]
  exact ((expanded_map_perm T available ha).erase a).erase b

theorem legal_transport {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (available : List Nat) (ha : ∀ w ∈ available, w < k) :
    Offline.legal (expand n k available) (a,b) ↔
      Offline.legal (expand n k available) (u,v) := by
  have h := legal_rename T.permutation (expand n k available) (u,v)
  have hp := expanded_map_perm T available ha
  simpa only [T.first, T.second, Offline.legal, hp.mem_iff] using h

/-- The full-reference child values are equal for a representative edge and any
actual edge in its fresh-label class, derived from the successor relation. -/
theorem child_values {n k u v a b : Nat} (T : FreshTransport n k u v a b)
    (original history : List Offline.Edge) (available : List Nat) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ e ∈ original, e.1 < e.2)
    (hb : ∀ e ∈ original, e.1 < n ∧ e.2 < n)
    (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hseen : ∀ e ∈ history, e.1 < k ∧ e.2 < k)
    (ha : ∀ w ∈ available, w < k)
    (huv : u ≤ v) (hab : a ≤ b) (hfresh : (u,v) ∉ history) :
    value (referenceModel n original) fuel ⟨(a,b)::history, expand n k available⟩ =
      value (referenceModel n original) fuel ⟨(u,v)::history, expand n k available⟩ ∧
    value (referenceModel n original) fuel
        ⟨(a,b)::history, Offline.remove (expand n k available) (a,b)⟩ =
      value (referenceModel n original) fuel
        ⟨(u,v)::history, Offline.remove (expand n k available) (u,v)⟩ := by
  have hchild : ((u,v)::history).Nodup := List.nodup_cons.mpr ⟨hfresh,hh⟩
  have hsort : ∀ e ∈ (u,v)::history, e.1 ≤ e.2 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact huv
    · exact hs e he
  have ht := child_history_mapped T history hs hseen hab
  constructor
  · have hmap := Symmetry.value_map T.finite original
      ⟨(u,v)::history, expand n k available⟩ fuel hn ho hb hchild hsort
    change value (referenceModel n original) fuel
      ⟨Symmetry.history T.permutation.forward ((u,v)::history),
        (expand n k available).map T.permutation.forward⟩ = _ at hmap
    rw [ht] at hmap
    exact (Symmetry.value_free_perm n original ((a,b)::history) _ _
      (reject_free_mapped T available ha) fuel).symm.trans hmap
  · have hmap := Symmetry.value_map T.finite original
      ⟨(u,v)::history, Offline.remove (expand n k available) (u,v)⟩
      fuel hn ho hb hchild hsort
    change value (referenceModel n original) fuel
      ⟨Symmetry.history T.permutation.forward ((u,v)::history),
        (Offline.remove (expand n k available) (u,v)).map T.permutation.forward⟩ = _ at hmap
    rw [ht] at hmap
    exact (Symmetry.value_free_perm n original ((a,b)::history) _ _
      (accept_free_mapped T available ha) fuel).symm.trans hmap

end OnlineMatching.Compression

/-! ## Compressed recurrence -/

namespace OnlineMatching.CollapsedBellman
open ImplementationGraph Transitions

/-- One online decision with an arbitrary continuation on public states. -/
def branch (continuation : State → Rat) (s : State) (e : Offline.Edge) : Rat :=
  if decide (Offline.legal s.free e) then
    max (continuation (reject s e)) (1 + continuation (accept s e))
  else continuation (reject s e)

/-- For a nonterminal history, the concrete conditional-edge step equals the
three endpoint loops. No probability support or partition is assumed. -/
theorem step_three_classes (n k : Nat) (original : List Offline.Edge)
    (s : State) (hn : ∀ a ∈ original, a.1 ≠ a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hk : k ≤ n) (hs : ∀ a ∈ s.observed, a.1 < k ∧ a.2 < k)
    (ht : s.observed.length < original.length) (continuation : State → Rat) :
    total ((referenceModel n original).observations s)
        (fun e => (referenceModel n original).probability s e * branch continuation s e) =
      total (remainingEdges (freshPairs k) s.observed)
        (fun e => (referenceModel n original).probability s e * branch continuation s e) +
      total (List.range k) (fun u => total (List.range' k (n-k))
        (fun x => (referenceModel n original).probability s (u,x) *
          branch continuation s (u,x))) +
      total (freshPairs (n-k))
        (fun p => (referenceModel n original).probability s (k+p.1,k+p.2) *
          branch continuation s (k+p.1,k+p.2)) := by
  simp only [referenceModel, model, ht, ite_true]
  exact FullEdges.total_possible_three_classes n k original s hn hb hk hs _

/-- The actual reference Bellman recursion, written as explicit old-old,
old-new, and new-new edge loops. -/
theorem value_succ_three_classes (n k : Nat) (original : List Offline.Edge)
    (s : State) (fuel : Nat) (hn : ∀ a ∈ original, a.1 ≠ a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hk : k ≤ n) (hs : ∀ a ∈ s.observed, a.1 < k ∧ a.2 < k)
    (ht : s.observed.length < original.length) :
    value (referenceModel n original) (fuel+1) s =
      total (remainingEdges (freshPairs k) s.observed)
        (fun e => (referenceModel n original).probability s e *
          branch (value (referenceModel n original) fuel) s e) +
      total (List.range k) (fun u => total (List.range' k (n-k))
        (fun x => (referenceModel n original).probability s (u,x) *
          branch (value (referenceModel n original) fuel) s (u,x))) +
      total (freshPairs (n-k))
        (fun p => (referenceModel n original).probability s (k+p.1,k+p.2) *
          branch (value (referenceModel n original) fuel) s (k+p.1,k+p.2)) := by
  change total ((referenceModel n original).observations s)
    (fun e => (referenceModel n original).probability s e *
      branch (value (referenceModel n original) fuel) s e) = _
  exact step_three_classes n k original s hn hb hk hs ht _

/-- The reference step stops exactly when the observed-edge count reaches the
host edge count. The equation needs no reachability or positivity premise. -/
theorem value_succ_terminal (n : Nat) (original : List Offline.Edge)
    (s : State) (fuel : Nat) (ht : ¬s.observed.length < original.length) :
    value (referenceModel n original) (fuel+1) s = 0 := by
  simp only [value, referenceModel, model, ht, ite_false, total]

theorem branch_transport {n k u v a b : Nat} (T : Compression.FreshTransport n k u v a b)
    (original history : List Offline.Edge) (available : List Nat) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ e ∈ original, e.1 < e.2)
    (hb : ∀ e ∈ original, e.1 < n ∧ e.2 < n)
    (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hseen : ∀ e ∈ history, e.1 < k ∧ e.2 < k)
    (ha : ∀ w ∈ available, w < k)
    (huv : u ≤ v) (hab : a ≤ b) (hfresh : (u,v) ∉ history) :
    branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (a,b) =
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (u,v) := by
  obtain ⟨hr,haccept⟩ := Compression.child_values T original history available fuel
    hn ho hb hh hs hseen ha huv hab hfresh
  have hl : decide (Offline.legal (Implementation.expand n k available) (a,b)) =
      decide (Offline.legal (Implementation.expand n k available) (u,v)) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using Compression.legal_transport T available ha
  unfold branch
  rw [hl]
  simp only [reject, accept]
  rw [hr, haccept]

theorem old_new_sum (n k u : Nat) (original history : List Offline.Edge)
    (available : List Nat) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ e ∈ original, e.1 < e.2)
    (hb : ∀ e ∈ original, e.1 < n ∧ e.2 < n)
    (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hseen : ∀ e ∈ history, e.1 < k ∧ e.2 < k)
    (ha : ∀ w ∈ available, w < k) (hu : u < k) (hk : k < n) :
    total (List.range' k (n-k)) (fun x =>
      (referenceModel n original).probability ⟨history, Implementation.expand n k available⟩ (u,x) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (u,x)) =
      (n-k : Nat) *
        (referenceModel n original).probability ⟨history, Implementation.expand n k available⟩ (u,k) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (u,k) := by
  have hf : (u,k) ∉ history := by
    intro he
    have := (hseen (u,k) he).2
    omega
  have hc : total (List.range' k (n-k)) (fun x =>
      (referenceModel n original).probability ⟨history, Implementation.expand n k available⟩ (u,x) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (u,x)) =
    total (List.range' k (n-k)) (fun x =>
      (referenceModel n original).probability ⟨history, Implementation.expand n k available⟩ (u,x) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (u,k)) := by
    apply total_congr
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_range'.mp hx
    simp only [Nat.one_mul]
    rw [branch_transport (Compression.oldNew n k u (k+i) hu (by omega) (by omega))
      original history available fuel hn ho hb hh hs hseen ha (by omega) (by omega) hf]
  rw [hc, total_mul, reference_old_new_probability n k u original history
    (Implementation.expand n k available) hn ho hb hh hs hseen hu hk]

theorem new_new_sum (n k : Nat) (original history : List Offline.Edge)
    (available : List Nat) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ e ∈ original, e.1 < e.2)
    (hb : ∀ e ∈ original, e.1 < n ∧ e.2 < n)
    (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hseen : ∀ e ∈ history, e.1 < k ∧ e.2 < k)
    (ha : ∀ w ∈ available, w < k) (hk : k+1 < n) :
    total (freshPairs (n-k)) (fun p =>
      (referenceModel n original).probability
        ⟨history, Implementation.expand n k available⟩ (k+p.1,k+p.2) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (k+p.1,k+p.2)) =
      ((n-k)*(n-k-1)/2 : Nat) *
        (referenceModel n original).probability
          ⟨history, Implementation.expand n k available⟩ (k,k+1) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (k,k+1) := by
  have hf : (k,k+1) ∉ history := by
    intro he
    have := (hseen (k,k+1) he).1
    omega
  have hc : total (freshPairs (n-k)) (fun p =>
      (referenceModel n original).probability
        ⟨history, Implementation.expand n k available⟩ (k+p.1,k+p.2) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (k+p.1,k+p.2)) =
    total (freshPairs (n-k)) (fun p =>
      (referenceModel n original).probability
        ⟨history, Implementation.expand n k available⟩ (k+p.1,k+p.2) *
      branch (value (referenceModel n original) fuel)
        ⟨history, Implementation.expand n k available⟩ (k,k+1)) := by
    apply total_congr
    intro p hp
    have hp' := (mem_freshPairs (n-k) p.1 p.2).mp hp
    rw [branch_transport (Compression.newNew n k (k+p.1) (k+p.2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hk)
      original history available fuel hn ho hb hh hs hseen ha (by omega) (by omega) hf]
  rw [hc, total_mul, reference_new_new_probability n k original history
    (Implementation.expand n k available) hn ho hb hh hs hseen hk]

/-- The Bellman sum uses one old-new representative per seen vertex and one
new-new representative, with the corresponding multiplicities. -/
theorem value_succ_compressed (n k : Nat) (original history : List Offline.Edge)
    (available : List Nat) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ e ∈ original, e.1 < e.2)
    (hb : ∀ e ∈ original, e.1 < n ∧ e.2 < n)
    (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 ≤ e.2)
    (hseen : ∀ e ∈ history, e.1 < k ∧ e.2 < k)
    (ha : ∀ w ∈ available, w < k) (hk : k ≤ n)
    (ht : history.length < original.length) :
    let s : State := ⟨history, Implementation.expand n k available⟩
    let V := value (referenceModel n original) fuel
    value (referenceModel n original) (fuel+1) s =
      total (remainingEdges (freshPairs k) history)
        (fun e => (referenceModel n original).probability s e * branch V s e) +
      (if k < n then total (List.range k)
        (fun u => (n-k : Nat) * (referenceModel n original).probability s (u,k) *
          branch V s (u,k)) else 0) +
      (if k+1 < n then ((n-k)*(n-k-1)/2 : Nat) *
        (referenceModel n original).probability s (k,k+1) *
          branch V s (k,k+1) else 0) := by
  dsimp only
  rw [value_succ_three_classes n k original _ fuel
    (fun e he => Nat.ne_of_lt (ho e he)) hb hk hseen ht]
  congr 1
  · congr 1
    by_cases hkn : k < n
    · rw [ite_eq_left hkn]
      apply total_congr
      intro u hu
      exact old_new_sum n k u original history available fuel hn ho hb hh hs hseen ha
        (List.mem_range.mp hu) hkn
    · have hzero : n-k = 0 := by omega
      simp only [ite_eq_right hkn, hzero, List.range'_zero, total, total_const, Rat.mul_zero]
  · by_cases hkn : k+1 < n
    · rw [ite_eq_left hkn]
      exact new_new_sum n k original history available fuel hn ho hb hh hs hseen ha hkn
    · rw [ite_eq_right hkn]
      have hsmall : n-k = 0 ∨ n-k = 1 := by omega
      rcases hsmall with hzero | hone
      · simp only [hzero, freshPairs, total]
      · simp only [hone, freshPairs, List.range_zero, List.map_nil, List.append_nil, total]

end OnlineMatching.CollapsedBellman

/-! ## Revealing fresh labels -/

namespace OnlineMatching.Implementation

theorem old_not_fresh (seen added v : Nat) (hv : v < seen) :
    v ∉ List.range' seen added := by
  intro h
  obtain ⟨i, _, he⟩ := List.mem_range'.mp h
  simp only [Nat.one_mul] at he
  omega

theorem mem_expand_old (n seen : Nat) (available : List Nat) (v : Nat)
    (hv : v < seen) : v ∈ expand n seen available ↔ v ∈ available := by
  simp [expand, old_not_fresh seen (n-seen) v hv]

theorem legal_expand_old (n seen : Nat) (available : List Nat) (e : Offline.Edge)
    (he : e.1 < seen ∧ e.2 < seen) :
    Offline.legal (expand n seen available) e ↔ Offline.legal available e := by
  simp only [Offline.legal, mem_expand_old n seen available e.1 he.1,
    mem_expand_old n seen available e.2 he.2]

theorem erase_append_of_not_mem_right (left right : List Nat) (v : Nat)
    (hv : v ∉ right) : (left ++ right).erase v = left.erase v ++ right := by
  by_cases hl : v ∈ left
  · exact List.erase_append_left right hl
  · rw [List.erase_append_right right hl, List.erase_of_not_mem hv,
      List.erase_of_not_mem hl]

theorem expand_remove (n seen : Nat) (available : List Nat) (e : Offline.Edge)
    (he : e.1 < seen ∧ e.2 < seen) :
    expand n seen (Offline.remove available e) =
      Offline.remove (expand n seen available) e := by
  simp only [expand, Offline.remove]
  rw [erase_append_of_not_mem_right _ _ e.1 (old_not_fresh _ _ _ he.1),
    erase_append_of_not_mem_right _ _ e.2 (old_not_fresh _ _ _ he.2)]

/-- The fresh-vertex bitmask operation has the same state meaning as revealing
these labels in the stored list; all other unseen labels remain implicit. -/
theorem reveal_legal (n seen added : Nat) (available : List Nat) (e : Offline.Edge)
    (hk : seen + added ≤ n) (he : e.1 < seen + added ∧ e.2 < seen + added) :
    Offline.legal (revealList available seen added) e ↔
      Offline.legal (expand n seen available) e := by
  rw [← expand_reveal n seen added available hk]
  exact (legal_expand_old n (seen+added) (revealList available seen added) e he).symm

theorem reveal_accept (n seen added : Nat) (available : List Nat) (e : Offline.Edge)
    (hk : seen + added ≤ n) (he : e.1 < seen + added ∧ e.2 < seen + added) :
    expand n (seen+added) (Offline.remove (revealList available seen added) e) =
      Offline.remove (expand n seen available) e := by
  rw [expand_remove n (seen+added) _ e he, expand_reveal n seen added available hk]

theorem reveal_bound (seen added : Nat) (available : List Nat)
    (ha : ∀ v ∈ available, v < seen) :
    ∀ v ∈ revealList available seen added, v < seen + added := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · have := ha v hv
    omega
  · obtain ⟨i,hi,he⟩ := List.mem_range'.mp hv
    simp only [Nat.one_mul] at he
    omega

theorem remove_bound (seen : Nat) (available : List Nat) (e : Offline.Edge)
    (ha : ∀ v ∈ available, v < seen) :
    ∀ v ∈ Offline.remove available e, v < seen := by
  intro v hv
  exact ha v (List.mem_of_mem_erase (List.mem_of_mem_erase hv))

end OnlineMatching.Implementation
