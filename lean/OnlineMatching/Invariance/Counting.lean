import OnlineMatching.Invariance.Symmetry

/-!
# Counting compatible labelings

Transition weights are computed by a depth-first count of the labelings of the
input graph consistent with the observed graph, with the degree pruning of
`count_fits` in `opt.py`. The count equals the number of compatible hidden
labelings and is invariant under relabeling.
-/

/-! ## Depth-first count -/

namespace OnlineMatching.Counting

abbrev Placement := Nat × Nat

/-- Distinct images, preserving observed edges in either orientation. -/
def compatible (g original : Graph Nat) (a b : Placement) : Bool :=
  decide (a.2 ≠ b.2) && (!g a.1 b.1 || original a.2 b.2) &&
    (!g b.1 a.1 || original b.2 a.2)

def Good (g original : Graph Nat) (placed : List Placement) : Prop :=
  placed.Pairwise (fun a b => compatible g original a b = true)

def choices (g original : Graph Nat) (host : List Nat)
    (v : Nat) (placed : List Placement) : List Nat :=
  host.filter (fun w => placed.all (fun p => compatible g original (v,w) p))

/-- The unpruned placement backtracking loop: choose an unused image compatible
with every earlier observed edge. The vertex order is an arbitrary input. -/
def dfs (g original : Graph Nat) (host : List Nat) :
    List Nat → List Placement → Nat
  | [], _ => 1
  | v :: order, placed =>
      ((choices g original host v placed).map
        (fun w => dfs g original host order ((v,w) :: placed))).sum

/-- An explicit list of the placements counted by `dfs`. -/
def enumerate (g original : Graph Nat) (host : List Nat) :
    List Nat → List Placement → List (List Placement)
  | [], _ => [[]]
  | v :: order, placed =>
      (choices g original host v placed).flatMap (fun w =>
        (enumerate g original host order ((v,w) :: placed)).map (fun xs => (v,w) :: xs))

theorem dfs_eq_length (g original : Graph Nat) (host order : List Nat)
    (placed : List Placement) :
    dfs g original host order placed = (enumerate g original host order placed).length := by
  induction order generalizing placed with
  | nil => rfl
  | cons v order ih =>
    simp [dfs, enumerate, List.length_flatMap, ih]

theorem mem_choices (g original : Graph Nat) (host : List Nat)
    (v w : Nat) (placed : List Placement) :
    w ∈ choices g original host v placed ↔
      w ∈ host ∧ ∀ p ∈ placed, compatible g original (v,w) p = true := by
  simp [choices]

theorem good_cons (g original : Graph Nat) (p : Placement) (placed : List Placement) :
    Good g original (p :: placed) ↔
      (∀ q ∈ placed, compatible g original p q = true) ∧ Good g original placed := by
  simp [Good]

/-- Declarative specification: prescribed source order, host-valued images,
and all pairwise injection/edge constraints. -/
def Valid (g original : Graph Nat) (host order : List Nat)
    (placed result : List Placement) : Prop :=
  result.map Prod.fst = order ∧
  (∀ p ∈ result, p.2 ∈ host) ∧ Good g original (result.reverse ++ placed)

theorem enumerate_spec (g original : Graph Nat) (host order : List Nat)
    (placed result : List Placement) (hp : Good g original placed) :
    result ∈ enumerate g original host order placed ↔
      Valid g original host order placed result := by
  induction order generalizing placed result with
  | nil =>
    cases result <;> simp [enumerate, Valid, hp]
  | cons v order ih =>
    cases result with
    | nil => simp [enumerate, Valid]
    | cons p rest =>
      constructor
      · intro hm
        obtain ⟨w, hw, hs⟩ := List.mem_flatMap.mp hm
        obtain ⟨xs, hxs, heq⟩ := List.mem_map.mp hs
        cases heq
        obtain ⟨hw, hc⟩ := (mem_choices g original host v w placed).mp hw
        have hr := (ih ((v,w) :: placed) rest ((good_cons _ _ _ _).mpr ⟨hc,hp⟩)).mp hxs
        rcases hr with ⟨horder, hhost, hgood⟩
        refine ⟨by simp [horder], ?_, ?_⟩
        · intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hw
          · exact hhost q hq
        · simpa [List.reverse_cons, List.append_assoc] using hgood
      · intro hv
        rcases hv with ⟨horder, hhost, hgood⟩
        have hk : p.1 = v := by simpa using congrArg List.head? horder
        have ht : rest.map Prod.fst = order := by simpa using congrArg List.tail horder
        have hgood' : Good g original (rest.reverse ++ p :: placed) := by
          simpa [List.reverse_cons, List.append_assoc] using hgood
        have hc : Good g original (p :: placed) := (List.pairwise_append.mp hgood').2.1
        apply List.mem_flatMap.mpr
        refine ⟨p.2, ?_, ?_⟩
        · apply (mem_choices g original host v p.2 placed).mpr
          refine ⟨hhost p (by simp), ?_⟩
          simpa [← hk] using ((good_cons _ _ _ _).mp hc).1
        · apply List.mem_map.mpr
          refine ⟨rest, ?_, ?_⟩
          · apply (ih ((v,p.2) :: placed) rest (by simpa [← hk] using hc)).mpr
            refine ⟨ht, ?_, ?_⟩
            · intro q hq; exact hhost q (by simp [hq])
            · simpa [← hk] using hgood'
          · simp [← hk]

end OnlineMatching.Counting

namespace OnlineMatching.Counting

private theorem prefix_map_nodup (p : Placement) (xs : List (List Placement))
    (h : xs.Nodup) : (xs.map (p :: ·)).Nodup :=
  List.Pairwise.map _ (fun _ _ hne heq => hne (List.cons.inj heq).2) h

private theorem branch_nodup (v : Nat) (ws : List Nat) (f : Nat → List (List Placement))
    (hw : ws.Nodup) (hf : ∀ w ∈ ws, (f w).Nodup) :
    (ws.flatMap (fun w => (f w).map ((v,w) :: ·))).Nodup := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hw
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨prefix_map_nodup _ _ (hf w (by simp)),
      ih htail (fun w hw => hf w (by simp [hw])), ?_⟩
    intro a ha b hb heq
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp ha
    obtain ⟨z, hz, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hb
    have hwz : w = z := congrArg Prod.snd (List.cons.inj heq).1
    exact hnot (hwz ▸ hz)

theorem enumerate_nodup (g original : Graph Nat) (host order : List Nat)
    (placed : List Placement) (hh : host.Nodup) :
    (enumerate g original host order placed).Nodup := by
  induction order generalizing placed with
  | nil => simp [enumerate]
  | cons v order ih =>
    apply branch_nodup
    · exact hh.filter _
    · intro w _; exact ih _

end OnlineMatching.Counting

namespace OnlineMatching.Counting

theorem compatible_iff (g original : Graph Nat) (a b : Placement) :
    compatible g original a b = true ↔ a.2 ≠ b.2 ∧
      (g a.1 b.1 = true → original a.2 b.2 = true) ∧
      (g b.1 a.1 = true → original b.2 a.2 = true) := by
  simp [compatible]
  grind

private theorem pairwise_mem {A : Type} {R : A → A → Prop}
    (sym : ∀ a b, R a b → R b a) {xs : List A} (h : xs.Pairwise R)
    {a b : A} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : R a b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hne rfl)
      · exact hx b hb
    · rcases hb with rfl | hb
      · exact sym b a (hx a ha)
      · exact ih ht ha hb

/-- An injective edge-preserving map on precisely the observed vertices. -/
def EmbedsOn (observed : List Nat) (g original : Graph Nat) (f : Nat → Nat) : Prop :=
  (∀ u ∈ observed, ∀ v ∈ observed, f u = f v → u = v) ∧
  (∀ u ∈ observed, ∀ v ∈ observed, g u v = true → original (f u) (f v) = true)

theorem good_map_iff_embeds (g original : Graph Nat) (order : List Nat)
    (f : Nat → Nat) (hn : order.Nodup) (hi : ∀ v, g v v = false) :
    Good g original (order.map (fun v => (v,f v))) ↔ EmbedsOn order g original f := by
  rw [Good, List.pairwise_map]
  constructor
  · intro h
    have pair : ∀ u ∈ order, ∀ v ∈ order, u ≠ v →
        compatible g original (u,f u) (v,f v) = true := by
      intro u hu v hv hne
      apply pairwise_mem (xs := order) _ h hu hv hne
      intro a b hab
      rw [compatible_iff] at hab ⊢
      exact ⟨Ne.symm hab.1, hab.2.2, hab.2.1⟩
    constructor
    · intro u hu v hv he
      by_cases huv : u = v
      · exact huv
      · exact False.elim (((compatible_iff _ _ _ _).mp (pair u hu v hv huv)).1 he)
    · intro u hu v hv he
      by_cases huv : u = v
      · subst v; simp [hi] at he
      · exact ((compatible_iff _ _ _ _).mp (pair u hu v hv huv)).2.1 he
  · intro h
    apply List.Pairwise.imp_of_mem _ hn
    intro u v hu hv hne
    rw [compatible_iff]
    exact ⟨fun he => hne (h.1 u hu v hv he), h.2 u hu v hv, h.2 v hv u hu⟩

end OnlineMatching.Counting

namespace OnlineMatching.Counting

/-- Remove already occupied images. -/
def unused : List Nat → List Nat → List Nat
  | host, [] => host
  | host, w :: used => unused (host.erase w) used

theorem unused_length (host used : List Nat) (hn : used.Nodup)
    (hs : used ⊆ host) : (unused host used).length = host.length - used.length := by
  induction used generalizing host with
  | nil => simp [unused]
  | cons w used ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hn
    have hw : w ∈ host := hs (by simp)
    have ht : used ⊆ host.erase w := by
      intro v hv
      have hne : v ≠ w := by intro he; subst v; exact hnot hv
      exact (List.mem_erase_of_ne hne).mpr (hs (by simp [hv]))
    rw [unused, ih _ hn ht, List.length_erase_of_mem hw]
    simp only [List.length_cons]
    omega

theorem unused_nodup (host used : List Nat) (hn : host.Nodup) :
    (unused host used).Nodup := by
  induction used generalizing host with
  | nil => exact hn
  | cons w used ih => exact ih _ (List.erase_sublist.nodup hn)

theorem good_reverse (g original : Graph Nat) (xs : List Placement) :
    Good g original xs.reverse ↔ Good g original xs := by
  simp only [Good, List.pairwise_reverse]
  constructor <;> intro h <;> apply List.Pairwise.imp _ h <;> intro a b hab
  all_goals
    rw [compatible_iff] at hab ⊢
    exact ⟨Ne.symm hab.1, hab.2.2, hab.2.1⟩

theorem good_images_nodup (g original : Graph Nat) (xs : List Placement)
    (h : Good g original xs) : (xs.map Prod.snd).Nodup := by
  apply List.Pairwise.map Prod.snd _ h
  intro a b hab
  exact ((compatible_iff _ _ _ _).mp hab).1

theorem valid_unused_length (g original : Graph Nat) (host order : List Nat)
    (result : List Placement) (h : Valid g original host order [] result) :
    (unused host (result.map Prod.snd)).length = host.length - order.length := by
  obtain ⟨hk, ht, hg⟩ := h
  have hg' : Good g original result := (good_reverse _ _ _).mp (by simpa using hg)
  rw [unused_length _ _ (good_images_nodup _ _ _ hg')]
  · have hl := congrArg List.length hk
    simp only [List.length_map] at hl ⊢
    rw [hl]
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact ht p hp

/-- A full hidden labeling consists of the observed placement and a permutation
of the unused host vertices assigned to the unseen labels in fixed order. -/
def fullLabellings (g original : Graph Nat) (host order : List Nat) :=
  (enumerate g original host order []).flatMap (fun placed =>
    (completions (host.length - order.length) (unused host (placed.map Prod.snd))).map
      (fun suffix => (placed, suffix)))

def countFits (g original : Graph Nat) (host order : List Nat) : Nat :=
  dfs g original host order [] * factorial (host.length - order.length)

/-- The factorial multiplication counts the independent unseen-label completions,
not merely the observed embeddings. -/
theorem countFits_eq_fullLabellings_length (g original : Graph Nat)
    (host order : List Nat) :
    countFits g original host order = (fullLabellings g original host order).length := by
  rw [fullLabellings, List.length_flatMap]
  have hc : ∀ placed ∈ enumerate g original host order [],
      ((completions (host.length - order.length) (unused host (placed.map Prod.snd))).map
        (fun suffix => (placed, suffix))).length = factorial (host.length - order.length) := by
    intro placed hp
    rw [List.length_map]
    apply completions_length
    exact valid_unused_length _ _ _ _ _
      ((enumerate_spec _ _ _ _ _ _ (by simp [Good])).mp hp)
  rw [sum_map_constant _ _ _ hc, countFits, dfs_eq_length]

end OnlineMatching.Counting

namespace OnlineMatching.Counting

theorem placements_as_function (placed : List Placement)
    (hn : (placed.map Prod.fst).Nodup) :
    ∃ f : Nat → Nat, ∀ p ∈ placed, f p.1 = p.2 := by
  induction placed with
  | nil => exact ⟨fun _ => 0, by simp⟩
  | cons p placed ih =>
    obtain ⟨hnot, ht⟩ := List.nodup_cons.mp hn
    obtain ⟨f, hf⟩ := ih ht
    refine ⟨fun v => if v = p.1 then p.2 else f v, ?_⟩
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp
    · have hne : q.1 ≠ p.1 := by
        intro he
        exact hnot (List.mem_map.mpr ⟨q,hq,he⟩)
      simp [hne, hf q hq]

theorem map_representation (placed : List Placement) (f : Nat → Nat)
    (hf : ∀ p ∈ placed, f p.1 = p.2) :
    (placed.map Prod.fst).map (fun v => (v,f v)) = placed := by
  induction placed with
  | nil => rfl
  | cons p placed ih =>
    simp only [List.map_cons]
    rw [hf p (by simp), ih (fun q hq => hf q (by simp [hq]))]

/-- The degree test is valid for embeddings on the observed vertex set; no
assumption about the mapping outside that set is required. -/
theorem degree_pruning_on (g original : Graph Nat) (observed host : List Nat)
    (f : Nat → Nat) (hf : EmbedsOn observed g original f) (hn : observed.Nodup)
    (hhost : ∀ u ∈ observed, f u ∈ host) (v : Nat) (hv : v ∈ observed) :
    (observed.filter (g v)).length ≤ (host.filter (original (f v))).length := by
  let neighbours := observed.filter (g v)
  have hn' : neighbours.Nodup := hn.filter _
  have hm : (neighbours.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ hn'
    intro a b ha hb hab he
    exact hab (hf.1 a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 he)
  have hs : neighbours.map f ⊆ host.filter (original (f v)) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hu, he⟩ := List.mem_filter.mp hu
    exact List.mem_filter.mpr ⟨hhost u hu, hf.2 v hv u hu he⟩
  simpa [neighbours] using hm.length_le_of_subset hs

def degreeOK (g original : Graph Nat) (observed host : List Nat) (p : Placement) : Bool :=
  decide ((observed.filter (g p.1)).length ≤ (host.filter (original p.2)).length)

/-- Every complete valid placement passes every degree check used during search. -/
theorem valid_passes_degree (g original : Graph Nat) (observed host : List Nat)
    (hn : observed.Nodup) (hi : ∀ v, g v v = false) (placed : List Placement)
    (h : Valid g original host observed [] placed) :
    ∀ p ∈ placed, degreeOK g original observed host p = true := by
  obtain ⟨hk, ht, hg⟩ := h
  obtain ⟨f, hf⟩ := placements_as_function placed (by simpa [hk])
  have hr : observed.map (fun v => (v,f v)) = placed := by
    rw [← hk]; exact map_representation placed f hf
  have hgood : Good g original (observed.map (fun v => (v,f v))) := by
    rw [hr]
    exact (good_reverse _ _ _).mp (by simpa using hg)
  have he := (good_map_iff_embeds g original observed f hn hi).mp hgood
  have hhost : ∀ v ∈ observed, f v ∈ host := by
    intro v hv
    exact ht (v,f v) (by rw [← hr]; exact List.mem_map.mpr ⟨v,hv,rfl⟩)
  intro p hp
  have hv : p.1 ∈ observed := by rw [← hk]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hd := degree_pruning_on g original observed host f he hn hhost p.1 hv
  simpa [degreeOK, hf p hp] using hd

end OnlineMatching.Counting

namespace OnlineMatching.Counting

def enumeratePruned (g original : Graph Nat) (host : List Nat) (guard : Placement → Bool) :
    List Nat → List Placement → List (List Placement)
  | [], _ => [[]]
  | v :: order, placed =>
      (choices g original host v placed).flatMap (fun w =>
        (if guard (v,w) then enumeratePruned g original host guard order ((v,w) :: placed)
         else []).map (fun xs => (v,w) :: xs))

def dfsPruned (g original : Graph Nat) (host : List Nat) (guard : Placement → Bool) :
    List Nat → List Placement → Nat
  | [], _ => 1
  | v :: order, placed =>
      ((choices g original host v placed).map (fun w =>
        if guard (v,w) then dfsPruned g original host guard order ((v,w) :: placed)
        else 0)).sum

theorem dfsPruned_eq_length (g original : Graph Nat) (host order : List Nat)
    (guard : Placement → Bool) (placed : List Placement) :
    dfsPruned g original host guard order placed =
      (enumeratePruned g original host guard order placed).length := by
  induction order generalizing placed with
  | nil => rfl
  | cons v order ih =>
    simp only [dfsPruned, enumeratePruned, List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro w hw
    split <;> simp [ih]

theorem enumeratePruned_spec (g original : Graph Nat) (host order : List Nat)
    (guard : Placement → Bool) (placed result : List Placement) :
    result ∈ enumeratePruned g original host guard order placed ↔
      result ∈ enumerate g original host order placed ∧
      ∀ p ∈ result, guard p = true := by
  induction order generalizing placed result with
  | nil => simp [enumeratePruned, enumerate]; grind
  | cons v order ih =>
    cases result with
    | nil => simp [enumeratePruned, enumerate]
    | cons p rest =>
      constructor
      · intro hm
        obtain ⟨w, hw, hs⟩ := List.mem_flatMap.mp hm
        obtain ⟨xs, hxs, heq⟩ := List.mem_map.mp hs
        cases heq
        split at hxs
        next hg =>
          obtain ⟨hr, hall⟩ := (ih _ _).mp hxs
          refine ⟨List.mem_flatMap.mpr ⟨w, hw, List.mem_map.mpr ⟨rest,hr,rfl⟩⟩, ?_⟩
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hg
          · exact hall p hp
        next hg => simp at hxs
      · rintro ⟨hm, hall⟩
        obtain ⟨w, hw, hs⟩ := List.mem_flatMap.mp hm
        obtain ⟨xs, hxs, heq⟩ := List.mem_map.mp hs
        cases heq
        apply List.mem_flatMap.mpr
        refine ⟨w,hw,List.mem_map.mpr ⟨rest,?_,rfl⟩⟩
        have hg := hall (v,w) (by simp)
        simp only [hg, ↓reduceIte]
        apply (ih _ _).mpr
        exact ⟨hxs, fun p hp => hall p (by simp [hp])⟩

theorem enumeratePruned_nodup (g original : Graph Nat) (host order : List Nat)
    (guard : Placement → Bool) (placed : List Placement) (hh : host.Nodup) :
    (enumeratePruned g original host guard order placed).Nodup := by
  induction order generalizing placed with
  | nil => simp [enumeratePruned]
  | cons v order ih =>
    apply branch_nodup
    · exact hh.filter _
    · intro w _
      split
      · exact ih _
      · simp

/-- Degree-pruned counting for any duplicate-free traversal of the observed vertices. -/
theorem degree_pruned_dfs_eq_dfs (g original : Graph Nat) (host order : List Nat)
    (hh : host.Nodup) (ho : order.Nodup) (hi : ∀ v, g v v = false) :
    dfsPruned g original host (degreeOK g original order host) order [] =
      dfs g original host order [] := by
  rw [dfsPruned_eq_length, dfs_eq_length]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup
    (enumeratePruned_nodup _ _ _ _ _ _ hh) (enumerate_nodup _ _ _ _ _ hh)).mpr
  intro result
  rw [enumeratePruned_spec]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    exact valid_passes_degree g original order host ho hi result
      ((enumerate_spec _ _ _ _ _ _ (by simp [Good])).mp h)

end OnlineMatching.Counting

namespace OnlineMatching.Counting

end OnlineMatching.Counting

/-! ## Completing partial labelings -/

namespace OnlineMatching.Counting

private theorem pairBranches_nodup {A B : Type} (xs : List A) (f : A → List B)
    (hx : xs.Nodup) (hf : ∀ x ∈ xs, (f x).Nodup) :
    (xs.flatMap (fun x => (f x).map (fun y => (x,y)))).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, ht⟩ := List.nodup_cons.mp hx
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, ih ht (fun y hy => hf y (by simp [hy])), ?_⟩
    · exact List.Pairwise.map _ (fun _ _ hne he => hne (congrArg Prod.snd he))
        (hf x (by simp))
    · intro a ha b hb heq
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      have hxy : x = y := congrArg Prod.fst heq
      exact hnot (hxy ▸ hy)

/-- No full hidden labeling is counted twice. -/
theorem fullLabellings_nodup (g original : Graph Nat) (host order : List Nat)
    (hh : host.Nodup) : (fullLabellings g original host order).Nodup := by
  apply pairBranches_nodup
  · exact enumerate_nodup _ _ _ _ _ hh
  · intro placed hp
    exact Prefix.completions_nodup _ _ (unused_nodup _ _ hh)

theorem fullLabellings_spec (g original : Graph Nat) (host order : List Nat)
    (placed : List Placement) (suffix : List Nat) :
    (placed,suffix) ∈ fullLabellings g original host order ↔
      Valid g original host order [] placed ∧
      suffix.Perm (unused host (placed.map Prod.snd)) := by
  constructor
  · intro hm
    obtain ⟨p, hp, hs⟩ := List.mem_flatMap.mp hm
    obtain ⟨s, hs, he⟩ := List.mem_map.mp hs
    cases he
    have hv := (enumerate_spec _ _ _ _ _ _ (by simp [Good])).mp hp
    refine ⟨hv, ?_⟩
    exact (completions_spec _ _ _ (valid_unused_length _ _ _ _ _ hv)).mp hs
  · rintro ⟨hv, hs⟩
    apply List.mem_flatMap.mpr
    refine ⟨placed, (enumerate_spec _ _ _ _ _ _ (by simp [Good])).mpr hv,
      List.mem_map.mpr ⟨suffix, ?_, rfl⟩⟩
    exact (completions_spec _ _ _ (valid_unused_length _ _ _ _ _ hv)).mpr hs

theorem used_unused_perm (host used : List Nat) (hn : used.Nodup)
    (hs : used ⊆ host) : (used ++ unused host used).Perm host := by
  induction used generalizing host with
  | nil => simp [unused]
  | cons w used ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hn
    have hw : w ∈ host := hs (by simp)
    have ht : used ⊆ host.erase w := by
      intro v hv
      have hne : v ≠ w := by intro he; subst v; exact hnot hv
      exact (List.mem_erase_of_ne hne).mpr (hs (by simp [hv]))
    exact ((ih _ hn ht).cons w).trans (List.perm_cons_erase hw).symm

/-- In each enumerated completion every host vertex occurs exactly once: this is
bijectivity of the complete image list, not merely injectivity of the prefix. -/
theorem fullLabellings_bijective (g original : Graph Nat) (host order : List Nat)
    (placed : List Placement) (suffix : List Nat)
    (h : (placed,suffix) ∈ fullLabellings g original host order) :
    (placed.map Prod.snd ++ suffix).Perm host := by
  obtain ⟨hv, hs⟩ := (fullLabellings_spec _ _ _ _ _ _).mp h
  obtain ⟨hk, ht, hg⟩ := hv
  have hg' : Good g original placed := (good_reverse _ _ _).mp (by simpa using hg)
  apply (hs.append_left _).trans
  apply used_unused_perm _ _ (good_images_nodup _ _ _ hg')
  intro w hw
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  exact ht p hp

/-- Conversely any full bijective image list with a valid observed prefix is
included. Thus the completion count omits no hidden labelings. -/
theorem fullLabellings_iff_bijective (g original : Graph Nat) (host order : List Nat)
    (placed : List Placement) (suffix : List Nat) :
    (placed,suffix) ∈ fullLabellings g original host order ↔
      Valid g original host order [] placed ∧
      (placed.map Prod.snd ++ suffix).Perm host := by
  constructor
  · intro h
    exact ⟨((fullLabellings_spec _ _ _ _ _ _).mp h).1,
      fullLabellings_bijective _ _ _ _ _ _ h⟩
  · rintro ⟨hv, hb⟩
    apply (fullLabellings_spec _ _ _ _ _ _).mpr
    refine ⟨hv, ?_⟩
    obtain ⟨hk, ht, hg⟩ := hv
    have hg' : Good g original placed := (good_reverse _ _ _).mp (by simpa using hg)
    have hu : (placed.map Prod.snd ++ unused host (placed.map Prod.snd)).Perm host := by
      apply used_unused_perm _ _ (good_images_nodup _ _ _ hg')
      intro w hw
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
      exact ht p hp
    exact (List.perm_append_left_iff _).mp (hb.trans hu.symm)

end OnlineMatching.Counting

/-! ## Inverse labelings -/

namespace OnlineMatching.CountingReference

/-- The inverse of a hidden host-to-public labeling, represented in public-label order. -/
def inverse (labels : List Nat) : List Nat :=
  (List.range labels.length).map labels.idxOf

theorem lookup_iff_preimage (p : List Nat) (hn : p.Nodup) (a u : Nat)
    (hu : u ∈ p) : p[a]? = some u ↔ p.idxOf u = a := by
  constructor
  · intro h
    have ha : a < p.length := by
      by_cases ha : a < p.length
      · exact ha
      · have hnone : p[a]? = none := List.getElem?_eq_none (by omega)
        rw [hnone] at h
        contradiction
    have he : p[a] = u := by simpa [List.getElem?_eq_getElem ha] using h
    rw [← he]
    exact hn.idxOf_getElem a ha
  · intro h
    have hi := List.idxOf_lt_length_of_mem hu
    subst a
    simp [List.getElem?_eq_getElem hi]

theorem inverse_lookup (p : List Nat) (u : Nat) (hu : u < p.length) :
    (inverse p)[u]? = some (p.idxOf u) := by
  simp [inverse, hu]

/-- Edge membership on host vertex IDs, with undirected orientation. -/
def originalGraph (edges : List (Nat × Nat)) : Graph Nat :=
  fun u v => edges.any (fun e => decide (e = (u,v) ∨ e = (v,u)))

/-- A relabeled observed edge is present exactly when the inverse images form
an original host edge. This identifies the two directions of the hidden map. -/
theorem edgePresent_inverse (edges : List (Nat × Nat)) (p : List Nat)
    (hn : p.Nodup) (u v : Nat) (hu : u ∈ p) (hv : v ∈ p) :
    Anonymous.edgePresent edges p u v = originalGraph edges (p.idxOf u) (p.idxOf v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Anonymous.edgePresent, originalGraph, List.any_eq_true]
  constructor
  · rintro ⟨e,he,h⟩
    refine ⟨e,he,?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    simp only [decide_eq_true_eq, Prod.ext_iff]
    rcases h with h | h
    · exact Or.inl ⟨((lookup_iff_preimage p hn e.1 u hu).mp h.1).symm,
        ((lookup_iff_preimage p hn e.2 v hv).mp h.2).symm⟩
    · exact Or.inr ⟨((lookup_iff_preimage p hn e.1 v hv).mp h.1).symm,
        ((lookup_iff_preimage p hn e.2 u hu).mp h.2).symm⟩
  · rintro ⟨e,he,h⟩
    refine ⟨e,he,?_⟩
    simp only [decide_eq_true_eq, Prod.ext_iff] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    rcases h with h | h
    · exact Or.inl ⟨(lookup_iff_preimage p hn e.1 u hu).mpr h.1.symm,
        (lookup_iff_preimage p hn e.2 v hv).mpr h.2.symm⟩
    · exact Or.inr ⟨(lookup_iff_preimage p hn e.1 v hv).mpr h.1.symm,
        (lookup_iff_preimage p hn e.2 u hu).mpr h.2.symm⟩

/-- Uniform-host compatibility is precisely preservation of every observed edge
under the inverse assignment used by count_fits. -/
theorem historyCompatible_inverse (n : Nat) (edges history : List (Nat × Nat))
    (p : List Nat) (hp : p ∈ Anonymous.labels n)
    (hb : ∀ e ∈ history, e.1 < n ∧ e.2 < n) :
    Anonymous.historyCompatible edges p history = true ↔
      ∀ e ∈ history, originalGraph edges (p.idxOf e.1) (p.idxOf e.2) = true := by
  have hperm := (Counting.completions_spec n (List.range n) p (by simp)).mp hp
  have hn := hperm.nodup_iff.mpr List.nodup_range
  simp only [Anonymous.historyCompatible, List.all_eq_true]
  constructor <;> intro h e he
  all_goals
    have hu : e.1 ∈ p := hperm.mem_iff.mpr (List.mem_range.mpr (hb e he).1)
    have hv : e.2 ∈ p := hperm.mem_iff.mpr (List.mem_range.mpr (hb e he).2)
    have hi := edgePresent_inverse edges p hn e.1 e.2 hu hv
  · rw [← hi]; exact h e he
  · rw [hi]; exact h e he

end OnlineMatching.CountingReference

namespace OnlineMatching.CountingReference

private theorem idxOf_injective (p : List Nat) {u v : Nat} (hu : u ∈ p) (hv : v ∈ p)
    (h : p.idxOf u = p.idxOf v) : u = v := by
  have ha := List.getElem_idxOf (List.idxOf_lt_length_of_mem hu)
  have hb := List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)
  have h' : p[p.idxOf u]? = p[p.idxOf v]? := congrArg (fun i => p[i]?) h
  simpa [List.getElem?_eq_getElem, List.idxOf_lt_length_of_mem hu,
    List.idxOf_lt_length_of_mem hv] using h'

theorem inverse_perm (n : Nat) (p : List Nat) (hp : p.Perm (List.range n)) :
    (inverse p).Perm (List.range n) := by
  have hl : p.length = n := by simpa using hp.length_eq
  have hn : p.Nodup := hp.nodup_iff.mpr List.nodup_range
  have hi : (inverse p).Nodup := by
    unfold inverse
    rw [List.Nodup, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro u v hu hv hne he
    exact hne (idxOf_injective p
      (hp.mem_iff.mpr (by simpa [hl] using hu))
      (hp.mem_iff.mpr (by simpa [hl] using hv)) he)
  apply (List.perm_ext_iff_of_nodup hi List.nodup_range).mpr
  intro a
  constructor
  · intro ha
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
    have hu' : u ∈ p := hp.mem_iff.mpr (by simpa [hl] using hu)
    exact List.mem_range.mpr (by simpa [hl] using List.idxOf_lt_length_of_mem hu')
  · intro ha
    have hai : a < p.length := by simpa [hl] using List.mem_range.mp ha
    have hv : p[a] ∈ p := List.getElem_mem hai
    apply List.mem_map.mpr
    exact ⟨p[a], by simpa [hl] using hp.mem_iff.mp hv, hn.idxOf_getElem a hai⟩

theorem inverse_involution (n : Nat) (p : List Nat) (hp : p.Perm (List.range n)) :
    inverse (inverse p) = p := by
  have hl : p.length = n := by simpa using hp.length_eq
  have hn : p.Nodup := hp.nodup_iff.mpr List.nodup_range
  have hip := inverse_perm n p hp
  have hin : (inverse p).Nodup := hip.nodup_iff.mpr List.nodup_range
  have hil : (inverse p).length = n := by simpa using hip.length_eq
  apply List.ext_getElem?; intro i
  by_cases hi : i < n
  · have hi' : i < p.length := by omega
    have hv : p[i] ∈ p := List.getElem_mem hi'
    have hv' : p[i] < p.length := by
      have := List.mem_range.mp (hp.mem_iff.mp hv)
      omega
    have hlookup : (inverse p)[p[i]]? = some i := by
      rw [inverse_lookup p _ hv', hn.idxOf_getElem i hi']
    have himem : i ∈ inverse p := hip.mem_iff.mpr (List.mem_range.mpr hi)
    have hidx : (inverse p).idxOf i = p[i] :=
      (lookup_iff_preimage _ hin _ _ himem).mp hlookup
    rw [inverse_lookup _ i (by omega), hidx, List.getElem?_eq_getElem hi']
  · have hleft : (inverse (inverse p))[i]? = none :=
      List.getElem?_eq_none (by simp [inverse, hl]; omega)
    have hright : p[i]? = none := List.getElem?_eq_none (by omega)
    rw [hleft, hright]

theorem inverse_labels_perm (n : Nat) :
    ((Anonymous.labels n).map inverse).Perm (Anonymous.labels n) := by
  have hn := Prefix.completions_nodup n (List.range n) List.nodup_range
  have hmem (p : List Nat) (hp : p ∈ Anonymous.labels n) : inverse p ∈ Anonymous.labels n :=
    (Counting.completions_spec n _ _ (by simp)).mpr
      (inverse_perm n p ((Counting.completions_spec n _ _ (by simp)).mp hp))
  have hround (p : List Nat) (hp : p ∈ Anonymous.labels n) : inverse (inverse p) = p :=
    inverse_involution n p ((Counting.completions_spec n _ _ (by simp)).mp hp)
  have hm : ((Anonymous.labels n).map inverse).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ hn
    intro a b ha hb hne he
    have := congrArg inverse he
    rw [hround a ha, hround b hb] at this
    exact hne this
  apply (List.perm_ext_iff_of_nodup hm hn).mpr
  intro p
  constructor
  · intro h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact hmem q hq
  · intro hp
    exact List.mem_map.mpr ⟨inverse p, hmem p hp, hround p hp⟩

end OnlineMatching.CountingReference

/-! ## Placement filter -/

namespace OnlineMatching.CountingImages
open Counting

instance (g original : Graph Nat) (ps : List Placement) : Decidable (Good g original ps) :=
  inferInstanceAs (Decidable (ps.Pairwise _))

def pack (label : List Placement × List Nat) : List Nat := label.1.map Prod.snd ++ label.2

def unpack (order images : List Nat) : List Placement × List Nat :=
  (order.zip (images.take order.length), images.drop order.length)

def imageCompatible (g original : Graph Nat) (order images : List Nat) : Bool :=
  decide (Good g original ((unpack order images).1.reverse))

theorem unpack_pack (order : List Nat) (placed : List Placement) (suffix : List Nat)
    (hk : placed.map Prod.fst = order) : unpack order (pack (placed,suffix)) = (placed,suffix) := by
  have hl : (placed.map Prod.snd).length = order.length := by
    simpa using congrArg List.length hk
  unfold unpack pack
  rw [← hl, List.take_append_length, List.drop_append_length]
  rw [← List.zip_of_prod hk rfl]

theorem pack_unpack (order images : List Nat) (hl : order.length ≤ images.length) :
    pack (unpack order images) = images := by
  unfold pack unpack
  rw [List.map_snd_zip (by simp; omega), List.take_append_drop]

theorem unpack_valid (g original : Graph Nat) (host order images : List Nat)
    (hl : order.length ≤ images.length) (hp : images.Perm host)
    (hc : imageCompatible g original order images = true) :
    Valid g original host order [] (unpack order images).1 := by
  refine ⟨List.map_fst_zip (by simp; omega), ?_, ?_⟩
  · intro p hmem
    have hm := (List.of_mem_zip hmem).2
    exact hp.mem_iff.mp (List.mem_of_mem_take hm)
  · simpa [imageCompatible] using hc

theorem pack_universe (n : Nat) (g original : Graph Nat) (order : List Nat)
    (hk : order.length ≤ n) :
    ((fullLabellings g original (List.range n) order).map pack).Perm
      ((Anonymous.labels n).filter (imageCompatible g original order)) := by
  have hn := fullLabellings_nodup g original (List.range n) order List.nodup_range
  have hm : ((fullLabellings g original (List.range n) order).map pack).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ hn
    intro a b ha hb hne heq
    obtain ⟨hva, _⟩ := (fullLabellings_spec _ _ _ _ _ _).mp ha
    obtain ⟨hvb, _⟩ := (fullLabellings_spec _ _ _ _ _ _).mp hb
    have := congrArg (unpack order) heq
    rw [unpack_pack _ _ _ hva.1, unpack_pack _ _ _ hvb.1] at this
    exact hne this
  apply (List.perm_ext_iff_of_nodup hm
    ((Prefix.completions_nodup n (List.range n) List.nodup_range).filter _)).mpr
  intro images
  constructor
  · intro h
    obtain ⟨label, hl, rfl⟩ := List.mem_map.mp h
    obtain ⟨hv, hp⟩ := (fullLabellings_iff_bijective _ _ _ _ _ _).mp hl
    apply List.mem_filter.mpr
    refine ⟨(Counting.completions_spec n _ _ (by simp)).mpr hp, ?_⟩
    unfold imageCompatible
    rw [unpack_pack _ _ _ hv.1]
    simpa using hv.2.2
  · intro h
    obtain ⟨hp, hc⟩ := List.mem_filter.mp h
    have hperm := (Counting.completions_spec n (List.range n) images (by simp)).mp hp
    have hlen : images.length = n := by simpa using hperm.length_eq
    have hlen' : order.length ≤ images.length := by omega
    apply List.mem_map.mpr
    refine ⟨unpack order images, ?_, pack_unpack order images hlen'⟩
    apply (fullLabellings_iff_bijective _ _ _ _ _ _).mpr
    refine ⟨unpack_valid _ _ _ _ _ hlen' hperm hc, ?_⟩
    change (pack (unpack order images)).Perm (List.range n)
    rw [pack_unpack order images hlen']
    exact hperm

theorem countFits_eq_imageCount (n : Nat) (g original : Graph Nat) (order : List Nat)
    (hk : order.length ≤ n) :
    countFits g original (List.range n) order =
      ((Anonymous.labels n).filter (imageCompatible g original order)).length := by
  rw [countFits_eq_fullLabellings_length]
  have := (pack_universe n g original order hk).length_eq
  simpa using this

end OnlineMatching.CountingImages

namespace OnlineMatching.CountingImages
open Counting CountingReference

theorem originalGraph_sym (edges : List (Nat × Nat)) (u v : Nat) :
    originalGraph edges u v = originalGraph edges v u := by
  unfold originalGraph
  congr 1
  funext e
  simp [or_comm]

theorem originalGraph_irreflexive (edges : List (Nat × Nat))
    (h : ∀ e ∈ edges, e.1 ≠ e.2) (u : Nat) : originalGraph edges u u = false := by
  cases he : originalGraph edges u u with
  | false => rfl
  | true =>
    obtain ⟨e,he',heq⟩ := List.any_eq_true.mp he
    have heq' : e = (u,u) := by simpa using heq
    subst e
    exact False.elim (h _ he' rfl)

theorem embedsOn_history (history host : List (Nat × Nat)) (order : List Nat)
    (f : Nat → Nat) (hi : ∀ u ∈ order, ∀ v ∈ order, f u = f v → u = v)
    (hc : ∀ e ∈ history, e.1 ∈ order ∧ e.2 ∈ order) :
    EmbedsOn order (originalGraph history) (originalGraph host) f ↔
      ∀ e ∈ history, originalGraph host (f e.1) (f e.2) = true := by
  constructor
  · intro he e hm
    apply he.2 e.1 (hc e hm).1 e.2 (hc e hm).2
    exact List.any_eq_true.mpr ⟨e,hm,by simp⟩
  · intro he
    refine ⟨hi, ?_⟩
    intro u hu v hv huv
    obtain ⟨e,hm,heq⟩ := List.any_eq_true.mp huv
    have heq' : e = (u,v) ∨ e = (v,u) := by simpa using heq
    rcases heq' with rfl | rfl
    · exact he _ hm
    · rw [originalGraph_sym]; exact he _ hm

theorem imageCompatible_prefix (g original : Graph Nat) (order images : List Nat)
    (f : Nat → Nat) (hprefix : images.take order.length = order.map f)
    (hn : order.Nodup) (hi : ∀ v, g v v = false) :
    imageCompatible g original order images = true ↔ EmbedsOn order g original f := by
  unfold imageCompatible
  rw [decide_eq_true_eq]
  change Good g original (order.zip (images.take order.length)).reverse ↔ _
  rw [hprefix, ← List.map_prod_left_eq_zip]
  rw [good_reverse, good_map_iff_embeds g original order f hn hi]

/-- Once inverse images are arranged in the chosen vertex order, the actual
placement filter is exactly the reference model's hidden-labeling event. -/
theorem imageCompatible_inverse_prefix (n : Nat) (host history : List (Nat × Nat))
    (order images p : List Nat) (hp : p ∈ Anonymous.labels n)
    (ho : order.Nodup) (hob : ∀ u ∈ order, u < n)
    (hh : ∀ e ∈ history, e.1 ≠ e.2)
    (hc : ∀ e ∈ history, e.1 ∈ order ∧ e.2 ∈ order)
    (hprefix : images.take order.length = order.map p.idxOf) :
    imageCompatible (originalGraph history) (originalGraph host) order images =
      Anonymous.historyCompatible host p history := by
  have hperm := (Counting.completions_spec n (List.range n) p (by simp)).mp hp
  apply Bool.eq_iff_iff.mpr
  rw [imageCompatible_prefix _ _ _ _ _ hprefix ho (originalGraph_irreflexive history hh)]
  rw [embedsOn_history history host order p.idxOf ?_ hc]
  · exact (historyCompatible_inverse n host history p hp (fun e he =>
      ⟨hob e.1 (hc e he).1, hob e.2 (hc e he).2⟩)).symm
  · intro u hu v hv he
    have hup : u ∈ p := hperm.mem_iff.mpr (List.mem_range.mpr (hob u hu))
    have hvp : v ∈ p := hperm.mem_iff.mpr (List.mem_range.mpr (hob v hv))
    have hu' := List.idxOf_lt_length_of_mem hup
    have hv' := List.idxOf_lt_length_of_mem hvp
    have he' := congrArg (fun i => p[i]?) he
    simpa [List.getElem?_eq_getElem hu', List.getElem?_eq_getElem hv'] using he'

end OnlineMatching.CountingImages

/-! ## Reindexing -/

namespace OnlineMatching.Reindex

open CountingReference

def lookup (xs : List Nat) (i : Nat) : Nat := xs[i]?.getD 0

def reindex (indices images : List Nat) : List Nat := indices.map (lookup images)

theorem range_at (images : List Nat) :
    (List.range images.length).map (lookup images) = images := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < images.length
  · simp [hi, lookup]
  · simp [hi]

theorem reindex_perm (n : Nat) (indices images : List Nat)
    (hi : indices.Perm (List.range n)) (hp : images.Perm (List.range n)) :
    (reindex indices images).Perm (List.range n) := by
  have hl : images.length = n := by simpa using hp.length_eq
  have h := hi.map (lookup images)
  have he : (List.range n).map (lookup images) = images := by rw [← hl, range_at]
  exact (h.trans (by rw [he])).trans hp

theorem at_reindex (indices images : List Nat) (i : Nat) (hi : i < indices.length) :
    lookup (reindex indices images) i = lookup images (lookup indices i) := by
  simp [lookup, reindex, List.getElem?_eq_getElem hi]

theorem reindex_inverse (n : Nat) (indices images : List Nat)
    (hi : indices.Perm (List.range n)) (hp : images.Perm (List.range n)) :
    reindex (inverse indices) (reindex indices images) = images := by
  have hil : indices.length = n := by simpa using hi.length_eq
  have hpl : images.length = n := by simpa using hp.length_eq
  have hn : indices.Nodup := hi.nodup_iff.mpr List.nodup_range
  have hiip := inverse_perm n indices hi
  have hiil : (inverse indices).length = n := by simpa using hiip.length_eq
  apply List.ext_getElem?
  intro i
  by_cases hin : i < n
  · have himem : i ∈ indices := hi.mem_iff.mpr (List.mem_range.mpr hin)
    have hidx : indices.idxOf i < indices.length := List.idxOf_lt_length_of_mem himem
    have hlookup : (inverse indices)[i]? = some (indices.idxOf i) :=
      inverse_lookup indices i (by omega)
    simp only [reindex, List.getElem?_map, hlookup, Option.map_some]
    rw [show lookup (indices.map (lookup images)) (indices.idxOf i) =
        lookup images (lookup indices (indices.idxOf i)) from at_reindex indices images _ hidx]
    simp [lookup, List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem (show i < images.length by omega)]
  · have hn1 : (reindex (inverse indices) (reindex indices images)).length = n := by
      simp [reindex, hiil]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem labels_reindex (n : Nat) (indices : List Nat)
    (hi : indices.Perm (List.range n)) :
    ((Anonymous.labels n).map (reindex indices)).Perm (Anonymous.labels n) := by
  have hn := Prefix.completions_nodup n (List.range n) List.nodup_range
  have spec (p : List Nat) : p ∈ Anonymous.labels n ↔ p.Perm (List.range n) :=
    Counting.completions_spec n (List.range n) p (by simp)
  have hm : ((Anonymous.labels n).map (reindex indices)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ hn
    intro a b ha hb hne he
    have h := congrArg (reindex (inverse indices)) he
    rw [reindex_inverse n indices a hi ((spec a).mp ha),
      reindex_inverse n indices b hi ((spec b).mp hb)] at h
    exact hne h
  apply (List.perm_ext_iff_of_nodup hm hn).mpr
  intro p
  constructor
  · intro h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (spec _).mpr (reindex_perm n indices q hi ((spec q).mp hq))
  · intro hp
    have hip := inverse_perm n indices hi
    refine List.mem_map.mpr ⟨reindex (inverse indices) p,
      (spec _).mpr (reindex_perm n _ p hip ((spec p).mp hp)), ?_⟩
    have h := reindex_inverse n (inverse indices) p hip ((spec p).mp hp)
    rw [inverse_involution n indices hi] at h
    exact h

theorem take_reindex (order suffix images : List Nat) :
    (reindex (order ++ suffix) images).take order.length = order.map (lookup images) := by
  unfold reindex
  rw [List.map_append, ← List.length_map (f := lookup images) (as := order),
    List.take_append_length]

theorem fullOrder_perm (n k : Nat) (order : List Nat)
    (ho : order.Perm (List.range k)) (hk : k ≤ n) :
    (order ++ List.range' k (n-k)).Perm (List.range n) := by
  have h := ho.append_right (List.range' k (n-k))
  have he : List.range k ++ List.range' k (n-k) = List.range n := by
    simpa [Nat.add_sub_of_le hk, List.range_eq_range'] using
      (List.range'_append (s := 0) (m := k) (n := n-k) (step := 1))
  exact h.trans (by rw [he])

end OnlineMatching.Reindex

/-! ## Count equals labeling count -/

namespace OnlineMatching.CountingEndToEnd
open Counting CountingReference CountingImages

/-- The full count_fits count agrees with the uniform hidden-permutation count,
including arbitrary traversal order of the observed labels and inversion of the
host-to-public convention used by the reference probability model. -/
theorem countFits_eq_compatibleCount (n k : Nat) (host history : List (Nat × Nat))
    (order : List Nat) (ho : order.Perm (List.range k)) (hk : k ≤ n)
    (hh : ∀ e ∈ history, e.1 ≠ e.2)
    (hc : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    countFits (originalGraph history) (originalGraph host) (List.range n) order =
      Anonymous.compatibleCount n host history := by
  have hol : order.length = k := by simpa using ho.length_eq
  have hon : order.Nodup := ho.nodup_iff.mpr List.nodup_range
  let fullOrder := order ++ List.range' k (n-k)
  let transform := fun p => Reindex.reindex fullOrder (inverse p)
  have hfull : fullOrder.Perm (List.range n) := Reindex.fullOrder_perm n k order ho hk
  have hp : ((Anonymous.labels n).map transform).Perm (Anonymous.labels n) := by
    have h1 := (inverse_labels_perm n).map (Reindex.reindex fullOrder)
    have h2 := Reindex.labels_reindex n fullOrder hfull
    simpa [List.map_map, transform, Function.comp_def] using h1.trans h2
  have he : ∀ p ∈ Anonymous.labels n,
      imageCompatible (originalGraph history) (originalGraph host) order (transform p) =
        Anonymous.historyCompatible host p history := by
    intro p hpl
    have hperm := (Counting.completions_spec n (List.range n) p (by simp)).mp hpl
    have hlen : p.length = n := by simpa using hperm.length_eq
    apply imageCompatible_inverse_prefix n host history order (transform p) p hpl hon
    · intro u hu
      have := List.mem_range.mp (ho.mem_iff.mp hu)
      omega
    · exact hh
    · intro e he
      exact ⟨ho.mem_iff.mpr (List.mem_range.mpr (hc e he).1),
        ho.mem_iff.mpr (List.mem_range.mpr (hc e he).2)⟩
    · rw [show transform p = Reindex.reindex (order ++ List.range' k (n-k)) (inverse p) from rfl,
        Reindex.take_reindex]
      apply List.map_congr_left
      intro u hu
      have hu' : u < p.length := by
        have := List.mem_range.mp (ho.mem_iff.mp hu)
        omega
      simp only [Reindex.lookup, inverse_lookup p u hu', Option.getD_some]
  rw [countFits_eq_imageCount n _ _ order (by omega)]
  have hcount := (hp.filter (imageCompatible (originalGraph history) (originalGraph host) order)).length_eq
  rw [List.filter_map, List.length_map] at hcount
  have hfilter : (Anonymous.labels n).filter
      ((imageCompatible (originalGraph history) (originalGraph host) order) ∘ transform) =
      (Anonymous.labels n).filter (Anonymous.historyCompatible host · history) := by
    apply List.filter_congr
    exact he
  rw [hfilter] at hcount
  exact hcount.symm

/-- The degree-pruned count equals the number of compatible labelings. -/
theorem count_fits_eq_compatibleCount (n k : Nat)
    (host history : List (Nat × Nat)) (order : List Nat)
    (ho : order.Perm (List.range k)) (hk : k ≤ n)
    (hh : ∀ e ∈ history, e.1 ≠ e.2)
    (hc : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    dfsPruned (originalGraph history) (originalGraph host) (List.range n)
        (degreeOK (originalGraph history) (originalGraph host) order (List.range n)) order [] *
      factorial (n-k) = Anonymous.compatibleCount n host history := by
  rw [degree_pruned_dfs_eq_dfs _ _ _ _ List.nodup_range
    (ho.nodup_iff.mpr List.nodup_range) (originalGraph_irreflexive history hh)]
  have hl : order.length = k := by simpa using ho.length_eq
  simpa [countFits, hl] using countFits_eq_compatibleCount n k host history order ho hk hh hc

end OnlineMatching.CountingEndToEnd

/-! ## Invariance under relabeling -/

namespace OnlineMatching.CanonicalCounting
open ImplementationGraph CanonicalState Counting CountingReference

theorem compatibleCount_history_perm (n : Nat) (original a b : List Offline.Edge)
    (h : a.Perm b) :
    Anonymous.compatibleCount n original a = Anonymous.compatibleCount n original b := by
  unfold Anonymous.compatibleCount
  congr 1
  apply List.filter_congr
  intro p _
  exact h.all_eq

/-- The canonicalizer's permutation/adjacency contract preserves the number of
compatible hidden labelings. -/
theorem compatibleCount_canonical (n k : Nat) (original history : List Offline.Edge)
    (r : CanonicalResult k (graph history)) (hk : k ≤ n)
    (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 < e.2)
    (hb : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    Anonymous.compatibleCount n original (edges k r.canonical) =
      Anonymous.compatibleCount n original history := by
  have hperm := canonical_edges_perm history r hh hs hb
  rw [← compatibleCount_history_perm n original _ _ hperm]
  exact Symmetry.compatibleCount_map (r.permutation.finite hk) original history

/-- The actual degree-pruned DFS and its factorial completion factor. -/
abbrev countFits (n k : Nat) (original history : List Offline.Edge) (order : List Nat) : Nat :=
  dfsPruned (originalGraph history) (originalGraph original) (List.range n)
      (degreeOK (originalGraph history) (originalGraph original) order (List.range n)) order [] *
    factorial (n-k)

theorem countFits_eq (n k : Nat) (original history : List Offline.Edge)
    (order : List Nat) (ho : order.Perm (List.range k)) (hk : k ≤ n)
    (hh : ∀ e ∈ history, e.1 ≠ e.2)
    (hb : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    countFits n k original history order = Anonymous.compatibleCount n original history :=
  CountingEndToEnd.count_fits_eq_compatibleCount n k original history order ho hk hh hb

/-- Relabeling and traversal order preserve the embedding count. -/
theorem countFits_canonical (n k : Nat) (original history : List Offline.Edge)
    (r : CanonicalResult k (graph history)) (order canonicalOrder : List Nat)
    (ho : order.Perm (List.range k)) (hco : canonicalOrder.Perm (List.range k))
    (hk : k ≤ n) (hh : history.Nodup) (hs : ∀ e ∈ history, e.1 < e.2)
    (hb : ∀ e ∈ history, e.1 < k ∧ e.2 < k) :
    countFits n k original (edges k r.canonical) canonicalOrder =
      countFits n k original history order := by
  rw [countFits_eq n k original history order ho hk (fun e he => Nat.ne_of_lt (hs e he)) hb,
    countFits_eq n k original (edges k r.canonical) canonicalOrder hco hk]
  · exact compatibleCount_canonical n k original history r hk hh hs hb
  · intro e he
    exact Nat.ne_of_lt ((mem_edges k r.canonical e).mp he).1
  · intro e he
    have h := (mem_edges k r.canonical e).mp he
    exact ⟨by omega,h.2.1⟩

end OnlineMatching.CanonicalCounting
