import OnlineMatching.Reference.Model

/-!
# Permutation and list invariance

The reference value is invariant under every permutation of the observed
labels (`Symmetry.value_map`) and does not depend on the order in which the
history and the unmatched labels are listed. `CanonicalState` packages these
facts for an arbitrary relabeling oracle.
-/

/-! ## Permutation invariance -/

namespace OnlineMatching.Symmetry

open ImplementationGraph Transitions

structure FinitePermutation (n : Nat) extends Permutation Nat where
  forward_lt : ∀ v, v < n → forward v < n
  backward_lt : ∀ v, v < n → backward v < n

def FinitePermutation.symm {n : Nat} (p : FinitePermutation n) : FinitePermutation n where
  forward := p.backward
  backward := p.forward
  left_inverse := p.right_inverse
  right_inverse := p.left_inverse
  forward_lt := p.backward_lt
  backward_lt := p.forward_lt

def edge (f : Nat → Nat) (e : Offline.Edge) : Offline.Edge :=
  (min (f e.1) (f e.2), max (f e.1) (f e.2))

def history (f : Nat → Nat) (es : List Offline.Edge) := es.map (edge f)

theorem range_map_perm {n : Nat} (p : FinitePermutation n) :
    ((List.range n).map p.forward).Perm (List.range n) := by
  have hn : ((List.range n).map p.forward).Nodup :=
    List.Pairwise.map _ (fun _ _ hn he => hn (p.toPermutation.injective he)) List.nodup_range
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr
  intro v
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact p.forward_lt w hw
  · intro hv
    exact ⟨p.backward v, p.backward_lt v hv, p.right_inverse v⟩

theorem labels_map_perm {n : Nat} (p : FinitePermutation n) :
    ((hiddenLabels n).map (fun ls => ls.map p.forward)).Perm (hiddenLabels n) := by
  have hn := Prefix.completions_nodup n (List.range n) List.nodup_range
  have hinv (ls : List Nat) : (ls.map p.forward).map p.backward = ls := by
    simp [List.map_map, Function.comp_def, p.left_inverse]
  have hmap : ((hiddenLabels n).map (fun ls => ls.map p.forward)).Nodup :=
    List.Pairwise.map _ (fun _ _ hne he => hne (by
      have := congrArg (fun ls => ls.map p.backward) he
      simpa only [hinv] using this)) hn
  apply (List.perm_ext_iff_of_nodup hmap hn).mpr
  intro ls
  constructor
  · intro h
    obtain ⟨src, hs, rfl⟩ := List.mem_map.mp h
    apply (hiddenLabels_spec n _).mpr
    exact (((hiddenLabels_spec n _).mp hs).map p.forward).trans (range_map_perm p)
  · intro hs
    have hb : ls.map p.backward ∈ hiddenLabels n := by
      apply (hiddenLabels_spec n _).mpr
      exact (((hiddenLabels_spec n _).mp hs).map p.backward).trans (range_map_perm p.symm)
    apply List.mem_map.mpr
    refine ⟨ls.map p.backward, hb, ?_⟩
    simp [List.map_map, Function.comp_def, p.right_inverse]

theorem mapped_lookup (p : Permutation Nat) (ls : List Nat) (a u : Nat) :
    ((ls.map p.forward)[a]? == some (p.forward u)) = (ls[a]? == some u) := by
  simp only [List.getElem?_map]
  cases ls[a]? with
  | none => rfl
  | some w =>
    apply Bool.eq_iff_iff.mpr
    simp only [Option.map_some, beq_iff_eq, Option.some.injEq]
    exact ⟨p.injective, congrArg p.forward⟩

theorem edgePresent_map (p : Permutation Nat) (original : List Offline.Edge)
    (ls : List Nat) (u v : Nat) :
    Anonymous.edgePresent original (ls.map p.forward) (p.forward u) (p.forward v) =
      Anonymous.edgePresent original ls u v := by
  unfold Anonymous.edgePresent
  congr 1
  funext e
  simp only [mapped_lookup]

theorem edgePresent_sorted (original : List Offline.Edge) (ls : List Nat) (u v : Nat) :
    Anonymous.edgePresent original ls (min u v) (max u v) =
      Anonymous.edgePresent original ls u v := by
  by_cases huv : u ≤ v
  · simp [Nat.min_eq_left huv, Nat.max_eq_right huv]
  · have hvu : v ≤ u := by omega
    simp only [Nat.min_eq_right hvu, Nat.max_eq_left hvu, Anonymous.edgePresent]
    congr 1
    funext e
    exact Bool.or_comm _ _

theorem historyCompatible_map (p : Permutation Nat) (original es : List Offline.Edge)
    (ls : List Nat) :
    Anonymous.historyCompatible original (ls.map p.forward) (history p.forward es) =
      Anonymous.historyCompatible original ls es := by
  simp only [Anonymous.historyCompatible, history, List.all_map]
  congr 1
  funext e
  simp only [Function.comp_def, edge, edgePresent_sorted, edgePresent_map]

theorem compatibleCount_map {n : Nat} (p : FinitePermutation n)
    (original es : List Offline.Edge) :
    Anonymous.compatibleCount n original (history p.forward es) =
      Anonymous.compatibleCount n original es := by
  have hp := ((labels_map_perm p).filter
    (fun ls => Anonymous.historyCompatible original ls (history p.forward es))).length_eq
  rw [List.filter_map, List.length_map] at hp
  have hfilter : (hiddenLabels n).filter
      ((fun ls => Anonymous.historyCompatible original ls (history p.forward es)) ∘
        (fun ls => ls.map p.forward)) =
      (hiddenLabels n).filter (fun ls => Anonymous.historyCompatible original ls es) := by
    apply List.filter_congr
    intro ls _
    exact historyCompatible_map p.toPermutation original es ls
  rw [hfilter] at hp
  exact hp.symm

theorem edge_inverse (p : Permutation Nat) (e : Offline.Edge) (he : e.1 ≤ e.2) :
    edge p.backward (edge p.forward e) = e := by
  unfold edge
  by_cases h : p.forward e.1 ≤ p.forward e.2
  · simp only [Nat.min_eq_left h, Nat.max_eq_right h, p.left_inverse,
      Nat.min_eq_left he, Nat.max_eq_right he]
  · have h' : p.forward e.2 ≤ p.forward e.1 := by omega
    simp only [Nat.min_eq_right h', Nat.max_eq_left h', p.left_inverse,
      Nat.min_eq_right he, Nat.max_eq_left he]

theorem edge_injective (p : Permutation Nat) (e f : Offline.Edge)
    (he : e.1 ≤ e.2) (hf : f.1 ≤ f.2) (h : edge p.forward e = edge p.forward f) : e = f := by
  have hi := congrArg (edge p.backward) h
  simpa only [edge_inverse p e he, edge_inverse p f hf] using hi

theorem edge_sorted (f : Nat → Nat) (e : Offline.Edge) : (edge f e).1 ≤ (edge f e).2 := by
  simp only [edge]
  omega

theorem history_inverse (p : Permutation Nat) (es : List Offline.Edge)
    (hs : ∀ e ∈ es, e.1 ≤ e.2) : history p.backward (history p.forward es) = es := by
  simp only [history, List.map_map]
  exact List.map_congr_left (fun e he => edge_inverse p e (hs e he)) |>.trans (List.map_id es)

theorem history_sorted (f : Nat → Nat) (es : List Offline.Edge) :
    ∀ e ∈ history f es, e.1 ≤ e.2 := by
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  exact edge_sorted f a

theorem history_nodup (p : Permutation Nat) (es : List Offline.Edge)
    (hn : es.Nodup) (hs : ∀ e ∈ es, e.1 ≤ e.2) : (history p.forward es).Nodup := by
  rw [history, List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_ hn
  intro a b ha hb hne he
  exact hne (edge_injective p a b (hs a ha) (hs b hb) he)

theorem edge_mem_history (p : Permutation Nat) (es : List Offline.Edge) (e : Offline.Edge)
    (hs : ∀ f ∈ es, f.1 ≤ f.2) (he : e.1 ≤ e.2) :
    edge p.forward e ∈ history p.forward es ↔ e ∈ es := by
  constructor
  · intro h
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp h
    exact (edge_injective p f e (hs f hf) he hfe) ▸ hf
  · intro h
    exact List.mem_map.mpr ⟨e, h, rfl⟩

theorem possible_iff (labels : List L) (host : L → List Offline.Edge)
    (s : ImplementationGraph.State) (e : Offline.Edge) :
    e ∈ possible labels host s ↔
      e ∉ s.observed ∧ compatibleLabels labels host (e :: s.observed) ≠ [] := by
  constructor
  · exact possible_reachable labels host s e
  · rintro ⟨hfresh, hc⟩
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hc
    have hl' := List.mem_filter.mp hl
    have hcompat := (compatible_iff _ _).mp hl'.2
    have hparent : l ∈ compatibleLabels labels host s.observed :=
      List.mem_filter.mpr ⟨hl'.1, (compatible_iff _ _).mpr (fun a ha =>
        hcompat a (List.mem_cons_of_mem _ ha))⟩
    simp only [possible, List.mem_eraseDups, List.mem_map]
    refine ⟨(l,e), ?_, rfl⟩
    simp only [graphOutcomes, outcomes, List.mem_flatMap, List.mem_map]
    exact ⟨l, hparent, e, List.mem_filter.mpr ⟨hcompat e (by simp), by simpa⟩, rfl⟩

theorem possible_sorted (n : Nat) (original : List Offline.Edge)
    (s : ImplementationGraph.State) (e : Offline.Edge)
    (he : e ∈ possible (hiddenLabels n) (labelledHost original) s) : e.1 ≤ e.2 := by
  simp only [possible, List.mem_eraseDups, List.mem_map] at he
  obtain ⟨p, hp, hpedge⟩ := he
  simp only [graphOutcomes, outcomes, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨l, _, a, ha, hpa⟩ := hp
  subst p
  simp only at hpedge
  subst e
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp ha).1
  simp only [labelledHost] at *
  exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)

def state (f : Nat → Nat) (s : ImplementationGraph.State) : ImplementationGraph.State :=
  ⟨history f s.observed, s.free.map f⟩

theorem possible_map_iff {n : Nat} (p : FinitePermutation n) (original : List Offline.Edge)
    (s : ImplementationGraph.State) (e : Offline.Edge)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hs : ∀ a ∈ s.observed, a.1 ≤ a.2) (he : e.1 ≤ e.2) :
    edge p.forward e ∈ possible (hiddenLabels n) (labelledHost original) (state p.forward s) ↔
      e ∈ possible (hiddenLabels n) (labelledHost original) s := by
  rw [possible_iff, possible_iff]
  change (edge p.forward e ∉ history p.forward s.observed ∧ _) ↔ _
  rw [edge_mem_history p.toPermutation s.observed e hs he]
  have hcount := labelledHost_count n original (e :: s.observed)
    (by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact he; exact hs a ha) hb
  have hcount' := labelledHost_count n original (history p.forward (e :: s.observed))
    (history_sorted p.forward _) hb
  rw [compatibleCount_map p] at hcount'
  have hh : (compatibleLabels (hiddenLabels n) (labelledHost original)
      (edge p.forward e :: (state p.forward s).observed)).length =
      (compatibleLabels (hiddenLabels n) (labelledHost original) (e :: s.observed)).length :=
    hcount'.trans hcount.symm
  apply and_congr_right
  intro _
  apply not_congr
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hh]

theorem remove_perm (a b : List Nat) (e : Offline.Edge) (h : a.Perm b) :
    (Offline.remove a e).Perm (Offline.remove b e) :=
  (h.erase e.1).erase e.2

theorem value_free_perm (n : Nat) (original es : List Offline.Edge) (a b : List Nat)
    (h : a.Perm b) (fuel : Nat) :
    value (referenceModel n original) fuel ⟨es,a⟩ =
      value (referenceModel n original) fuel ⟨es,b⟩ := by
  induction fuel generalizing es a b with
  | zero => rfl
  | succ fuel ih =>
    simp only [value]
    apply total_congr
    intro e _
    have hl : Offline.legal a e ↔ Offline.legal b e := by
      simp only [Offline.legal, h.mem_iff]
    change nextWeight (hiddenLabels n) (labelledHost original) ⟨es,a⟩ e *
        (if decide (Offline.legal a e) then
          max (value (referenceModel n original) fuel ⟨e::es,a⟩) (1 + value (referenceModel n original) fuel ⟨e::es,Offline.remove a e⟩)
        else value (referenceModel n original) fuel ⟨e::es,a⟩) =
      nextWeight (hiddenLabels n) (labelledHost original) ⟨es,b⟩ e *
        (if decide (Offline.legal b e) then
          max (value (referenceModel n original) fuel ⟨e::es,b⟩) (1 + value (referenceModel n original) fuel ⟨e::es,Offline.remove b e⟩)
        else value (referenceModel n original) fuel ⟨e::es,b⟩)
    have hlb : decide (Offline.legal a e) = decide (Offline.legal b e) := by
      apply Bool.eq_iff_iff.mpr; simpa using hl
    rw [hlb, ih (e::es) a b h, ih (e::es) _ _ (remove_perm a b e h)]
    rfl

theorem possible_map_perm {n : Nat} (p : FinitePermutation n) (original : List Offline.Edge)
    (s : ImplementationGraph.State)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hs : ∀ a ∈ s.observed, a.1 ≤ a.2) :
    ((possible (hiddenLabels n) (labelledHost original) s).map (edge p.forward)).Perm
      (possible (hiddenLabels n) (labelledHost original) (state p.forward s)) := by
  have hpn := dedup_nodup
    ((graphOutcomes (hiddenLabels n) (labelledHost original) s.observed).map Prod.snd)
  have hmapn := history_nodup p.toPermutation
    (possible (hiddenLabels n) (labelledHost original) s) hpn
    (possible_sorted n original s)
  apply (List.perm_ext_iff_of_nodup hmapn (dedup_nodup _)).mpr
  intro e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact (possible_map_iff p original s f hb hs (possible_sorted n original s f hf)).mpr hf
  · intro he
    have hes := possible_sorted n original (state p.forward s) e he
    have h := (possible_map_iff p.symm original (state p.forward s) e hb
      (history_sorted _ _) hes).mpr he
    have hstate : state p.backward (state p.forward s) = s := by
      cases s with
      | mk es free =>
        simp only [state]
        rw [history_inverse p.toPermutation es hs]
        congr 1
        simp [List.map_map, Function.comp_def, p.left_inverse]
    change edge p.backward e ∈ possible _ _ (state p.backward (state p.forward s)) at h
    rw [hstate] at h
    refine List.mem_map.mpr ⟨edge p.backward e, h, ?_⟩
    exact edge_inverse p.symm.toPermutation e hes

theorem observations_map_perm {n : Nat} (p : FinitePermutation n)
    (original : List Offline.Edge) (s : ImplementationGraph.State)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hs : ∀ a ∈ s.observed, a.1 ≤ a.2) :
    (((referenceModel n original).observations s).map (edge p.forward)).Perm
      ((referenceModel n original).observations (state p.forward s)) := by
  simp only [referenceModel, model, state, history, List.length_map]
  split
  · exact possible_map_perm p original s hb hs
  · simp

theorem probability_map {n : Nat} (p : FinitePermutation n) (original : List Offline.Edge)
    (s : ImplementationGraph.State) (e : Offline.Edge)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hsn : s.observed.Nodup) (hs : ∀ a ∈ s.observed, a.1 ≤ a.2)
    (he : e.1 ≤ e.2) (hef : e ∉ s.observed) :
    (referenceModel n original).probability (state p.forward s) (edge p.forward e) =
      (referenceModel n original).probability s e := by
  cases s with | mk es free =>
  change (referenceModel n original).probability ⟨history p.forward es, free.map p.forward⟩ (edge p.forward e) = _
  rw [reference_weight_formula n original _ _ _ hn ho hb
    (history_nodup p.toPermutation _ hsn hs) (history_sorted _ _) (edge_sorted _ _)
    (by exact fun h => hef ((edge_mem_history p.toPermutation _ _ hs he).mp h)),
    reference_weight_formula n original _ _ _ hn ho hb hsn hs he hef]
  change (Anonymous.compatibleCount n original (history p.forward (e::es)) : Rat) / _ = _
  rw [compatibleCount_map p]
  simp only [history, List.length_map]
  rw [show Anonymous.compatibleCount n original (es.map (edge p.forward)) =
      Anonymous.compatibleCount n original es from compatibleCount_map p original _]

theorem legal_sorted (free : List Nat) (a b : Nat) :
    Offline.legal free (min a b,max a b) ↔ Offline.legal free (a,b) := by
  by_cases h : a ≤ b
  · simp [Nat.min_eq_left h, Nat.max_eq_right h]
  · have h' : b ≤ a := by omega
    simp only [Nat.min_eq_right h', Nat.max_eq_left h', Offline.legal]
    grind

theorem legal_map (p : Permutation Nat) (free : List Nat) (e : Offline.Edge) :
    Offline.legal (free.map p.forward) (edge p.forward e) ↔ Offline.legal free e := by
  rw [edge, legal_sorted, Implementation.legal_rename]

theorem remove_sorted (free : List Nat) (a b : Nat) :
    Offline.remove free (min a b,max a b) = Offline.remove free (a,b) := by
  by_cases h : a ≤ b
  · simp [Nat.min_eq_left h, Nat.max_eq_right h]
  · have h' : b ≤ a := by omega
    simp only [Nat.min_eq_right h', Nat.max_eq_left h', Offline.remove]
    exact List.erase_comm _ _

theorem remove_map (p : Permutation Nat) (free : List Nat) (e : Offline.Edge) :
    Offline.remove (free.map p.forward) (edge p.forward e) =
      (Offline.remove free e).map p.forward := by
  rw [edge, remove_sorted, Implementation.remove_rename]

/-- The concrete reference Bellman recursion is invariant under every permutation
of the public labels. The proof transports its enumerated observations and their
conditional weights; it does not postulate equality of Bellman values. -/
theorem value_map {n : Nat} (p : FinitePermutation n) (original : List Offline.Edge)
    (s : ImplementationGraph.State) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hsn : s.observed.Nodup) (hs : ∀ a ∈ s.observed, a.1 ≤ a.2) :
    value (referenceModel n original) fuel (state p.forward s) =
      value (referenceModel n original) fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [value]
    rw [← total_perm (observations_map_perm p original s hb hs), total_map]
    apply total_congr
    intro e he
    have heposs : e ∈ possible (hiddenLabels n) (labelledHost original) s := by
      change e ∈ (if s.observed.length < original.length then _ else []) at he
      split at he
      · exact he
      · simp at he
    have hes := possible_sorted n original s e heposs
    have hef := (possible_reachable (hiddenLabels n) (labelledHost original) s e heposs).1
    have hchild : (e :: s.observed).Nodup := List.nodup_cons.mpr ⟨hef, hsn⟩
    have horder : ∀ a ∈ e :: s.observed, a.1 ≤ a.2 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hes
      · exact hs a ha
    have hr : (referenceModel n original).reject (state p.forward s) (edge p.forward e) =
        state p.forward ((referenceModel n original).reject s e) := rfl
    have ha : (referenceModel n original).accept (state p.forward s) (edge p.forward e) =
        state p.forward ((referenceModel n original).accept s e) := by
      simp only [referenceModel, model, accept, state, history, List.map_cons,
        remove_map p.toPermutation]
    have hl : (referenceModel n original).legal (state p.forward s) (edge p.forward e) =
        (referenceModel n original).legal s e := by
      apply Bool.eq_iff_iff.mpr
      simpa only [referenceModel, model, state, decide_eq_true_eq] using
        legal_map p.toPermutation s.free e
    rw [probability_map p original s e hn ho hb hsn hs hes hef, hr, ha, hl,
      ih ((referenceModel n original).reject s e) hchild horder,
      ih ((referenceModel n original).accept s e) hchild horder]

end OnlineMatching.Symmetry

/-! ## List invariance -/

namespace OnlineMatching.Symmetry

open ImplementationGraph Transitions

theorem compatible_history_perm [DecidableEq E] (a b host : List E) (h : a.Perm b) :
    compatible a host = compatible b host := h.all_eq

theorem graphOutcomes_history_perm [DecidableEq E] (labels : List L) (host : L → List E)
    (a b : List E) (h : a.Perm b) :
    graphOutcomes labels host a = graphOutcomes labels host b := by
  have hc : compatibleLabels labels host a = compatibleLabels labels host b := by
    unfold compatibleLabels
    congr 1
    funext l
    exact compatible_history_perm a b (host l) h
  have hr (l : L) : remainingEdges (host l) a = remainingEdges (host l) b := by
    unfold remainingEdges
    congr 1
    funext e
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using not_congr (h.mem_iff (a := e))
  simp only [graphOutcomes, hc, hr]

theorem value_history_perm (n : Nat) (original a b : List Offline.Edge) (free : List Nat)
    (h : a.Perm b) (fuel : Nat) :
    value (referenceModel n original) fuel ⟨a,free⟩ =
      value (referenceModel n original) fuel ⟨b,free⟩ := by
  induction fuel generalizing a b free with
  | zero => rfl
  | succ fuel ih =>
    have hout := graphOutcomes_history_perm (hiddenLabels n) (labelledHost original) a b h
    have hobs : (referenceModel n original).observations ⟨a,free⟩ =
        (referenceModel n original).observations ⟨b,free⟩ := by
      simp only [referenceModel, model, h.length_eq, possible, hout]
    simp only [value]
    rw [← hobs]
    apply total_congr
    intro e _
    have hp : (referenceModel n original).probability ⟨a,free⟩ e =
        (referenceModel n original).probability ⟨b,free⟩ e := by
      simp only [referenceModel, model, nextWeight, hout]
    rw [hp]
    change _ *
        (if decide (Offline.legal free e) then
          max (value (referenceModel n original) fuel ⟨e::a,free⟩)
            (1 + value (referenceModel n original) fuel ⟨e::a,Offline.remove free e⟩)
        else value (referenceModel n original) fuel ⟨e::a,free⟩) =
      _ *
        (if decide (Offline.legal free e) then
          max (value (referenceModel n original) fuel ⟨e::b,free⟩)
            (1 + value (referenceModel n original) fuel ⟨e::b,Offline.remove free e⟩)
        else value (referenceModel n original) fuel ⟨e::b,free⟩)
    rw [ih (e::a) (e::b) free (h.cons e), ih (e::a) (e::b) _ (h.cons e)]

end OnlineMatching.Symmetry

/-! ## Relabeled states -/

namespace OnlineMatching.CanonicalState

open ImplementationGraph Symmetry

/-- A permutation of observed labels, extended by the identity on unseen labels. -/
structure LocalPermutation (k : Nat) extends Permutation Nat where
  fixes : ∀ v, k ≤ v → forward v = v

theorem LocalPermutation.backward_fixes {k : Nat} (p : LocalPermutation k)
    (v : Nat) (hv : k ≤ v) : p.backward v = v := by
  have hi := p.left_inverse v
  rwa [p.fixes v hv] at hi

def LocalPermutation.finite {k n : Nat} (p : LocalPermutation k) (hkn : k ≤ n) :
    FinitePermutation n where
  toPermutation := p.toPermutation
  forward_lt v hv := by
    apply Nat.lt_of_not_ge
    intro h
    have hfix := p.backward_fixes (p.forward v) (by omega)
    rw [p.left_inverse] at hfix
    omega
  backward_lt v hv := by
    apply Nat.lt_of_not_ge
    intro h
    have hfix := p.fixes (p.backward v) (by omega)
    rw [p.right_inverse] at hfix
    omega

/-- An adjacency representation of a sorted undirected edge list. -/
def graph (es : List Offline.Edge) : Graph Nat :=
  fun u v => decide ((min u v,max u v) ∈ es)

/-- A local permutation together with its action on adjacency. -/
structure CanonicalResult (k : Nat) (g : Graph Nat) where
  permutation : LocalPermutation k
  canonical : Graph Nat
  correct : canonical = renameGraph permutation.toPermutation g

/-- Reading a graph back into a sorted edge list has a fixed deterministic order. -/
def edges (k : Nat) (g : Graph Nat) : List Offline.Edge :=
  (Transitions.freshPairs k).filter fun e => g e.1 e.2

theorem edges_nodup (k : Nat) (g : Graph Nat) : (edges k g).Nodup :=
  (Transitions.freshPairs_nodup k).filter _

theorem mem_edges (k : Nat) (g : Graph Nat) (e : Offline.Edge) :
    e ∈ edges k g ↔ e.1 < e.2 ∧ e.2 < k ∧ g e.1 e.2 = true := by
  cases e with | mk u v =>
  simp only [edges, List.mem_filter, Transitions.mem_freshPairs]
  exact and_assoc

theorem inverse_edge_mem (p : Permutation Nat) (es : List Offline.Edge) (e : Offline.Edge)
    (hs : ∀ a ∈ es, a.1 ≤ a.2) (he : e.1 ≤ e.2) :
    e ∈ history p.forward es ↔ edge p.backward e ∈ es := by
  have h := edge_mem_history p es (edge p.backward e) hs (edge_sorted _ _)
  have hback : edge p.forward (edge p.backward e) = e :=
    edge_inverse ⟨p.backward,p.forward,p.right_inverse,p.left_inverse⟩ e he
  rwa [hback] at h

/-- The edge list read from the canonical adjacency is a permutation of the
explicitly relabeled source list; forgetting edge order therefore loses no state. -/
theorem canonical_edges_perm {k : Nat} (es : List Offline.Edge)
    (r : CanonicalResult k (graph es)) (hn : es.Nodup)
    (hs : ∀ a ∈ es, a.1 < a.2) (hb : ∀ a ∈ es, a.1 < k ∧ a.2 < k) :
    (history r.permutation.forward es).Perm (edges k r.canonical) := by
  have hsn : ∀ a ∈ es, a.1 ≤ a.2 := fun a ha => Nat.le_of_lt (hs a ha)
  apply (List.perm_ext_iff_of_nodup
    (history_nodup r.permutation.toPermutation es hn hsn) (edges_nodup k _)).mpr
  intro e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    have hab := hb a ha
    have ha1 := (r.permutation.finite (Nat.le_refl k)).forward_lt a.1 hab.1
    have ha2 := (r.permutation.finite (Nat.le_refl k)).forward_lt a.2 hab.2
    change r.permutation.forward a.1 < k at ha1
    change r.permutation.forward a.2 < k at ha2
    have hne : r.permutation.forward a.1 ≠ r.permutation.forward a.2 := by
      intro heq
      have := r.permutation.toPermutation.injective heq
      have := hs a ha
      omega
    apply (mem_edges k _ _).mpr
    refine ⟨by simp only [edge]; omega, by simp only [edge]; omega, ?_⟩
    have hi := edge_inverse r.permutation.toPermutation a (hsn a ha)
    change (min (r.permutation.backward (edge r.permutation.forward a).1)
      (r.permutation.backward (edge r.permutation.forward a).2),
      max (r.permutation.backward (edge r.permutation.forward a).1)
      (r.permutation.backward (edge r.permutation.forward a).2)) = a at hi
    rw [r.correct]
    simpa only [renameGraph, graph, hi, decide_eq_true_eq] using ha
  · intro he
    obtain ⟨hes, _, hgraph⟩ := (mem_edges k _ e).mp he
    rw [r.correct] at hgraph
    have hmem : edge r.permutation.backward e ∈ es := by
      simpa only [renameGraph, graph, edge, decide_eq_true_eq] using hgraph
    exact (inverse_edge_mem r.permutation.toPermutation es e hsn (Nat.le_of_lt hes)).mpr hmem

theorem expand_map {n k : Nat} (p : LocalPermutation k) (available : List Nat) :
    Implementation.expand n k (available.map p.forward) =
      (Implementation.expand n k available).map p.forward := by
  simp only [Implementation.expand, List.map_append]
  congr 1
  symm
  calc
    _ = (List.range' k (n-k)).map id := List.map_congr_left (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hv
      exact p.fixes _ (by omega))
    _ = _ := List.map_id _

/-- Canonicalizing the observed adjacency and relabeling its available vertices
preserves the actual reference Bellman value, including implicit unseen vertices. -/
theorem value_canonical {n k : Nat} (original es : List Offline.Edge)
    (available : List Nat) (r : CanonicalResult k (graph es)) (hkn : k ≤ n) (fuel : Nat)
    (hn : original.Nodup) (ho : ∀ a ∈ original, a.1 < a.2)
    (hb : ∀ a ∈ original, a.1 < n ∧ a.2 < n)
    (hesn : es.Nodup) (hes : ∀ a ∈ es, a.1 < a.2)
    (heb : ∀ a ∈ es, a.1 < k ∧ a.2 < k) :
    value (referenceModel n original) fuel
      ⟨edges k r.canonical, Implementation.expand n k (available.map r.permutation.forward)⟩ =
    value (referenceModel n original) fuel ⟨es,Implementation.expand n k available⟩ := by
  rw [expand_map]
  have hp := canonical_edges_perm es r hesn hes heb
  have hh := value_history_perm n original _ _
    ((Implementation.expand n k available).map r.permutation.forward) hp fuel
  rw [← hh]
  exact value_map (r.permutation.finite hkn) original
    ⟨es,Implementation.expand n k available⟩ fuel hn ho hb hesn
    (fun a ha => Nat.le_of_lt (hes a ha))

end OnlineMatching.CanonicalState
