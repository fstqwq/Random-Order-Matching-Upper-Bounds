import OnlineMatching.Reference.Model

/-!
# Optimality of the reference recurrence

The online experiment samples a hidden labeling and an edge order.
`Experiment.experiment_ratio_optimal` shows that `referenceRatio` is the best
ratio of a deterministic strategy, and `Randomized.experiment_ratio_optimal`
extends this to randomized strategies.
-/

/-! ## Deterministic strategies -/

namespace OnlineMatching.Experiment
open Transitions

/-- Sample one hidden vertex labeling and one complete order of its edges. -/
def samples (labels : List L) (host : L → List Offline.Edge) : List (L × List Offline.Edge) :=
  outcomes labels (fun l => Counting.completions (host l).length (host l))

def fullSamples (n : Nat) (edges : List Offline.Edge) :=
  samples (ImplementationGraph.hiddenLabels n) (ImplementationGraph.labelledHost edges)

/-- Reward on a fixed complete edge order. A strategy sees only the next edge,
never the hidden labeling or the remaining suffix of the order. -/
def reward : (fuel : Nat) → List Nat → Strategy Offline.Edge fuel → List Offline.Edge → Rat
  | 0, _, _, _ => 0
  | _ + 1, _, _, [] => 0
  | k + 1, free, strategy, e :: rest =>
      if (strategy e).1 && decide (Offline.legal free e) then
        1 + reward k (Offline.remove free e) (strategy e).2 rest
      else reward k free (strategy e).2 rest

def average (xs : List A) (f : A → Rat) : Rat := total xs f / (xs.length : Rat)

def experimentExpectation (n : Nat) (edges : List Offline.Edge)
    (strategy : Strategy Offline.Edge edges.length) : Rat :=
  average (fullSamples n edges) (fun outcome => reward edges.length (List.range n) strategy outcome.2)

theorem total_indicator_weight [DecidableEq E] (catalog : List E) (e : E) (c : Rat) :
    total catalog (fun x => if x == e then c else 0) = (catalog.count e : Rat) * c := by
  have h : total catalog (fun x => if x == e then c else 0) =
      total catalog (fun x => (if x == e then 1 else 0) * c) := by
    apply total_congr
    intro x _
    cases x == e <;> simp [Rat.zero_mul, Rat.one_mul]
  rw [h, total_mul, total_indicator]

/-- Exact law of total sum on a finite sample space, grouping by a public observation. -/
theorem total_by_observation [DecidableEq E] (xs : List A) (observe : A → E)
    (catalog : List E) (hn : catalog.Nodup)
    (hc : ∀ x ∈ xs, observe x ∈ catalog) (f : A → Rat) :
    total xs f = total catalog (fun e => total (xs.filter (fun x => observe x == e)) f) := by
  induction xs with
  | nil => simp [total, total_const]
  | cons x xs ih =>
    have h : total catalog (fun e => total ((x :: xs).filter (fun y => observe y == e)) f) =
        total catalog (fun e => total (xs.filter (fun y => observe y == e)) f +
          if e == observe x then f x else 0) := by
      apply total_congr
      intro e _
      by_cases he : observe x = e
      · simp [he, total, Rat.add_comm]
      · have he' : e ≠ observe x := Ne.symm he
        simp [he, he', Rat.add_zero]
    rw [h, Transitions.total_add, total_indicator_weight, hn.count, ite_eq_left (hc x (by simp))]
    rw [← ih (fun y hy => hc y (by simp [hy]))]
    simp [total, Rat.one_mul, Rat.add_comm]

/-- The finite conditional expectation identity. Each conditional average is weighted
by its actual fibre frequency; neither conditional expectations nor weights are assumed. -/
theorem average_by_observation [DecidableEq E] (xs : List A) (observe : A → E)
    (catalog : List E) (hn : catalog.Nodup)
    (hc : ∀ x ∈ xs, observe x ∈ catalog) (f : A → Rat) :
    average xs f = total catalog (fun e =>
      probability xs (fun x => observe x == e) *
      average (xs.filter (fun x => observe x == e)) f) := by
  unfold average
  rw [total_by_observation xs observe catalog hn hc f]
  simp only [Rat.div_def]
  rw [← total_mul]
  apply total_congr
  intro e _
  let fiber := xs.filter (fun x => observe x == e)
  change total fiber f * (xs.length : Rat)⁻¹ =
      ((fiber.length : Rat) * (xs.length : Rat)⁻¹) *
        (total fiber f * (fiber.length : Rat)⁻¹)
  by_cases hz : fiber = []
  · simp [hz, total, Rat.zero_mul, Rat.mul_zero]
  · have hlen : (fiber.length : Rat) ≠ 0 := by
      simpa using Nat.ne_of_gt (List.length_pos_iff.mpr hz)
    have hi := Rat.mul_inv_cancel (fiber.length : Rat) hlen
    grind

/-- The conditional continuation after revealing an edge consists of the tails
of exactly those complete edge orders whose first edge is that edge. -/
def tails (orders : List (List Offline.Edge)) (edge : Offline.Edge) : List (List Offline.Edge) :=
  (orders.filter (fun order => order.headD (0,0) == edge)).map List.tail

theorem average_map (xs : List A) (g : A → B) (f : B → Rat) :
    average (xs.map g) f = average xs (fun x => f (g x)) := by
  simp [average, total_map]

theorem average_add_constant (xs : List A) (f : A → Rat) (c : Rat) (hx : xs ≠ []) :
    average xs (fun x => c + f x) = c + average xs f := by
  unfold average
  rw [Transitions.total_add, Transitions.total_const]
  have hn : (xs.length : Rat) ≠ 0 := by
    simpa using Nat.ne_of_gt (List.length_pos_iff.mpr hx)
  have hi := Rat.mul_inv_cancel (xs.length : Rat) hn
  simp only [Rat.div_def]
  grind

/-- Conditioning complete trajectories on their first edge gives precisely the
one-step reward plus the conditional average of the remaining suffix. -/
theorem reward_conditional (orders : List (List Offline.Edge)) (edge : Offline.Edge)
    (fuel : Nat) (free : List Nat) (strategy : Strategy Offline.Edge (fuel+1))
    (hsize : ∀ order ∈ orders, order ≠ [])
    (hoccurs : edge ∈ orders.map (fun order => order.headD (0,0))) :
    average (orders.filter (fun order => order.headD (0,0) == edge))
      (reward (fuel+1) free strategy) =
      if (strategy edge).1 && decide (Offline.legal free edge) then
        1 + average (tails orders edge) (reward fuel (Offline.remove free edge) (strategy edge).2)
      else average (tails orders edge) (reward fuel free (strategy edge).2) := by
  let fiber := orders.filter (fun order => order.headD (0,0) == edge)
  have hn : fiber ≠ [] := by
    obtain ⟨order, ho, he⟩ := List.mem_map.mp hoccurs
    have hf : order ∈ fiber := List.mem_filter.mpr ⟨ho, by simpa using he⟩
    intro hnil
    rw [hnil] at hf
    simp at hf
  have ht : total fiber (reward (fuel+1) free strategy) =
      total fiber (fun order =>
        if (strategy edge).1 && decide (Offline.legal free edge) then
          1 + reward fuel (Offline.remove free edge) (strategy edge).2 order.tail
        else reward fuel free (strategy edge).2 order.tail) := by
    apply total_congr
    intro order ho
    obtain ⟨hm, he⟩ := List.mem_filter.mp ho
    cases order with
    | nil => exact False.elim (hsize [] hm rfl)
    | cons e rest =>
      have heq : e = edge := by simpa using he
      subst e
      rfl
  change total fiber (reward (fuel+1) free strategy) / (fiber.length : Rat) = _
  rw [ht]
  cases ha : (strategy edge).1 && decide (Offline.legal free edge)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (average_map fiber List.tail (reward fuel free (strategy edge).2)).symm
  · simp only [↓reduceIte]
    change average fiber (fun order => 1 + reward fuel (Offline.remove free edge) (strategy edge).2 order.tail) = _
    rw [average_add_constant _ _ _ hn]
    congr 1
    exact (average_map fiber List.tail (reward fuel (Offline.remove free edge) (strategy edge).2)).symm

/-- Exact Bellman decomposition of the actual average reward over complete edge
orders. The probability weights are derived from the finite sample space. -/
theorem reward_average_recursion (orders : List (List Offline.Edge))
    (fuel : Nat) (free : List Nat) (strategy : Strategy Offline.Edge (fuel+1))
    (hsize : ∀ order ∈ orders, order ≠ []) :
    average orders (reward (fuel+1) free strategy) =
      total ((orders.map (fun order => order.headD (0,0))).eraseDups) (fun edge =>
        probability orders (fun order => order.headD (0,0) == edge) *
        if (strategy edge).1 && decide (Offline.legal free edge) then
          1 + average (tails orders edge) (reward fuel (Offline.remove free edge) (strategy edge).2)
        else average (tails orders edge) (reward fuel free (strategy edge).2)) := by
  rw [average_by_observation orders (fun order => order.headD (0,0))
    ((orders.map (fun order => order.headD (0,0))).eraseDups)
    (ImplementationGraph.dedup_nodup _) (by
      intro order ho
      simp only [List.mem_eraseDups]
      exact List.mem_map.mpr ⟨order, ho, rfl⟩)]
  apply total_congr
  intro e he
  rw [reward_conditional orders e fuel free strategy hsize (List.mem_eraseDups.mp he)]

private theorem flatMap_select [DecidableEq E] (xs : List E) (f : E → List A) (e : E)
    (hn : xs.Nodup) :
    (xs.flatMap (fun x => if x = e then f x else [])) = if e ∈ xs then f e else [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    by_cases he : x = e
    · subst x
      simp [List.flatMap_cons, ih htail, hnot]
    · have he' : e ≠ x := Ne.symm he
      simp [List.flatMap_cons, ih htail, he, he']

/-- The conditional suffix list from uniform complete permutations is exactly
the complete permutation list of the remaining edges. -/
theorem tails_completions (free : List Offline.Edge) (r : Nat) (edge : Offline.Edge)
    (hn : free.Nodup) :
    tails (Counting.completions (r+1) free) edge =
      if edge ∈ free then Counting.completions r (free.erase edge) else [] := by
  simp only [tails, Counting.completions, List.filter_flatMap, List.map_flatMap,
    List.filter_map, List.map_map]
  have heq : (fun a => List.map (List.tail ∘ (a :: ·))
      (List.filter ((fun order => order.headD (0,0) == edge) ∘ (a :: ·))
        (Counting.completions r (free.erase a)))) =
      (fun a => if a = edge then Counting.completions r (free.erase a) else []) := by
    funext a
    by_cases ha : a = edge
    · simp [ha, Function.comp_def]
    · simp [ha, Function.comp_def]
  rw [heq]
  exact flatMap_select free (fun a => Counting.completions r (free.erase a)) edge hn

theorem erase_eq_filter [DecidableEq E] (xs : List E) (e : E) (hn : xs.Nodup) :
    xs.erase e = xs.filter (fun x => decide (x ≠ e)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    by_cases he : x = e
    · subst x
      rw [List.erase_cons_head]
      simp only [ne_eq, not_true_eq_false, decide_false, List.filter_cons, Bool.false_eq_true, ↓reduceIte]
      symm
      apply List.filter_eq_self.mpr
      intro x hx
      exact decide_eq_true (by intro he; subst x; exact hnot hx)
    · simp [he, ih htail]

theorem remaining_erase (host observed : List Offline.Edge) (edge : Offline.Edge)
    (hn : host.Nodup) :
    (remainingEdges host observed).erase edge = remainingEdges host (edge :: observed) := by
  have hrem : (remainingEdges host observed).Nodup := hn.filter _
  rw [erase_eq_filter _ _ hrem]
  simp only [remainingEdges, List.filter_filter]
  congr 1
  funext e
  simp [List.mem_cons]

theorem tails_append (xs ys : List (List Offline.Edge)) (e : Offline.Edge) :
    tails (xs ++ ys) e = tails xs e ++ tails ys e := by
  simp [tails, List.filter_append]

/-- Uniform remaining orders after conditioning on the observed history. -/
def residualOrders (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) : List (List Offline.Edge) :=
  (compatibleLabels labels host observed).flatMap fun l =>
    let remaining := remainingEdges (host l) observed
    Counting.completions remaining.length remaining

theorem residualOrders_nil (host : L → List Offline.Edge) (observed : List Offline.Edge) :
    residualOrders [] host observed = [] := rfl

theorem residualOrders_cons (label : L) (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) :
    residualOrders (label :: labels) host observed =
      (if compatible observed (host label) then
        Counting.completions (remainingEdges (host label) observed).length
          (remainingEdges (host label) observed)
      else []) ++ residualOrders labels host observed := by
  unfold residualOrders compatibleLabels
  cases h : compatible observed (host label) <;> simp [h]

/-- Conditioning the hidden-label mixture on its first arriving edge updates
the compatible labels and residual edge permutations exactly as the model does. -/
theorem residualOrders_tails (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) (edge : Offline.Edge) (m r : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (hr : m - observed.length = r+1) (hf : edge ∉ observed) :
    tails (residualOrders labels host observed) edge =
      residualOrders labels host (edge :: observed) := by
  induction labels with
  | nil => simp [residualOrders_nil, tails]
  | cons l labels ih =>
    rw [residualOrders_cons, tails_append, residualOrders_cons,
      ih (fun a ha => hh a (by simp [ha])) (fun a ha => hm a (by simp [ha]))]
    congr 1
    by_cases hc : compatible observed (host l) = true
    · have hlen : (remainingEdges (host l) observed).length = r+1 := by
        rw [remainingEdges, remaining_length _ _ (hh l (by simp)) ho
          ((compatible_iff _ _).mp hc), hm l (by simp), hr]
      simp only [hc, ↓reduceIte, hlen]
      have hnrem : (remainingEdges (host l) observed).Nodup := (hh l (by simp)).filter _
      rw [tails_completions _ _ edge hnrem]
      have hmem : edge ∈ remainingEdges (host l) observed ↔ edge ∈ host l := by
        simp [remainingEdges, List.mem_filter, hf]
      simp only [hmem]
      have hcomp : compatible (edge :: observed) (host l) = decide (edge ∈ host l) := by
        change (decide (edge ∈ host l) && compatible observed (host l)) = _
        simp [hc]
      rw [hcomp]
      simp only [decide_eq_true_eq]
      split
      · rename_i he
        have hrem := remaining_erase (host l) observed edge (hh l (by simp))
        have he' : edge ∈ remainingEdges (host l) observed := hmem.mpr he
        have hchildlen : (remainingEdges (host l) (edge :: observed)).length = r := by
          rw [← hrem, List.length_erase_of_mem he', hlen]
          omega
        rw [hchildlen, hrem]
      · rfl
    · have hchild : compatible (edge :: observed) (host l) = false := by
        simp [compatible] at hc ⊢
        simp [hc]
      simp [hc, hchild, tails]

theorem residualOrders_length (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) (m : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup) :
    (residualOrders labels host observed).length =
      (compatibleLabels labels host observed).length * Counting.factorial (m-observed.length) := by
  unfold residualOrders
  have hc : ∀ l ∈ compatibleLabels labels host observed,
      (Counting.completions (remainingEdges (host l) observed).length
        (remainingEdges (host l) observed)).length = Counting.factorial (m-observed.length) := by
    intro l hl
    obtain ⟨hl, hcomp⟩ := List.mem_filter.mp hl
    rw [Counting.completions_length _ _ rfl]
    congr 1
    exact compatible_remaining_length labels host observed m hh hm ho l (List.mem_filter.mpr ⟨hl,hcomp⟩)
  generalize compatibleLabels labels host observed = ls at *
  induction ls with
  | nil => simp
  | cons l ls ih =>
    rw [List.flatMap_cons, List.length_append, hc l (by simp),
      ih (fun a ha => hc a (by simp [ha]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem factorial_positive (r : Nat) : 0 < Counting.factorial r := by
  induction r with
  | zero => decide
  | succ r ih => exact Nat.mul_pos (Nat.succ_pos _) ih

theorem residualOrders_order_length (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) (m : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (order : List Offline.Edge) (horder : order ∈ residualOrders labels host observed) :
    order.length = m - observed.length := by
  obtain ⟨l, hl, hmemb⟩ := List.mem_flatMap.mp horder
  have hp := (Counting.completions_spec _ _ _ rfl).mp hmemb
  rw [hp.length_eq]
  exact compatible_remaining_length labels host observed m hh hm ho l hl

theorem residualOrders_first_probability (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) (edge : Offline.Edge) (m r : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (hr : m-observed.length = r+1) (hf : edge ∉ observed) :
    probability (residualOrders labels host observed) (fun order => order.headD (0,0) == edge) =
      probability (graphOutcomes labels host observed) (fun x => x.2 == edge) := by
  have hnum : ((residualOrders labels host observed).filter
      (fun order => order.headD (0,0) == edge)).length =
      (compatibleLabels labels host (edge::observed)).length * Counting.factorial r := by
    have heq := congrArg List.length (residualOrders_tails labels host observed edge m r hh hm ho hr hf)
    simp only [tails, List.length_map] at heq
    rw [heq, residualOrders_length labels host (edge::observed) m hh hm (List.nodup_cons.mpr ⟨hf,ho⟩)]
    congr 2
    simp only [List.length_cons]
    omega
  rw [graph_next_edge_probability labels host observed m edge hh hm ho hf]
  unfold probability
  rw [hnum, residualOrders_length labels host observed m hh hm ho, hr]
  have hfac : (Counting.factorial r : Rat) ≠ 0 := by
    simpa using Nat.ne_of_gt (factorial_positive r)
  have hinv := Rat.mul_inv_cancel (Counting.factorial r : Rat) hfac
  simp only [Counting.factorial, Rat.natCast_mul, Rat.natCast_add, Rat.div_def]
  simp only [Rat.inv_mul_rev]
  grind

theorem first_edges_iff (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) (free : List Nat) (edge : Offline.Edge) (m r : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (hr : m-observed.length = r+1) :
    edge ∈ (residualOrders labels host observed).map (fun order => order.headD (0,0)) ↔
      edge ∈ ImplementationGraph.possible labels host ⟨observed,free⟩ := by
  simp only [ImplementationGraph.possible, List.mem_eraseDups]
  constructor
  · intro he
    obtain ⟨order,ho',he⟩ := List.mem_map.mp he
    have hlen := residualOrders_order_length labels host observed m hh hm ho order ho'
    obtain ⟨l,hl,hp⟩ := List.mem_flatMap.mp ho'
    have hp := (Counting.completions_spec _ _ _ rfl).mp hp
    have heorder : edge ∈ order := by
      cases order with
      | nil => simp [hr] at hlen
      | cons a rest => simpa only [List.headD_cons] using he ▸ List.mem_cons_self
    have hem := hp.mem_iff.mp heorder
    apply List.mem_map.mpr
    refine ⟨(l,edge),?_,rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨l,hl,List.mem_map.mpr ⟨edge,hem,rfl⟩⟩
  · intro he
    obtain ⟨⟨l,e⟩,hp,he⟩ := List.mem_map.mp he
    change e = edge at he
    subst e
    obtain ⟨l',hl',hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hp
    cases heq
    let rem := remainingEdges (host l) observed
    apply List.mem_map.mpr
    refine ⟨edge :: rem.erase edge, ?_, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨l,hl',?_⟩
    apply (Counting.completions_spec _ _ _ rfl).mpr
    exact (List.perm_cons_erase he).symm

theorem first_edges_perm (labels : List L) (host : L → List Offline.Edge)
    (observed : List Offline.Edge) (free : List Nat) (m r : Nat)
    (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m) (ho : observed.Nodup)
    (hr : m-observed.length = r+1) :
    ((residualOrders labels host observed).map (fun order => order.headD (0,0))).eraseDups.Perm
      (ImplementationGraph.possible labels host ⟨observed,free⟩) := by
  apply List.perm_iff_count.mpr
  intro e
  have hn : (ImplementationGraph.possible labels host ⟨observed,free⟩).Nodup :=
    ImplementationGraph.dedup_nodup _
  rw [(ImplementationGraph.dedup_nodup _).count, hn.count]
  simp only [List.mem_eraseDups]
  congr 1
  exact propext (first_edges_iff labels host observed free e m r hh hm ho hr)

/-- The reference model is the conditional expectation of the original uniform
hidden-labeling and full edge-order experiment, for every deterministic strategy. -/
theorem conditional_average_eq_eval (labels : List L) (host : L → List Offline.Edge)
    (m fuel : Nat) (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m)
    (observed : List Offline.Edge) (free : List Nat)
    (ho : observed.Nodup) (hr : m-observed.length = fuel)
    (strategy : Strategy Offline.Edge fuel) :
    average (residualOrders labels host observed) (reward fuel free strategy) =
      eval (ImplementationGraph.model labels host m) fuel ⟨observed,free⟩ strategy := by
  induction fuel generalizing observed free with
  | zero => simp [reward, average, total_const, Rat.mul_zero, Rat.div_def, Rat.zero_mul, eval]
  | succ fuel ih =>
    have hsize : ∀ order ∈ residualOrders labels host observed, order ≠ [] := by
      intro order horder hnil
      have hlen := residualOrders_order_length labels host observed m hh hm ho order horder
      simp [hnil,hr] at hlen
    rw [reward_average_recursion _ fuel free strategy hsize]
    rw [total_perm (first_edges_perm labels host observed free m fuel hh hm ho hr)]
    have hlt : observed.length < m := by omega
    change _ = total (if observed.length < m then
      ImplementationGraph.possible labels host ⟨observed,free⟩ else []) _
    rw [ite_eq_left hlt]
    apply total_congr
    intro e he
    have hf := (ImplementationGraph.possible_reachable labels host ⟨observed,free⟩ e he).1
    rw [residualOrders_first_probability labels host observed e m fuel hh hm ho hr hf,
      residualOrders_tails labels host observed e m fuel hh hm ho hr hf]
    have hn := List.nodup_cons.mpr ⟨hf,ho⟩
    have hr' : m-(e::observed).length = fuel := by simp only [List.length_cons]; omega
    rw [ih (e::observed) (Offline.remove free e) hn hr' (strategy e).2,
      ih (e::observed) free hn hr' (strategy e).2]
    rfl

theorem residualOrders_initial (labels : List L) (host : L → List Offline.Edge) :
    residualOrders labels host [] = (samples labels host).map Prod.snd := by
  have hlabels : labels.filter (fun _ => true) = labels :=
    List.filter_eq_self.mpr (by simp)
  have hhost (l : L) : (host l).filter (fun _ => true) = host l :=
    List.filter_eq_self.mpr (by simp)
  simp [residualOrders, samples, outcomes, compatibleLabels, compatible, remainingEdges,
    List.map_flatMap, List.map_map, Function.comp_def, hlabels, hhost]

theorem full_average_eq_eval (labels : List L) (host : L → List Offline.Edge)
    (m : Nat) (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m)
    (free : List Nat) (strategy : Strategy Offline.Edge m) :
    average (samples labels host) (fun outcome => reward m free strategy outcome.2) =
      eval (ImplementationGraph.model labels host m) m ⟨[],free⟩ strategy := by
  rw [← average_map (samples labels host) Prod.snd (reward m free strategy),
    ← residualOrders_initial]
  exact conditional_average_eq_eval labels host m m hh hm [] free (by simp) (by simp) strategy

/-- Specialization to the graph's actual vertex permutations and complete edge orders. -/
theorem experiment_eq_reference_eval (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n)
    (strategy : Strategy Offline.Edge edges.length) :
    experimentExpectation n edges strategy =
      eval (ImplementationGraph.referenceModel n edges) edges.length
        (ImplementationGraph.initial n) strategy := by
  apply full_average_eq_eval (ImplementationGraph.hiddenLabels n)
    (ImplementationGraph.labelledHost edges) edges.length
  · intro p hp
    exact ImplementationGraph.labelledHost_nodup n edges p hn hp hs hb
  · intro p _
    simp [ImplementationGraph.labelledHost]

theorem experiment_ratio_optimal (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hne : edges ≠ []) :
    (∀ strategy, experimentExpectation n edges strategy /
      (ImplementationGraph.denominator n edges : Rat) ≤ ImplementationGraph.referenceRatio n edges) ∧
    (∃ strategy, experimentExpectation n edges strategy /
      (ImplementationGraph.denominator n edges : Rat) = ImplementationGraph.referenceRatio n edges) := by
  have he := List.head_mem hne
  obtain ⟨hu,hv⟩ := hb (edges.head hne) he
  have hdistinct : (edges.head hne).1 ≠ (edges.head hne).2 := Nat.ne_of_lt (hs _ he)
  have hopt := ImplementationGraph.reference_ratio_optimal n edges (edges.head hne) he hu hv hdistinct
  simpa only [ImplementationGraph.strategyRatio,
    ← experiment_eq_reference_eval n edges hn hs hb] using hopt

end OnlineMatching.Experiment

/-! ## Randomized strategies -/

namespace OnlineMatching.Randomized

/-- An action coin and separate future policies after rejection and acceptance. -/
def Strategy (O : Type) : Nat → Type
  | 0 => Unit
  | k+1 => O → Rat × Strategy O k × Strategy O k

def Valid : {k : Nat} → Strategy O k → Prop
  | 0, _ => True
  | _+1, p => ∀ o, 0 ≤ (p o).1 ∧ (p o).1 ≤ 1 ∧
      Valid (p o).2.1 ∧ Valid (p o).2.2

/-- Exact conditional expected reward of a finite behavioral policy. -/
def eval (M : Model S O) : (k : Nat) → S → Strategy O k → Rat
  | 0, _, _ => 0
  | k+1, s, p => total (M.observations s) fun o =>
      M.probability s o *
        (if M.legal s o then
          (p o).1 * (1 + eval M k (M.accept s o) (p o).2.2) +
          (1-(p o).1) * eval M k (M.reject s o) (p o).2.1
        else eval M k (M.reject s o) (p o).2.1)

theorem convex_le (q a b c : Rat) (hq : 0 ≤ q) (h1 : q ≤ 1)
    (ha : a ≤ c) (hb : b ≤ c) : q*a + (1-q)*b ≤ c := by
  have hq' : 0 ≤ 1-q := (Rat.le_iff_sub_nonneg q 1).mp h1
  have hleft := Rat.mul_le_mul_of_nonneg_left ha hq
  have hright := Rat.mul_le_mul_of_nonneg_left hb hq'
  have hsum : q*a + (1-q)*b ≤ q*c + (1-q)*c :=
    Rat.le_trans (Rat.add_le_add_right.mpr hleft) (Rat.add_le_add_left.mpr hright)
  have heq : q*c + (1-q)*c = c := by grind
  rwa [heq] at hsum

theorem eval_le_value (M : Model S O) (fuel : Nat) (s : S)
    (p : Strategy O fuel) (hp : Valid p) : eval M fuel s p ≤ value M fuel s := by
  induction fuel generalizing s with
  | zero => exact Rat.le_refl
  | succ fuel ih =>
    apply total_mono
    intro o ho
    apply Rat.mul_le_mul_of_nonneg_left _ (M.nonnegative s o ho)
    obtain ⟨hq,hq1,hreject,haccept⟩ := hp o
    cases hl : M.legal s o
    · simpa [hl] using ih (M.reject s o) (p o).2.1 hreject
    · simp only [↓reduceIte]
      apply convex_le _ _ _ _ hq hq1
      · exact Rat.le_trans (Rat.add_le_add_left.mpr (ih (M.accept s o) (p o).2.2 haccept))
          (le_max_right _ _)
      · exact Rat.le_trans (ih (M.reject s o) (p o).2.1 hreject) (le_max_left _ _)

/-- Every deterministic policy is a valid behavioral policy with zero/one coins. -/
def deterministic : {k : Nat} → OnlineMatching.Strategy O k → Strategy O k
  | 0, _ => ()
  | _+1, p => fun o => (if (p o).1 then 1 else 0,
      deterministic (p o).2, deterministic (p o).2)

theorem deterministic_valid (fuel : Nat) (p : OnlineMatching.Strategy O fuel) :
    Valid (deterministic p) := by
  induction fuel with
  | zero => trivial
  | succ fuel ih =>
    intro o
    have h := ih (p o).2
    cases he : (p o).1 <;> simp [deterministic,he, h] <;> decide

theorem eval_deterministic (M : Model S O) (fuel : Nat) (s : S)
    (p : OnlineMatching.Strategy O fuel) :
    eval M fuel s (deterministic p) = OnlineMatching.eval M fuel s p := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    apply total_congr
    intro o _
    simp only [deterministic]
    rw [ih,ih]
    cases M.legal s o <;> cases (p o).1 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true] <;> grind

/-- Random action coins cannot improve on Bellman's deterministic optimum, and
that optimum remains attained within this explicitly defined randomized model. -/
theorem value_correct (M : Model S O) (fuel : Nat) (s : S) :
    (∀ p, Valid p → eval M fuel s p ≤ value M fuel s) ∧
    (∃ p, Valid p ∧ eval M fuel s p = value M fuel s) := by
  obtain ⟨_,p,hbest⟩ := OnlineMatching.value_correct M fuel s
  exact ⟨eval_le_value M fuel s, deterministic p, deterministic_valid fuel p,
    (eval_deterministic M fuel s p).trans hbest⟩

open Experiment Transitions

def reward : (fuel : Nat) → List Nat → Strategy Offline.Edge fuel → List Offline.Edge → Rat
  | 0, _, _, _ => 0
  | _+1, _, _, [] => 0
  | fuel+1, free, p, e::rest =>
      if Offline.legal free e then
        (p e).1 * (1 + reward fuel (Offline.remove free e) (p e).2.2 rest) +
        (1-(p e).1) * reward fuel free (p e).2.1 rest
      else reward fuel free (p e).2.1 rest

def experimentExpectation (n : Nat) (edges : List Offline.Edge)
    (p : Strategy Offline.Edge edges.length) : Rat :=
  average (fullSamples n edges) (fun outcome => reward edges.length (List.range n) p outcome.2)

theorem average_add (xs : List A) (f g : A → Rat) :
    average xs (fun x => f x + g x) = average xs f + average xs g := by
  unfold average
  rw [Transitions.total_add]
  simp only [Rat.div_def]
  grind

theorem average_mul (xs : List A) (f : A → Rat) (c : Rat) :
    average xs (fun x => c * f x) = c * average xs f := by
  have heq : total xs (fun x => c*f x) = total xs (fun x => f x*c) :=
    total_congr _ _ _ (fun _ _ => Rat.mul_comm _ _)
  unfold average
  rw [heq,total_mul]
  simp only [Rat.div_def]
  grind

theorem reward_conditional (orders : List (List Offline.Edge)) (edge : Offline.Edge)
    (fuel : Nat) (free : List Nat) (p : Strategy Offline.Edge (fuel+1))
    (hsize : ∀ order ∈ orders, order ≠ [])
    (hoccurs : edge ∈ orders.map (fun order => order.headD (0,0))) :
    average (orders.filter (fun order => order.headD (0,0) == edge))
      (reward (fuel+1) free p) =
      if Offline.legal free edge then
        (p edge).1 * (1 + average (tails orders edge)
          (reward fuel (Offline.remove free edge) (p edge).2.2)) +
        (1-(p edge).1) * average (tails orders edge) (reward fuel free (p edge).2.1)
      else average (tails orders edge) (reward fuel free (p edge).2.1) := by
  let fiber := orders.filter (fun order => order.headD (0,0) == edge)
  have hn : fiber ≠ [] := by
    obtain ⟨order,ho,he⟩ := List.mem_map.mp hoccurs
    have hf : order ∈ fiber := List.mem_filter.mpr ⟨ho, by simpa using he⟩
    intro hnil
    rw [hnil] at hf
    simp at hf
  have ht : total fiber (reward (fuel+1) free p) =
      total fiber (fun order =>
        if Offline.legal free edge then
          (p edge).1 * (1 + reward fuel (Offline.remove free edge) (p edge).2.2 order.tail) +
          (1-(p edge).1) * reward fuel free (p edge).2.1 order.tail
        else reward fuel free (p edge).2.1 order.tail) := by
    apply total_congr
    intro order ho
    obtain ⟨hm,he⟩ := List.mem_filter.mp ho
    cases order with
    | nil => exact False.elim (hsize [] hm rfl)
    | cons e rest =>
      have heq : e = edge := by simpa using he
      subst e
      rfl
  change total fiber (reward (fuel+1) free p) / (fiber.length : Rat) = _
  rw [ht]
  by_cases hlegal : Offline.legal free edge
  · simp only [hlegal, ↓reduceIte]
    change average fiber (fun order =>
      (p edge).1 * (1 + reward fuel (Offline.remove free edge) (p edge).2.2 order.tail) +
      (1-(p edge).1) * reward fuel free (p edge).2.1 order.tail) = _
    rw [average_add,average_mul,average_mul,average_add_constant _ _ _ hn]
    rw [← average_map fiber List.tail (reward fuel (Offline.remove free edge) (p edge).2.2),
      ← average_map fiber List.tail (reward fuel free (p edge).2.1)]
    rfl
  · simp only [hlegal, ↓reduceIte]
    exact (average_map fiber List.tail (reward fuel free (p edge).2.1)).symm

theorem conditional_average_eq_eval (labels : List L) (host : L → List Offline.Edge)
    (m fuel : Nat) (hh : ∀ l ∈ labels, (host l).Nodup)
    (hm : ∀ l ∈ labels, (host l).length = m)
    (observed : List Offline.Edge) (free : List Nat)
    (ho : observed.Nodup) (hr : m-observed.length = fuel)
    (p : Strategy Offline.Edge fuel) :
    average (residualOrders labels host observed) (reward fuel free p) =
      eval (ImplementationGraph.model labels host m) fuel ⟨observed,free⟩ p := by
  induction fuel generalizing observed free with
  | zero => simp [reward,average,total_const,Rat.mul_zero,Rat.div_def,Rat.zero_mul,eval]
  | succ fuel ih =>
    have hsize : ∀ order ∈ residualOrders labels host observed, order ≠ [] := by
      intro order horder hnil
      have hlen := residualOrders_order_length labels host observed m hh hm ho order horder
      simp [hnil,hr] at hlen
    let orders := residualOrders labels host observed
    let catalog := (orders.map (fun order => order.headD (0,0))).eraseDups
    rw [average_by_observation orders (fun order => order.headD (0,0))
      catalog (ImplementationGraph.dedup_nodup _) (by
        intro order ho
        simp only [catalog,List.mem_eraseDups]
        exact List.mem_map.mpr ⟨order,ho,rfl⟩)]
    have hlt : observed.length < m := by omega
    change _ = total (if observed.length < m then
      ImplementationGraph.possible labels host ⟨observed,free⟩ else []) _
    rw [ite_eq_left hlt]
    rw [← total_perm (first_edges_perm labels host observed free m fuel hh hm ho hr)]
    apply total_congr
    intro e he
    have hepossible := (first_edges_iff labels host observed free e m fuel hh hm ho hr).mp
      (List.mem_eraseDups.mp he)
    have hf := (ImplementationGraph.possible_reachable labels host ⟨observed,free⟩ e hepossible).1
    rw [reward_conditional orders e fuel free p hsize (List.mem_eraseDups.mp he),
      residualOrders_first_probability labels host observed e m fuel hh hm ho hr hf,
      residualOrders_tails labels host observed e m fuel hh hm ho hr hf]
    have hn := List.nodup_cons.mpr ⟨hf,ho⟩
    have hr' : m-(e::observed).length = fuel := by simp only [List.length_cons]; omega
    rw [ih (e::observed) (Offline.remove free e) hn hr' (p e).2.2,
      ih (e::observed) free hn hr' (p e).2.1]
    simp only [ImplementationGraph.model,decide_eq_true_eq,ImplementationGraph.nextWeight,
      ImplementationGraph.accept,ImplementationGraph.reject]

theorem experiment_eq_reference_eval (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n)
    (p : Strategy Offline.Edge edges.length) :
    experimentExpectation n edges p =
      eval (ImplementationGraph.referenceModel n edges) edges.length (ImplementationGraph.initial n) p := by
  unfold experimentExpectation fullSamples
  rw [← average_map _ Prod.snd (reward edges.length (List.range n) p), ← residualOrders_initial]
  apply conditional_average_eq_eval (ImplementationGraph.hiddenLabels n)
    (ImplementationGraph.labelledHost edges) edges.length edges.length
  · intro label hlabel
    exact ImplementationGraph.labelledHost_nodup n edges label hn hlabel hs hb
  · intro label _
    simp [ImplementationGraph.labelledHost]
  · simp
  · simp

/-- Finite-horizon policies with rational action coins have the same attained
optimal expectation as the deterministic Bellman recursion. -/
theorem experiment_optimal (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    (∀ p, Valid p → experimentExpectation n edges p ≤
      prunedValue (ImplementationGraph.referenceModel n edges)
        (ImplementationGraph.upper edges.length) edges.length (ImplementationGraph.initial n)) ∧
    (∃ p, Valid p ∧ experimentExpectation n edges p =
      prunedValue (ImplementationGraph.referenceModel n edges)
        (ImplementationGraph.upper edges.length) edges.length (ImplementationGraph.initial n)) := by
  have hprune : prunedValue (ImplementationGraph.referenceModel n edges)
      (ImplementationGraph.upper edges.length) edges.length (ImplementationGraph.initial n) =
      value (ImplementationGraph.referenceModel n edges) edges.length (ImplementationGraph.initial n) :=
    ImplementationGraph.graph_pruning_correct (ImplementationGraph.hiddenLabels n)
      (ImplementationGraph.labelledHost edges) edges.length edges.length (ImplementationGraph.initial n)
  rw [hprune]
  simpa only [experiment_eq_reference_eval n edges hn hs hb] using
    value_correct (ImplementationGraph.referenceModel n edges) edges.length (ImplementationGraph.initial n)

theorem experiment_ratio_optimal (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (hne : edges ≠ []) :
    (∀ p, Valid p → experimentExpectation n edges p /
      (ImplementationGraph.denominator n edges : Rat) ≤ ImplementationGraph.referenceRatio n edges) ∧
    (∃ p, Valid p ∧ experimentExpectation n edges p /
      (ImplementationGraph.denominator n edges : Rat) = ImplementationGraph.referenceRatio n edges) := by
  have he := List.head_mem hne
  obtain ⟨hu,hv⟩ := hb (edges.head hne) he
  have hd : 0 < (ImplementationGraph.denominator n edges : Rat) :=
    Rat.natCast_pos.mpr (ImplementationGraph.denominator_positive n edges (edges.head hne)
      he hu hv (Nat.ne_of_lt (hs _ he)))
  have hi : 0 ≤ (ImplementationGraph.denominator n edges : Rat)⁻¹ :=
    Rat.le_of_lt (Rat.inv_pos.mpr hd)
  obtain ⟨hbound,p,hp,hbest⟩ := experiment_optimal n edges hn hs hb
  constructor
  · intro p hp
    unfold ImplementationGraph.referenceRatio
    simp only [Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right (hbound p hp) hi
  · exact ⟨p,hp,congrArg (fun x => x / (ImplementationGraph.denominator n edges : Rat)) hbest⟩

end OnlineMatching.Randomized
