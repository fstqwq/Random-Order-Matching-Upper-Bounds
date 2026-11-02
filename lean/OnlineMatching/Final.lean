import OnlineMatching.Invariance.Memo

/-!
# Lean solver

`RefinedOrder.order` relabels the observed graph by color refinement with
branching and twin pruning. Correctness does not depend on whether it produces
a complete canonical form for graph isomorphism. Every vertex permutation gives a valid oracle
(`PermutationOrder.oracle`), so correctness follows from the invariance layer.
`Final.opt` is the function run by the executable.
-/

/-! ## Oracles from vertex orders -/

namespace OnlineMatching.PermutationOrder

/-- The output contract: an arbitrary ordering of the observed vertices. -/
def Valid (k : Nat) (order : List Nat) : Prop := order.Perm (List.range k)

def backward (order : List Nat) (v : Nat) : Nat := order[v]?.getD v

def forward (order : List Nat) (v : Nat) : Nat :=
  if v < order.length then order.idxOf v else v

theorem length_eq (h : Valid k order) : order.length = k := by
  simpa using h.length_eq

theorem mem_iff (h : Valid k order) : v ∈ order ↔ v < k := by
  simpa using h.mem_iff

theorem backward_forward (h : Valid k order) (v : Nat) :
    backward order (forward order v) = v := by
  by_cases hv : v < k
  · have hi := List.idxOf_lt_length_of_mem ((mem_iff h).mpr hv)
    simp [forward, backward, length_eq h, hv, List.getElem?_eq_getElem hi]
  · simp [forward, backward, length_eq h, hv]

theorem forward_backward (h : Valid k order) (v : Nat) :
    forward order (backward order v) = v := by
  by_cases hv : v < order.length
  · have hm : order[v] ∈ order := List.getElem_mem hv
    have hb := (mem_iff h).mp hm
    have hi := List.idxOf_lt_length_of_mem hm
    have hn : order.Nodup := h.nodup_iff.mpr List.nodup_range
    have he : order.idxOf order[v] = v := hn.getElem_inj.mp (List.getElem_idxOf hi)
    simp [backward, List.getElem?_eq_getElem hv, forward, length_eq h, hb, he]
  · simp [backward, forward, hv]

def permutation (h : Valid k order) : CanonicalState.LocalPermutation k where
  forward := forward order
  backward := backward order
  left_inverse := backward_forward h
  right_inverse := forward_backward h
  fixes v hv := by simp [forward, length_eq h, show ¬ v < k by omega]

/-- Any returned permutation supplies a valid solver oracle. -/
def oracle (orders : (k : Nat) → Graph Nat → List Nat)
    (valid : ∀ k g, Valid k (orders k g)) : Solver.Oracle := fun k g => {
  permutation := permutation (valid k g)
  canonical := renameGraph (permutation (valid k g)).toPermutation g
  correct := rfl
}

end OnlineMatching.PermutationOrder

/-! ## Color refinement -/

namespace OnlineMatching.RefinedOrder

abbrev Order (k : Nat) := { xs : List Nat // xs.Perm (List.range k) }

def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a == b then lexLE as bs else a < b

def adjacency (rows : Array Nat) (u v : Nat) : Bool :=
  (rows[u]?.getD 0).testBit v

def signature (k : Nat) (rows colors : Array Nat) (v : Nat) : List Nat :=
  colors[v]?.getD 0 :: (List.range k).map (fun c =>
    ((List.range k).filter (fun u => colors[u]?.getD 0 == c && adjacency rows v u)).length)

def refineStep (k : Nat) (rows colors : Array Nat) : Array Nat := Id.run do
  let sigs := ((List.range k).map (signature k rows colors)).toArray
  let classes := (sigs.toList.mergeSort lexLE).eraseDups
  return sigs.map (fun s => classes.idxOf s)

def refine (k : Nat) (rows : Array Nat) : Nat → Array Nat → Array Nat
  | 0, colors => colors
  | fuel+1, colors =>
    let next := refineStep k rows colors
    if next == colors then colors else refine k rows fuel next

def ordered (k : Nat) (colors : Array Nat) : Order k :=
  ⟨Ordering.orderBy (fun _ a b => colors[b]?.getD 0 < colors[a]?.getD 0)
      k (List.range k) [],
    Ordering.orderBy_perm _ k (List.range k) [] (by simp)⟩

def code (rows : Array Nat) (xs : List Nat) : List Nat :=
  xs.map (fun v => xs.foldl (fun acc u => 2*acc + if adjacency rows v u then 1 else 0) 0)

def better (rows : Array Nat) (a b : Order k) : Order k :=
  if lexLE (code rows a.val) (code rows b.val) then a else b

/-- Twin pruning shortens the search; every returned leaf is certified as a
permutation. -/
def twins (k : Nat) (rows : Array Nat) (u v : Nat) : Bool :=
  (List.range k).all (fun w => w == u || w == v || adjacency rows u w == adjacency rows v w)

def representatives (k : Nat) (rows : Array Nat) (cell : List Nat) : List Nat :=
  cell.foldl (fun kept v => if kept.any (twins k rows v) then kept else kept ++ [v]) []

def search (k : Nat) (rows : Array Nat) : Nat → Array Nat → Order k
  | 0, colors => ordered k colors
  | fuel+1, colors =>
    let colors := refine k rows k colors
    let cells := (List.range k).map (fun c => (List.range k).filter (fun v => colors[v]?.getD 0 == c))
    match cells.find? (fun cell => cell.length > 1) with
    | none => ordered k colors
    | some cell =>
      let choices := representatives k rows cell
      let leaves := choices.map (fun v =>
        let split := ((List.range k).map (fun u => 2*(colors[u]?.getD 0) + if u == v then 0 else 1)).toArray
        search k rows fuel split)
      match leaves with
      | [] => ordered k colors
      | first::rest => rest.foldl (better rows) first

def order (k : Nat) (g : Graph Nat) : Order k :=
  let rows := ((List.range k).map (fun v => (List.range k).foldl
    (fun row u => if g v u then row + 2^u else row) 0)).toArray
  search k rows k (Array.replicate k 0)

def oracle : Solver.Oracle :=
  PermutationOrder.oracle (fun k g => (order k g).val) (fun k g => (order k g).property)

end OnlineMatching.RefinedOrder

/-! ## Final solver -/

namespace OnlineMatching.Final

/-- The function run by the executable: the memoized solver with the
color-refinement relabeling. -/
def opt (n : Nat) (edges : List Offline.Edge) : Rat :=
  Memoized.ratio RefinedOrder.oracle n edges

theorem opt_eq_reference (n : Nat) (edges : List Offline.Edge)
    (hn : edges.Nodup) (hs : ∀ e ∈ edges, e.1 < e.2)
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    opt n edges = ImplementationGraph.referenceRatio n edges := by
  unfold opt
  rw [Memoized.ratio_eq]
  exact Uncached.ratio_reference _ n edges hn hs hb

end OnlineMatching.Final
