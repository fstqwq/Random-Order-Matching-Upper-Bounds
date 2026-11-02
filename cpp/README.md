# Exact solver in C++

`solver.cpp` evaluates the same Bellman recurrence as [`../opt.py`](../opt.py)
for larger graphs. It implements the natural-number recurrence
`IntegerSolver.solve`, which is proved equal to the reference ratio in
[`../lean`](../lean). The correspondence with the Lean specification is described below.

## Build

Requirements: Linux, a C++20 compiler with pthreads, Boost (header-only
`cpp_int`), and nauty 2.8 built with thread-local storage (`nautyT.a`). The
parallel-hashmap headers are vendored in `vendor-phmap/` (Apache 2.0, see its
`LICENSE`).

```bash
(cd /path/to/nauty && ./configure --enable-tls && make nautyT.a)
make NAUTY_DIR=/path/to/nauty BOOST_INCLUDE=/path/to/boost/include
```

## Usage

```bash
./solver THREADS < ../graphs/general/10.in
```

> [!WARNING]
> Evaluating `../graphs/bipartite/16.in` ($B_{2,3,3}$) is slow. In our experiments, it takes about 14 minutes with 128 threads and requires around 63 GiB of memory.

`THREADS` is a positive integer. The input is `n m` followed by `m` zero-based
edges of a simple graph with $1 \le n \le 16$ and $m \ge 1$.

The program prints a single line `ratio p/q`, the exact ratio
$V^\star(G)/\mathrm{OPT}(G)$ as a reduced fraction.

## Method

Let $H$ contain all arrived edges on the $n$ labels, including rejected edges,
and let $U \subseteq [n]$ be the unmatched labels. Write $C(H)$ for the number
of vertex bijections consistent with $H$, and $V(H,U)$ for the maximum
expected number of additional matched edges. With $r = m - |E(H)|$ remaining
edges, the solver stores the integer

$$
F(H,U) = r!\,C(H)\,V(H,U).
$$

Multiplying the recurrence by $r!\,C(H)$ cancels its denominators: each next
edge $e \notin E(H)$ with $C(H+e) > 0$ contributes

$$
\max\bigl\{F(H+e,U),\; (r-1)!\,C(H+e) + F(H+e,U \setminus e)\bigr\}
$$

when $e \subseteq U$, and $F(H+e,U)$ otherwise. Since $C(\varnothing) = n!$
and $V^\star(G) = V(\varnothing,[n])$, the ratio is

$$
\frac{V^\star(G)}{\mathrm{OPT}(G)} = \frac{F(\varnothing,[n])}{m!\,n!\,\mathrm{OPT}(G)}.
$$

States are stored up to relabeling. If $E(H)$ touches $k$ labels, these
observed labels are renamed $0,\dots,k-1$ by nauty, and only
$U \cap \{0,\dots,k-1\}$ is stored as a bitmask `available`. The other $n-k$
labels are unseen, so they are always in $U$ and interchangeable; in
particular, $\lvert U\rvert = \lvert\texttt{available}\rvert + n - k$.
Accordingly, the edges from an observed label to the unseen labels are grouped
into one transition of multiplicity $n-k$, and the edges between two unseen
labels into one transition of multiplicity $\binom{n-k}{2}$; an edge between
two observed labels has multiplicity $1$. After each transition the child
graph is relabeled and the mask is transported by the same permutation.

Parallelism: the states reachable in the first few layers are expanded,
stopping once the frontier reaches `2 * THREADS` states. Worker threads solve
these states with a shared answer table. After all workers have joined, the
main thread solves the root and computes any missing states itself.

## Trusted components

* Boost.Multiprecision `cpp_int` performs exact integer arithmetic.
* The phmap `parallel_flat_hash_map` (with `std::shared_mutex`) is a correct
  concurrent map. A successful `if_contains` copies a complete value that was
  inserted by `lazy_emplace_l`, while the map lock is held.
* The C++ compiler, standard library and runtime (`mutex`, `call_once`,
  `shared_ptr`, `thread_local`, the memory model) behave as specified.
* nauty is memory safe and honors its thread-local-storage build contract.
  Its output is **not** trusted to be correct or canonical: the solver checks
  that the returned labeling is a bijection before using it, and checks every
  adjacency bit of the relabeled graph.

## Correspondence with Lean

The Lean theorems below establish the correctness of the integer recurrence
and memoization invariants; the following subsections map the C++ state
representation and operations to the Lean specification.

### What is proved in Lean

* `reference_optimal`, `reference_randomized` (`Theorems.lean`): no
  deterministic strategy, and no randomized strategy with rational action
  probabilities, has an expected matching size divided by $\mathrm{OPT}(G)$
  exceeding `referenceRatio n edges`.
* `IntegerSolver.ratio_reference`: `solve oracle n edges m initial` divided by
  $m!\,n!\,\mathrm{OPT}(G)$ equals `referenceRatio n edges`, for every
  relabeling oracle.
* `IntegerMemo.solve_correct`: the memoized version of the same recurrence
  returns the uncached value from every sound cache and leaves the cache
  sound. `IntegerMemo.warmup_root_correct` and `warmup_root_ratio` extend this
  to an arbitrary list of prewarming calls, possibly repeated or incomplete,
  followed by the root call.
* `IntegerMemo.oracle_independent`, `normalized_reference`: the value of a
  valid state with a positive labeling count does not depend on which legal
  relabeling is used.
* `IntegerSolver.sumNat_perm`: a sum of natural numbers does not depend on the
  order of its terms.

### State

A C++ state is a registered graph node together with a 16-bit mask. It
represents the Lean state `Solver.State` with `seen = node.g.k`, `observed`
the edges $(u,v)$, $u < v$, of the adjacency rows of `node.g`, and
`available` the set bits of the mask. Lists are taken in sorted order; the
value does not depend on the order of `observed` or `available`
(`Symmetry.value_history_perm`, `AvailableOrder.solve_perm`).

The Lean recurrence carries a fuel argument. The C++ code omits it because
the fuel is always $m - t$, where $t$ is the length of `observed`: every
transition adds exactly one edge (`IntegerMemo.child_fuel`,
`IntegerMemo.stateKey_injective`).

### Operations

| C++ | Lean | Correspondence |
|---|---|---|
| `count_fits` | `CountingEndToEnd.count_fits_eq_compatibleCount` | Depth-first search over injective maps of the observed vertices that send observed edges to host edges, with the degree filter, times $(n-k)!$ for the unseen labels. |
| `upper == 0` returns 0 | `Solver.capacity`, `IntegerSolver.solve` | Both equal $\min\{m-\lvert E(H)\rvert,\ \lfloor\lvert U\rvert/2\rfloor\} = \min\{m-t,\ \lfloor(\lvert\texttt{available}\rvert + n - k)/2\rfloor\}$. |
| `enumerate_transitions` | `IntegerSolver.solve` | Edges between two observed vertices that are not yet observed (`remainingEdges (freshPairs k)`), with multiplicity $1$; edges $(u,k)$ with multiplicity $n-k$ when $k < n$; the edge $(k,k+1)$ with multiplicity $\binom{n-k}{2}$ when $k+1 < n$. |
| child with `fits == 0` omitted | `IntegerSolver.term` | Lean includes the term with value 0. |
| `canonical`, then `rename_mask` of `free` and of `free & ~ends` | `normalize`, `reveal`, `remove` | Both branches use the same old-to-new permutation. The permutation is checked to be a bijection and the relabeled graph is checked bit by bit (`CanonicalResult.correct`). |
| `scale + accept`, `max`, `multiplicity * best` | `IntegerSolver.term` | `scale` $= (m-t-1)!\,C(H')$. |
| `solve` loop | `IntegerSolver.solve` | Sums the non-zero terms of `oldOld ++ oldNew ++ newNew`, rotated by a task-dependent offset (`sumNat_perm`). |
| accept evaluated before or after reject | `IntegerSolver.term` | Both branches are evaluated before taking the maximum. |
| shared table `lookup` / `publish` | `IntegerMemo.solve_correct`, `publish_solve` | Only completed values are inserted. A duplicate insertion must equal the stored value, otherwise the run aborts. |
| thread-local `read_cache` | `IntegerMemo.two_level_hit`, `copy_hit` | Entries are copies of values from the shared table. A hit requires full-key equality; the tag is invalidated before copying and set only after the copy succeeds. |
| `frontier`, workers, join, root `solve` | `IntegerMemo.warmup_root_correct`, `warmup_root_ratio` | Workers prewarm the shared table; the root call computes any remaining states. |
| final division | `IntegerSolver.ratio_reference` | $F(\varnothing,[n]) / (m!\,n!\,\mathrm{OPT}(G))$. |

### Representation checks

* $n \le 16$, so `uint16_t` holds every mask, and masks never contain a vertex
  $\ge k$. A permutation stores the image of each vertex in four bits, so
  shifts are at most 60.
* Registry keys contain $k$ and both bytes of every adjacency row. Node
  identifiers are unique, stable and below `INT_MAX`, so the answer key
  `(id << 16) | mask` is injective.
* All metadata of a node (its graph, labeling count and transitions) depends
  only on the graph, so it is shared by all masks. Transitions are built once
  under `call_once` and are immutable afterwards. Nodes remain alive throughout evaluation.
* $\mathrm{OPT}(G)$ is computed by a bitmask recurrence over vertex subsets:
  leave the lowest vertex unmatched, or match it to an available neighbor.

### Relabeling choices

The Lean recurrence takes a fixed oracle function, whereas the C++ program
calls nauty at each transition. Because `oracle_independent` and
`normalized_reference` show that the integer value of every valid state with a
positive labeling count is the same for every legal relabeling, each verified
runtime relabeling yields the same term as any fixed oracle.

### Concurrent execution

Rank each call by the number of remaining edges $m - t$.

1. Every cache, shared or thread-local, is initially empty and therefore
   sound: every entry equals the specification value of its key.
2. A hit in a sound cache returns the specification value.
3. On a miss, every recursive call has smaller rank. By induction, each
   returns its specification value. The current call computes the exact sum of
   maxima, which equals the specification value by the table above, and only
   then publishes it.
4. Publishing or caching a correct value keeps every cache sound.
5. Only completed values are published. On any exception or interrupt, all
   workers stop and the program exits without printing a ratio.
6. After the workers join, the root call runs on a sound shared table and
   returns $F(\varnothing,[n])$ by steps 2 and 3.
