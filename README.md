# Upper bounds for online matching with random edge arrivals

Companion code for the upper bounds in *Improved Bounds for Online Matching with Random Edge Arrivals*. For a nonempty graph $G$, the edges arrive in a uniformly random order and each edge must be accepted or rejected irrevocably when it arrives. The ratio of $G$ is the best expected matching size of an online algorithm divided by the maximum matching size $\mathrm{OPT}(G)$, when the algorithm knows $G$ up to isomorphism and only the vertex labels are hidden.

| Graph | $n$ | $m$ | Ratio |
|---|---:|---:|---|
| $G_{10}$ ([general](graphs/general/10.in)) | 10 | 19 | $2941136911678289/4223788208640000 < 0.696327$ |
| $B_{2,3,3}$ ([bipartite](graphs/bipartite/16.in)) | 16 | 29 | $3970969041694879055111207/5638303485447723417600000 < 0.704285$ |

Smaller worst-case graphs are listed in [graphs/general](graphs/general/README.md) and [graphs/bipartite](graphs/bipartite/README.md).

## The recurrence

Let $H$ contain all arrived edges on the $n$ labels, including rejected edges, and let $U$ be the unmatched labels. Write $C(H)$ for the number of vertex bijections consistent with $H$. These bijections remain equally likely, so a possible next edge $e$ has probability

$$
p(e\mid H)=\frac{C(H+e)}{(m-|E(H)|)\,C(H)}.
$$

Let $V(H,U)$ be the maximum expected number of additional matched edges. Then

$$
V(H,U)=\sum_{\substack{e\notin E(H)\\ C(H+e)>0}} p(e\mid H)
\begin{cases}
\max\{V(H+e,U),\;1+V(H+e,U\setminus e)\}, & e\subseteq U,\\
V(H+e,U), & e\not\subseteq U,
\end{cases}
$$

with $V(H,U)=0$ when $|E(H)|=m$. The ratio is $V(\varnothing,[n])/\mathrm{OPT}(G)$.

## Contents

| Path | Purpose |
|---|---|
| [`opt.py`](opt.py) | Reference implementation of the recurrence in exact rational arithmetic, with states identified up to relabeling by nauty. |
| [`cpp/`](cpp/README.md) | Multithreaded C++ implementation of the same recurrence in division-free integer form, for larger graphs. |
| [`lean/`](lean/README.md) | Lean 4 proof that the recurrence bounds every deterministic or randomized online strategy, that the memoized and integer solvers compute it, and an executable verified solver. |
| [`greedy_filter.cpp`](greedy_filter.cpp) | Greedy ratio by a subset recurrence, used to screen graphs. |
| [`enumerate_graphs.py`](enumerate_graphs.py) | Exhaustive search for the worst graph on at most $n$ vertices (general or bipartite). |
| [`graphs/`](graphs) | Input graphs, and the LaTeX source of their drawing (`illustration/`, rendered by `draw.py`). |

## Setup

```bash
sudo apt install nauty python3-pynauty
g++ -O3 -std=c++17 greedy_filter.cpp -o greedy_filter
```

The C++ solver additionally needs Boost and nauty built with thread-local storage; see [cpp/README.md](cpp/README.md). The Lean development needs only the toolchain in [lean/lean-toolchain](lean/lean-toolchain).

## Usage

Evaluate one graph (input: `n m`, then `m` zero-based edges):

```bash
python3 opt.py < graphs/general/10.in
(cd cpp && make && ./solver 8 < ../graphs/general/10.in)
(cd lean && lake build && .lake/build/bin/opt < ../graphs/general/4.in)
```

> [!WARNING]
> Evaluating `graphs/bipartite/16.in` ($B_{2,3,3}$) with the C++ solver is slow. In our experiments, it takes about 14 minutes with 128 threads and requires around 63 GiB of memory.

Search all nonisomorphic nonempty graphs on at most $n$ vertices (pass `-b` for bipartite graphs) for a ratio below a threshold:

```bash
python3 enumerate_graphs.py [-b] <n> [<workers>=1] [<threshold>=1]
```

It prints the smallest ratio strictly below the threshold and a graph attaining it, or `No solution`. Graphs from `nauty-geng` are first screened by `greedy_filter` (with floating-point tolerance $10^{-6}$) before exact evaluation by `opt.py`.
