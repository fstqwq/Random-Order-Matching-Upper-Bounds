# Bipartite inputs

The files use the same `n m` edge-list format as `../general/10.in`.

For positive integers $a_1,\dots,a_r$ with $k=\sum_i a_i$, the graph $B_{a_1,\dots,a_r}$ is obtained from $k$ disjoint edges grouped into ordered blocks $M_1,\dots,M_r$ of sizes $a_1,\dots,a_r$, by joining every left endpoint in $M_i$ to every right endpoint in $M_j$ for all $i<j$. Its unique perfect matching is $M_1\cup\dots\cup M_r$.

| $n$ | Input | Graph | $m$ | Ratio |
|---:|---|---|---:|---|
| 4 | [4.in](4.in) | $B_{1,1}$ | 3 | $5/6$ |
| 6 | [6.in](6.in) | $B_{1,1,1}$ | 6 | $7/9$ |
| 8 | [8.in](8.in) | $B_{1,1,1,1}$ | 10 | $343613/453600 < 0.757525$ |
| 10 | [10.in](10.in) | $B_{2,1,2}$ | 13 | $359546399/486486000 < 0.739069$ |
| 12 | [12.in](12.in) | $B_{2,2,2}$ | 18 | $57736824250727/80029671321600 < 0.721443$ |
| 14 | [14.in](14.in) | $B_{2,2,3}$ | 23 | $24938647877172388313/34908201615006720000 < 0.714407$ |
| 16 | [16.in](16.in) | $B_{2,3,3}$ | 29 | $3970969041694879055111207/5638303485447723417600000 < 0.704285$ |

For $n\le 12$, each graph has the smallest ratio among all nonempty bipartite graphs on $n$ vertices. The 16-vertex graph $B_{2,3,3}$ gives the bipartite upper bound in the paper.
