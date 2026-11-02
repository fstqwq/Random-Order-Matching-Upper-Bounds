# General inputs

Each file is a zero-based edge list: the first line is `n m`, followed by `m` lines `u v`.

| $n$ | Nonisomorphic nonempty graphs | Input | $m$ | Ratio |
|---:|---:|---|---:|---|
| 4 | 10 | [4.in](4.in) | 4 | $3/4 = 0.75$ |
| 6 | 155 | [6.in](6.in) | 9 | $4915/6804 < 0.722370$ |
| 8 | 12,345 | [8.in](8.in) | 13 | $13137079/18532800 < 0.708856$ |
| 10 | 12,005,167 | [10.in](10.in) | 19 | $2941136911678289/4223788208640000 < 0.696327$ |

Each graph has the smallest ratio among all nonempty graphs on $n$ vertices. The 10-vertex graph $G_{10}$ gives the general upper bound in the paper.
