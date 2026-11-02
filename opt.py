"""Input: n m and m zero-based edges. Output: one exact reduced fraction.
Dependency: pynauty (see README.md, Setup).
"""
from functools import cache
from fractions import Fraction
from math import factorial

import pynauty


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def rename(mask, permutation):
    return sum(1 << permutation[v] for v in vertices(mask))


def ratio(n, edges):
    original = [0] * n
    for u, v in edges:
        original[u] |= 1 << v
        original[v] |= 1 << u
    m = len(edges)
    full = (1 << n) - 1

    @cache
    def canonical(g):
        graph = pynauty.Graph(len(g), adjacency_dict={
            v: list(vertices(neighbors)) for v, neighbors in enumerate(g)
        })
        # order[new] = old; permutation[old] = new.
        order = pynauty.canon_label(graph)
        permutation = [0] * len(g)
        for new, old in enumerate(order):
            permutation[old] = new
        return tuple(rename(g[v], permutation) for v in order), permutation

    @cache
    def count_fits(g):
        # Number of labelings of the hidden graph consistent with the observed graph g.
        # Only observed edges constrain the hidden labeling.
        order, placed = [], 0
        for _ in g:
            v = max((v for v in range(len(g)) if not placed >> v & 1),
                    key=lambda v: ((g[v] & placed).bit_count(), g[v].bit_count(), -v))
            order.append(v)
            placed |= 1 << v
        mapping = [0] * len(g)

        def dfs(at, used):
            if at == len(g):
                return 1
            v = order[at]
            choices = full & ~used
            for w in order[:at]:
                if g[v] >> w & 1:
                    choices &= original[mapping[w]]
            total = 0
            for w in vertices(choices):
                if original[w].bit_count() >= g[v].bit_count():
                    mapping[v] = w
                    total += dfs(at + 1, used | (1 << w))
            return total

        return dfs(0, 0) * factorial(n - len(g))

    @cache
    def transitions(g):
        # Possible next observed graphs, each with its conditional probability.
        k = len(g)
        unseen = n - k
        denominator = (m - sum(row.bit_count() for row in g) // 2) * count_fits(g)
        result = []

        def add(u, v, added, multiplicity):
            child = list(g) + [0] * added
            child[u] |= 1 << v
            child[v] |= 1 << u
            child, permutation = canonical(tuple(child))
            fits = count_fits(child)
            if fits:
                ends = (1 << u) | (1 << v)
                fresh = ((1 << added) - 1) << k
                result.append((child, permutation, ends, fresh,
                               Fraction(multiplicity * fits, denominator)))

        for u in range(k):
            for v in range(u + 1, k):
                if not g[u] >> v & 1:
                    add(u, v, 0, 1)
            if unseen:
                add(u, k, 1, unseen)
        if unseen >= 2:
            add(k, k + 1, 2, unseen * (unseen - 1) // 2)
        return result

    @cache
    def solve(g, available):
        remaining = m - sum(row.bit_count() for row in g) // 2
        upper = min(remaining, (available.bit_count() + n - len(g)) // 2)
        if not upper:
            return 0
        result = 0
        for child, permutation, ends, fresh, probability in transitions(g):
            free = available | fresh
            best = 0
            if free & ends == ends:
                best = 1 + solve(child, rename(free & ~ends, permutation))
            # Revealing the fresh vertices keeps |available| + unseen unchanged,
            # so the reject value is at most upper; skip it once best reaches upper.
            if best < upper:
                best = max(best, solve(child, rename(free, permutation)))
            result += probability * best
        return result

    masks = [(1 << u) | (1 << v) for u, v in edges]

    @cache
    def matching(mask):
        return max((1 + matching(mask ^ e) for e in masks if mask & e == e), default=0)

    return solve((), 0) / matching(full)


if __name__ == "__main__":
    n, m = map(int, input().split())
    edges = [tuple(map(int, input().split())) for _ in range(m)]
    print(ratio(n, edges))
