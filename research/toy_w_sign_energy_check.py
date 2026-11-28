#!/usr/bin/env python3
"""Exhaustive small-field check of the W-SIGN primitive-relation energy bound.

Curve: E/F_163: y^2=x^3+7, #E=139 prime, T={1,...,13}, m=2.
For every dilation u and every ordered 4-tuple of abscissae, count the
u for which the one-sided group relation holds. This is a numerical referee,
not a proof of the Semaev nondegeneracy lemma.
"""
from collections import Counter
from itertools import product
from math import factorial

P = 163
B = 7
N = 139
G = (2, 34)
M = 2
X = 13
D_PRIME = (2 * M - 1) * 2 ** (2 * M - 2)


def inv(a, mod):
    return pow(a % mod, -1, mod)


def add(Pt, Qt):
    if Pt is None:
        return Qt
    if Qt is None:
        return Pt
    x1, y1 = Pt
    x2, y2 = Qt
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if Pt == Qt:
        lam = (3 * x1 * x1 * inv(2 * y1, P)) % P
    else:
        lam = ((y2 - y1) * inv(x2 - x1, P)) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return x3, y3


def mul(k, Pt):
    R = None
    while k:
        if k & 1:
            R = add(R, Pt)
        Pt = add(Pt, Pt)
        k >>= 1
    return R


def log_table():
    out = {}
    Pt = None
    for k in range(N):
        out[Pt] = k
        Pt = add(Pt, G)
    assert Pt is None and len(out) == N
    return out


def main():
    logs = log_table()
    assert mul(N, G) is None
    assert pow(B, (P - 1) // 2, P) == P - 1
    assert P % 3 == 1
    assert X < P // 3

    # For each u, store the discrete log of the unique canonical point
    # (x,y) on E_u with x in T and 0<y<= (p-1)/2, transported back to E.
    by_u = {}
    f_sym = []
    total_energy = 0
    trivial_energy = 0

    for u in range(1, P):
        Bu = (pow(u, 6, P) * B) % P
        invu2 = inv(pow(u, 2, P), P)
        invu3 = inv(pow(u, 3, P), P)
        smap = {}
        for x in range(1, X + 1):
            rhs = (x**3 + Bu) % P
            ys = [y for y in range(P) if y * y % P == rhs]
            if ys:
                y = min(ys)
                if y > P // 2:
                    y = P - y
                x0 = (invu2 * x) % P
                y0 = (invu3 * y) % P
                smap[x] = logs[(x0, y0)]
        by_u[u] = smap
        f_sym.append(2 * len(smap))

        sums = Counter()
        xs = list(smap)
        for a in xs:
            for b in xs:
                sums[(smap[a] + smap[b]) % N] += 1
        total_energy += sum(v * v for v in sums.values())

        # Exact trivial contribution: right pair is a permutation of left pair.
        for a in xs:
            for b in xs:
                trivial_energy += 1 if a == b else 2

    # Count roots in u for every nontrivial ordered pair-of-pairs.
    root_hist = Counter()
    max_roots = 0
    max_tuple = None
    for a, b, c, d in product(range(1, X + 1), repeat=4):
        if sorted((a, b)) == sorted((c, d)):
            continue
        roots = 0
        for smap in by_u.values():
            if a in smap and b in smap and c in smap and d in smap:
                if (smap[a] + smap[b] - smap[c] - smap[d]) % N == 0:
                    roots += 1
        root_hist[roots] += 1
        if roots > max_roots:
            max_roots = roots
            max_tuple = (a, b, c, d)

    M_bar = factorial(M) * X**M + (
        2 * D_PRIME * X ** (2 * M) / (P - 1)
    )
    variance_ratio = sum((f - X) ** 2 for f in f_sym) / ((P - 1) * X)

    print("p=163, group order=139, m=2, X=13, D'=", D_PRIME)
    print("max nontrivial dilation roots:", max_roots,
          "at tuple", max_tuple, "(bound 2D' =", 2 * D_PRIME, ")")
    print("root histogram:", dict(sorted(root_hist.items())))
    print("sum_u energy:", total_energy)
    print("mean_u energy:", total_energy / (P - 1))
    print("trivial energy:", trivial_energy)
    print("new one-sided M_bar:", M_bar)
    print("FactorBaseVar ratio:", variance_ratio,
          "(claimed upper bound", 13 + 2 / X, ")")

    assert max_roots <= 2 * D_PRIME
    assert total_energy / (P - 1) <= M_bar
    assert variance_ratio <= 13 + 2 / X
    print("PASS: exhaustive small-field energy/root-count checks")


if __name__ == "__main__":
    main()
