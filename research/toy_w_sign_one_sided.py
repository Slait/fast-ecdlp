#!/usr/bin/env python3
"""Toy referee for W-SIGN/W-PD2 on E/F_163: y^2=x^3+7.

This is an algebraic test only. The decomposition oracle is brute force and
must not be confused with the asymptotic p^{o(1)} count oracle.
"""
from collections import Counter
import random

P_MOD = 163
B_CURVE = 7
N = 139
GEN = (2, 34)
X = 13


def inv(a, mod):
    return pow(a % mod, -1, mod)


def add(P, Q, p=P_MOD, A=0):
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        if y1 % p == 0:
            return None
        lam = ((3 * x1 * x1 + A) * inv(2 * y1, p)) % p
    else:
        lam = ((y2 - y1) * inv(x2 - x1, p)) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return x3, y3


def neg(P, p=P_MOD):
    if P is None:
        return None
    return P[0], (-P[1]) % p


def mul(k, P, p=P_MOD, A=0):
    if k < 0:
        return mul(-k, neg(P, p), p, A)
    R = None
    while k:
        if k & 1:
            R = add(R, P, p, A)
        P = add(P, P, p, A)
        k >>= 1
    return R


def invmat_mod(A, mod):
    n = len(A)
    Mx = [
        [x % mod for x in row]
        + [1 if i == j else 0 for j in range(n)]
        for i, row in enumerate(A)
    ]
    for c in range(n):
        pivot = next((r for r in range(c, n) if Mx[r][c] % mod), None)
        if pivot is None:
            return None
        Mx[c], Mx[pivot] = Mx[pivot], Mx[c]
        iv = pow(Mx[c][c], -1, mod)
        Mx[c] = [(x * iv) % mod for x in Mx[c]]
        for r in range(n):
            if r == c:
                continue
            fac = Mx[r][c] % mod
            if fac:
                Mx[r] = [
                    (Mx[r][j] - fac * Mx[c][j]) % mod
                    for j in range(2 * n)
                ]
    return [row[n:] for row in Mx]


def row_mul(a, matrix, mod):
    return [
        sum(a[i] * matrix[i][j] for i in range(len(a))) % mod
        for j in range(len(matrix[0]))
    ]


def make_factor_base():
    F = []
    for x in range(1, X + 1):
        rhs = (x**3 + B_CURVE) % P_MOD
        ys = [y for y in range(P_MOD) if y * y % P_MOD == rhs]
        if ys:
            # Exactly one representative has 0 < y <= (p-1)/2.
            y = min(ys)
            if y > P_MOD // 2:
                y = P_MOD - y
            assert 0 < y <= P_MOD // 2
            F.append((x, y))
    return F


def make_log_table():
    table = {}
    R = None
    for k in range(N):
        table[R] = k
        R = add(R, GEN)
    assert R is None and len(table) == N
    return table


def make_generic_pair_oracle(F):
    dec = {}
    for i, P1 in enumerate(F):
        for j, P2 in enumerate(F):
            # For a one-sided base, equal x means equal point.
            # This is exactly the m=2 genericity condition.
            if P1[0] == P2[0]:
                continue
            target = add(P1, P2)
            dec.setdefault(target, (i, j))
    return dec


def coverage(F):
    targets = set()
    for P1 in F:
        for P2 in F:
            if P1[0] != P2[0]:
                targets.add(add(P1, P2))
    return targets


def run_round(d, F, flogs, dec, log_table, rng):
    f = len(F)
    nu = rng.randrange(N)
    T_rows = []
    A_rows = []
    attempts = 0

    # f planted rows.
    for row_index in range(f):
        while True:
            attempts += 1
            a, b = rng.randrange(N), rng.randrange(N)
            target_scalar = (a + b * d + nu * flogs[row_index]) % N
            target = mul(target_scalar, GEN)
            if target in dec:
                i, j = dec[target]
                row = [0] * f
                row[i] += 1
                row[j] += 1
                T_rows.append(row)
                A_rows.append([a, b])
                break
            if attempts > 100000:
                return "timeout", attempts

    # One final unplanted row.
    while True:
        attempts += 1
        a0, b0 = rng.randrange(N), rng.randrange(N)
        target = mul((a0 + b0 * d) % N, GEN)
        if target in dec:
            i, j = dec[target]
            r = [0] * f
            r[i] += 1
            r[j] += 1
            break
        if attempts > 100000:
            return "timeout", attempts

    Bmat = [
        [
            (T_rows[i][j] - (nu if i == j else 0)) % N
            for j in range(f)
        ]
        for i in range(f)
    ]
    Binv = invmat_mod(Bmat, N)
    if Binv is None:
        return "singular", attempts

    y = row_mul(r, Binv, N)
    yA = [
        sum(y[i] * A_rows[i][j] for i in range(f)) % N
        for j in range(2)
    ]
    mu = [(a0 - yA[0]) % N, (b0 - yA[1]) % N]
    if mu == [0, 0]:
        return "zero", attempts
    if mu[1] == 0:
        return "bad-v", attempts

    recovered = (-mu[0] * pow(mu[1], -1, N)) % N
    return ("ok" if recovered == d else "wrong"), attempts


def main():
    assert mul(N, GEN) is None
    F = make_factor_base()
    log_table = make_log_table()
    flogs = [log_table[P] for P in F]
    dec = make_generic_pair_oracle(F)
    sym = F + [neg(P) for P in F]

    assert len(F) == 9
    assert len(coverage(F)) == 34
    assert len(coverage(sym)) == 112

    print("curve: E/F_163: y^2=x^3+7")
    print("group order:", N, "generator:", GEN)
    print("one-sided factor-base size:", len(F), "points:", F)
    print("generic pair coverage: one-sided", len(coverage(F)), "/", N)
    print("generic pair coverage: symmetric", len(coverage(sym)), "/", N)

    rng = random.Random(20261128)
    stats = Counter()
    attempts = []
    for _ in range(2000):
        d = rng.randrange(N)
        status, count = run_round(d, F, flogs, dec, log_table, rng)
        stats[status] += 1
        attempts.append(count)
    print("2,000 random planted rounds:", dict(stats))
    print("mean target attempts:", sum(attempts) / len(attempts))

    rng = random.Random(1234)
    exhaustive = {}
    max_retries = 0
    for d in range(N):
        for retries in range(100):
            status, _ = run_round(d, F, flogs, dec, log_table, rng)
            if status == "ok":
                # Recompute the result is unnecessary: status already checks d.
                exhaustive[d] = True
                max_retries = max(max_retries, retries)
                break
        else:
            raise RuntimeError("exhaustive target failed: %d" % d)
    assert len(exhaustive) == N
    print("exhaustive target logs:", len(exhaustive), "/", N,
          "max retries:", max_retries)

    # Interval wrapper: Q=[A+x]P, then Q' = Q-[A]P=[x]P.
    A0, W = 40, 32
    rng = random.Random(2026)
    interval_stats = Counter()
    interval_attempts = []
    for _ in range(500):
        x = rng.randrange(W)
        Q = mul(A0 + x, GEN)
        Qprime = add(Q, neg(mul(A0, GEN)))
        assert log_table[Qprime] == x
        status, count = run_round(x, F, flogs, dec, log_table, rng)
        interval_stats[status] += 1
        interval_attempts.append(count)
    print("interval A=40, W=32:", dict(interval_stats))
    print("interval mean target attempts:",
          sum(interval_attempts) / len(interval_attempts))

    assert stats["wrong"] == 0
    assert stats["timeout"] == 0
    assert interval_stats["wrong"] == 0
    assert interval_stats["timeout"] == 0
    print("PASS: one-sided algebraic toy referee")


if __name__ == "__main__":
    main()
