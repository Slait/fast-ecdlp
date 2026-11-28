#!/usr/bin/env python3
"""W-SIGN toy referee using streaming sparse Wiedemann, not a matrix inverse.

Curve: E/F_163: y^2=x^3+7, group order 139, generator (2,34).
The dense inverse is used only by the toy harness to label failed rounds
as singular; the algorithm itself only solves B^T y=r^T and verifies
the residual. The decomposition oracle is brute force, not the p^{o(1)}
count oracle.
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


def add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % P_MOD == 0:
        return None
    if P == Q:
        if y1 % P_MOD == 0:
            return None
        lam = ((3 * x1 * x1) * inv(2 * y1, P_MOD)) % P_MOD
    else:
        lam = ((y2 - y1) * inv(x2 - x1, P_MOD)) % P_MOD
    x3 = (lam * lam - x1 - x2) % P_MOD
    y3 = (lam * (x1 - x3) - y1) % P_MOD
    return x3, y3


def neg(P):
    if P is None:
        return None
    return P[0], (-P[1]) % P_MOD


def mul(k, P):
    if k < 0:
        return mul(-k, neg(P))
    R = None
    while k:
        if k & 1:
            R = add(R, P)
        P = add(P, P)
        k >>= 1
    return R


def invmat_mod(A, mod):
    """Toy-only reference rank test; not used by the algorithm."""
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


def bm(seq, mod):
    """Berlekamp–Massey; C[0]=1, returns C and linear complexity L."""
    C = [1]
    Bp = [1]
    L = 0
    shift = 1
    last_delta = 1
    for t in range(len(seq)):
        delta = seq[t]
        for i in range(1, L + 1):
            if i < len(C):
                delta = (delta + C[i] * seq[t - i]) % mod
        delta %= mod
        if delta == 0:
            shift += 1
            continue
        old_C = C[:]
        coef = delta * pow(last_delta, -1, mod) % mod
        if len(C) < len(Bp) + shift:
            C += [0] * (len(Bp) + shift - len(C))
        for i, x in enumerate(Bp):
            C[i + shift] = (C[i + shift] - coef * x) % mod
        if 2 * L <= t:
            L = t + 1 - L
            Bp = old_C
            last_delta = delta
            shift = 1
        else:
            shift += 1
    return C[:L + 1], L


def sparse_mv(rows, x, mod):
    return [
        sum(value * x[index] for index, value in row) % mod
        for row in rows
    ]


def streaming_wiedemann(A_rows, b, mod, rng, max_retries=5):
    """Solve A y=b with O(f) scratch and exact residual verification."""
    f = len(b)
    matvecs = 0
    for attempt in range(max_retries):
        projection = [rng.randrange(mod) for _ in range(f)]
        cur = b[:]
        sequence = []
        for _ in range(2 * f):
            sequence.append(
                sum(u * v for u, v in zip(projection, cur)) % mod
            )
            cur = sparse_mv(A_rows, cur, mod)
            matvecs += 1

        C, L = bm(sequence, mod)
        if not C or C[L] % mod == 0:
            continue

        # A^{-1}b = -C[L]^{-1} * sum_{k=0}^{L-1} C[L-1-k] A^k b.
        accum = [0] * f
        cur = b[:]
        for k in range(L):
            coeff = C[L - 1 - k]
            if coeff:
                accum = [
                    (z + coeff * v) % mod
                    for z, v in zip(accum, cur)
                ]
            cur = sparse_mv(A_rows, cur, mod)
            matvecs += 1

        inv_const = pow(C[L], -1, mod)
        y = [(-inv_const * z) % mod for z in accum]
        if sparse_mv(A_rows, y, mod) == [v % mod for v in b]:
            matvecs += 1
            return y, matvecs, attempt + 1
        matvecs += 1
    return None, matvecs, max_retries


def make_factor_base():
    F = []
    for x in range(1, X + 1):
        rhs = (x**3 + B_CURVE) % P_MOD
        ys = [y for y in range(P_MOD) if y * y % P_MOD == rhs]
        if ys:
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


def make_oracle(F):
    dec = {}
    for i, P1 in enumerate(F):
        for j, P2 in enumerate(F):
            if P1[0] == P2[0]:
                continue
            dec.setdefault(add(P1, P2), (i, j))
    return dec


def coverage(F):
    return {
        add(P1, P2)
        for P1 in F for P2 in F
        if P1[0] != P2[0]
    }


def run_round(d, F, flogs, dec, rng):
    f = len(F)
    nu = rng.randrange(N)
    T_rows = []
    A_rows = []
    attempts = 0

    for row_index in range(f):
        while True:
            attempts += 1
            a, b = rng.randrange(N), rng.randrange(N)
            target = mul((a + b * d + nu * flogs[row_index]) % N, GEN)
            if target in dec:
                i, j = dec[target]
                row = [0] * f
                row[i] += 1
                row[j] += 1
                T_rows.append(row)
                A_rows.append([a, b])
                break
            if attempts > 100000:
                return "timeout", attempts, 0, 0

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
            return "timeout", attempts, 0, 0

    Bmat = [
        [
            (T_rows[i][j] - (nu if i == j else 0)) % N
            for j in range(f)
        ]
        for i in range(f)
    ]

    # Test-only rank classification. The actual algorithm does not invert B.
    is_singular = invmat_mod(Bmat, N) is None

    # A = B^T, stored sparsely as (column_index, coefficient) pairs.
    A_sparse = [
        [(j, Bmat[j][i]) for j in range(f) if Bmat[j][i] % N]
        for i in range(f)
    ]
    y, matvecs, solver_tries = streaming_wiedemann(
        A_sparse, r, N, rng, max_retries=5
    )
    if y is None:
        return (
            "singular" if is_singular else "solver-fail",
            attempts,
            matvecs,
            solver_tries,
        )

    yA = [
        sum(y[i] * A_rows[i][j] for i in range(f)) % N
        for j in range(2)
    ]
    mu = [(a0 - yA[0]) % N, (b0 - yA[1]) % N]
    if mu == [0, 0]:
        return "zero", attempts, matvecs, solver_tries
    if mu[1] == 0:
        return "bad-v", attempts, matvecs, solver_tries

    recovered = (-mu[0] * pow(mu[1], -1, N)) % N
    return (
        "ok" if recovered == d else "wrong",
        attempts,
        matvecs,
        solver_tries,
    )


def main():
    assert mul(N, GEN) is None
    F = make_factor_base()
    log_table = make_log_table()
    flogs = [log_table[P] for P in F]
    dec = make_oracle(F)
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
    attempts = matvecs = solver_tries = 0
    for _ in range(2000):
        d = rng.randrange(N)
        status, count, mv, st = run_round(d, F, flogs, dec, rng)
        stats[status] += 1
        attempts += count
        matvecs += mv
        solver_tries += st
    print("2,000 streaming-Wiedemann rounds:", dict(stats))
    print("mean target attempts:", attempts / 2000)
    print("mean sparse matvecs:", matvecs / 2000)
    print("mean Wiedemann projections:", solver_tries / 2000)

    rng = random.Random(1234)
    exhaustive = {}
    max_retries = 0
    for d in range(N):
        for retries in range(100):
            status, _, _, _ = run_round(d, F, flogs, dec, rng)
            if status == "ok":
                exhaustive[d] = True
                max_retries = max(max_retries, retries)
                break
        else:
            raise RuntimeError("exhaustive target failed: %d" % d)
    print("exhaustive target logs:", len(exhaustive), "/", N,
          "max retries:", max_retries)

    A0, W = 40, 32
    rng = random.Random(2026)
    interval_stats = Counter()
    interval_attempts = interval_mvs = interval_projections = 0
    for _ in range(500):
        x = rng.randrange(W)
        Q = mul(A0 + x, GEN)
        Qprime = add(Q, neg(mul(A0, GEN)))
        assert log_table[Qprime] == x
        status, count, mv, st = run_round(x, F, flogs, dec, rng)
        interval_stats[status] += 1
        interval_attempts += count
        interval_mvs += mv
        interval_projections += st
    print("interval A=40, W=32:", dict(interval_stats))
    print("interval mean target attempts:", interval_attempts / 500)
    print("interval mean sparse matvecs:", interval_mvs / 500)
    print("interval mean Wiedemann projections:", interval_projections / 500)

    assert stats["wrong"] == 0 and stats["solver-fail"] == 0
    assert stats["timeout"] == 0
    assert interval_stats["wrong"] == 0
    assert interval_stats["solver-fail"] == 0
    assert interval_stats["timeout"] == 0
    assert len(exhaustive) == N
    print("PASS: one-sided streaming-Wiedemann toy referee")


if __name__ == "__main__":
    main()
