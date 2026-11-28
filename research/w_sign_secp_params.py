#!/usr/bin/env python3
"""Recompute W-SIGN finite parameters for secp256k1 using only stdlib."""
from math import factorial, log2, sqrt

P = int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16)
N = int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16)


def ceil_nth_root(n, k):
    lo, hi = 0, 1
    while hi**k < n:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**k >= n:
            hi = mid
        else:
            lo = mid
    return hi


def optimise(m):
    B = ceil_nth_root(P, m)
    X = B - 1
    D = (2 * m - 1) * 2 ** (2 * m - 2)
    cF = 13 + 2 / X
    a = cF / X

    def quantities(eps):
        delta = a / (eps * eps)
        rho = 1 - delta
        fmin = (1 - eps) * X / 2
        Mbar = factorial(m) * X**m + 2 * D * X**(2*m) / (P - 1)
        q = (
            4 * N * Mbar
            / (rho * fmin ** (2*m - 1))
            * (1 + 1 / fmin)
        )
        return delta, rho, fmin, Mbar, q

    def derivative(eps):
        delta, rho, fmin, _, _ = quantities(eps)
        # d/d eps of log(q); the final term differentiates (1 + 1/fmin).
        return (
            (2 * m - 1) / (1 - eps)
            - 2 * a / (eps**3 * rho)
            + (X / 2) / (fmin**2 * (1 + 1 / fmin))
        )

    lo = sqrt(a) * (1 + 1e-8)
    hi = 0.5
    assert derivative(lo) < 0 and derivative(hi) > 0
    for _ in range(120):
        mid = (lo + hi) / 2
        if derivative(mid) > 0:
            hi = mid
        else:
            lo = mid
    eps = (lo + hi) / 2
    delta, rho, fmin, Mbar, q = quantities(eps)
    fmax = (1 + eps) * X / 2
    return {
        "m": m,
        "B": B,
        "X": X,
        "Dprime": D,
        "m_factorial_plus_2D": factorial(m) + 2 * D,
        "epsilon": eps,
        "delta": delta,
        "rho": rho,
        "fmin": fmin,
        "fmax": fmax,
        "Mbar_log2": log2(Mbar),
        "expected_probe_log2": log2(q),
        "sparse_m_f2_log2": 2 * log2(fmax) + log2(m),
    }


def main():
    assert P % 3 == 1
    assert pow(7, (P - 1) // 2, P) == P - 1
    assert P > 3 * (2**32)

    print("secp256k1 p =", hex(P))
    print("secp256k1 n =", hex(N))
    print("p mod 3 =", P % 3)
    print("Legendre(7,p) =", pow(7, (P - 1) // 2, P))
    for m in (8, 16, 17):
        r = optimise(m)
        assert r["X"] >= 12 * m
        assert r["X"] < P // 3
        print(r)

    r8 = optimise(8)
    r16 = optimise(16)
    r17 = optimise(17)
    assert abs(r8["expected_probe_log2"] - 68.0446490611) < 1e-7
    assert abs(r16["expected_probe_log2"] - 94.9344146448) < 1e-7
    assert abs(r17["expected_probe_log2"] - 100.6162690291) < 1e-7
    assert abs(r16["sparse_m_f2_log2"] - 34.0740886734) < 1e-7
    assert abs(r17["sparse_m_f2_log2"] - 32.2977169695) < 1e-7
    print("PASS: W-SIGN secp256k1 finite-parameter arithmetic")


if __name__ == "__main__":
    main()
