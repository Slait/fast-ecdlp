# X265 SNF/Weil candidate — run guide

## Files

- `x265_snf_weil.py` — exact-arithmetic producer.
- `x265_snf_weil_verify.py` — separate certificate verifier.
- `x265_snf_weil_tests.py` — deterministic test suite.
- `x260_pairing_results.json` — frozen small-curve fixtures used by tests.
- `x265_snf_weil_test_results.json` — output of the latest successful test run.
- `X265_SNF_WEIL_IMPLEMENTATION_REPORT_v1.md` — mathematical and engineering report.
- `X265_SNF_WEIL_CONTRACTS_v1.md` — proposed Lean interfaces.

## Runtime dependencies

`x265_snf_weil.py` and `x265_snf_weil_verify.py` use only the Python standard
library. SymPy is optional and used only by the tests as a differential oracle.

## Run tests

```bash
python x265_snf_weil_tests.py
```

Expected summary: 1,000 rectangular X265 SNF cases, 2,000 square SNF cases,
10 small-curve group/basis cases, 9 non-cyclic pairing property cases, and one
65-bit Pocklington/Weil case all pass.

## SNF producer

The matrix must have the exact X265 shape
`M = [mu_1 ... mu_s | N*I_3]`, with each relation coordinate in `[0,N)`.

```python
from x265_snf_weil import smith_decomposition_3xn, verify_snf_certificate

S, T, D, telemetry = smith_decomposition_3xn(
    M, N=N, max_coefficient_bits=100_000
)
assert verify_snf_certificate(M, S, T, D)
```

The optional coefficient cap fails closed with `CoefficientLimitExceeded`.
A cap failure is `RETRY_ATTEMPT` at the algorithm level, never `NO_LOG`.

## Weil pairing producer and verifier

```python
from x265_snf_weil import (
    ShortWeierstrassCurve, weil_pairing_certificate,
    verify_weil_certificate,
)
from x265_snf_weil_verify import verify_weil_certificate as independent_verify

E = ShortWeierstrassCurve(p, a, b, prime_certificate=prime_cert_if_needed)
cert = weil_pairing_certificate(
    E, n, P, Q, prime_divisors_n,
    group_order_N=N,
    max_aux_attempts=None,  # unbounded Las Vegas auxiliary-point search
)
assert verify_weil_certificate(E, cert, prime_divisors_n)
assert independent_verify((p, a, b, prime_cert_if_needed), cert, prime_divisors_n)
```

For `p >= 2^64`, provide a Pocklington certificate. For prime divisors of `n`
that are at least `2^64`, provide their certificates in the `prime_certificates`
map. The full factorization and curve group order are upstream inputs.

## Security note

This is research exact-arithmetic code, not constant-time cryptographic software.
Do not deploy it against secret scalars without replacing Python big integers and
modular inversions with a reviewed constant-time backend.

For the pinned source archive, file hashes, and reproducible test summary, see [`research/X265_SNF_WEIL_SOURCE_MANIFEST_v1.md`](../../research/X265_SNF_WEIL_SOURCE_MANIFEST_v1.md).
