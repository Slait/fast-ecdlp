# X265 SNF/Weil source manifest v1

**Branch:** `x265/production-spec-v1`  
**Artifact status:** exact-arithmetic implementation candidate; Lean proof and external audit open.

## Companion source archive

The complete reproducible source package is distributed as `X265_SNF_WEIL_IMPLEMENTATION_v1.zip`.

- SHA-256: `2419cdcfc615ec7958224733577a91d9ab336e660929bc8b6a9a7dd951f8d461`
- Contains:
  - `X265_SNF_WEIL_PRODUCER_v1.py`
  - `X265_SNF_WEIL_VERIFIER_v1.py`
  - `X265_SNF_WEIL_TESTS_v1.py`
  - `X265_SNF_WEIL_FIXTURES_v1.json`
  - `X265_SNF_WEIL_TEST_RESULTS_v1.json`
  - `X265_SNF_WEIL_IMPLEMENTATION_REPORT_v1.md`
  - `X265_SNF_WEIL_CONTRACTS_v1.md`
  - `X265_SNF_WEIL_README.md`

## Individual source hashes

| File | SHA-256 |
|---|---|
| Producer | `0f2fa51c2e35feafd5e24830dcc8bacbbaf65669d1bf5dd405616a1b12d37236` |
| Independent verifier | `84a3b7671604ee656fe4381b4159640f2349c767dad8f06f6c629277830763ed` |
| Tests | `edde81f3105d291cfad85bbe80f45ce2d6fbbc0a14773e4f04899157a3dcdfdd` |
| Test results | `7f781357a48bc576ac0dcff04f7f2d4ebae5be16cefe41e5b1af23dab55be750` |

## Latest reproducible test run

Seed: `20261127`.

- 1,000 X265 rectangular SNF cases, differential check against SymPy.
- 2,000 square 3x3 SNF cases, differential check against SymPy.
- Six coefficient sizes from 64 to 2048 bits; up to 80 columns.
- Ten small-curve group/basis cases.
- Nine non-cyclic pairing property cases.
- One 65-bit Pocklington prime / Weil pairing case.
- Independent verifier rejects tampered S, T, D and pairing transcript values.

## Frozen interfaces

- `research/X265_SNF_WEIL_IMPLEMENTATION_REPORT_v1.md`
- `research/X265_SNF_WEIL_CONTRACTS_v1.md`
- `v2/python/README.md`

The source archive is a research implementation candidate. It is not a constant-time
cryptographic library, not a unified Lean build, and not an externally reviewed release.
