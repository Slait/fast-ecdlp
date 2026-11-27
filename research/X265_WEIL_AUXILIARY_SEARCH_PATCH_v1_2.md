# X265 Weil auxiliary-search implementation patch v1.2

This patch aligns the Python SNF/Weil candidate with the paper-level X268 auxiliary-point lemma.

## Exact changes

1. `weil_auxiliary_bad_point_bound(n)` now returns
   `40 * floor(log2(n)) + 4`.
   The four additional shifts are the standard exceptional set
   `{O, P, -Q, P-Q}`.

2. The producer explicitly rejects all four exceptional shifts before running Miller:
   `S = O`, `S = P`, `S = -Q`, or `S = P-Q`.

3. If all four Miller evaluations are finite and nonzero but the shifted ratio does not satisfy
   `eta^n = 1`, the producer raises an implementation error. It does not retry another shift:
   for valid shifts the Weil value is independent of the auxiliary point.

4. The independent verifier explicitly checks the four excluded shifts.

5. The test's sufficient half-success condition is updated to
   `N > 80 * floor(log2(n)) + 8`.

6. The proof-aligned mode remains `max_aux_attempts=None`, i.e. the unbounded Las Vegas sampler. A finite cap must fail closed and be included in the outer probability analysis.

## Reproducible test results

After the patch:

- `x265_snf_weil_tests.py`: PASS.
  - 1,000 rectangular SNF cases; 1,000 SymPy oracle comparisons.
  - 2,000 square 3x3 SNF cases.
  - 10 Weil/group-basis curves; 9 bilinearity curves.
  - 65-bit Pocklington prime test and independent pairing verifier: PASS.
- `x265_snf_weil_composite_tests.py`: PASS.
  - 32 composite moduli.
  - 384 random rectangular cases.
  - 32 structured group-lattice cases.

## File hashes

- Producer `x265_snf_weil.py`: `52e8729a71c35cc75dade4931c187be5ce8693c970266ad8de0adb2cbf64b493`
- Independent verifier `x265_snf_weil_verify.py`: `beba0d7720107b35596a83df0b03c4d021a96edd4acbc843fa9ce2b05d2fc599`

## Scope

This patch closes the auxiliary-point bound/exceptional-shift mismatch in the Python candidate. It does **not** prove the custom rectangular SNF producer's bit complexity; X267's Kannan–Bachem route remains the proof-aligned algorithm specification. It also does not constitute a full production ECDLP implementation or a unified Lean proof.
