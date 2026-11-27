# X265 Lean port status v1

**Branch:** `x265/production-spec-v1`  
**Lean project:** `v2/lean`  
**Toolchain:** `leanprover/lean4:v4.35.0`

## What was added

New module:

`v2/lean/ECDLPv2/X265_SNFWielInterface.lean`

Git blob: `dfb32d47712ed2c09ce9f057b4959ae84b8b0461`

The module declares:

- X265 input matrix shape (M=[\mu_1,\ldots,\mu_s\mid NI_3]) with reduced relation entries;
- determinant-based integer unimodularity;
- Smith-diagonal predicate with positivity and divisibility;
- explicit `SNFCertificate` carrying (S,T,D) and (SMT=D);
- lattice endpoint (d_1=1), (d_1d_2d_3=N);
- the four Miller evaluation slots for the shifted Weil formula;
- the exact primitive-root predicate checked by prime divisors.

The module contains no `sorry`. It is included by the existing `ECDLPv2.+` library glob, but has not yet been imported into `Verify.lean`.

## Repository facts checked

- `v2/lean/lean-toolchain` is Lean 4.35.0.
- `v2/lean/lakefile.toml` defines library `ECDLPv2` with glob `ECDLPv2.+`.
- `v2/lean/Verify.lean` currently imports Count15 and the X263/v2 reduction modules, but not the new X265 interface.
- The existing GitHub workflow builds the root `lean/` project, not `v2/lean`; therefore its success would not certify this module.
- The external `JJYYY-JJY/lean-normal-forms` project is pinned to Lean 4.32.0, so it cannot be assumed to drop into the v2 project without a port or version bridge.

## Not yet proved

1. The local (4\times3) row-HNF insertion algorithm and its explicit unimodular transform.
2. The inductive invariant (UM^T=[H;0]), including the (N\mathbb Z^3\subseteq L(H)) fact.
3. The (O(s\log N)) coefficient-bit bound for the rectangular wrapper.
4. The exact Kannan–Bachem square SNF implementation and its bit-complexity theorem in the v2 Lean toolchain.
5. Quotient-lattice isomorphism and extraction of (U,V) from (S^{-1}).
6. Miller recurrence semantics, divisor identities, the shifted Weil formula, and verifier soundness.
7. A unified `Verify.lean` import and a clean v2 project build.

## Build status

No Lean or Lake executable was available in the working container, and no v2 build was run. The file is a Lean interface draft, not a compiled/formally verified result. Do not mark the SNF/Weil item proved until the exact code and all the obligations above are discharged.
