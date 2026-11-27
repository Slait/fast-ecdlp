# X265 — production algorithm specification and checked pseudocode (draft v1)

**Date:** 27 November 2026  
**Scope:** close limitation 1: a single end-to-end specification for X263 + X264 + Count15 + X265, including the corrected fresh-dilation coordinate rounds.  
**Status:** `PSEUDOCODE_SPECIFIED / IMPLEMENTATION_OPEN / AUDIT_REVISION_1`. This document is a reviewed mathematical specification, not a production executable and not a unified Lean proof.  
**Parameters:** `m = 15`; integer security parameter `lambda >= 1`; `s = lambda + 9`. The stated `N^(1/5+o(1))` bound is for fixed `lambda`, or more generally `lambda = polylog(N)`; arbitrary growth of `lambda` is not covered by that bound.

## 0. Status discipline

Three objects must not be conflated:

1. **Mathematical specification:** the algorithm below, with exact contracts for each primitive.
2. **Reference implementation:** the supplied Python code, which uses a slow exact dynamic-programming Count15 oracle and small-field exhaustive referees.
3. **Production implementation:** still absent. It must instantiate the Count15 machine, bit-controlled SNF/HNF, and bounded/expected-time Miller/Weil routines with tested code and a bit-complexity proof.

The target theorem remains conditional on the Count15 theorem and the stated classical inputs, and `ECDLP-MAIN` remains `OPEN` until the unified formalization and implementations exist.

## 1. Mathematical input and notation

Input:

- prime `p > 3`;
- nonsingular short Weierstrass curve `E/F_p: y^2 = x^3 + A*x + B`, with `4*A^3 + 27*B^2 != 0`;
- arbitrary public points `P,Q in E(F_p)`;
- integer `lambda >= 1`.

Let `N = #E(F_p)`. Compute `N` exactly by deterministic Schoof (or an exact certified SEA implementation), then compute its complete prime factorization by the deterministic Harvey–Hittmeir factorization algorithm. All arithmetic in coefficient vectors is in `Z/NZ`. The theorem takes `p` prime and `P,Q in E(F_p)` as preconditions. A production API must either validate primality and curve membership of `P,Q` or carry independently checkable certificates; invalid inputs return `INVALID_INPUT`.

Set

- `m := 15`;
- `X := min {b in N : p <= b^m} = ceil(p^(1/m))`;
- `s := lambda + 9`;
- `h(u) := f_u + 2`, where `f_u = |F_u|`;
- `D_m := 24^(2m)`;
- `C_m := 2^(4m+5) * ( (2m-1)!! + 2^(m+1)*D_m )`;
- `P_m := 2*C_m`.

For `m=15`, the frozen constants are:

```
D_15 = 254880876153761202627773829926908776677376
C_15 = 616264144216561108751959464108765646258832518075703635287685988352
P_15 = 1232528288433122217503918928217531292517665036151407270575371976704
X(P_15) = 25472
q_15 = 1/(4*C_15) ~= 4.0567020221e-67
```

For `p < P_15`, use the finite direct algorithm: enumerate `E(F_p)` (or compute `N` and test every `k in [0,N)`) and return the exact answer. This is an astronomically large but fixed finite base case and does not change the asymptotic exponent. The asymptotic branch below is for `p >= P_15`.

## 2. Exact primitive contracts

### 2.1 Unbiased sampling

`UniformBelow(M)` returns an exactly uniform integer in `{0,...,M-1}` using rejection sampling on random bits; it must not use a biased `% M` reduction.

`UniformModN(d)` returns `d` independent calls to `UniformBelow(N)`.

The mathematical Las Vegas theorem uses ideal independent uniform bits. A deployed cryptographic implementation may use a CSPRNG/DRBG, but then the implementation claim is computational pseudorandomness, not literal information-theoretic uniformity.

### 2.2 Uniform point sampler

For `E: y^2=x^3+a*x+b`, sample a token `z` uniformly from `{0,...,2p}`:

- `z = 2p` represents `O` and is accepted;
- otherwise `x = floor(z/2)` and `sign = z mod 2`;
- compute `r = x^3+a*x+b mod p`;
- reject if `r` is a nonsquare;
- if `r=0`, accept only `sign=0` and return `(x,0)`;
- if `r != 0`, compute the canonical root `y0=min(y,p-y)` from a square root `y`, so `0<y0<= (p-1)/2`; return `(x,y0)` for `sign=0`, `(x,p-y0)` for `sign=1`.

Every point of `E(F_p)` has exactly one accepted token. Thus the accepted point is exactly uniform. The acceptance probability is `N/(2p+1)`, which is bounded below by a positive constant in the asymptotic range by Hasse. For Tonelli–Shanks, first find a quadratic nonresidue by sampling uniform nonzero field elements and checking Euler's criterion; this takes fewer than two trials in expectation, and the test certifies the chosen nonresidue. Reuse it for all square roots in the field. Tonelli–Shanks is then deterministic given that certified nonresidue. A deterministic nonresidue search must not be silently assumed to take polylogarithmic time.

### 2.3 Dilation and factor base

For fresh `u in F_p^*`, define

```
E_u: y^2 = x^3 + (A*u^4)*x + B*u^6
phi_u(x,y) = (u^2*x, u^3*y),  phi_u(O)=O.
```

`phi_u: E -> E_u` is an explicitly checked group isomorphism.

Let `F_u` be the list of all nonzero points `(x,y) in E_u(F_p)` with `0 <= x < X`, ordered by the fixed Count15 encoding: the `Nat.size(X)` big-endian bits of `x`, followed by the sign bit `[(p-1)/2 < y]`. If `y=0`, only sign zero is present. Write `f=|F_u|`.

### 2.4 Exact Count15 oracle

For an affine target `R=(x_R,y_R) != O` and a bit prefix `pi`, define

```
Count15(E_u,R,pi)
```

as the exact number of encoded ordered 15-tuples `(P_1,...,P_15)` satisfying:

- each `P_i` is nonzero and has `x(P_i)<X`;
- each partial sum `S_k=P_1+...+P_k`, `1<=k<15`, is nonzero and `x(S_k) != x(P_{k+1})`;
- the total sum is the nonzero target `R`;
- the concatenated fixed-width `(x,sign)` encoding begins with `pi`.

If `R=O`, define `Count15(E_u,O,pi)=0` outside the Lean interface; the Lean encoding uses an affine target and explicitly excludes zero total sums. No `Count15` query for `O` is needed.

The query encodes `p`, the canonical residues of the two curve coefficients, and the affine target coordinates as natural numbers separated by the Lean input delimiters, followed by the bit prefix. The upstream Lean source is `v2/lean/ECDLPv2/L109_CountChallenge.lean`; `v2/lean/ECDLPv2/L132_Final.lean` proves `countingRate_all`. For fixed `m=15`, the theorem supplies exact binary counts for all prefixes in `p^(o(1))` time.

### 2.5 Canonical witness extraction

`Witness15(E_u,R)`:

1. If `R=O`, return `NONE`.
2. If `Count15(E_u,R,empty)=0`, return `NONE`.
3. Let `L=15*(Nat.size(X)+1)`. Start with empty prefix `pi`.
4. For each of the `L` bit positions, query `Count15(E_u,R,pi||0)`. If it is positive, append `0`; otherwise append `1`. Since the current prefix has positive count and all strings have fixed length, the latter branch has positive count.
5. Decode the resulting string into 15 factor-base points of `F_u` by the fixed-width encoding (the decoding of each point is unique; **repetitions among the 15 tuple entries are allowed**). Independently verify every genericity condition and that their sum is `R`.
6. Return the multiplicity row `t in {0,...,15}^f`, where `t_j` is the number of occurrences of `F_u[j]` in the witness. It satisfies `sum_j t_j=15` and `sum_j t_j F_u[j]=R`.

This rule selects the lexicographically first witness. The witness therefore depends only on `R` and the fixed model/factor-base ordering, never on the random masks. That determinism is essential to the mask-uniformity proof.

## 3. Modular left inverse of the rectangular mask matrix

Input: `B` is an `h x f` matrix over `Z/NZ`, with `h=f+2`, and the complete factorization `N=prod ell^e` is known.

For every prime power `ell^e || N`:

1. Reduce `B` modulo `ell`.
2. Perform ordinary Gaussian elimination over `F_ell` to test full column rank `f` and choose `f` pivot rows `I_ell`.
3. If rank is less than `f` for any `ell`, return `FAIL`.
4. The square submatrix `B[I_ell,:]` has determinant not divisible by `ell`, hence is invertible modulo `ell^e`. Compute its inverse modulo `ell^e` and place it in the corresponding columns of a local left inverse `L_ell` (zero in other columns). Then `L_ell B = I_f mod ell^e`.
5. Combine each entry of the `L_ell` by CRT to obtain `L in (Z/NZ)^(f x h)` with `L B=I_f`.

This is a batch-level operation. No row is filtered while it is being collected. For independent uniform rows, its exact success probability is

```
P_left = product_{ell|N} product_{j=3}^{f+2} (1-ell^(-j)) > zeta(2)-1 > 3/5.
```

## 4. Basis attempt: build a certified basis of E(F_p)

### 4.1 One basis attempt

`BasisAttempt(E,N,lambda)`:

1. Sample three independent uniform points `H_1,H_2,H_3 in E(F_p)`. Sample an independent uniform `u in F_p^*`.
2. Construct `E_u`, `phi_u`, and `F=F_u`. If `f<3`, fail this attempt.
3. Transport the three points: `H_i^u=phi_u(H_i)`. Define

   ```
   ev(a_1,a_2,a_3) = a_1*H_1^u + a_2*H_2^u + a_3*H_3^u.
   ```

4. Set `h=f+2`, `s=lambda+9`, and

   ```
   L_basis = ceil(16*C_15*(h+s)).
   ```

5. Collect exactly `h` upper accepted relations, then exactly `s` lower accepted relations, using a single raw-probe counter bounded by `L_basis`:

   **Upper probe** (while fewer than `h` upper rows have been accepted):
   - draw fresh independent `a in (Z/NZ)^3`, `c in (Z/NZ)^f`;
   - set `R=ev(a)+sum_j c_j F_j`;
   - call `Witness15(E_u,R)`; if it returns `NONE`, reject only this target probe and continue;
   - otherwise store the triple `(a,c,t(R))` as the next upper row.

   **Lower probe** (after exactly `h` upper rows have been accepted):
   - draw fresh independent `a in (Z/NZ)^3`;
   - set `R=ev(a)`;
   - call `Witness15(E_u,R)`; if it returns `NONE`, reject only this target probe and continue;
   - otherwise store `(a,t(R))` as the next lower row.

   The only per-probe acceptance condition is `Count15(R)>0`. Do not inspect the current rank, pivot status, determinant, or SNF contribution of the row. If the cap is exhausted before all `h+s` rows are obtained, fail the entire attempt.

6. Form the upper matrices:

   - `A_top`: the `h x 3` matrix whose rows are the stored upper `a_i`;
   - `B_top`: the `h x f` matrix whose rows are `t_i-c_i mod N`.

   Compute one left inverse `L` of `B_top` as in §3. If it fails, fail the entire attempt. Set `C=L*A_top mod N`, an `f x 3` matrix.

7. For each lower row `(a,t)`, compute

   ```
   mu = a - (t*L)*A_top  mod N.
   ```

   Verify directly in `E_u(F_p)` that `ev(mu)=O`. Store all `s` vectors; do not filter them by linear independence or rank.

8. Lift each `mu_i` to its canonical integer representative in `[0,N)^3` and form the full-rank lattice

   ```
   Lambda = span_Z{mu_1,...,mu_s, N*e_1,N*e_2,N*e_3} subset Z^3.
   ```

   Run a deterministic bit-size-controlled Smith normal form routine. It must return positive `d_1|d_2|d_3`, and unimodular matrices `S,T` satisfying `S*M*T=diag(d_1,d_2,d_3)` for the generator matrix `M` of `Lambda`. Independently verify the matrix identity and `det(S),det(T) in {+1,-1}`.

9. Require

   ```
   (d_1,d_2,d_3)=(1,n_1,n_2),  n_1|n_2,  n_1*n_2=N.
   ```

   Otherwise fail the attempt. Set `S_inv=S^(-1)` over `Z`. The candidate points are

   ```
   G_j = sum_{i=1}^3 (S_inv)[i,j] * H_i^u,  j=1,2,3.
   ```

   The first candidate must be `O`; denote the other two by `U_u,V_u`.

10. Independently certify the basis:

    - verify `n_1 | n_2` and `n_1*n_2=N`;
    - verify `ord(U_u)=n_1` and `ord(V_u)=n_2` using the known prime factorization of `N`;
    - if `n_1=1`, these checks suffice;
    - if `n_1>1`, set `W=(n_2/n_1)*V_u`; verify `ord(W)=n_1`, verify `n_1 | p-1`, compute `eta=e_{n_1}(U_u,W)` by the production Weil routine, and verify `eta^(n_1)=1` and `eta^(n_1/ell) != 1` for every prime `ell|n_1`.

    If any check fails, fail the entire attempt. Otherwise return the basis `(U,V,n_1,n_2)` on the original curve by applying `phi_u^(-1)` to `U_u,V_u`, together with the full certificate transcript.

### 4.2 Why the basis attempt has positive constant success probability

Condition on the event that `H_1,H_2,H_3` generate `E_u(F_p)`. This event has probability greater than `1/2` for three independent uniform points in a finite abelian group of rank at most two.

For a good dilation, X263+X264+X265 give a target success probability at least `q_15=1/(4*C_15)` for every independent uniform target. The expected number of raw probes to collect `h+s` successes is at most `4*C_15*(h+s)`. Markov's inequality gives probability at least `3/4` of staying within `L_basis`.

The accepted upper masks are independent uniform rows of `(Z/NZ)^f`; the left inverse succeeds with probability greater than `3/5`. Conditional on the upper history, each lower vector `mu` is an independent uniform element of `K=ker(ev)`. Since `K` is a subgroup of `(Z/NZ)^3`, it needs at most three generators; with `s=lambda+9`, the probability that the lower vectors fail to generate `K` is less than `2^(-lambda)`.

The good-dilation probability is at least `1/8`. Thus

```
delta_basis >= (1/2)*(1/8)*(3/4)*(3/5)*(1-2^(-lambda))
             = 9/320 * (1-2^(-lambda)).
```

The exact basis certificate prevents a false positive if a sampled kernel batch is incomplete or the original three points do not generate the group.

## 5. Coordinate attempt for one arbitrary public point

This stage is run separately for `T=P` and `T=Q`. Every attempt uses a **fresh independent dilation**; the good-dilation property of the basis attempt is not reused.

`CoordinateAttempt(E,N,U,V,n_1,n_2,T)`:

1. If `T=O`, return coordinates `(0,0)`.
2. Draw fresh uniform `u in F_p^*`; construct `E_u`, `phi_u`, and `F_u`. Set `U_u=phi_u(U)`, `V_u=phi_u(V)`, `T_u=phi_u(T)` and `H=(U_u,V_u,O)`. Since `U,V` are a certified basis, `ev:(Z/NZ)^3 -> E_u(F_p)` is surjective.
3. Set `h=f+2` and

   ```
   L_coord = ceil(16*C_15*(h+1)).
   ```

4. Collect exactly `h` upper rows exactly as in steps 5(upper) of §4.1, with fresh independent `a,c`, target `R=ev(a)+cF`, and target-only acceptance. The raw-probe counter is shared with the final target search and bounded by `L_coord`. If fewer than `h` rows are collected within the cap, fail this attempt.
5. Form `A_top`, `B_top`; compute a left inverse `L`. If no left inverse exists, fail this attempt. Set `C=L*A_top mod N`, so `F=ev(C)`.
6. Until the shared cap is exhausted, draw a fresh uniform `a in (Z/NZ)^3` and set

   ```
   R = T_u + ev(a).
   ```

   If `Witness15(E_u,R)=NONE`, continue with another fresh `a`. Otherwise let `t` be its multiplicity row and set

   ```
   z = t*C - a mod N.
   ```

   Verify directly that `T_u = z_1*U_u + z_2*V_u`. If not, raise an internal consistency error and do not return coordinates. If the equality holds, return `(z_1 mod n_1, z_2 mod n_2)` and the verification transcript.

7. If the shared cap is exhausted, fail this attempt. The outer algorithm retries with a fresh independent `u`. Exhaustion is never interpreted as `NO_LOG`.

Correctness of a successful coordinate extraction:

```
T_u = R - ev(a) = t*F - ev(a) = ev(t*C-a) = ev(z).
```

The third generator is `O`, so the first two coordinates give the required expression. The direct group equality is checked before returning.

For a good dilation, each target is uniform in `E_u(F_p)` and succeeds with probability at least `q_15`. There are `h+1` required successful targets. The cap succeeds with probability at least `3/4`; the left inverse succeeds with probability greater than `3/5`; the good dilation occurs with probability at least `1/8`. Hence

```
delta_coord >= (1/8)*(3/5)*(3/4) = 9/160.
```

Therefore the expected number of coordinate attempts for each of `P,Q` is at most `160/9`.

## 6. Final LOG / NO_LOG decision

After independently obtaining verified coordinates

```
P = p_1*U + p_2*V,  Q = q_1*U + q_2*V,
```

solve

```
k*p_1 = q_1 (mod n_1)
k*p_2 = q_2 (mod n_2).
```

For each coordinate `i`:

1. `g_i := gcd(p_i,n_i)`.
2. If `g_i` does not divide `q_i`, return `NO_LOG` with the certificate `(p_i,q_i,n_i,g_i)`.
3. Otherwise put `m_i=n_i/g_i` and compute the unique residue `r_i mod m_i` satisfying

   ```
   (p_i/g_i)*r_i = q_i/g_i (mod m_i).
   ```

   If `m_i=1`, use residue zero.

Combine `k=r_1 mod m_1` and `k=r_2 mod m_2` by generalized CRT. If the residues disagree modulo `gcd(m_1,m_2)`, return `NO_LOG` with that incompatibility certificate. Otherwise return the CRT solution modulo `lcm(m_1,m_2)` as `LOG(k)` only after the independent group check `[k]P=Q`.

For a verified basis, `ord(P)=lcm(m_1,m_2)`. Thus the congruence system is necessary and sufficient. Every `NO_LOG` certificate is deterministic and checkable from the certified basis and the verified coordinates. A failed Count15 query or exhausted cap is only `RETRY`, never `NO_LOG`.

Special case: if `P=O`, return `LOG(0)` iff `Q=O`; otherwise return `NO_LOG` with certificate `P=O, Q!=O`.

## 7. Top-level Las Vegas algorithm

```text
X265(E,P,Q,lambda):
    validate p>3 and nonsingularity
    if p < P_15:
        compute/ enumerate E(F_p)
        test k=0,...,N-1 and return exact LOG or NO_LOG

    N := SchoofCount(E)
    factorization := DeterministicFactor(N)

    if P == O:
        return LOG(0) if Q == O else NO_LOG(P=O,Q!=O)

    repeat:
        basis := BasisAttempt(E,N,lambda)
    until basis is CERTIFIED

    repeat:
        coordsP := CoordinateAttempt(E,N,basis.U,basis.V,
                                     basis.n1,basis.n2,P)
    until coordsP is VERIFIED

    repeat:
        coordsQ := CoordinateAttempt(E,N,basis.U,basis.V,
                                     basis.n1,basis.n2,Q)
    until coordsQ is VERIFIED

    return SolveByGeneralizedCRTAndVerify(P,Q,basis,coordsP,coordsQ)
```

Every loop has a positive lower bound on success probability and each individual attempt has a finite raw-probe cap. This is Las Vegas: the output is always correct, and the expected number of attempts is finite.

## 8. Exact expected attempts and asymptotic bit cost

Let `epsilon_s < 2^(-lambda)` be the failure probability for the lower kernel batch. Then

```
E[attempts_total] <= 320/(9*(1-epsilon_s)) + 320/9.
```

For `lambda>=1`, this is less than `960/9 < 106.67` attempts.

On a good dilation, `f=Theta(p^(1/15))=Theta(N^(1/15))`. The complexity claim in this section assumes fixed `lambda` (or `lambda=polylog(N)`). If `lambda` is treated as a free growing input, retain its dependence: the lower batch has `s=lambda+9` samples, the cap is proportional to `f+lambda`, and the SNF input has `lambda+12` columns. In one capped attempt:

- factor-base construction: `O(f*polylog(p))` bit operations;
- raw upper probes: `O(C_15*f)`; each dense mask costs `O(f*polylog(N))`, total `O(C_15*f^2*polylog(N))`;
- exact Count15 calls: `O(C_15*(f+s)*log(p))` prefix/count invocations, each `p^(o(1))` by the fixed-15 Lean theorem;
- rectangular left inverse and `C=L*A_top`: `O(f^3*polylog(N))` bit operations;
- lower kernel vectors: at most `s` sparse multiplicity rows; polynomial in `f,log N` and dominated by `f^3 polylog(N)`;
- SNF/HNF in dimension 3, exact orders, Miller/Weil, CRT, and final point checks: `polylog(N)` **provided** the production algorithms have the required coefficient/auxiliary-point bounds.

The two coordinate attempts add two further `O(f^3 polylog N)` batches. The deterministic factorization of `N` costs `N^(1/5+o(1))`. Since `f^3=N^(1/5+o(1))`, the intended bound is

```
T(N)=N^(1/5+o(1)),   S(N)<=N^(1/5+o(1)).
```

The memory bound includes the `h x f` rectangular matrix, `O(f^2 log N)` bits, plus the `O(lambda log N)` lower-kernel samples and the SNF workspace. For fixed `lambda` or `lambda=polylog(N)`, these do not change `S(N)<=N^(1/5+o(1))`. For arbitrary `lambda`, state the dependence explicitly. The factorization algorithm's own memory bound must be included when selecting the production implementation.

## 9. SNF/Weil implementation contracts still required

### 9.1 SNF/HNF

The production routine must:

- accept a `3 x (s+3)` integer matrix with entries of `O(log N)` bits;
- return `S,T,D` with `S*M*T=D`, `S,T` unimodular, `D=diag(1,n_1,n_2)`;
- return the full row transformation `S` (not only diagonal invariant factors);
- verify all identities independently;
- prove polynomial bit complexity and polynomial bounds on intermediate coefficient lengths.

The current `x260_snf_basis.py` is explicitly a reference algorithm with uncontrolled coefficient growth. It does not satisfy this contract.

### 9.2 Weil/Miller

The production routine must:

- verify `n_1 | p-1`, `n_1 U_u=n_1 W=O`;
- evaluate the four Miller terms for an auxiliary point `S` avoiding all zeros/poles of all intermediate line/vertical functions;
- use exact finite-field arithmetic and check `eta^(n_1)=1` plus exact order tests for every prime divisor of `n_1`;
- have an explicit expected-time or bounded-time argument for finding a valid auxiliary point.

Write `f_{n,R}` for the Miller function with divisor `n(R)-n(O)`. The shifted-divisor formula used by the reference implementation is
```
eta = f_{n_1,U_u}(W+S) / f_{n_1,U_u}(S)
    * f_{n_1,W}(-S) / f_{n_1,W}(U_u-S).
```
All four values must be finite and nonzero. This is the Weil-pairing evaluation for the translated degree-zero divisors `(W+S)-(S)` and `(U_u-S)-(-S)`; the implementation must preserve this exact orientation (or prove an equivalent formula).

For the affine line/vertical Miller implementation, one factor evaluation `g_{A,B}(T)=line(A,B)(T)/vertical(A+B)(T)` excludes at most five evaluation points: if `A,B,A+B` are nonzero, the numerator line has at most three intersections, the vertical denominator has two finite zeros, one of which is the third line intersection `-(A+B)`, and the point at infinity `O` is the remaining pole; hence the union has size at most five. If `A+B=O`, the factor is vertical and has at most three support points; if `A=O` or `B=O`, the factor is `1`. Thus the bound of five includes the point at infinity and the overlap; it is not merely `3+2` affine points.

A binary Miller evaluation uses at most `2*floor(log2(n_1))` factor evaluations. Four Miller evaluations therefore exclude at most `40*floor(log2(n_1))` choices of the auxiliary translation `S`, since each evaluation argument is a translate or inverse-translate of `S`. For `p>=P_15`, `N` is much larger than `80*floor(log2(n_1))` (and `n_1<=N`), so a uniform random `S` is valid with probability greater than `1/2`; rejection sampling has expected fewer than two trials. The exact shifted-divisor identity and this support count must be formalized alongside the production implementation.

The small-field `x260_pairing_certificates.py` is a referee, not a production implementation: it uses trial factorization and a finite 600-point auxiliary search. The file `x260_independent_pairing_referee.py` reuses the same `weil_pairing` function; its all-pairs ECDLP truth check is independent via exhaustive enumeration, but its pairing checks are not an independent second Miller implementation.

## 9.3 Minimum verifier transcript

A serialized result must carry enough data for a verifier that does not trust the search process:

- `p,A,B,P,Q`, canonical encodings, and the nonsingularity check;
- `N` and the complete prime factorization with primality certificates (or a verifier that independently refactors);
- `n_1,n_2,U,V`, the exact-order scalar-multiplication checks, and `n_1 | p-1`;
- the auxiliary point `S`, the four Miller chains or enough data to recompute them, every finite-field denominator check, `eta`, and its exact-order checks;
- the coordinate witnesses `(p_1,p_2)` and `(q_1,q_2)`, each checked by direct point equality;
- for `NO_LOG`, either `(p_i,q_i,n_i,g_i)` with `g_i=gcd(p_i,n_i)` and `g_i ∤ q_i`, or the two reduced CRT residues and their failed congruence modulo `gcd(m_1,m_2)`.

A final `LOG(k)` still requires the independent check `[k]P=Q`. A `NO_LOG` verifier must check the basis certificate and both coordinate equalities before accepting the divisibility/CRT obstruction.

## 10. Explicit failure semantics

The implementation must use only these statuses:

- `REJECT_TARGET`: this target has `Count15=0`; draw a fresh target.
- `RETRY_ATTEMPT`: cap, left-inverse, SNF, or basis certificate failed; restart the entire relevant attempt with fresh independent randomness.
- `INTERNAL_ERROR`: a deterministic algebraic identity or direct group verification failed; abort and preserve the transcript. Do not silently retry a broken implementation.
- `LOG(k)`: returned only after `[k]P=Q`.
- `NO_LOG(cert)`: returned only from the exact congruence incompatibility certificate or the `P=O,Q!=O` case.

No rank-based row filtering is permitted. No failure to find a decomposition is evidence of `NO_LOG`.

## 11. Reference validation performed for this draft

A new small-field referee, `x265_coordinate_target_referee.py`, tests the corrected direct target-coordinate round with `H=(U,V,O)` and a fresh dilation per attempt. It uses the existing exact but slow DP Count15 oracle.

Result file: `x265_coordinate_target_results.json`.

Observed result: **15/15 coordinate tasks passed on five toy curves** (`p=67,97,101,109,73`), including the neutral point. Scope qualification: this coordinate referee calls the precomputed exact-DP `Count15.get` lookup, so it checks the coordinate algebra and target-only protocol, but it does not exercise per-bit prefix unranking on those 15 tasks. Separately, `x263_independent_m15_results.json` records one `m=15` prefix self-reduction using 91 prefix queries and 368 brute-prefix comparisons for `m=3,4`. None of these tests verifies the asymptotic Count15 machine, the density bound, production SNF/Weil, or large-field performance.

The existing X263 reference pipeline still provides the independent small-field LOG/NO_LOG referee. Its own header explicitly says the DP is `O(m*|E(F_p)|*|F_B|)` precomputation and is not the `p^(o(1))` engine.

## 12. Source anchors

- User's pinned repository: `https://github.com/Slait/fast-ecdlp`.
- Current repository main commit inspected: `966db963c3e43f04bfca9c86a18b1b4ff8e09e2f`.
- Count interface: `v2/lean/ECDLPv2/L109_CountChallenge.lean`.
- Count theorem: `v2/lean/ECDLPv2/L132_Final.lean`.
- Count wrapper: `v2/lean/ECDLPv2/L132_Cc.lean`, `L132_Ora.lean`.
- Engine branches: `v2/lean/ECDLPv2/L132_Eng.lean`, `L132_Br.lean`.
- Proof integration: `X265_main_proof_closure.md`, `X264_elementary_full_algorithm_proof.md`, `X263_main_algorithm_proof.md`.
- Reference pipeline: `x263_independent_m15_pipeline.py`.
- Reference rectangular inverse: `x259_rectangular_referee.py`.
- Reference SNF: `x260_snf_basis.py`.
- Reference pairing: `x260_pairing_certificates.py`.
- Integration audit: `X265_INTEGRATION_AUDIT.md`.

## 13. Final status of limitation 1

This document closes the **specification/pseudocode draft** part of limitation 1, subject to independent mathematical review. It does **not** close the production implementation part. The next implementation gate is to instantiate the certified Count15 command as a callable executable and to implement the exact modular matrix/SNF/Weil contracts above without changing the probabilistic acceptance rules.