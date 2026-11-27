# X268 — End-to-end bit-complexity ledger for X265

**Status:** paper-level conditional complexity theorem completed. It composes the already audited X263/X264/Count₁₅/X265 probability and algebraic statements with deterministic point-counting/factorisation and the X267 Kannan–Bachem normal-form route. The auxiliary-point search bound for the four-Miller-term Weil evaluator is made explicit below.

**Not claimed:** a unified Lean build, a production implementation of the full algorithm, external peer review, or practical performance on cryptographic-size curves.

## 1. The theorem being proved

Fix \(m=15\). Let \(p>3\) be prime, let

\[
E/\mathbb F_p:\quad y^2=x^3+Ax+B,\qquad 4A^3+27B^2\ne0,
\]

and write \(N=\#E(\mathbb F_p)\). Let \(P,Q\in E(\mathbb F_p)\) be arbitrary.

Assume the paper-level X263 first-moment theorem, X264 `DilationNondeg`, the X265 energy/coverage and mask/kernel lemmas, and the exact Count₁₅ theorem audited in `COUNT15_PAPER_AUDIT.md`. Instantiate the relation-lattice normal-form step by the deterministic Kannan–Bachem rectangular HNF followed by \(3\times3\) SNF route of X267.

Then the X265 Las Vegas procedure, with the fresh-dilation coordinate attempts of the integration audit and the auxiliary-point routine of §6 below, returns:

- `LOG(k)` only after verifying \([k]P=Q\);
- `NO_LOG` only after the two verified coordinate congruences are incompatible;
- otherwise it retries, never interpreting a failed witness search as `NO_LOG`.

For fixed \(\lambda\ge1\), or \(\lambda=\operatorname{polylog}N\), its expected bit complexity and working space satisfy

\[
\boxed{T(N)=N^{1/5+o(1)},\qquad S(N)\le N^{1/5+o(1)}.}
\]

This is a conditional composition theorem: the cited X263/X264/Count₁₅ paper-level inputs remain assumptions of this statement, and the full ECDLP goal is not thereby Lean-verified.

## 2. Relating \(p\) and \(N\)

Hasse gives

\[
p+1-2\sqrt p\le N\le p+1+2\sqrt p.
\]

In particular, \(N=\Theta(p)\), \(\log N=\Theta(\log p)\), and

\[
X=\lceil p^{1/15}\rceil=\Theta(N^{1/15}).
\tag{1}
\]

The finite branch \(p<P_{15}\) is handled by exhaustive search. Since \(P_{15}\) is a fixed constant, this does not affect the asymptotic statement.

For \(p\ge P_{15}\), the X263/X264/X265 coverage theorem supplies a set of good dilations of relative size at least \(1/8\). On every dilation, good or bad, \(f=|F_u|\le2X\), because each of the \(X\) candidate abscissae contributes at most two points. On a good dilation the coverage theorem additionally gives \(f>X/2\). Thus

\[
f\le2X\quad\text{always},\qquad f=\Theta(N^{1/15})\quad\text{on good dilations}.
\tag{2}
\]

The upper complexity bounds below use \(f\le2X\) on **every** attempt, including failed/bad dilations; the lower bound \(f>X/2\) is used only in the success-probability and asymptotic-size arguments.

## 3. Point counting and complete factorisation of \(N\)

### 3.1 Computing \(N\)

Schoof's deterministic point-counting algorithm computes \(\#E(\mathbb F_p)\) in \(O((\log p)^9)\) bit operations for \(p>3\). Hence

\[
T_{\rm count}(N)=\operatorname{polylog}N.
\tag{3}
\]

This is a deterministic preprocessing step, performed once.

### 3.2 Factoring \(N\)

Harvey and Hittmeir prove a deterministic algorithm that factors every positive integer \(N\) completely into primes in at most

\[
O\!\left(
\frac{N^{1/5}\log^{16/5}N}{(\log\log N)^{3/5}}
\right)
\]

bit operations. Therefore

\[
\boxed{T_{\rm factor}(N)=N^{1/5+o(1)}.}
\tag{4}
\]

The factorisation is computed once and reused in every basis and coordinate attempt. It supplies:

- the distinct prime divisors needed for exact point-order tests;
- the prime powers \(\ell^e\Vert N\) needed to construct a left inverse over \(\mathbb Z/N\mathbb Z\);
- the prime divisors of \(n_1,n_2\), since \(n_1,n_2\mid N\);
- the prime divisors needed to verify that the Weil value has exact order \(n_1\).

No separate factorisation of \(n_1\) or \(n_2\) is required.

## 4. Exact cost of Count₁₅ and witness extraction

The pinned Lean-v2 result `L132_Final.countingRate_all` gives, for fixed \(m=15\), one deterministic exact counting machine such that for every integer \(k\ge1\) there is a constant \(C_k\) with

\[
T_{\rm Count}(L)\le C_k\,2^{L/k}.
\tag{5}
\]

The Count₁₅ query encodes a fixed number of field elements and a prefix of a 15-point encoding. Each field element uses \(O(\log p)\) bits, and the complete encoding has length

\[
15(\operatorname{Nat.size}(X)+1)=O(\log p).
\]

Thus every Count₁₅ query has input length \(L\le c\log p+O(1)\), for an absolute constant \(c\). Given any \(\varepsilon>0\), choose fixed \(k>c/\varepsilon\). Equation (5) then gives

\[
T_{\rm Count}(p)=O_\varepsilon(p^\varepsilon).
\]

Since this holds for every \(\varepsilon>0\),

\[
\boxed{T_{\rm Count}(p)=p^{o(1)}=N^{o(1)}.}
\tag{6}
\]

The exact count has \(O(\log p)\) output bits: the first 14 points have at most \(2X\) choices each, and the final point is uniquely determined by the target. Prefix-unranking therefore needs at most

\[
15(\operatorname{Nat.size}(X)+1)+1=O(\log p)
\]

Count₁₅ queries to recover the lexicographically first valid witness.

In one capped basis or coordinate attempt, the number of raw target probes is \(O(C_{15}(f+s))\), where \(s=\lambda+9\), and each raw probe makes one empty-prefix count query. Each accepted target causes at most \(O(\log p)\) additional prefix queries. Hence the total number of Count₁₅ invocations in one attempt is

\[
O(C_{15}(f+s)\log p).
\]

As \(C_{15}\) is a fixed constant and \(s=\operatorname{polylog}N\), equations (2) and (6) give

\[
\boxed{T_{\rm Count,total}=N^{1/15+o(1)}.}
\tag{7}
\]

This is a worst-case bound within the explicit raw-probe cap; it is not merely an expected-count estimate.

## 5. Cost of factor-base, mask, and modular-left-inverse operations

### 5.1 Factor-base construction

For a fixed dilation \(u\), there are \(X\) candidate abscissae. Each requires a quadratic-residue test and, when appropriate, one square root in \(\mathbb F_p\). A single certified quadratic nonresidue can be found by uniform sampling: exactly half of the nonzero field elements are nonsquares, so the expected number of trials is 2. Reuse that nonresidue for Tonelli–Shanks on all abscissae.

With standard binary finite-field arithmetic, each residue test and Tonelli–Shanks square root costs \(\operatorname{polylog}p\) bit operations. Therefore, on every dilation,

\[
T_{\rm factorbase}=O(X\operatorname{polylog}p)
\tag{8}
\]

and this is \(O(N^{1/15}\operatorname{polylog}N)\). On good dilations it is also \(O(f\operatorname{polylog}N)\). The number of good-dilation attempts has constant expectation because the good-dilation probability is at least \(1/8\).

### 5.2 Computing each masked target

For an upper probe, compute

\[
R=\operatorname{ev}(a)+\sum_{j=1}^{f}c_jF_j.
\]

There are \(f\) scalar multiplications by integers of \(O(\log N)\) bits. Binary double-and-add and elliptic-curve arithmetic over \(\mathbb F_p\) cost \(\operatorname{polylog}N\) per scalar multiplication. Thus one upper raw probe costs

\[
O(f\operatorname{polylog}N).
\]

The fixed cap is \(O(C_{15}(f+s))=O(C_{15}(X+s))\) raw probes, since \(f\le2X\) on every dilation. Hence all upper masked-target computations cost

\[
O(C_{15}f(f+s)\operatorname{polylog}N)
=O(X^2\operatorname{polylog}N),
\tag{9}
\]

using \(f\le2X\) and \(s=\operatorname{polylog}N=o(X)\). On good dilations this is also \(O(f^2\operatorname{polylog}N)\). Lower probes and coordinate-target probes require only a constant number of scalar multiplications and are cheaper.

### 5.3 Modular left inverse

The upper matrix \(B_{\rm top}\) has \(h=f+2\) rows and \(f\) columns over \(\mathbb Z/N\mathbb Z\). For every prime power \(\ell^e\Vert N\):

1. Gaussian elimination over \(\mathbb F_\ell\) tests full column rank and finds \(f\) pivot rows.
2. The corresponding \(f\times f\) minor has determinant a unit modulo \(\ell^e\), so it is invertible modulo \(\ell^e\).
3. Its inverse gives a local left inverse \(L_\ell\).
4. Entrywise CRT combines the local inverses into \(L\) with \(LB_{\rm top}=I_f\pmod N\).

There are at most \(\log_2N\) distinct prime divisors. Naive elimination costs \(O(f^3)\) ring operations per prime power, and each ring operation on \(O(\log N)\)-bit residues costs \(\operatorname{polylog}N\). Therefore, on every attempt,

\[
T_{\rm left-inverse}=O(f^3\operatorname{polylog}N)
=O(X^3\operatorname{polylog}N)
=N^{1/5+o(1)},
\tag{10}
\]

whenever the left-inverse routine is reached. On good dilations \(f=\Theta(X)\), so this bound is attained at the stated scale.

The exact success probability, for the fixed batch of \(h=f+2\) iid uniform rows, is

\[
P_{\rm left}
=\prod_{\ell\mid N}\prod_{j=3}^{f+2}(1-\ell^{-j})
> \zeta(2)-1>3/5.
\]

The rank test occurs once after the complete batch. No row is accepted or rejected according to its current rank.

### 5.4 Lower kernel batch and relation SNF

There are \(s=\lambda+9=\operatorname{polylog}N\) lower kernel samples. Computing each \(\mu_i=a_i-(t_iL)A_{\rm top}\) costs \(O(f\operatorname{polylog}N)\), so the complete lower batch costs \(O(sf\operatorname{polylog}N)\), below (10).

The relation matrix is

\[
M=[\mu_1\ \cdots\ \mu_s\mid NI_3]
\in\mathbb Z^{3\times(s+3)}.
\]

Its binary input length is \(O((s+3)\log N)=\operatorname{polylog}N\). By X267, the proof-level Kannan–Bachem rectangular HNF followed by \(3\times3\) SNF costs \(\operatorname{polylog}N=N^{o(1)}\) bit operations. The existing custom Python producer is not thereby certified; the algorithm specification must use the Kannan–Bachem route or separately prove the custom routine's bounds.

Combining (8)–(10), lower-sample construction, and X267, all relation-processing work in one capped attempt, whether or not its dilation is good, is bounded by

\[
\boxed{T_{\rm relations}=O(X^3\operatorname{polylog}N)
=N^{1/5+o(1)}.}
\tag{11}
\]

## 6. Missing Miller/Weil auxiliary-point bound — now explicit

The noncyclic basis certificate computes

\[
e_n(P,Q),\qquad n=n_1>1,
\]

where \(P=U\), \(Q=(n_2/n_1)V\), and both are rational \(n\)-torsion points. Since \(n\mid p-1\), the Weil pairing takes values in \(\mathbb F_p^\times\).

Use the shifted-divisor formula

\[
e_n(P,Q)=
\frac{f_{n,P}(Q+R)}{f_{n,P}(R)}
\cdot
\frac{f_{n,Q}(-R)}{f_{n,Q}(P-R)},
\tag{12}
\]

for an auxiliary point \(R\) for which all four Miller evaluations are defined and nonzero. Here \(\operatorname{div}(f_{n,P})=n(P)-n(O)\), and similarly for \(Q\). The verifier receives \(R\), first checks \(R\notin\{O,P,-Q,P-Q\}\), recomputes the four Miller values, and checks (12) and the exact order of the result. The shifted formula and its four excluded shifts are the standard Miller/Weil formula; see the cited pairing algorithm in the sources.

### Lemma 6.1 — number of bad auxiliary points

For fixed \(P,Q,n\), at most

\[
\boxed{40\lfloor\log_2n\rfloor+4}
\tag{13}
\]

points \(R\in E(\mathbb F_p)\) can cause one of the four Miller evaluations in (12) to encounter a zero, a pole, or an excluded point at infinity, when the implementation rejects any such intermediate line-factor evaluation.

**Proof.**

A Miller doubling/addition step evaluates a line quotient

\[
g_{A,B}(T)=\frac{\ell_{A,B}(T)}{v_{A+B}(T)}.
\]

If \(A,B\ne O\) and \(A+B\ne O\), the numerator line meets the cubic \(E\) in at most three points and the denominator vertical line meets it in at most two points. Therefore the union of their zero/pole supports contains at most five points of \(E(\overline{\mathbb F}_p)\), and hence at most five rational points. If \(A+B=O\), the vertical-line case has at most three support points. If \(A=O\) or \(B=O\), the implementation uses the constant factor 1 and contributes no bad points.

The binary Miller loop has \(\lfloor\log_2n\rfloor\) bit rounds after the leading bit, with at most one doubling factor and one addition factor per round. Thus one Miller evaluation uses at most \(2\lfloor\log_2n\rfloor\) line factors. Formula (12) uses four Miller evaluations, hence at most \(8\lfloor\log_2n\rfloor\) factors in total.

The four evaluation arguments are \(Q+R\), \(R\), \(-R\), and \(P-R\). Each is a bijection of \(E(\mathbb F_p)\) as a function of \(R\). The preimage of the support of one line factor therefore contains at most five auxiliary points. The union bound gives at most \(40\lfloor\log_2n\rfloor\) points. Also reject the standard four exceptional shifts \(R\in\{O,P,-Q,P-Q\}\) from the shifted-divisor Weil formula. This includes every case in which one of the four evaluation arguments is \(O\). Adding these at most four points gives (13). \(\square\)

### Corollary 6.2 — expected auxiliary search time

In the asymptotic branch \(p\ge P_{15}\), we have \(N\ge1024\). Since \(n\le N\),

\[
40\lfloor\log_2n\rfloor+4
\le40\log_2N+4
\le N/2.
\]

The final inequality holds at \(N=1024\) and the difference \(N-80\log_2N-8\) is increasing thereafter. Thus at least half of all \(R\in E(\mathbb F_p)\) are valid auxiliary points.

A uniform-point sampler therefore needs at most two candidate points in expectation. By Hasse, for \(p\ge16\),

\[
N\ge p/2,\qquad
\frac{N}{2p+1}>\frac15.
\]

The token sampler for a uniform curve point consequently needs fewer than five tokens in expectation. Tonelli–Shanks, with one previously found nonresidue reused throughout the field, and each Miller evaluation use \(\operatorname{polylog}p\) bit operations.

Therefore the auxiliary search plus the four Miller evaluations has expected cost

\[
\boxed{T_{\rm Weil}=\operatorname{polylog}N.}
\tag{14}
\]

This search is Las Vegas: it retries only when an evaluation is undefined or zero, and it never changes a failed pairing attempt into a false certificate. The exact-order test for the resulting value uses the known prime divisors of \(n\) and at most \(O(\log n)\) modular exponentiations, also polylogarithmic.

The small-field direct branch handles \(p<P_{15}\), so no separate small-\(N\) auxiliary-point bound is needed.

**Implementation boundary.** The older X260 small-field referee `x260_pairing_certificates.py` has a finite loop cap of 600 and is not the proof-level routine. The X265 producer `x265_snf_weil.py` already supports the unbounded Las Vegas mode `max_aux_attempts=None`; the patch accompanying X268 makes it explicitly reject all four standard shifts, updates its bad-point bound to (13), and fails closed if a valid shifted ratio is not an n-th root of unity. A finite cap remains permissible only if the outer success probability includes its explicit non-exhaustion probability.

## 7. Probability of attempts and expected total number

The paper-level probability analysis gives, for \(\epsilon_s<2^{-\lambda}\),

\[
\delta_{\rm basis}\ge
\frac9{320}(1-\epsilon_s),
\qquad
\delta_{\rm coord}\ge\frac9{160}.
\]

The basis attempt includes the good-dilation event, the fixed capped collection of \(h+s\) successful targets, the one-shot left-inverse test, and generation of the kernel. The independent Weil auxiliary search terminates almost surely and has expected constant many trials, so it does not reduce this success probability.

Each of the two coordinate stages uses a fresh independent dilation and a shared cap for \(h+1\) target successes. Its success probability is at least \(9/160\). Therefore

\[
\mathbb E[\#\text{basis attempts}]
\le\frac{320}{9(1-\epsilon_s)},
\]

and

\[
\mathbb E[\#\text{coordinate attempts for }P,Q]
\le\frac{320}{9}.
\]

For \(\lambda\ge1\), \(\epsilon_s<1/2\), giving

\[
\boxed{
\mathbb E[\#\text{all attempts}]
<
\frac{960}{9}<106.67.
}
\tag{15}
\]

The bound is independent of \(N\). All failed attempts are detected by a cap, a failed left inverse, or a failed exact group-basis certificate. A failed coordinate witness search returns `RETRY`, never `NO_LOG`.

## 8. Complete bit-cost ledger

Let \(X=\Theta(N^{1/15})\) always and \(f\le2X\) always; on good dilations \(f=\Theta(X)\). The global preprocessing costs and per-capped-attempt costs are:

| Component | Bit cost | Frequency |
|---|---:|---|
| Schoof point count | \(\operatorname{polylog}N\) | once |
| Complete deterministic factorisation of \(N\) | \(N^{1/5+o(1)}\) | once |
| Factor-base construction | \(O(X\operatorname{polylog}N)\) | per attempt |
| Count₁₅ probes and witness extraction | \(N^{1/15+o(1)}\) | per attempt |
| Upper mask generation \(cF\) | \(O(X^2\operatorname{polylog}N)\) | per attempt |
| Modular left inverse of \((f+2)\times f\) matrix | \(O(X^3\operatorname{polylog}N)\) | per attempt |
| Lower kernel sample construction | \(O(sX\operatorname{polylog}N)\) | per attempt |
| Relation HNF/SNF via X267 | \(\operatorname{polylog}N\) | per basis attempt |
| Point-order checks, Miller/Weil, CRT, final scalar check | \(\operatorname{polylog}N\) expected | per basis/coordinate attempt |

Since \(f\le2X\), every attempt's matrix step costs at most \(O(X^3\operatorname{polylog}N)\), and on good dilations \(f=\Theta(X)\). In particular \(X^3=\Theta(N^{3/15})=\Theta(N^{1/5})\), so the matrix left-inverse step is bounded by \(N^{1/5}\operatorname{polylog}N\). The factorisation cost is \(N^{1/5+o(1)}\). Every other contribution is smaller:

\[
f^2\operatorname{polylog}N=N^{2/15+o(1)},
\]

\[
f\cdot N^{o(1)}=N^{1/15+o(1)}.
\]

The number of attempts has bounded expectation by (15), so multiplying the per-attempt costs by the expected attempt count changes only a constant factor. The one-time factorisation cost is not repeated.

Consequently

\[
\boxed{T(N)=N^{1/5+o(1)}.}
\]

### Space

The largest explicit relation/mask arrays have \(O(f^2)\) entries of \(O(\log N)\) bits. Since \(f\le2X\) on every dilation,

\[
S_{\rm masks}=O(X^2\log N)=N^{2/15+o(1)}.
\]

The factor-base storage is \(O(X\log N)\), and the compact HNF/SNF certificate is polylogarithmic by X267. A deterministic Turing machine using \(T\) steps can visit at most \(O(T)\) tape cells; hence the factorisation and Count₁₅ subroutines use at most their time bounds in space. Therefore

\[
\boxed{S(N)\le N^{1/5+o(1)}.}
\]

## 9. What this closes — and what it does not

**Closed at paper level by X268:**

- exact \(p\)-to-\(N\) scale conversion;
- Schoof point-counting cost;
- deterministic complete factorisation cost and its one-time reuse;
- Count₁₅ input length, exact witness extraction, and total query count;
- factor-base, mask, and modular-left-inverse costs;
- relation HNF/SNF contribution using the X267 proof-aligned Kannan–Bachem route;
- expected auxiliary-point search for the four-Miller-term Weil evaluator;
- fresh-dilation P/Q attempts and their constant expected number;
- the full sum of costs and the space bound.

**Still open:**

1. A unified Lean development of X263 + X264 + Count₁₅ + X265 + X266 + X267 + X268.
2. A production executable that uses the proof-aligned Kannan–Bachem routine and the explicit Miller auxiliary search; the existing Python code is a reference implementation.
3. External independent mathematical review of the X263/X264 geometric arguments and the full composition.
4. A production cryptographic RNG/constant-time implementation. The theorem uses ideal independent uniform bits; a CSPRNG deployment gives a computational pseudorandomness claim, not literal information-theoretic uniformity.

Thus X268 closes the **paper-level global bit-cost accounting conditional on the earlier mathematical lemmas**. It does not close `ECDLP-MAIN` as a single formally verified or production-executed theorem.

## 10. Sources

1. René Schoof, *Elliptic Curves Over Finite Fields and the Computation of Square Roots mod p*, Mathematics of Computation 44 (1985), 483–494. The paper states a deterministic point-counting algorithm taking \(O(\log^9q)\) bit operations for characteristic not 2 or 3: https://pages.cs.wisc.edu/~cs812-1/Schoof85.pdf
2. David Harvey and Markus Hittmeir, *A log-log speedup for exponent one-fifth deterministic integer factorisation*, Mathematics of Computation 91 (2022), 1367–1379. The deterministic complete-factorisation bound is \(O(N^{1/5}\log^{16/5}N/(\log\log N)^{3/5})\) bit operations: https://arxiv.org/abs/2105.11105
3. Kannan and Bachem, *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, SIAM J. Comput. 8(4) (1979), DOI 10.1137/0208040.
4. Shifted-divisor Weil formula with excluded shifts \(\{O,P,-Q,P-Q\}\): https://www.siam.org/media/wr5lq3ul/s153290r.pdf and https://static.aminer.org/pdf/PDF/000/097/531/a_remark_on_implementing_the_weil_pairing.pdf.
5. Pinned Count₁₅ source: `kaarelkaarelson/fast-ecdlp`, commit `d1deb5abe008e981206ed58cbd83012b6afc3740`, especially `v2/lean/ECDLPv2/L132_Final.lean`.
6. Internal inputs: `COUNT15_PAPER_AUDIT.md`, `X265_main_proof_closure.md`, `X265_INTEGRATION_AUDIT.md`, `X265_PROBABILITY_SAMPLING_MASK_AUDIT.md`, `X267_SNF_BIT_COMPLEXITY_THEOREM_v1.md`, and `X266_KERNEL_GROUP_BASIS_THEOREM.md`.