# W-SIGN + W-PD2 — integrated prime-order interval algorithm

This is the integrated algorithmic statement obtained by combining the one-sided factor-base coverage argument with the two-axis planted-diagonal reduction. It is a conditional paper-level proof, not a practical implementation claim.

## 1. Input and interval wrapper

Let \(G=\langle P\rangle\) be a cyclic group of prime order \(n\), let \(Q=[k]P\), and suppose
\[
A\le k<A+W<n.
\]
Compute
\[
Q'=Q-[A]P=[x]P,\qquad 0\le x<W.
\]
Solve the full DLP \(x=\log_P Q'\), verify \([x]P=Q'\), check \(x<W\), and return \(k=A+x\). The shift adds \(O(\log n)\) group operations.

For secp256k1, \(G=E(\mathbb F_p)\), \(P\) is the standard generator, and \(n\) is prime.

## 2. One-sided factor base and exact decomposition oracle

Choose \(m\), \(B=\lceil p^{1/m}\rceil\), \(T=\{1,\ldots,B-1\}\), \(X=B-1\). For a random dilation \(u\in\mathbb F_p^\times\), work on
\[
E_u:y^2=x^3+u^6\cdot7.
\]
Let
\[
F_u^+=\{(x,y)\in E_u(\mathbb F_p):x\in T,\ 0<y\le(p-1)/2\}
=\{F_1,\ldots,F_f\}.
\]
The x-projection is injective. The count oracle is the upstream exact generic-decomposition count/search machine with its input wires permuted so all m sign bits precede all x-bits. Prefix \(0^m\) forces every summand into \(F_u^+\). The wire permutation preserves the arithmetic network size and the \(p^{o(1)}\) count bound; its paper-level proof is in W_SIGN_COUNT_ORACLE_PERMUTATION.md. The current upstream Lean source has not yet formalized this relabelled instance.

The oracle, on a target \(R\), returns a generic ordered decomposition
\[
R=\sum_{j=1}^m F_{t_j},\qquad t_j\in\{1,\ldots,f\},
\]
or failure. Repeated labels are allowed. Its multiplicity row has at most m nonzero entries. It is deterministic and target-only.

## 3. Planted-diagonal construction

Define
\[
\operatorname{ev}(a,b)=[a]P+[b]Q.
\]
Because \(P\) generates \(G\), ev is surjective and
\[
\ker(\operatorname{ev})=\{(u,v)\in\mathbb F_n^2:u+kv=0\}
=\langle(-k,1)\rangle.
\]

Choose \(\nu\) uniformly in \(\mathbb F_n\). For each \(i=1,\ldots,f\), independently sample \(a_i=(a_{i1},a_{i2})\) uniformly in \(\mathbb F_n^2\), and query the decomposition oracle on
\[
R_i=\operatorname{ev}(a_i)+[\nu]F_i.
\]
Repeat with fresh tags until an accepted generic decomposition is returned. Let \(t_i\in\mathbb Z_{\ge0}^f\) be its multiplicity row.

After the f planted rows, sample \(a_0=(a_{01},a_{02})\) uniformly and query the oracle on \(R_0=\operatorname{ev}(a_0)\) until one accepted decomposition returns the row \(r\).

Let \(T_0\) be the f-by-f matrix with rows \(t_i\), let \(A_0\) be the f-by-2 matrix with rows \(a_i\), and set
\[
B_0=T_0-\nu I_f.
\]
Oracle soundness gives the exact group identities
\[
B_0F=A_0V,\qquad rF=a_0V,\qquad V=(P,Q)^T.
\]
Do not form \(B_0^{-1}\). Instead solve the sparse linear system
\[
B_0^T y=r^T.
\]
If the solver returns a vector with an exactly verified residual, then \(y^TB_0=r\). Multiplying \(B_0F=A_0V\) by \(y^T\) gives \(rF=y^TA_0V\). The final row gives \(rF=a_0V\), so
\[
\mu:=a_0-y^TA_0=(u,v)\in\ker(\operatorname{ev}).
\]
If \(\mu\ne0\), then \(v\ne0\) and
\[
\boxed{k=-u\,v^{-1}\pmod n.}
\]
Always verify \([k]P=Q\). A singular \(B_0\) may still admit a verified solution and is then safe; if no verified solution is found, or \(\mu=0\), retry. No unverified solution is ever accepted.

## 4. Failure probabilities

For every attempted planted or final query, the tag pair is uniform in \(\mathbb F_n^2\). Since ev is surjective, \(\operatorname{ev}(a)\) is uniform in \(G\); adding the fixed shift \([\nu]F_i\) preserves uniformity. Thus the target presented to the deterministic target-only oracle is uniform, independently of \(\nu\). The transcript distribution is therefore independent of \(\nu\), by induction over the adaptive accepted rows.

Conditional on a transcript, \(T_0\) is fixed and
\[
\det(T_0-\nu I)=(-1)^f\chi_{T_0}(\nu),
\]
where \(\chi_{T_0}\) is monic of degree f. It has at most f roots in \(\mathbb F_n\), so
\[
\Pr[B_0\text{ singular}]\le f/n.
\]
This is a sufficient bound for solvability: whenever \(B_0\) is nonsingular, the system \(B_0^Ty=r^T\) has a unique solution. A singular matrix may also be consistent; any solution with an exactly verified residual is safe by the algebra above.

For the final unplanted accepted row, condition on its accepted target. The tag \(a_0\) is uniform in the affine fibre of ev over that target, i.e. a coset of \(\ker(\operatorname{ev})\). Conditional on the transcript and on the solver's independent random projection coins, the returned \(y\) is fixed. Subtracting \(y^TA_0\) leaves \(\mu\) uniform in the one-dimensional kernel, hence \(\Pr[\mu=0]=1/n\). For nonsingular \(B_0\), standard Wiedemann succeeds with probability at least \(1-f/n\) per random projection; use a fixed number of projections, verify each candidate exactly, and retry the round if none verifies. The per-round success probability is therefore at least \((1-f/n)(1-(f/n)^R)(1-1/n)\) for R projections, ignoring any additional success on singular-but-consistent matrices. The algorithm is Las Vegas after exact final verification.

## 5. Expected relation-probe count

Let \(\mathcal E_u^+\) be the one-sided m-fold additive energy. The primitive-relation argument gives
\[
\overline{\mathcal E^+}
:=\frac1{p-1}\sum_{u\ne0}\mathcal E_u^+
\le
M_+(m,X,p)
=
m!X^m+\frac{2D'_mX^{2m}}{p-1},
\qquad D'_m=(2m-1)2^{2m-2}.
\]
The proof is in W_SIGN_ONE_SIDED_FACTOR_BASE_v1.md and is conditional on the upstream A=0 Semaev/dilation nondegeneracy input.

For a size-good dilation, with \(f_{\min}=(1-\epsilon)X/2\), the generic nonzero sumset has at least \(f^{2m}/(4\mathcal E_u^+)\) elements. Therefore the expected raw target probes to collect f+1 accepted rows are at most
\[
\frac{4n\mathcal E_u^+}{f_{\min}^{2m-1}}
\left(1+\frac1{f_{\min}}\right).
\]
The upstream factor-base variance bound gives a size-good fraction
\[
\rho\ge1-\frac{13+2/X}{\epsilon^2X}.
\]
Sampling u until it is size-good and averaging the energy over this set yields
\[
\boxed{
N_{\rm probes}
\le
\frac{4nM_+(m,X,p)}
{\rho f_{\min}^{2m-1}}
\left(1+\frac1{f_{\min}}\right).
}
\]

## 6. Sparse linear algebra

Each row of \(T_0\) has at most m nonzero entries; \(B_0=T_0-\nu I\) has at most m+1. Sparse Wiedemann/Berlekamp–Massey solves \(B_0^Ty=r^T\). Put \(A=B_0^T\), \(b=r^T\), choose a random projection vector \(w\), and form \(s_j=w^TA^jb\) for \(0\le j<2f\). Berlekamp–Massey returns \(C_0=1,C_1,\ldots,C_L\). If \(C_L\ne0\), form
\[
y=-C_L^{-1}\sum_{j=0}^{L-1}C_{L-1-j}A^jb,
\]
then verify \(Ay=b\) exactly. On a nonsingular A, the standard Wiedemann projection succeeds with probability at least \(1-f/n\); use R independent projections, so the probability all fail is at most \((f/n)^R\). The exact residual check makes the solver Las Vegas: an incorrect candidate is rejected, never used. A streaming/two-pass implementation stores the sparse rows plus \(O(f)\) field-element scratch; it must not retain all Krylov vectors. The upstream toy solver currently stores \(f+1\) full vectors and therefore uses \(O(f^2)\) memory; that implementation is not production-suitable. A new streaming toy referee is in research/toy_w_sign_one_sided_wiedemann.py. A full finite expected bit-cost audit of this solver is still required.

For fixed m, \(f=\Theta(p^{1/m})\), so the algebraic solve is \(p^{2/m+o(1)}\). The target-probe count is as in (9). Each target probe is one full L61 decomposition-driver invocation, not one raw count-engine call. The L61 source bound uses \(m(L+1)+1\) driver rounds, and each round can make two count-oracle zero tests (first the 0-child, then the 1-child if needed). Here \(L\) is the L61 Bool-alphabet input length. Its encoding is prefix-first and block-codes each bit as two bits plus a terminator. For secp256k1, with the m=8 sign prefix, the worst-case length is at most \(L=1{,}564\): prefix block 17; p block 513; a=0 block 1; b=7 block 7; target x and y blocks at most 513 each. Thus m=8 requires at most \(2(8(1{,}564+1)+1)=25{,}042\) raw count-engine calls per decomposition. The \(2^{68.044649}\) target-probe estimate therefore corresponds to at most about \(2^{82.6557}\) raw count-engine evaluations, before charging the cost of each evaluation. The asymptotic factor is only \(O(mL)=p^{o(1)}\), but the finite constant is significant.

## 7. secp256k1 finite estimates and limitations

For production \(W=2^{140}\), choose m=8:
\[
\log_2 N_{\rm probes}\le68.0446490611,\qquad
\log_2(mf_{\max}^2)\le65.0021349086.
\]
Here \(f_{\max}\approx2.1491\cdot10^9\). Storing m 32-bit factor-base indices per row alone takes about 68.8 GB (64 GiB); row/solver vectors each contain about 2.15 billion 256-bit field elements, about 68.8 GB apiece. The two tag coordinates per planted row add another roughly 137.5 GB if stored directly; they can instead be replayed from a recorded random tape/seed plus accepted-attempt counters, or streamed from disk. Thus even an O(mf)-memory implementation needs a multi-hundred-GB memory budget once Krylov/Berlekamp–Massey state, tag recovery, and sparse relation rows are included. The upstream toy Wiedemann code stores all Krylov vectors and is O(f^2) memory; it must be replaced by a streaming two-pass solver. The interval BSGS scale is \(2^{70}\). This is only a relation-probe count comparison; it is not a total runtime comparison because the finite cost per count-oracle call is not calibrated. The upstream v2 paper explicitly states that its asymptotic crossover is far beyond cryptographic sizes.

For test \(W=2^{67}\), m=17 is the first value whose explicit \(O(mf^2)\) field-operation estimate falls below \(2^{33.5}\), but its expected probe count is \(\log_2 N_{\rm probes}\le100.6162690291\). This branch does not solve the test interval.

## 8. Proof closure checklist

1. Reconstruct the upstream \(A=0\) Semaev nondegeneracy proof, including the \(\omega\)-orbit exception, for \(X<p/3\).
2. Prove the exact factor-base variance bound with \(c_F=13+2/X\).
3. Formalize or include the sign-first wire-permutation count-oracle lemma.
4. Audit the sparse solver's exact expected bit cost and memory.
5. Reproduce both toy referees from the committed scripts.
6. Calibrate the finite count-oracle cost; without this, no practical speedup claim is permitted.
7. Only after all six items close, prepare Final.md.

**Current status:** planted-diagonal algebra is manually proved conditional on prime group order and exact oracle soundness; one-sided energy and expected-probe bounds are manually derived conditional on upstream analytic lemmas; sign-first count-oracle reduction is paper-level but not Lean-integrated; finite total runtime remains unproved.
