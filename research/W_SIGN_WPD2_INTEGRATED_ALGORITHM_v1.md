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
If \(B_0\) is invertible, then \(F=B_0^{-1}A_0V\), hence
\[
\mu:=a_0-rB_0^{-1}A_0=(u,v)\in\ker(\operatorname{ev}).
\]
If \(\mu\ne0\), then \(v\ne0\) and
\[
\boxed{k=-u\,v^{-1}\pmod n.}
\]
Always verify \([k]P=Q\). A singular matrix or zero \(\mu\) causes a fresh round; it never produces a wrong accepted answer.

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

For the final unplanted accepted row, condition on its accepted target. The tag \(a_0\) is uniform in the affine fibre of ev over that target, i.e. a coset of \(\ker(\operatorname{ev})\). The transcript and \(rB_0^{-1}A_0\) are fixed under this conditioning. Subtracting this fixed vector leaves \(\mu\) uniform in the one-dimensional kernel, hence
\[
\Pr[\mu=0\mid B_0\text{ invertible}]=1/n.
\]
Thus a round fails with probability at most \(f/n+1/n\), and the algorithm is Las Vegas after exact final verification.

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

Each row of \(T_0\) has at most m nonzero entries; \(B_0=T_0-\nu I\) has at most m+1. Sparse Wiedemann/Berlekamp–Massey solves \(B_0^Ty=r^T\) using \(O(f)\) sparse matrix-vector products, each \(O(mf)\), for \(O(mf^2)\) field operations and \(O(mf)\) storage. Verify the solution exactly and retry with fresh random projections on a failed verification. A full finite expected bit-cost audit of this solver is still required.

For fixed m, \(f=\Theta(p^{1/m})\), so the algebraic solve is \(p^{2/m+o(1)}\). The target-probe count is as in (9); each probe invokes the \(p^{o(1)}\) decomposition/counting engine.

## 7. secp256k1 finite estimates and limitations

For production \(W=2^{140}\), choose m=8:
\[
\log_2 N_{\rm probes}\le68.0446490611,\qquad
\log_2(mf_{\max}^2)\le65.0021349086.
\]
The interval BSGS scale is \(2^{70}\). This is only a relation-probe count comparison; it is not a total runtime comparison because the finite cost per count-oracle call is not calibrated. The upstream v2 paper explicitly states that its asymptotic crossover is far beyond cryptographic sizes.

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
