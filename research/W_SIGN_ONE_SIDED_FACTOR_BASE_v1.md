# W-SIGN v1 — one-sided factor base and primitive-relation energy bound

**Status: promising paper-level branch; not a completed algorithm.** This note records a new manual derivation and a toy referee. The key new estimate is conditional on the upstream Semaev/dilation nondegeneracy theorem for the \(A=0\) curve family and on a small extension of the count-oracle input encoding.

## 1. Target and notation

For secp256k1 write
\[
E/\mathbb F_p:\quad y^2=x^3+7,\qquad \#E(\mathbb F_p)=n,
\]
where \(p\) and \(n\) are the standard secp256k1 field and prime group orders. We use:
- \(p\equiv1\pmod3\);
- \(\left(\frac7p\right)=-1\);
- \(n\) is odd and prime.

Fix \(m\ge2\), let \(B=\lceil p^{1/m}\rceil\), and set
\[
T=\{1,\ldots,B-1\},\qquad X=|T|=B-1.
\]
For \(u\in\mathbb F_p^\times\), use the isomorphic model
\[
E_u:\quad y^2=x^3+u^6\cdot7.
\]
Since \(u^6\) is a square, \(x=0\) is never an affine point on any \(E_u\): \(\left(\frac{u^6 7}{p}\right)=\left(\frac7p\right)=-1\). Thus the count oracle's bound \(x<B\) automatically agrees with \(T\), despite the binary encoding allowing zero.

## 2. One-sided factor base

For each \(u\), define
\[
F_u^+=\{(x,y)\in E_u(\mathbb F_p):x\in T,\ 0<y\le(p-1)/2\}.
\]
Because the group has odd prime order, there is no rational point with \(y=0\). For every \(x\in T\) for which the right-hand side is a square, exactly one of the two points \((x,\pm y)\) lies in \(F_u^+\). Hence:
- \(x:F_u^+\to T\) is injective;
- if \(F_u\) denotes the symmetric factor base containing both signs, then
  \[
  |F_u|=2|F_u^+|.
  \]

The upstream count-string sign bit is \(1\) iff \((p-1)/2<y\). Thus sign bit \(0\) selects exactly \(F_u^+\).

**Count-oracle extension needed.** The current source serializes each point as its \(x\)-bits followed by its sign bit. Define instead a fixed serialization with all \(m\) sign bits first, followed by the \(m\) \(x\)-blocks. The prefix \(0^m\) then restricts all summands to \(F_u^+\) in one count query. The arithmetic constraint network is unchanged; only its input wires are permuted. Network size, maximum degree, and gate constraints are invariant under this fixed wire permutation, so the same \(p^{o(1)}\) counting bound should follow by relabelling the input wires. This relabelling lemma is not yet added to the upstream Lean development and must be written explicitly before claiming a closed oracle proof.

## 3. Primitive-relation lemma: the key improvement

Let \(x_1,\ldots,x_m,z_1,\ldots,z_m\in T\). For a fixed \(u\), write \(P_u(x)\) for the unique point of \(F_u^+\) with abscissa \(x\), when it exists. Suppose
\[
\sum_{i=1}^m P_u(x_i)=\sum_{j=1}^m P_u(z_j).
\tag{1}
\]

If the two multisets \(\{x_i\}\) and \(\{z_j\}\) are equal, call the tuple *trivial*. There are at most
\[
m!X^m
\tag{2}
\]
such ordered \(2m\)-tuples.

Now suppose the multisets differ. For each \(a\in T\), put
\[
c_a=\#\{i:x_i=a\}-\#\{j:z_j=a\}.
\]
Then not all \(c_a\) vanish and \(\sum_a c_a=0\). Let \(g=\gcd\{|c_a|:c_a\ne0\}\). Since \(1\le g\le m<n\) and \(n\) is prime, multiplication by \(g\) is invertible in the group. Equation (1) therefore implies
\[
\sum_a (c_a/g)P_u(a)=O.
\tag{3}
\]

Make a signed list \(Z\) by taking \(|c_a|/g\) copies of \(a\), with sign \(\operatorname{sgn}(c_a)\). Its length \(r\) is even, \(2\le r\le2m\). The gcd of its multiplicities is \(1\), so at least one multiplicity is odd. Thus \(Z\) is not a trivial even-multiplicity tuple.

Pad \(Z\) to length \(2m\) by adding \((2m-r)/2\) cancelling pairs \((a_0,+),(a_0,-)\), where \(a_0\) is any abscissa already occurring in \(Z\). For every \(u\) for which (1) holds, the required point at \(a_0\) exists, so the padded tuple is a valid nontrivial \(2m\)-point relation. Adding pairs preserves the odd multiplicity, hence preserves nontriviality.

Consequently, the upstream DilationNondeg bound applies to this padded tuple. If its Semaev polynomial has degree at most
\[
D'_m=(2m-1)2^{2m-2}
\tag{4}
\]
in \(s=u^{-2}\), then it has at most \(D'_m\) roots \(s\), and at most \(2D'_m\) corresponding dilation parameters \(u\).

**Conclusion.** For every fixed nontrivial ordered \(2m\)-tuple of abscissae, at most \(2D'_m\) dilations can make its one-sided group relation hold. This extends the nondegeneracy bound from tuples that are directly nontrivial in the TrivL sense to every nontrivial left/right multiset relation.

The degree in (4) follows from the weighted degree \(w_{2m}=(2m-1)2^{2m-1}\) of the Semaev polynomial, with \(x\) of weight \(2\), after substituting \(x_i=s t_i\) and fixing \(A=0,B=7\).

For \(A=0\), the upstream paper has a special nondegeneracy argument for tuples containing an \(\omega\)-pair, where \(\omega^3=1\). The only identically-zero full-orbit exception is excluded by \(X<p/3\): if \(a,\omega a,\omega^2a\) all had representatives in \([1,X]\), their integer representatives would sum to a positive multiple of \(p\) smaller than \(p\), impossible. This \(A=0\) classification is paper-level upstream input, not yet independently formalized here.

## 4. One-sided energy bound

Define the ordered \(m\)-fold additive energy
\[
\mathcal E_u^+
=
\#\left\{(\mathbf P,\mathbf Q)\in(F_u^+)^m\times(F_u^+)^m:
\sum_iP_i=\sum_jQ_j\right\}.
\]

For each ordered \(2m\)-tuple of abscissae:
- if the left and right multisets agree, it contributes for at most every \(u\), and (2) bounds the number of such tuples by \(m!X^m\);
- otherwise, the primitive-relation lemma bounds the number of contributing \(u\)'s by \(2D'_m\);
- for a fixed \(u\) and abscissa tuple there is at most one lift to points of \(F_u^+\), because the \(x\)-projection is injective.

Summing over \(u\in\mathbb F_p^\times\) gives the new bound
\[
\boxed{
\frac1{p-1}\sum_{u\ne0}\mathcal E_u^+
\le
M_+(m,X,p)
:=
m!X^m+\frac{2D'_mX^{2m}}{p-1}.
}
\tag{5}
\]

This replaces the symmetric-base estimate's large \(4^m\) lift factor and \((2m-1)!!\) pairing count. The improvement is not obtained by simply halving the old factor base: it depends on the one-sided base and the primitive-relation reduction above.

## 5. Generic nonzero sums and coverage

Because \(x:F_u^+\to T\) is injective, the number of non-generic ordered \(m\)-tuples is at most
\[
2(m-1)f_u^{m-1},\qquad f_u=|F_u^+|.
\]
Indeed, for each partial-sum index:
- the condition that the partial sum is \(O\) determines the final point in at most one way;
- the condition that the partial-sum abscissa equals the next abscissa determines the next factor-base point in at most one way.

Among all tuples, at most \(f_u^{m-1}\) have total sum \(O\), because the last point is uniquely determined by the first \(m-1\). Hence the number of generic tuples with nonzero total is at least
\[
f_u^m-(2m-1)f_u^{m-1}\ge f_u^m/2
\]
whenever \(f_u\ge2(2m-1)\).

Let \(G_u^+\) be the set of nonzero group elements having a generic decomposition into \(m\) points of \(F_u^+\). Cauchy–Schwarz and the energy definition give
\[
\boxed{
|G_u^+|\ge\frac{f_u^{2m}}{4\mathcal E_u^+}.
}
\tag{6}
\]
For a uniform target in the prime-order group, the generic-decomposition acceptance probability is therefore at least \(f_u^{2m}/(4n\mathcal E_u^+)\).

## 6. Expected target-probe bound without a Markov energy cutoff

Let \(f_{\rm sym}(u)=2f_u\) be the symmetric factor-base size. The upstream \(A=0\) factor-base variance lemma gives
\[
\frac1{p-1}\sum_{u\ne0}(f_{\rm sym}(u)-X)^2
\le c_F X,\qquad c_F=13+2/X.
\tag{7}
\]
For \(\epsilon\in(0,1)\), define a dilation to be size-good when
\[
(1-\epsilon)X/2\le f_u\le(1+\epsilon)X/2.
\]
Chebyshev gives
\[
\rho:=\Pr_u[\text{size-good}]
\ge1-\delta,\qquad
\delta=\frac{c_F}{\epsilon^2X}.
\tag{8}
\]
Set \(f_{\min}=(1-\epsilon)X/2\).

For a fixed size-good \(u\), (6) implies that the expected number of independent uniform target probes needed to collect \(f_u+1\) successful decompositions is at most
\[
\frac{4n\mathcal E_u^+}{f_u^{2m-1}}\left(1+\frac1{f_u}\right)
\le
\frac{4n\mathcal E_u^+}{f_{\min}^{2m-1}}
\left(1+\frac1{f_{\min}}\right).
\]
The algorithm samples \(u\) uniformly and rejects it immediately if it is not size-good; this test is computable by enumerating \(T\). Conditional on being size-good,
\[
\mathbb E[\mathcal E_u^+\mid\text{size-good}]
\le \frac{M_+(m,X,p)}{\rho}
\]
by (5). Therefore the expected number of target probes, including the size-good dilation selection, is bounded by
\[
\boxed{
N_{\rm probes}
\le
\frac{4nM_+(m,X,p)}
{\rho f_{\min}^{2m-1}}
\left(1+\frac1{f_{\min}}\right).
}
\tag{9}
\]
Unlike the previous Markov-cutoff route, this uses the average energy directly and does not introduce a separate \(K_c\) energy threshold.

The planted-diagonal algebra from W-PD2 is unchanged: collect \(f_u\) planted rows and one unplanted row, set \(B=T-\nu I\), solve \(BF=AV\), and extract the one-dimensional kernel vector. The determinant failure is at most \(f_u/n\), and the final kernel vector is zero with probability \(1/n\); both cause a retry, never a wrong answer.

## 7. secp256k1 finite parameter calculation

Use the exact secp256k1 field prime and group order. For the production interval \(W=2^{140}\), choose \(m=8\):
- \(B=\lceil p^{1/8}\rceil=2^{32}\);
- \(X=B-1=2^{32}-1\);
- \(D'_8=15\cdot2^{14}=245{,}760\);
- \(8!+2D'_8=531{,}840\);
- optimize (9) over \(\epsilon\), giving \(\epsilon\approx0.0007401769676\);
- \(\delta\approx0.0055247465260\), so \(\rho\approx0.994475253474\);
- \(f_{\min}\approx2.1458941296\cdot10^9\).

Substitution in (9), using the exact \(p,n,X\), gives
\[
\boxed{\log_2N_{\rm probes}\le68.0446490611\text{ (expected target probes).}}
\]
The sparse matrix dimension is at most \(f_{\max}\approx2.1490731654\cdot10^9\). Wiedemann with \(O(f)\) sparse matvecs and \(O(mf)\) nonzeros per matvec costs \(O(mf^2)\), whose leading field-operation exponent is at most \(2^{65.00214}\).

For comparison, interval BSGS at \(W=2^{140}\) takes on the order of \(2^{70}\) group operations. The *number of relation-target probes* is below that count by about \(1.96\) bits. This is **not** a finite runtime comparison: each target probe invokes the \(p^{o(1)}\) decomposition/counting engine, whose finite constants are not known and whose upstream crossover is astronomically beyond cryptographic sizes. No practical secp256k1 speedup is claimed.

For the test interval \(W=2^{67}\), the leading exponent \(p^{2/m}\) first falls below \(2^{33.5}\) at \(m=16\), but the explicit sparse-solver factor \(m\) matters at this finite size: the bound \(O(mf^2)\) is \(2^{34.0741}\) field operations for \(m=16\), slightly above BSGS. Taking \(m=17\) brings the explicit sparse field-operation scale to \(2^{32.2977}\), but the optimized expected probe bound is \(\log_2N_{\rm probes}\le100.61627\), still far above interval BSGS \(2^{33.5}\). Thus W-SIGN improves the production branch only; it does not rescue the \(2^{67}\) interval.

## 8. Toy referee on E/F_163

Curve \(E/\mathbb F_{163}:y^2=x^3+7\), group order \(139\) prime, generator \(P=(2,34)\). Take \(m=2\), \(B=13\), \(T=\{1,\ldots,13\}\).

The one-sided factor base has \(f=9\) points:
\[
(2,34),(3,69),(4,76),(5,28),(6,68),(7,26),(9,35),(11,69),(13,30).
\]
A brute-force generic pair-sum oracle covers \(34/139\) targets (24.46%). The symmetric factor base has 18 points and covers \(112/139\) targets (80.58%); the one-sided construction deliberately trades lower per-probe acceptance for a smaller and much better-behaved energy.

Reference simulation results:
- 2,000 planted-diagonal rounds: 1,928 correct outputs in one round, 59 singular-matrix retries, 13 zero-kernel retries, 0 wrong outputs;
- exhaustive target-log check: all 139 logarithms recovered, at most one retry;
- interval wrapper \(A=40,W=32\): 487/500 correct in one round, 11 singular-matrix retries, 2 zero-kernel retries, 0 wrong outputs.

This is an algebraic referee only. The oracle is brute-force on a tiny group; it does not test the asymptotic count engine or finite-size secp256k1 performance.

## 9. Remaining proof obligations

1. Write the primitive-relation lemma in full detail, including the gcd division and padding argument, and verify every use of the prime-order hypothesis \(m<n\).
2. Reconstruct the upstream \(A=0\) DilationNondeg proof for \(T=[1,X]\), \(X<p/3\), including the full \(\omega\)-orbit exception.
3. Prove the \(A=0\) factor-base variance estimate (7) with the exact constant used in (9).
4. Add the sign-first input-wire permutation lemma to the count-oracle proof; do not silently assume the old coordinate-major prefix machine already enforces all sign bits.
5. Recheck the exact \(m=8\) finite arithmetic and the negative \(x=0\) Legendre-symbol claim in a standalone script.
6. Re-run the toy simulation from the committed standalone script and add a second independent implementation.
7. Audit expected bit cost per count-oracle call. The \(2^{68.04}\) number is a probe count, not a runtime bound.
8. Only after these items are closed, merge W-SIGN into the main algorithm and revise Final.md.

**Current status:** new energy inequality and expected-probe derivation are manually closed conditional on the upstream analytic inputs; sign-first count encoding and the \(A=0\) nondegeneracy proof remain open. No Final.md yet.
