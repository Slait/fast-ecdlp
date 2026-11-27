# X267 — Bit complexity of the X265 relation-lattice SNF

**Status:** paper proof complete for the proof-level X265 SNF subroutine obtained by instantiating the unspecified deterministic HNF/SNF call with the Kannan–Bachem algorithms.  
**Not claimed:** the existing custom Python producer has not thereby become a formal implementation of Kannan–Bachem; it remains a separate implementation candidate.

## 1. Exact X265 input size

The X265 basis-attempt specification sets

\[
s=\lambda+9,\qquad n=s+3=\lambda+12,
\]

and constructs

\[
M=[\mu_1\ \cdots\ \mu_s\mid NI_3]\in\mathbb Z^{3\times n},
\qquad 0\le (\mu_j)_i<N.
\]

Put \(b=\lceil\log_2(N+1)\rceil\). Every entry of \(M\) has at most \(b\) bits, and its binary encoding length is

\[
L_M=O(n b)=O((\lambda+12)\log N).
\tag{1}
\]

The final \(NI_3\) block makes \(M\) full row rank over \(\mathbb Q\), for every \(N\ge1\).

The X265 asymptotic regime explicitly requires \(\lambda\) to be fixed or polylogarithmic in \(N\). More generally, assume

\[
\lambda\le C(\log N)^c
\tag{2}
\]

for constants \(C,c\) independent of \(N\). Then \(L_M=(\log N)^{O(1)}\).

## 2. External normal-form theorem used

We instantiate the X265 normal-form call with the deterministic algorithms of:

R. Kannan and A. Bachem, *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*, SIAM Journal on Computing **8**(4) (1979), 499–507, DOI [10.1137/0208040](https://doi.org/10.1137/0208040).

The paper proves that its HNF and SNF algorithms use a polynomial number of integer arithmetic operations and that every intermediate integer has a number of binary digits bounded by a polynomial in the binary input length. It also computes the unimodular multiplier matrices. Its HNF construction is explicitly extended from square nonsingular matrices to arbitrary rectangular full-row-rank matrices; the SNF construction is then applied to the resulting square nonsingular block.

We use exactly that rectangular-HNF-plus-square-SNF route below. We do **not** infer a bound for an unrelated implementation merely because it has a similar name or pattern.

## 3. Construction of the full rectangular SNF certificate

Let \(K_H\in GL_n(\mathbb Z)\) be the multiplier returned by the rectangular HNF algorithm, so that

\[
M K_H=[B\mid 0],
\tag{3}
\]

where \(B\in\mathbb Z^{3\times3}\) is nonsingular and is in the chosen HNF convention.

Apply the square \(3\times3\) SNF algorithm to \(B\). It returns

\[
S_0,V_0\in GL_3(\mathbb Z),\qquad
S_0BV_0=D_0=\operatorname{diag}(d_1,d_2,d_3),
\]

where \(0<d_1\mid d_2\mid d_3\).

Define

\[
\widehat V=\operatorname{diag}(V_0,I_s),\qquad
S=S_0,\qquad T=K_H\widehat V.
\]

Then

\[
\begin{aligned}
SMT
&=S_0 M K_H\widehat V\\
&=S_0[B\mid0]\operatorname{diag}(V_0,I_s)\\
&=[D_0\mid0].
\end{aligned}
\tag{4}
\]

Because \(K_H\) and \(V_0\) are unimodular, \(T\in GL_n(\mathbb Z)\); also \(S\in GL_3(\mathbb Z)\). Thus (4) is a complete rectangular SNF certificate of exactly the shape required by X265.

The diagonal product is

\[
d_1d_2d_3=|\det B|=[\mathbb Z^3:\Lambda].
\]

X265 accepts the basis attempt only when this product is exactly \(N\) and the diagonal has the required form \((1,n_1,n_2)\).

## 4. Bit-complexity theorem

**Theorem X267.** Under (2), the deterministic HNF/SNF computation in Sections 2–3, including construction of the unimodular multipliers and exact verification of the resulting certificate, takes \(N^{o(1)}\) bit operations and uses \(N^{o(1)}\) bits of working space.

**Proof.**

Let \(L=L_M+O(1)\) be the binary input length. By the Kannan–Bachem theorem, there is a fixed polynomial \(P\) such that:

1. the number of arithmetic operations in the HNF and SNF computations is at most \(P(L)\);
2. every intermediate integer, including entries of \(K_H,S_0,V_0\), has at most \(P(L)\) bits.

Integer addition, multiplication, division with remainder, and extended gcd on \(P(L)\)-bit integers each have bit cost polynomial in \(P(L)\). Consequently the total bit cost is bounded by another fixed polynomial \(Q(L)\).

The multiplier \(K_H\) has \(n^2\) entries. Since \(n=O(L)\), and each entry has at most \(P(L)\) bits, writing or storing the full multiplier costs at most \(O(L^2P(L))\) bits, also polynomial in \(L\). The final \(3\times3\) stage and the composition \(T=K_H\widehat V\) are polynomial in \(L\).

By (1) and (2), \(L=(\log N)^{O(1)}\). Therefore

\[
Q(L)=(\log N)^{O(1)}=N^{o(1)}.
\]

The same argument gives the working-space bound. This proves the theorem. \(\square\)

### 4.1 Exact verification cost

A verifier checks:

- dimensions and the \(NI_3\) input block;
- \(SMT=[D_0\mid0]\) by exact integer matrix multiplication;
- \(\det S=\pm1\) and \(\det T=\pm1\);
- positivity, diagonality, and \(d_1\mid d_2\mid d_3\).

The matrices have polynomially many entries in \(L\), and all entries have polynomially many bits. Matrix multiplication and exact determinant computation (for example, fraction-free Bareiss elimination) therefore take polynomial bit time in \(L\), hence polylogarithmic time in \(N\).

For the determinant verifier, Bareiss intermediate entries are minors of \(T\). If each entry of \(T\) has at most \(P(L)\) bits, Hadamard's inequality bounds every \(k\times k\) minor by \(k^{k/2}2^{kP(L)}\); its bit length is \(O(k(P(L)+\log k))\), which is polynomial in \(L\) because \(k\le n=O(L)\).

Thus verification is also \(N^{o(1)}\).

## 5. Compact lattice certificate derived from HNF

The full right multiplier is not needed by the mathematical verifier of the lattice equality.

Let \(C_0\) be the first three columns of \(K_H\). Equation (3) gives

\[
B=MC_0.
\tag{5}
\]

Since the remaining columns in (3) are zero and \(K_H\) is unimodular, the columns of \(B\) generate exactly the column lattice of \(M\). Hence

\[
R:=B^{-1}M\in\mathbb Z^{3\times n},\qquad M=BR.
\tag{6}
\]

The compact certificate is

\[
\boxed{B=MC,\qquad M=BR,\qquad |\det B|=N,}
\tag{7}
\]

where \(C\in\mathbb Z^{n\times3}\) and \(R\in\mathbb Z^{3\times n}\).

### 5.1 Explicit height bounds for a compact certificate

Because \(\Lambda\supseteq N\mathbb Z^3\), the HNF basis \(B\) has diagonal pivots dividing \(N\); its reduced off-diagonal entries are smaller in absolute value than the corresponding pivots. Thus

\[
\|B\|_\infty\le N.
\tag{8}
\]

There is also a compact \(C\) with an explicit bound. For each column \(b_j\) of \(B\), its residue modulo \(N\) lies in the subgroup of \((\mathbb Z/N\mathbb Z)^3\) generated by the relation columns \(\mu_1,\ldots,\mu_s\). Since the exponent of this group divides \(N\), choose coefficients \(c_i\in\{0,\ldots,N-1\}\) such that

\[
b_j\equiv\sum_{i=1}^s c_i\mu_i\pmod N.
\]

Then

\[
z=\frac{b_j-\sum_i c_i\mu_i}{N}\in\mathbb Z^3
\]

and the corresponding column of \(C\) is \((c_1,\ldots,c_s,z_1,z_2,z_3)^T\). Using (8) and \(0\le(\mu_i)_k<N\),

\[
|z_k|
\le \frac{N+s(N-1)^2}{N}
\le sN+1.
\]

Consequently a certificate exists with

\[
\boxed{\|C\|_\infty\le sN+1.}
\tag{9}
\]

For \(R=B^{-1}M\), Cramer's rule expresses each entry as a \(3\times3\) determinant with entries of absolute value at most \(N\), divided by the nonzero integer \(\det B\). Hence

\[
\boxed{\|R\|_\infty\le 6N^3.}
\tag{10}
\]

Equations (8)–(10) show that the compact certificate has \(O(s)\) entries of \(O(\log N+\log(s+1))\) bits, i.e.

\[
O(s(\log N+\log(s+1)))
\]

bits in total.

The HNF multiplier \(K_H\) gives an initial \(C_0\). To enforce (9), reduce its first \(s\) entries in each column modulo \(N\) and compensate in the final three coefficients of the \(NI_3\) block. This preserves \(MC=B\) and yields the bound above. Then compute \(R=B^{-1}M\) exactly using the \(3\times3\) adjugate and \(\det B\).

A verifier of (7) performs \(O(s)\) scalar products on \(O(\log N+\log s)\)-bit integers and one \(3\times3\) determinant. Its bit complexity is \(O(s\,\operatorname{polylog}N)\), which is polylogarithmic under (2).

This compact certificate is therefore both small and efficiently checkable. The producer may use the Kannan–Bachem HNF multiplier internally and discard it after extracting \(C\).

## 6. Consequence for the global X265 exponent

The X265 basis attempt uses exactly \(s=\lambda+9\) lower relations, not \(s\) proportional to the factor-base size. Under the stated regime \(\lambda=\operatorname{polylog}N\), the relation matrix has polylogarithmic binary length.

Therefore the SNF/HNF producer, the full or compact certificate, and the independent certificate verifier each contribute only

\[
N^{o(1)}
\]

bit operations per basis attempt.

The basis attempt has a positive constant lower bound on success probability in the X265 analysis. Thus the expected number of basis attempts is \(O(1)\), and the expected total SNF/HNF contribution remains \(N^{o(1)}\).

If the other X263/X264/Count15/factorization contributions are indeed bounded by \(N^{1/5+o(1)}\), adding this SNF/HNF term does not change the target:

\[
N^{1/5+o(1)}+N^{o(1)}=N^{1/5+o(1)}.
\]

This closes the **SNF/HNF asymptotic contribution** under the polylogarithmic-\(\lambda\) hypothesis. It does not by itself prove the other components or the global ECDLP theorem.

## 7. Crucial implementation boundary

The existing file `x265_snf_weil.py` uses a custom incremental \(4\times3\) HNF insertion routine and a custom \(3\times3\) Smith reduction. Its empirical coefficient telemetry is not a proof that this code is the Kannan–Bachem algorithm, nor does the cited theorem automatically apply to it.

Accordingly the proof-critical X265 specification must make one of these choices:

1. **Proof-aligned route (recommended):** specify the deterministic Kannan–Bachem rectangular HNF followed by \(3\times3\) SNF as the normal-form subroutine; or
2. separately prove that the existing custom producer implements an algorithm with the same polynomial coefficient-height and operation-count guarantees.

Until the code is replaced or separately analyzed, the mathematical complexity theorem is closed for the specified Kannan–Bachem route, while the current Python producer remains an implementation candidate.

The Lean development must formalize the certificate checker and the compact lattice identities. Formalizing the Kannan–Bachem producer's full complexity theorem is a separate formalization task; it is not claimed here.

## 8. Final verdict

- Input length: \(L=O((\lambda+12)\log N)\).
- HNF/SNF bit complexity with Kannan–Bachem: \(\operatorname{poly}(L)\).
- For \(\lambda=\operatorname{polylog}N\): \(\operatorname{polylog}N=N^{o(1)}\).
- Compact certificate size: \(O((\lambda+9)\log N)\) bits up to constant factors.
- Compact certificate verification: \(O((\lambda+9)\operatorname{polylog}N)\) bit operations.
- Contribution to the target \(N^{1/5+o(1)}\): does not change the exponent.
- Existing custom Python producer: not yet certified as an implementation of the proof-level Kannan–Bachem routine.
- Full X265 / `ECDLP-MAIN`: remains OPEN.