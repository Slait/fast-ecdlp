# X265 pseudocode addendum — proof-aligned HNF/SNF call

Replace X265 basis-attempt step 8 with the following exact proof-level subroutine.

Input:
\[
M=[\mu_1\ \cdots\ \mu_s\mid NI_3]\in\mathbb Z^{3\times(s+3)},
\quad s=\lambda+9,\quad 0\le\mu_{ij}<N.
\]

1. Run the deterministic Kannan–Bachem rectangular HNF algorithm on the full-row-rank matrix \(M\). Obtain \(K_H\in GL_{s+3}(\mathbb Z)\) and \(B\in\mathbb Z^{3\times3}\) such that
   \[
   MK_H=[B\mid0].
   \]
2. Run the deterministic Kannan–Bachem square SNF algorithm on \(B\). Obtain \(S_0,V_0\in GL_3(\mathbb Z)\) and \(D_0=\operatorname{diag}(d_1,d_2,d_3)\) with
   \[
   S_0BV_0=D_0,\quad 0<d_1\mid d_2\mid d_3.
   \]
3. Set \(C_0\) to the first three columns of \(K_H\), so \(B=MC_0\). Reduce the first \(s\) entries of each column of \(C_0\) modulo \(N\), compensating in the last three coefficients, to obtain \(C\) with \(\|C\|_\infty\le sN+1\).
4. Compute \(R=B^{-1}M\in\mathbb Z^{3\times(s+3)}\), so \(M=BR\). Verify \(B=MC\), \(M=BR\), and \(|\det B|=d_1d_2d_3\).
5. Verify the \(3\times3\) SNF certificate \(S_0BV_0=D_0\), \(\det S_0,\det V_0\in\{\pm1\}\), and the divisibility chain.
6. Require \((d_1,d_2,d_3)=(1,n_1,n_2)\) and \(n_1n_2=N\). Extract the coefficient vectors \(S_0^{-1}e_2,S_0^{-1}e_3\) exactly as in X266.

For the X266 lattice proof, the compact certificate \(B=MC\), \(M=BR\), \(|\det B|=N\) replaces the need to materialize the full \((s+3)\times(s+3)\) right multiplier. The Kannan–Bachem theorem gives polynomial bit complexity in the binary input length \(O((s+3)\log N)\); since \(s=\lambda+9=\operatorname{polylog}N\), this is \(N^{o(1)}\).