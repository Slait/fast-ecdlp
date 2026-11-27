# X266 — Exact kernel-to-group basis theorem

**Status:** conditional theorem proved on paper; unconditional SNF-only shortcut refuted by an explicit elliptic-curve counterexample.  
**Scope:** the relation-lattice / SNF / group-generation interface of X265. This does not close the Hasse, dilation, Count15, or end-to-end complexity obligations.

## 1. Setup and notation

Let `G = E(F_p)` be a finite elliptic-curve group of known exact order `N`. Let

\[
H_1,H_2,H_3\in G,\qquad
\operatorname{ev}:\mathbb Z^3\to G,\quad
(a_1,a_2,a_3)\mapsto a_1H_1+a_2H_2+a_3H_3,
\]

and let `K = ker(ev)`. Let

\[
M=[\mu_1\ \cdots\ \mu_s\mid NI_3]\in\mathbb Z^{3\times(s+3)},
\qquad \Lambda=M\mathbb Z^{s+3}.
\]

Assume every relation column is checked in the actual group:

\[
\operatorname{ev}(\mu_j)=O\quad (1\le j\le s).
\]

By Lagrange, `N H_i=O`, hence `ev(N e_i)=O`. Therefore

\[
\boxed{\Lambda\subseteq K.}\tag{1}
\]

The final `N I_3` block also makes `M` full row rank, so `Lambda` has finite index in `Z^3`.

## 2. SNF certificate determines the lattice index

Suppose a complete rectangular SNF certificate is supplied:

\[
S\in GL_3(\mathbb Z),\quad T\in GL_{s+3}(\mathbb Z),\quad
SMT=D=[\operatorname{diag}(d_1,d_2,d_3)\mid 0],
\]

where `0 < d1 | d2 | d3`.

Since `T` is unimodular, right multiplication by `T` does not change the column lattice:

\[
(MT)\mathbb Z^{s+3}=M\mathbb Z^{s+3}=\Lambda.
\]

Since `S` is a lattice automorphism,

\[
S\Lambda=(SMT)\mathbb Z^{s+3}=D\mathbb Z^{s+3}
=d_1\mathbb Z e_1\oplus d_2\mathbb Z e_2\oplus d_3\mathbb Z e_3.
\]

Consequently,

\[
\boxed{[\mathbb Z^3:\Lambda]=d_1d_2d_3.}\tag{2}
\]

This conclusion uses the full SNF certificate, not merely a claimed diagonal. The checks `SMT=D`, `det S=±1`, and `det T=±1` are essential.

## 3. Kernel equality — the missing hypothesis is surjectivity

The first isomorphism theorem gives

\[
[\mathbb Z^3:K]=|\operatorname{im}(\operatorname{ev})|.
\]

Thus, if `ev` is surjective, then

\[
[\mathbb Z^3:K]=|G|=N.
\]

If the SNF certificate also gives `d1*d2*d3=N`, equation (2) yields

\[
[\mathbb Z^3:\Lambda]=[\mathbb Z^3:K]=N.
\]

Together with (1) and finite index, this forces equality:

\[
\boxed{\Lambda=K.}\tag{3}
\]

**Important correction:** without surjectivity, the conclusion does not follow. In general

\[
[\mathbb Z^3:K]=|\operatorname{im}(\operatorname{ev})|\le N,
\]

and `Lambda` can be a strict sublattice of `K` while still having index `N`.

## 4. Quotient generators and the group basis

Assume the hypotheses of Section 3, and suppose the SNF diagonal is

\[
D=[\operatorname{diag}(1,n_1,n_2)\mid0],
\qquad n_1\mid n_2,\quad n_1n_2=N.
\]

The map

\[
\Psi:\mathbb Z^3/\Lambda\to
\mathbb Z^3/(d_1\mathbb Z e_1+d_2\mathbb Z e_2+d_3\mathbb Z e_3),
\quad x+\Lambda\mapsto Sx+D\mathbb Z^3
\]

is a well-defined isomorphism. Its inverse is induced by `S^{-1}`. Therefore the classes of

\[
S^{-1}e_1,\quad S^{-1}e_2,\quad S^{-1}e_3
\]

have respective orders `1,n1,n2` and generate the quotient. By (3), `ev` induces an isomorphism

\[
\mathbb Z^3/\Lambda\cong\mathbb Z^3/K\cong G.
\]

Hence

\[
G_1=\operatorname{ev}(S^{-1}e_1)=O,
\quad U=\operatorname{ev}(S^{-1}e_2),
\quad V=\operatorname{ev}(S^{-1}e_3)
\]

satisfy

\[
\boxed{G\cong\langle U\rangle\oplus\langle V\rangle
\cong\mathbb Z/n_1\mathbb Z\oplus\mathbb Z/n_2\mathbb Z.}
\]

This proves exact orders, independence, and generation — but only after surjectivity has been established.

## 5. How X265 establishes surjectivity

The SNF diagonal and the individual order checks alone do not establish surjectivity. X265 therefore needs an additional group-generation certificate.

For the noncyclic case `n1 > 1`, the current certificate uses

\[
W=(n_2/n_1)V\in G[n_1]
\]

and verifies that the actual Weil pairing value

\[
\eta=e_{n_1}(U,W)
\]

has exact order `n1`. Exact order is checked by

\[
\eta^{n_1}=1,\qquad
\eta^{n_1/\ell}\ne1\quad\text{for every prime }\ell\mid n_1,
\]

with a certified complete prime-divisor list.

Assuming the standard Weil pairing theorem (bilinearity, alternation, and nondegeneracy on `E[n1]`, with `p` not dividing `n1`), primitivity implies that `U,W` are independent: if `aU+bW=O`, pairing with `W` and `U` gives `n1|a` and `n1|b`. Thus

\[
|\langle U,W\rangle|=n_1^2.
\]

Because `W` generates the unique subgroup of order `n1` in the cyclic group `\langle V\rangle`, this also forces

\[
\langle U\rangle\cap\langle V\rangle=\{O\}.
\]

As `ord(U)=n1` and `ord(V)=n2`,

\[
|\langle U,V\rangle|=n_1n_2=N=|G|,
\]

so `U,V` generate `G`. Since both are images of coefficient vectors under `ev`, `ev` is surjective. Section 3 now applies and gives `Lambda=K`.

In the cyclic case `n1=1`, the direct check `ord(V)=n2=N` already proves surjectivity; no Weil pairing is required.

**Therefore Weil is not redundant in the current X265 acceptance protocol.** It is the efficient certificate that the induced map from the SNF quotient to the actual elliptic-curve group is onto. It can only be removed if another independently verified surjectivity/generation certificate replaces it.

## 6. Concrete counterexample: SNF and individual orders are insufficient

Take

\[
E/\mathbb F_5:\quad y^2=x^3+4x.
\]

The curve is nonsingular and has eight rational points. Its group is

\[
E(\mathbb F_5)\cong\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z.
\]

Choose

\[
H_1=O,\quad H_2=(0,0),\quad H_3=(2,1).
\]

Here `ord(H2)=2`, `ord(H3)=4`, but these points generate only the cyclic subgroup of order four. Consider

\[
M=\begin{pmatrix}
1&0&0&8&0&0\\
0&2&0&0&8&0\\
0&0&4&0&0&8
\end{pmatrix}.
\]

The first three columns are valid relations and the last three are `8 I3`. The exact SNF certificate has

\[
S=I_3,\quad
D=[\operatorname{diag}(1,2,4)\mid0],\quad
\det S=\det T=1
\]

(for a suitable unimodular `T`; the displayed diagonal matrix itself is already obtained by the identity column transform). Thus the diagonal product is `8=N`, and the extracted points have orders `2` and `4`.

Nevertheless, they generate only four points. In this example

\[
W=(4/2)H_3=2H_3=H_2,
\]

so alternation gives `e_2(H2,W)=e_2(H2,H2)=1`, which fails the primitive-order test. The Weil certificate correctly rejects the false basis.

The referee script `x266_kernel_group_basis_referee.py` reproduces this counterexample using the existing X265 SNF producer.

## 7. Compact lattice certificate (optional implementation improvement)

A full `(s+3) x (s+3)` right transform `T` is not logically necessary for verifying equality of the relation lattice. It can be replaced by a compact certificate consisting of

\[
B\in\mathbb Z^{3\times3},\quad
C\in\mathbb Z^{(s+3)\times3},\quad
R\in\mathbb Z^{3\times(s+3)}
\]

such that

\[
\boxed{B=MC,\qquad M=BR,\qquad |\det B|=N.}\tag{4}
\]

The first identity proves `B Z^3 ⊆ M Z^(s+3)`; the second proves the reverse inclusion. Hence the column lattices are equal, and the determinant proves their index is `N`.

Now only a `3 x 3` SNF certificate

\[
S_0BT_0=\operatorname{diag}(1,n_1,n_2)
\]

is needed to extract the quotient structure and candidate coefficient vectors `S0^{-1}e2`, `S0^{-1}e3`. This reduces the *verification certificate* from a quadratic-size right transform to `O(s)` integer entries.

This is a valid certificate format. It is **not yet established** that the current HNF producer emits `B,C,R` with the required bit-size bound in the claimed time. That is a separate algorithmic/complexity obligation; do not claim it closed from this theorem alone.

## 8. Bit-complexity boundary

The algebraic theorem is exact and does not itself establish the `N^(1/5+o(1))` running-time claim. To close the SNF part of the global theorem, one still needs an explicit bound for:

- bit lengths of `B,C,R` (or `S,T`) produced from the X265 relation matrix;
- the number of integer arithmetic operations in the specialized 3-dimensional HNF/SNF routine;
- exact determinant, inverse, and verification costs;
- memory usage of the producer and certificate verifier.

The current Python telemetry is empirical. The implementation report explicitly leaves the rectangular HNF insertion and coefficient-growth proof open in Lean. Thus X266 closes the *logical kernel-to-group inference, with the surjectivity premise/certificate made explicit*, not the full SNF bit-complexity proof.

## 9. Verdict for the main algorithm

- `Lambda ⊆ ker(ev)`: proved from the checked relation columns and the `N I3` block.
- `index(Lambda)=N`: proved from a valid rectangular SNF certificate with diagonal product `N`, or from (4).
- `Lambda=ker(ev)`: proved **only after** surjectivity of `ev` is certified.
- `S^{-1}e2,S^{-1}e3` give a group basis: proved after kernel equality.
- In the current X265 protocol, the noncyclic Weil certificate is not redundant; it supplies the missing generation/surjectivity step.
- Full SNF bit-complexity and formal Lean proof remain open.

`ECDLP-MAIN` remains OPEN.