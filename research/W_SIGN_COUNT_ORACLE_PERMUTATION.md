# W-SIGN count-oracle encoding: sign-first wire permutation

This note isolates the only new count-oracle requirement in W-SIGN. It is a paper-level reduction; the current upstream Lean module proves the count theorem for the coordinate-major serialization and does not yet contain this relabelled instance.

## 1. Two encodings of the same decomposition

Let \(\ell=\operatorname{Nat.size}(B)\). Each of the \(m\) points is represented by \(\ell\) big-endian x-bits and one sign bit
\[
s_i=\mathbf 1\{(p-1)/2<y_i\}.
\]
The upstream coordinate-major serialization is
\[
z_{\rm old}=(x_{1,1},\ldots,x_{1,\ell},s_1,\,
             x_{2,1},\ldots,x_{2,\ell},s_2,\ldots).
\]
Define instead
\[
z_{\rm sign}=(s_1,\ldots,s_m,\,
             x_{1,1},\ldots,x_{1,\ell},\,
             x_{2,1},\ldots,x_{m,\ell}).
\]
The length is \(N=m(\ell+1)\) in both cases. The map \(\Pi_{m,\ell}\) that moves the sign bit of each point to the first m positions and preserves the relative order of all x-bits is a fixed permutation of the N input wires.

The point tuple, curve equations, partial-sum constraints, target-sum constraint, and genericity predicate are unchanged. Only the serialization is permuted.

## 2. Relabelling lemma

Let \(\mathcal N\) be the Boolean/arithmetic constraint network whose satisfying inputs are exactly the generic decomposition tuples. Let \(\mathcal N^\Pi\) be the same network with its N external input wires relabelled by \(\Pi_{m,\ell}\). Internal gates and all arithmetic constraints are identical.

Then:
- \(\mathcal N^\Pi\) has exactly the same number of gates, edges, maximum degree, field operations, and internal variables as \(\mathcal N\);
- for every bit string \(z\), \(z\) satisfies \(\mathcal N\) iff \(\Pi_{m,\ell}z\) satisfies \(\mathcal N^\Pi\);
- for every prefix \(\pi\), the number of satisfying sign-first strings extending \(\pi\) equals the number of satisfying old strings whose permuted encoding extends \(\pi\).

The counting engine in Theorem 2(i) operates on the constraint network and its external input wires. Its time bound depends on the network size, gate degrees, and input length, not on the names/order of the external wires. Applying the same construction to \(\mathcal N^\Pi\) therefore gives the same \(p^{o(1)}\) bound. Computing the permutation itself takes \(O(N)=O(m\log p)\) elementary bit operations, absorbed in the bound for fixed m.

The L61 lexicographic-search driver is generic in its zero-test oracle contract. Replacing the count oracle by the relabelled count oracle leaves the driver's proof and polynomial overhead unchanged.

## 3. One-sided prefix

In sign-first encoding the prefix
\[
\pi=0^m
\]
fixes every sign bit to zero while leaving every x-coordinate free. The upstream sign convention is
\[
s_i=0\iff y_i\le(p-1)/2.
\]
For secp256k1, and more generally for an odd prime-order group, there is no nonzero point with \(y=0\). Therefore each admissible x-coordinate has exactly one point with sign bit zero. The prefix \(0^m\) counts precisely the generic decompositions using the one-sided base \(F_u^+\).

The count oracle returns zero exactly when the target has no such decomposition; otherwise the L61 driver finds one lexicographically least sign-first decomposition. No extra factor \(2^m\) search over sign patterns is required.

## 4. What is proved and what remains

The wire-permutation argument is mathematically exact once the counting-engine theorem is stated for a network with an arbitrary fixed ordering of its external input wires. It does not change the arithmetic network or its asymptotic cost.

The current source tree proves ECDLP.L132.countingRate_all for the original coordinate-major string in ECDLP109.strings. It does not yet instantiate the proof for \(\mathcal N^\Pi\). To close the formal source gap:
1. define the sign-first string and its prefix-count function;
2. define the permuted input network by relabelling the external wires;
3. prove its Good/frame invariant by transporting the original invariant through \(\Pi_{m,\ell}\);
4. reuse the same count engine and L61 driver with the permuted input layout.

This is an encoding/interface proof, not a new elliptic-curve or Semaev estimate. Until those four formal steps or an equivalent paper-level network-invariance proof are included in the final write-up, the one-sided count oracle must be labelled conditional.
