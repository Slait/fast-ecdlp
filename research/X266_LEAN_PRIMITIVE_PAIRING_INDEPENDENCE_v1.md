# X266 Lean subproof — primitive Weil pairing implies independence

**Repository:** `Slait/fast-ecdlp`  
**Branch:** `work/x268-pairing-basis-lean-v1`  
**Latest code commit:** `ecee1951f8da82d78666faf30c928f05f6f0c337`  
**Verify integration commit:** `0c6e9de4d47b38400cdb19b6da3bf4c697a075dd`  
**Lean project:** `v2/lean`  
**Toolchain:** `leanprover/lean4:v4.35.0`  
**Status:** proof source added; **not compiled in this environment**.

## 1. What is now formalized

The new module `v2/lean/ECDLPv2/L266_BasisIndependence.lean` formalizes the algebraic step used in X266, under an abstract alternating bilinear pairing

\[
e:G\times G\to H
\]

from an additive abelian group to a commutative multiplicative group.

The pairing laws are:

\[
e(0,Y)=1,\quad e(X+Y,Z)=e(X,Z)e(Y,Z),
\]

\[
e(X,X)=1,\quad e(Y,X)=e(X,Y)^{-1}.
\]

The order premise is the semantic exact-order predicate: \(e(U,V)^n=1\), and no positive exponent smaller than \(n\) annihilates \(e(U,V)\).

## 2. Proved statements in the module

1. `exactOrder_dvd`: if \(\eta\) has exact order \(n\) and \(\eta^k=1\), then \(n\mid k\).
2. `relation_coefficients_divisible`: if \(aU+bV=0\), then \(n\mid a\) and \(n\mid b\). Pairing the relation with \(U\) detects \(b\), and pairing it with \(V\) detects \(a\).
3. `no_small_nontrivial_relation`: for \(0\le a,b<n\), the relation \(aU+bV=0\) forces \(a=b=0\).
4. `exactOrder_pow_injective`: powers of an element of exact order \(n\) are injective on exponents in \([0,n)\).
5. `coordinateCombination_injective`: the map

   \[
   (a,b)\mapsto aU+bV,\qquad (a,b)\in\{0,\ldots,n-1\}^2,
   \]

   is injective.
6. `coordinateCombination_card`: its image has exactly \(n^2\) elements.
7. `WeilBasisCertificate.U_has_exact_order` and `V_has_exact_order`: the two n-torsion points themselves have exact additive order n.

The certificate structure also records \(nU=nV=0\), as required for the X266 application. The injectivity proof itself uses the primitive pairing value and the pairing laws.

## 3. Proof idea

From \(aU+bV=0\), bilinearity and alternation give

\[
1=e(aU+bV,U)=e(U,U)^a e(V,U)^b=e(U,V)^{-b},
\]

so exact order implies \(n\mid b\). Pairing with \(V\) gives

\[
1=e(aU+bV,V)=e(U,V)^a e(V,V)^b=e(U,V)^a,
\]

hence \(n\mid a\). The bounded-coefficient statement follows immediately. For equality of two coefficient combinations, pairing with \(V\) and \(U\) separately identifies the two exponents modulo \(n\); their representatives in \([0,n)\) must be equal.

## 4. Integration

The file is included by the existing `v2/lean` library glob `ECDLPv2.+`. The branch's `v2/lean/Verify.lean` now imports the module and requests `#print axioms` for the exact-order divisibility, relation-divisibility, no-small-relation, injectivity, and image-cardinality theorems.

## 5. Explicit remaining gaps

This subproof does **not** yet close the whole X266 group-basis theorem. The following bridges remain open:

- prove that the actual elliptic-curve Weil pairing used by X265 satisfies these abstract pairing laws in the chosen Mathlib model;
- prove that the four-Miller shifted-divisor transcript computes that Weil pairing;
- connect the existing finite prime-divisor test `IsPrimitiveNRoot` in `L265_SNFWeil.lean` to the semantic `HasExactOrder` predicate used here, including completeness of the supplied prime-divisor list;
- combine the `n^2` distinct combinations with the theorem/cardinality of \(E[n]\), then transfer generation of \(E[n_1]\) to surjectivity on the full group using the cyclic-factor argument in the X266 paper proof;
- complete the cyclic branch and the SNF quotient-to-group map in Lean.

No statement in this note claims that these missing bridges have been proved.

## 6. Build status

The current runtime has neither `lean` nor `lake`, and outbound network access is unavailable. Therefore the new Lean source and updated `Verify.lean` have **not** been compiled or axiom-checked in this session. The source contains no `sorry` or custom axioms by inspection, but that is not a substitute for a Lean build.