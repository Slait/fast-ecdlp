# X265 SNF/Weil — Lean interface contracts v1

This document freezes the mathematical interfaces that the Python producer and
independent verifier expose.  It is a specification for the future Lean port,
not a Lean proof and not compiled Lean source.

## 1. Integer SNF certificate

For `s : Nat`, `N : Int` with `0 < N`, define

```lean
abbrev X265RelMat (s : Nat) := Matrix (Fin 3) (Fin (s + 3)) Int
abbrev X265Left  := Matrix (Fin 3) (Fin 3) Int
abbrev X265Right (s : Nat) := Matrix (Fin (s + 3)) (Fin (s + 3)) Int
```

Input predicate:

```lean
def X265Input (N : Int) (M : X265RelMat s) : Prop :=
  0 < N ∧
  (∀ i : Fin 3, ∀ j : Fin s, 0 ≤ M i j ∧ M i j < N) ∧
  (∀ i j : Fin 3,
    M i (Fin.castAdd s j) = if i = j then N else 0)
```

A certificate contains `S,T,D` and proves:

```lean
S * M * T = D
IsUnimodular S
IsUnimodular T
D.IsDiagonal
0 < D 0 0
D 0 0 ∣ D 1 1
D 1 1 ∣ D 2 2
(∀ i : Fin 3, ∀ j : Fin (s+3), 3 ≤ j → D i j = 0)
```

The X265 group-lattice endpoint adds:

```lean
D 0 0 = 1
D 0 0 * D 1 1 * D 2 2 = N
```

The extracted coefficient vectors are the columns of `S⁻¹`:

```lean
coeffO := S⁻¹ * ![1,0,0]
coeffU := S⁻¹ * ![0,1,0]
coeffV := S⁻¹ * ![0,0,1]
```

A separate theorem must show their images under `ev` have orders
`1, D 1 1, D 2 2`.

## 2. SNF verifier theorem

Target theorem:

```lean
theorem verifySNFCert_sound
    (M : X265RelMat s) (cert : SNFCert s)
    (hinput : X265Input N M)
    (hcheck : verifySNFCert M cert = true) :
    SmithNormalForm M cert.D := by
  ...
```

The verifier must not call the SNF producer.  It checks the exact matrix product,
integer determinants `±1`, diagonal shape, positivity, and divisibility.

## 3. Rectangular HNF insertion invariant

The executable rectangular stage should expose an inductive invariant:

```lean
structure HNFState (s : Nat) where
  processed : Nat
  H : Matrix (Fin 3) (Fin 3) Int
  U : Matrix (Fin (s+3)) (Fin (s+3)) Int
  hTransform : U * Mᵀ = blockMatrix H 0
  hUnimodular : IsUnimodular U
  hHNF : RowHNF H
  hContainsN : (N • 1) ⊆ rowLattice H
```

The one-row insertion theorem must prove that reducing the next relation row
modulo `H`, then applying a local `4 × 4` unimodular transform, preserves the
invariant and increments `processed` by one.

The bit-size proof should use the facts that `H` contains `N Z^3`, its diagonal
pivots divide `N`, all HNF entries are bounded by `N`, and each local transform
has fixed dimension `4 × 3`.

## 4. Miller/Weil certificate

For a certified prime field `Fp`, nonsingular short-Weierstrass curve, `n | p-1`,
and `nP=nQ=O`, define the four Miller arguments:

```lean
T₁ := Q + S
T₂ := S
T₃ := -S
T₄ := P - S
```

The transcript stores `S`, four nonzero Miller values `v₁..v₄`, and `eta`, with

```lean
eta = v₁ / v₂ * v₃ / v₄
eta ^ n = 1
```

The independent verifier recomputes the four Miller values from `P,Q,S`; it does
not trust transcript values.  For a group-basis certificate it additionally
checks

```lean
∀ ell ∈ primeDivisors(n), eta ^ (n / ell) ≠ 1
```

which proves `order eta = n`.

## 5. Basis certificate theorem

Given `n1 ∣ n2`, `n1*n2=N`, exact orders of `U,V`, and
`W=(n2/n1)•V`, the verifier proves:

```lean
order U = n1
order V = n2
order W = n1
order (weilPairing U W) = n1
```

The final theorem is that `U,V` generate the whole finite group of order `N`.
The cyclic case `n1=1` is a separate branch with `U=O`.

## 6. Toolchain compatibility blocker

The external Lean formalization at `JJYYY-JJY/lean-normal-forms` is pinned to
`leanprover/lean4:v4.32.0`; `Slait/fast-ecdlp` v2 uses
`leanprover/lean4:v4.35.0`.  A direct Lake dependency is therefore not assumed
compatible.  The integration must either port the relevant Kannan–Bachem modules
to the X265 toolchain or maintain a separate verified package and bridge the
interfaces explicitly.