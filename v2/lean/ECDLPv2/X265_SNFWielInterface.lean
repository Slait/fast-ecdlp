import Mathlib

/-!
# X265 SNF / Weil certificate interfaces

This module freezes the Lean-facing data contracts for the X265 production
candidate.  It intentionally contains no `sorry` and no unproved algorithm
claim.  In particular, it does NOT yet formalize the row-HNF insertion
algorithm, the Kannan–Bachem bit bound, Miller's divisor recurrence, or the
shifted-divisor identity on an elliptic curve.  Those are separate proof tasks.

The module is included in the ECDLPv2 library glob, but is not yet imported by
`Verify.lean`: the local environment has no Lean/Lake executable, so the
project build has not been run in this session.
-/

namespace ECDLPv2.X265

abbrev RelMat (s : Nat) := Matrix (Fin 3) (Fin (s + 3)) Int
abbrev LeftMat := Matrix (Fin 3) (Fin 3) Int
abbrev RightMat (s : Nat) := Matrix (Fin (s + 3)) (Fin (s + 3)) Int

def relIndex {s : Nat} (j : Fin s) : Fin (s + 3) :=
  ⟨j.val, by omega⟩

def torsionIndex {s : Nat} (j : Fin 3) : Fin (s + 3) :=
  ⟨s + j.val, by omega⟩

/-- Exact input shape used by the rectangular X265 SNF wrapper. -/
def IsX265Input {s : Nat} (N : Int) (M : RelMat s) : Prop :=
  0 < N ∧
  (∀ i : Fin 3, ∀ j : Fin s,
    0 ≤ M i (relIndex j) ∧ M i (relIndex j) < N) ∧
  (∀ i j : Fin 3,
    M i (torsionIndex j) = if i = j then N else 0)

/-- Integer unimodularity, matching the independent Python determinant check. -/
def IsUnimodular {n : Nat} (A : Matrix (Fin n) (Fin n) Int) : Prop :=
  A.det = 1 ∨ A.det = -1

/-- Smith diagonal predicate for a 3 x (s+3) matrix. -/
def IsSmithDiagonal {s : Nat} (D : RelMat s) : Prop :=
  (∀ i : Fin 3, ∀ j : Fin (s + 3), i.val ≠ j.val → D i j = 0) ∧
  0 < D 0 0 ∧
  0 < D 1 1 ∧
  0 < D 2 2 ∧
  D 0 0 ∣ D 1 1 ∧
  D 1 1 ∣ D 2 2

/--
A certificate for the exact identity S * M * T = D.
The producer is not part of this structure: a verifier receives the data and
checks every field independently.
-/
structure SNFCertificate {s : Nat} (M : RelMat s) where
  S : LeftMat
  T : RightMat s
  D : RelMat s
  transform : S * M * T = D
  leftUnimodular : IsUnimodular S
  rightUnimodular : IsUnimodular T
  smithDiagonal : IsSmithDiagonal D

theorem SNFCertificate.matrixIdentity
    {s : Nat} {M : RelMat s} (cert : SNFCertificate M) :
    cert.S * M * cert.T = cert.D :=
  cert.transform

theorem SNFCertificate.leftIsUnimodular
    {s : Nat} {M : RelMat s} (cert : SNFCertificate M) :
    IsUnimodular cert.S :=
  cert.leftUnimodular

theorem SNFCertificate.rightIsUnimodular
    {s : Nat} {M : RelMat s} (cert : SNFCertificate M) :
    IsUnimodular cert.T :=
  cert.rightUnimodular

/-- Additional endpoint required when the relation columns generate the full
    elliptic-curve relation lattice of order N. -/
structure LatticeSNFCertificate {s : Nat} (N : Int) (M : RelMat s)
    extends SNFCertificate M where
  firstInvariantOne : D 0 0 = 1
  quotientOrder : D 0 0 * D 1 1 * D 2 2 = N

theorem LatticeSNFCertificate.quotientInvariantFactors
    {s : Nat} {N : Int} {M : RelMat s}
    (cert : LatticeSNFCertificate N M) :
    cert.D 0 0 = 1 ∧
    cert.D 0 0 * cert.D 1 1 * cert.D 2 2 = N :=
  ⟨cert.firstInvariantOne, cert.quotientOrder⟩

/-- Abstract type of a Miller evaluator.  The elliptic-curve divisor semantics
    and the binary Miller recurrence must be proved in a later module. -/
abbrev MillerEval (Point F : Type) := Nat → Point → Point → F

/-- The exact four-evaluation shifted-divisor transcript used by X265 v1.1. -/
structure ShiftedWeilCertificate
    (Point F : Type) [Field F]
    (add : Point → Point → Point)
    (neg : Point → Point)
    (miller : MillerEval Point F)
    (n : Nat) (P Q S : Point) where
  v1 : F
  v2 : F
  v3 : F
  v4 : F
  eta : F
  eval1 : v1 = miller n P (add Q S)
  eval2 : v2 = miller n P S
  eval3 : v3 = miller n Q (neg S)
  eval4 : v4 = miller n Q (add P (neg S))
  denominatorsNonzero : v2 ≠ 0 ∧ v4 ≠ 0
  shiftedFormula : eta = (v1 / v2) * (v3 / v4)
  nTorsion : eta ^ n = 1

/-- Primitive n-th root predicate checked by factoring n and testing each
    prime divisor. -/
def IsPrimitiveWeilValue {F : Type} [Field F] (eta : F) (n : Nat) : Prop :=
  eta ^ n = 1 ∧
  ∀ ell : Nat, Nat.Prime ell → ell ∣ n → eta ^ (n / ell) ≠ 1

/-- A group-basis pairing transcript additionally proves primitivity. -/
structure PrimitiveShiftedWeilCertificate
    (Point F : Type) [Field F]
    (add : Point → Point → Point)
    (neg : Point → Point)
    (miller : MillerEval Point F)
    (n : Nat) (P Q S : Point)
    extends ShiftedWeilCertificate Point F add neg miller n P Q S where
  primitive : ∀ ell : Nat, Nat.Prime ell → ell ∣ n →
    eta ^ (n / ell) ≠ 1

theorem PrimitiveShiftedWeilCertificate.primitiveValue
    {Point F : Type} [Field F]
    {add : Point → Point → Point} {neg : Point → Point}
    {miller : MillerEval Point F} {n : Nat} {P Q S : Point}
    (cert : PrimitiveShiftedWeilCertificate Point F add neg miller n P Q S) :
    IsPrimitiveWeilValue cert.eta n :=
  ⟨cert.nTorsion, cert.primitive⟩

end ECDLPv2.X265
