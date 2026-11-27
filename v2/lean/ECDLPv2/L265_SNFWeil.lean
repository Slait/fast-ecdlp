import Mathlib

/-!
# X265 SNF / Weil certificate interfaces

This module is the first Lean integration boundary for the production
SNF/Weil candidate. It deliberately separates executable certificate
checking from the producer.

The SNF certificate is for the X265-shaped rectangular matrix
M : Matrix (Fin 3) (Fin (s + 3)) Int. The Weil checker is parametric
in a Miller evaluator. Consequently, the theorem below proves transcript
consistency relative to that evaluator; it does not yet prove that an
arbitrary evaluator is the divisor-theoretic Miller function.
-/

namespace ECDLP.L265

/-- The rectangular relation matrix used by X265. -/
abbrev X265RelMat (s : ℕ) := Matrix (Fin 3) (Fin (s + 3)) ℤ

/-- The left row transformation in the rectangular SNF certificate. -/
abbrev X265Left := Matrix (Fin 3) (Fin 3) ℤ

/-- The right column transformation in the rectangular SNF certificate. -/
abbrev X265Right (s : ℕ) := Matrix (Fin (s + 3)) (Fin (s + 3)) ℤ

/-- Input contract: reduced relation columns followed by exactly N • I₃. -/
def X265Input {s : ℕ} (N : ℤ) (M : X265RelMat s) : Prop :=
  0 < N ∧
    (∀ i : Fin 3, ∀ j : Fin (s + 3), j.val < s →
      0 ≤ M i j ∧ M i j < N) ∧
    (∀ i : Fin 3, ∀ j : Fin (s + 3), s ≤ j.val →
      M i j = if i.val = j.val - s then N else 0)

/-- Full rectangular SNF transcript. D has three diagonal entries and
zeroes in every other column, including the final s columns. -/
structure SNFCertificate (s : ℕ) where
  S : X265Left
  T : X265Right s
  D : X265RelMat s

/-- Mathematical predicate checked by the SNF verifier. -/
def SNFCertificate.Valid {s : ℕ} (M : X265RelMat s)
    (cert : SNFCertificate s) : Prop :=
  cert.S * M * cert.T = cert.D ∧
  Int.natAbs cert.S.det = 1 ∧
  Int.natAbs cert.T.det = 1 ∧
  (∀ i : Fin 3, ∀ j : Fin (s + 3), i.val ≠ j.val → cert.D i j = 0) ∧
  0 < cert.D 0 0 ∧
  cert.D 0 0 ∣ cert.D 1 1 ∧
  cert.D 1 1 ∣ cert.D 2 2

/-- Boolean checker: it computes the exact matrix product and determinants. -/
def verifySNFCertificate {s : ℕ} (M : X265RelMat s)
    (cert : SNFCertificate s) : Bool :=
  decide (cert.Valid M)

/-- Soundness of the SNF certificate checker. -/
theorem verifySNFCertificate_sound {s : ℕ} (M : X265RelMat s)
    (cert : SNFCertificate s)
    (hcheck : verifySNFCertificate M cert = true) :
    cert.Valid M := by
  exact of_decide_eq_true hcheck

/-- X265 group-lattice endpoint: the invariant factors are (1,n₁,n₂)
and their product is the group order N. -/
def SNFCertificate.IsX265Lattice {s : ℕ} (N : ℤ)
    (M : X265RelMat s) (cert : SNFCertificate s) : Prop :=
  cert.Valid M ∧ cert.D 0 0 = 1 ∧
    cert.D 0 0 * cert.D 1 1 * cert.D 2 2 = N

/-- A Weil transcript stores the auxiliary point, the four shifted Miller
values, and the resulting root of unity. -/
structure WeilTranscript (α : Type*) (p : ℕ) where
  S : α
  v₁ : ZMod p
  v₂ : ZMod p
  v₃ : ZMod p
  v₄ : ZMod p
  eta : ZMod p

/-- Exact X265 shifted-divisor orientation, relative to a supplied Miller
evaluator. All four values must be the evaluator outputs and nonzero. -/
def WeilTranscript.Valid {α : Type*} [AddGroup α] {p : ℕ}
    [Fact p.Prime]
    (miller : ℕ → α → α → Option (ZMod p))
    (n : ℕ) (P Q : α) (cert : WeilTranscript α p) : Prop :=
  miller n P (Q + cert.S) = some cert.v₁ ∧
  miller n P cert.S = some cert.v₂ ∧
  miller n Q (-cert.S) = some cert.v₃ ∧
  miller n Q (P - cert.S) = some cert.v₄ ∧
  cert.v₁ ≠ 0 ∧ cert.v₂ ≠ 0 ∧ cert.v₃ ≠ 0 ∧ cert.v₄ ≠ 0 ∧
  cert.eta = cert.v₁ / cert.v₂ * cert.v₃ / cert.v₄ ∧
  cert.eta ^ n = 1

/-- Transcript checker interface. The caller supplies the Miller evaluator;
this checker recomputes all four arguments and checks the quotient and
n-th-root condition. -/
def verifyWeilTranscript {α : Type*} [AddGroup α] {p : ℕ}
    [Fact p.Prime]
    (miller : ℕ → α → α → Option (ZMod p))
    (n : ℕ) (P Q : α) (cert : WeilTranscript α p) : Bool :=
  decide (cert.Valid miller n P Q)

/-- Soundness of the shifted Weil transcript checker. -/
theorem verifyWeilTranscript_sound {α : Type*} [AddGroup α] {p : ℕ}
    [Fact p.Prime]
    (miller : ℕ → α → α → Option (ZMod p))
    (n : ℕ) (P Q : α) (cert : WeilTranscript α p)
    (hcheck : verifyWeilTranscript miller n P Q cert = true) :
    cert.Valid miller n P Q := by
  exact of_decide_eq_true hcheck

/-- The primitive-root condition used by the group-basis verifier. The
primeDivisors list must itself be checked as the complete prime-divisor
list of n by the caller. -/
def IsPrimitiveNRoot {p : ℕ} [Fact p.Prime] (n : ℕ)
    (primeDivisors : Finset ℕ) (eta : ZMod p) : Prop :=
  eta ^ n = 1 ∧
    ∀ ell ∈ primeDivisors, eta ^ (n / ell) ≠ 1

end ECDLP.L265
