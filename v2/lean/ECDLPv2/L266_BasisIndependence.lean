import Mathlib

/-!
# X266 / X268: primitive alternating pairings force independence

This module proves the algebraic step that was missing between the X265
primitive-Weil-value check and the X266 group-basis argument.

It is deliberately abstract: the elliptic-curve Weil pairing must still be
shown to satisfy the pairing laws below, and the Miller transcript must still
be shown to compute that pairing. No such geometric/Miller theorem is assumed
or claimed here.
-/

namespace ECDLPv2.L266

universe u v

variable {G : Type u} {H : Type v}
variable [AddCommGroup G] [CommGroup H]

/-- The algebraic laws of an alternating bilinear pairing into a
commutative multiplicative group. -/
structure WeilPairingLaws (G : Type u) (H : Type v)
    [AddCommGroup G] [CommGroup H] where
  value : G → G → H
  value_zero_left : ∀ y, value 0 y = 1
  value_add_left : ∀ x y z, value (x + y) z = value x z * value y z
  value_add_right : ∀ x y z, value x (y + z) = value x y * value x z
  value_alternating : ∀ x, value x x = 1
  value_skew : ∀ x y, value y x = (value x y)⁻¹

/-- An exact-order certificate for a multiplicative element. The minimality
clause is the semantic content of saying that the order is exactly n. -/
structure HasExactOrder {H : Type v} [Group H] (η : H) (n : ℕ) : Prop where
  positive : 0 < n
  pow_eq_one : η ^ n = 1
  minimal : ∀ k : ℕ, 0 < k → k < n → η ^ k ≠ 1

/-- If an element has exact order n, every exponent annihilating it is
divisible by n. -/
theorem exactOrder_dvd {η : H} {n k : ℕ}
    (hη : HasExactOrder η n) (hk : η ^ k = 1) : n ∣ k := by
  have hdecomp : k % n + n * (k / n) = k := Nat.mod_add_div k n
  have hmod : η ^ (k % n) = 1 := by
    calc
      η ^ (k % n) = η ^ (k % n) * (η ^ n) ^ (k / n) := by
        simp [hη.pow_eq_one]
      _ = η ^ (k % n + n * (k / n)) := by
        rw [← pow_mul, ← pow_add]
      _ = 1 := by rw [hdecomp, hk]
  have hrem : k % n = 0 := by
    by_contra hne
    exact hη.minimal (k % n) (Nat.pos_of_ne_zero hne)
      (Nat.mod_lt _ hη.positive) hmod
  exact Nat.dvd_of_mod_eq_zero hrem

/-- Bilinearity in the first argument, iterated over natural multiples. -/
theorem value_nsmul_left (e : WeilPairingLaws G H)
    (k : ℕ) (x y : G) :
    e.value (k • x) y = e.value x y ^ k := by
  induction k with
  | zero =>
      simpa using e.value_zero_left y
  | succ k ih =>
      rw [succ_nsmul, e.value_add_left, ih, pow_succ]

/-- Bilinearity in the second argument, iterated over natural multiples. -/
theorem value_nsmul_right (e : WeilPairingLaws G H)
    (k : ℕ) (x y : G) :
    e.value x (k • y) = e.value x y ^ k := by
  induction k with
  | zero =>
      have h0 : e.value x 0 = (e.value 0 x)⁻¹ := by
        rw [e.value_skew]
      simpa [e.value_zero_left] using h0
  | succ k ih =>
      rw [succ_nsmul, e.value_add_right, ih, pow_succ]

/-- A basis candidate consists of two n-torsion elements whose pairing
value has exact order n. -/
structure WeilBasisCertificate (e : WeilPairingLaws G H) (n : ℕ) where
  U : G
  V : G
  U_torsion : n • U = 0
  V_torsion : n • V = 0
  pairing_exact_order : HasExactOrder (e.value U V) n

/-- Any relation a U + b V = 0 forces both coefficients to be multiples
of n. Pairing with U detects b; pairing with V detects a. -/
theorem relation_coefficients_divisible
    (e : WeilPairingLaws G H) {U V : G} {n a b : ℕ}
    (hη : HasExactOrder (e.value U V) n)
    (hrel : a • U + b • V = 0) :
    n ∣ a ∧ n ∣ b := by
  have hU : e.value (a • U + b • V) U = 1 := by
    rw [hrel, e.value_zero_left]
  rw [e.value_add_left, e.value_nsmul_left, e.value_nsmul_left] at hU
  rw [e.value_alternating, e.value_skew] at hU
  have hbpow : (e.value U V) ^ b = 1 := by
    have hInv : ((e.value U V) ^ b)⁻¹ = 1 := by
      simpa [inv_pow] using hU
    simpa using congrArg Inv.inv hInv

  have hV : e.value (a • U + b • V) V = 1 := by
    rw [hrel, e.value_zero_left]
  rw [e.value_add_left, e.value_nsmul_left, e.value_nsmul_left] at hV
  rw [e.value_alternating] at hV
  have hapow : (e.value U V) ^ a = 1 := by
    simpa using hV

  exact ⟨exactOrder_dvd hη hapow, exactOrder_dvd hη hbpow⟩

/-- In the coefficient window 0 ≤ a,b < n, a relation is necessarily
trivial. This is the precise independence statement needed before using
the cardinality of the elliptic n-torsion subgroup to conclude that U,V
form a basis. -/
theorem no_small_nontrivial_relation
    (e : WeilPairingLaws G H) {n a b : ℕ}
    (cert : WeilBasisCertificate e n)
    (ha : a < n) (hb : b < n)
    (hrel : a • cert.U + b • cert.V = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨hda, hdb⟩ :=
    relation_coefficients_divisible e cert.pairing_exact_order hrel
  constructor
  · rcases hda with ⟨q, hq⟩
    omega
  · rcases hdb with ⟨q, hq⟩
    omega

end ECDLPv2.L266
