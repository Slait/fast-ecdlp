import Mathlib
import ECDLP.L49_Dil
import ECDLP.L49_Transport

/-!
# L49: polynomial-root reduction for the dilation nondegeneracy input

This module isolates the exact algebraic certificate needed for Lemma N'. Once a nonzero
one-variable polynomial of degree at most `D'` vanishing on every dilated relation is supplied,
the bound `2 * D'` follows in Lean from the polynomial root bound and the two-to-one map
`u ↦ u⁻²`. The remaining mathematical task is to construct that polynomial certificate from the
Semaev summation polynomials and prove its nonvanishing for non-trivial tuples.
-/

open Finset

namespace ECDLP.L49

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- A map whose fibres have at most two explicitly described elements pulls back a polynomial's
root set to at most twice its degree. -/
theorem card_filter_roots_le_two_mul_natDegree
    {α K : Type*} [Fintype α] [DecidableEq α] [Field K] [DecidableEq K]
    (p : Polynomial K) (hp : p ≠ 0) (s : α → K) (neg : α → α)
    (hfiber : ∀ a b, s a = s b → b = a ∨ b = neg a) :
    ((univ : Finset α).filter (fun a => p.eval (s a) = 0)).card ≤ 2 * p.natDegree := by
  classical
  let S := (univ : Finset α).filter (fun a => p.eval (s a) = 0)
  have hmaps : (↑S : Set α).MapsTo s ↑(p.roots.toFinset) := by
    intro a ha
    simp only [S, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).2 (by simpa [Polynomial.IsRoot] using ha))
  have hfib : ∀ z ∈ p.roots.toFinset, (S.filter (fun a => s a = z)).card ≤ 2 := by
    intro z hz
    rcases (S.filter (fun a => s a = z)).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · simp [h]
    · have hsub : S.filter (fun b => s b = z) ⊆ {a, neg a} := by
        intro b hb
        simp only [mem_filter] at hb
        have hab : s a = s b := (mem_filter.mp ha).2.trans hb.2.symm
        rcases hfiber a b hab with h | h
        · simp [h]
        · simp [h]
      exact (card_le_card hsub).trans card_le_two
  calc
    S.card = ∑ z ∈ p.roots.toFinset, (S.filter (fun a => s a = z)).card :=
      card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ z ∈ p.roots.toFinset, 2 := sum_le_sum (fun z hz => hfib z hz)
    _ = 2 * p.roots.toFinset.card := by simp [mul_comm]
    _ ≤ 2 * p.natDegree := by
      gcongr
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p)

/-- A Semaev-style certificate specialised to a fixed curve: for each non-trivial tuple of
factor-base abscissas, a nonzero polynomial in the dilation parameter vanishes whenever the
corresponding points sum to zero. -/
def DilationPolynomialWitness (A B : K) (m : ℕ) (T : Finset K) (D' : ℕ) : Prop :=
  ∀ t : Fin (2 * m) → K, (∀ i, t i ∈ T) → ¬ TrivL (List.ofFn t) →
    ∃ p : Polynomial K, p ≠ 0 ∧ p.natDegree ≤ D' ∧
      ∀ s : K,
        (∃ P : Fin (2 * m) → (shortW A B).Point,
          (∀ i, P i ≠ 0 ∧ ECDLP.L43.xco _ (P i) = s * t i) ∧ ∑ i, P i = 0) →
        p.eval s = 0

def negUnit {K : Type*} [Field K] (u : Kˣ) : Kˣ :=
  Units.mk0 (-(u : K)) (neg_ne_zero.mpr u.ne_zero)

/-- The inverse-square map on `Kˣ` has fibres of size at most two. -/
theorem invSq_fiber_two {K : Type*} [Field K] (u v : Kˣ)
    (h : ((u : K)⁻¹) ^ 2 = ((v : K)⁻¹) ^ 2) :
    v = u ∨ v = negUnit u := by
  have hsq : (u : K) ^ 2 = (v : K) ^ 2 := by
    have h' := congrArg Inv.inv h
    simpa only [inv_pow, inv_inv] using h'
  have hprod : ((u : K) - (v : K)) * ((u : K) + (v : K)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hprod with hdiff | hsum
  · left
    apply Units.ext
    exact (sub_eq_zero.mp hdiff).symm
  · right
    apply Units.ext
    change (v : K) = -(u : K)
    linear_combination hsum

/-- Lemma N' reduces to the polynomial certificate above. The factor two is exactly the
multiplicity of `u ↦ u⁻²`; no assumption on the characteristic is needed for this fibre count. -/
theorem dilationNondeg_of_polynomialWitness
    (A B : K) (m : ℕ) (T : Finset K) (D' : ℕ)
    (hW : DilationPolynomialWitness A B m T D') :
    DilationNondeg A B m T D' := by
  classical
  intro t ht htriv
  obtain ⟨p, hp, hdeg, hvan⟩ := hW t ht htriv
  let s : Kˣ → K := fun u => ((u : K)⁻¹) ^ 2
  let S := (univ : Finset Kˣ).filter (fun u =>
    ∃ P : Fin (2 * m) → (Eu A B u).Point,
      (∀ i, P i ≠ 0 ∧ ECDLP.L43.xco _ (P i) = t i) ∧ ∑ i, P i = 0)
  have hsub : S ⊆ (univ : Finset Kˣ).filter (fun u => p.eval (s u) = 0) := by
    intro u hu
    simp only [S, mem_filter, mem_univ, true_and] at hu
    obtain ⟨P, hP, hsum⟩ := hu
    let e := dilEquiv A B u
    let Q : Fin (2 * m) → (shortW A B).Point := fun i => e.symm (P i)
    have heq : ∀ i, dil A B u (Q i) = P i := by
      intro i
      exact e.apply_symm_apply (P i)
    have hQne : ∀ i, Q i ≠ 0 := by
      intro i hzero
      have hzero' : P i = 0 := by rw [← heq i, hzero, map_zero]
      exact (hP i).1 hzero'
    have hQx : ∀ i, ECDLP.L43.xco _ (Q i) = s u * t i := by
      intro i
      have hscale : (u : K) ^ 2 * ECDLP.L43.xco _ (Q i) = t i := by
        calc
          (u : K) ^ 2 * ECDLP.L43.xco _ (Q i) = ECDLP.L43.xco _ (dil A B u (Q i)) :=
            (xco_dil A B u (Q i)).symm
          _ = ECDLP.L43.xco _ (P i) := by rw [heq i]
          _ = t i := (hP i).2
      calc
        ECDLP.L43.xco _ (Q i) = ((u : K) ^ 2)⁻¹ *
            ((u : K) ^ 2 * ECDLP.L43.xco _ (Q i)) := by
          field_simp [u.ne_zero]
        _ = s u * t i := by simp [s, inv_pow, hscale]
    have hQsum : ∑ i, Q i = 0 := by
      apply dil_injective A B u
      have hmap : dil A B u (∑ i, Q i) = ∑ i, P i := by
        rw [map_sum]
        exact sum_congr rfl (fun i hi => heq i)
      simpa [hsum] using hmap
    have hroot := hvan (s u) ⟨Q, fun i => ⟨hQne i, hQx i⟩, hQsum⟩
    exact mem_filter.mpr ⟨mem_univ _, hroot⟩
  have hfiber : ∀ u v : Kˣ, s u = s v → v = u ∨ v = negUnit u := by
    intro u v huv
    exact invSq_fiber_two u v huv
  have hroot := card_filter_roots_le_two_mul_natDegree p hp s negUnit hfiber
  calc
    S.card ≤ ((univ : Finset Kˣ).filter (fun u => p.eval (s u) = 0)).card := card_le_card hsub
    _ ≤ 2 * p.natDegree := hroot
    _ ≤ 2 * D' := Nat.mul_le_mul_left 2 hdeg

end ECDLP.L49
