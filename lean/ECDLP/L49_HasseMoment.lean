import Mathlib
import ECDLP.L49_Main

/-!
# L49: the exact second-moment reduction for the factor-base size

The factor-base deviation is a sum of quadratic characters. This file proves the exact expansion
of its second moment into pair-correlation sums, and also proves the unconditional but deliberately
coarse bound `FactorBaseVar ... |T|`.

The sharp constant used by the paper requires a Weil bound for the off-diagonal sextic character
sums `χ(f(sx) f(sy))` (a genus-two curve in the generic case). The separately available
Hasse--Weil development proves the elliptic-curve bound (genus one), which is not by itself that
sextic estimate. No such genus-two estimate is postulated here.
-/

open Finset ECDLP.L43

namespace ECDLP.L49

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The quadratic-character term for the factor-base count on the dilated curve `E_u`. -/
noncomputable def dilatedQuadraticCharacter (A B : K) (u : Kˣ) (x : K) : ℝ :=
  (quadraticChar K (x ^ 3 + (u : K) ^ 4 * A * x + (u : K) ^ 6 * B) : ℝ)

/-- Every x-coordinate contributes at most two points to the factor base. -/
theorem fb_card_le_two_mul (A B : K) (T : Finset K) :
    (fb A B T).card ≤ 2 * T.card := by
  classical
  let W := shortW A B
  have hmaps : (↑(fb A B T) : Set W.Point).MapsTo (xco W) ↑T := by
    intro P hP
    simp only [fb, mem_filter, mem_univ, true_and] at hP
    exact hP.2
  calc
    (fb A B T).card = ∑ x ∈ T, ((fb A B T).filter (fun P => xco W P = x)).card :=
      card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ x ∈ T, 2 := by
      refine sum_le_sum (fun x hx => ?_)
      have hsub : ((fb A B T).filter (fun P => xco W P = x)) ⊆
          (univ : Finset W.Point).filter (fun P => xc W P = some x) := by
        intro P hP
        simp only [mem_filter] at hP
        cases P <;> simp_all [fb, xc, xco]
      exact (card_le_card hsub).trans (card_fibre_le_two W univ (some x))
    _ = 2 * T.card := by simp [mul_comm]

/-- The factor-base variance over dilations is exactly the sum of pair correlations of the
quadratic-character sequence. -/
theorem factorBase_moment_eq_pairCorrelation
    (hK : ringChar K ≠ 2) (A B : K) (hd : disc A B ≠ 0) (T : Finset K) :
    ∑ u : Kˣ, (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - T.card) ^ 2 =
      ∑ u : Kˣ, ∑ x ∈ T, ∑ y ∈ T,
        dilatedQuadraticCharacter A B u x * dilatedQuadraticCharacter A B u y := by
  classical
  apply sum_congr rfl
  intro u hu
  have hdu : disc ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) ≠ 0 :=
    disc_dil_ne A B u hd
  have hcard := card_fb hK ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) hdu T
  have hcardR : ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) =
      (fsize T ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) : ℝ) := by
    exact_mod_cast hcard
  have hdev :
      ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - T.card =
        ∑ x ∈ T, dilatedQuadraticCharacter A B u x := by
    rw [hcardR]
    simp [fsize, dilatedQuadraticCharacter, Int.cast_sum, Int.cast_add,
      Int.cast_one, Finset.sum_add_distrib]
  rw [hdev, sq, Finset.sum_mul_sum]

/-- Any pair-correlation estimate immediately supplies `FactorBaseVar`. This is the precise
analytic interface needed for the sharp Weil/Hasse-moment argument. -/
theorem factorBaseVar_of_pairCorrelation
    (hK : ringChar K ≠ 2) (A B : K) (hd : disc A B ≠ 0) (T : Finset K) (c : ℝ)
    (hCorr : ∑ u : Kˣ, ∑ x ∈ T, ∑ y ∈ T,
      dilatedQuadraticCharacter A B u x * dilatedQuadraticCharacter A B u y
        ≤ c * T.card * Fintype.card Kˣ) :
    FactorBaseVar A B T c := by
  unfold FactorBaseVar
  rw [factorBase_moment_eq_pairCorrelation hK A B hd T]
  exact hCorr

/-- A fully formal unconditional fallback: the deviation from `|T|` is at most `|T|` for every
model, hence its second moment is at most `|T|² |Kˣ|`. This bound is generally too coarse to give
the paper's nontrivial coverage fraction, but it closes the variance inequality without an analytic
hypothesis. -/
theorem factorBaseVar_trivial (A B : K) (T : Finset K) :
    FactorBaseVar A B T (T.card : ℝ) := by
  classical
  unfold FactorBaseVar
  let X : ℝ := T.card
  have hdev (u : Kˣ) :
      -X ≤ ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X ∧
      ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X ≤ X := by
    have hlow : (0 : ℝ) ≤ (fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card := by positivity
    have hhigh : ((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) ≤ 2 * X := by
      dsimp [X]
      exact_mod_cast fb_card_le_two_mul A B T
    constructor <;> dsimp [X] <;> linarith
  have hsq (u : Kˣ) :
      (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X) ^ 2 ≤ X ^ 2 := by
    obtain ⟨hlo, hhi⟩ := hdev u
    have hleft : 0 ≤ X - (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X) := by linarith
    have hright : 0 ≤ X + (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - X) := by linarith
    nlinarith [mul_nonneg hleft hright]
  calc
    ∑ u : Kˣ, (((fb ((u : K) ^ 4 * A) ((u : K) ^ 6 * B) T).card : ℝ) - T.card) ^ 2
      ≤ ∑ u : Kˣ, X ^ 2 := sum_le_sum (fun u hu => hsq u)
    _ = (Fintype.card Kˣ : ℝ) * X ^ 2 := by simp
    _ = X * T.card * Fintype.card Kˣ := by dsimp [X]; ring

end ECDLP.L49
