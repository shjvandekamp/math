import PanelMoments.SourceInvariantTailBoundedExtension
import PanelMoments.SourceInvariantTailAlgebra
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Explicit interval conditions for the invariant-tail polynomial extension

The first old parameter is a=6/5 and z=1/10. The new parameter satisfies
17/10 ≤ A < 2; the previous parameter B lies in (1,2) and B<A. The
remaining old parameters alpha_i lie in (1,2) and differ from A.
With positive tau and the actual tail weights, these interval and
distinctness conditions discharge every TailUnits field. No nonzero
evaluation, matrix rank, or independence hypothesis is retained.

The old product is V=product_i(1-alpha_i X), and its scale is
(-3)^(n+2)*(6/5)*product_i alpha_i, for m=n+2. The final theorem proves
injectivity and a unique degree-bounded decomposition for the explicit
normalized polynomial extension on this region. The specific indexed
time schedule, the source-word bridge,
and the finite initialization are not asserted in this module.
-/

namespace PanelMoments.SourceInvariantTailSchedule

noncomputable section

open Polynomial
open scoped BigOperators
open SourceInvariantTailConcretePolynomials
open SourceInvariantTailAlgebra
open SourceInvariantTailPolynomialExtension
open SourceInvariantTailBoundedExtension

def scheduleProduct {n : ℕ} (alpha : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∏ i, form2 (alpha i)

def scheduleScale (n : ℕ) (alpha : Fin (n + 1) → ℝ) : ℝ :=
  (-3) ^ (n + 2) * (6 / 5) * ∏ i, alpha i

def tailGap (A B τ : ℝ) : ℝ :=
  (tailWeight A (1 / 10) τ - tailWeight B (1 / 10) τ) / 3

theorem xiNumerator_fixed_neg (A : ℝ) (hA : (17 / 10 : ℝ) ≤ A) :
    xiNumerator (6 / 5) A (1 / 10) < 0 := by
  unfold xiNumerator
  nlinarith [sq_nonneg A]

theorem pole0Numerator_fixed_neg (A : ℝ) (hA : (17 / 10 : ℝ) ≤ A) :
    pole0Numerator (6 / 5) A (1 / 10) < 0 := by
  unfold pole0Numerator
  nlinarith [sq_nonneg A]

theorem pole1Numerator_fixed_neg (A : ℝ) (hA : (17 / 10 : ℝ) ≤ A) :
    pole1Numerator (6 / 5) A (1 / 10) < 0 := by
  unfold pole1Numerator
  nlinarith [sq_nonneg A]

theorem form2_eval_xi_ne_zero (u A : ℝ) (hA : A ≠ 0) (huA : u ≠ A) :
    (form2 u).eval (xi A) ≠ 0 := by
  have heq : (form2 u).eval (xi A) = (A - u) / A := by
    simp [form2, xi]
    field_simp [hA]
  rw [heq]
  exact div_ne_zero (sub_ne_zero.mpr (Ne.symm huA)) hA

theorem form2_eval_pole0_ne_zero (u A : ℝ) (hu : 1 < u)
    (hApos : 0 < A) (hAupper : A < 2) :
    (form2 u).eval (pole0 A) ≠ 0 := by
  have heq : (form2 u).eval (pole0 A) = (A - 2 * u) / A := by
    simp [form2, pole0]
    field_simp [ne_of_gt hApos]
  rw [heq]
  exact div_ne_zero (ne_of_lt (by linarith : A - 2 * u < 0)) (ne_of_gt hApos)

theorem form2_eval_pole1_ne_zero (u A : ℝ) (hu : u < 2) (hA : 1 < A) :
    (form2 u).eval (pole1 A) ≠ 0 := by
  have hApos : 0 < A := by linarith
  have heq : (form2 u).eval (pole1 A) = (2 * A - u) / (2 * A) := by
    simp [form2, pole1]
    field_simp [ne_of_gt hApos]
  rw [heq]
  exact div_ne_zero (ne_of_gt (by linarith : 0 < 2 * A - u))
    (mul_ne_zero (by norm_num) (ne_of_gt hApos))

theorem form2_eval_fixed_z_pos (u : ℝ) (hu : u < 2) :
    0 < (form2 u).eval (1 / 10 : ℝ) := by
  simp [form2]
  linarith

theorem scheduleProduct_eval_ne_zero {n : ℕ} (alpha : Fin (n + 1) → ℝ) (r : ℝ)
    (h : ∀ i, (form2 (alpha i)).eval r ≠ 0) :
    (scheduleProduct alpha).eval r ≠ 0 := by
  simp only [scheduleProduct, eval_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => h i)

theorem scheduleProduct_natDegree_le {n : ℕ} (alpha : Fin (n + 1) → ℝ) :
    (scheduleProduct alpha).natDegree ≤ n + 1 := by
  have hform (u : ℝ) : (form2 u).natDegree ≤ 1 := by
    unfold form2
    exact (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  unfold scheduleProduct
  calc
    _ ≤ ∑ i : Fin (n + 1), (form2 (alpha i)).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin (n + 1), 1 := Finset.sum_le_sum (fun i _ => hform (alpha i))
    _ = n + 1 := by simp

theorem scheduleScale_ne_zero (n : ℕ) (alpha : Fin (n + 1) → ℝ)
    (h : ∀ i, 1 < alpha i) : scheduleScale n alpha ≠ 0 := by
  unfold scheduleScale
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero (n + 2) (by norm_num)) (by norm_num)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (by linarith [h i]))

theorem tailGap_pos (A B τ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hBA : B < A) (hτ : 0 < τ) : 0 < tailGap A B τ := by
  have hUA := tailUnit_pos A (1 / 10) hA (by norm_num)
  have hUB := tailUnit_pos B (1 / 10) hB (by norm_num)
  unfold tailGap
  rw [tailWeight_sub A B (1 / 10) τ (ne_of_gt hUA) (ne_of_gt hUB)]
  exact div_pos (div_pos (mul_pos hτ (sub_pos.mpr hBA)) (mul_pos hUA hUB)) (by norm_num)

/-- All concrete factor conditions hold throughout the actual tail region. -/
theorem tailUnits_of_intervals (n : ℕ) (A B τ : ℝ) (alpha : Fin (n + 1) → ℝ)
    (hA : (17 / 10 : ℝ) ≤ A ∧ A < 2) (hB : 1 < B ∧ B < 2)
    (hBA : B < A) (hτ : 0 < τ)
    (halpha : ∀ i, 1 < alpha i ∧ alpha i < 2) (hne : ∀ i, alpha i ≠ A) :
    TailUnits (6 / 5) A (1 / 10) (tailWeight A (1 / 10) τ) (tailGap A B τ)
      (scheduleScale n alpha) (scheduleProduct alpha) := by
  have hApos : 0 < A := by linarith [hA.1]
  have hAone : 1 < A := by linarith [hA.1]
  have hBpos : 0 < B := by linarith [hB.1]
  have hb := tailWeight_pos A (1 / 10) τ hApos (by norm_num) hτ
  have hell := tailGap_pos A B τ hApos hBpos hBA hτ
  have hxi : 0 < xi A - (1 / 10 : ℝ) := by
    apply sub_pos.mpr
    unfold xi
    apply (lt_div_iff₀ hApos).mpr
    linarith [hA.2]
  have hVxi : (scheduleProduct alpha).eval (xi A) ≠ 0 := by
    apply scheduleProduct_eval_ne_zero
    intro i
    exact form2_eval_xi_ne_zero (alpha i) A (ne_of_gt hApos) (hne i)
  have hUxi : (oldProduct (6 / 5) (scheduleProduct alpha)).eval (xi A) ≠ 0 := by
    have hfirst : (form2 (6 / 5)).eval (xi A) ≠ 0 :=
      form2_eval_xi_ne_zero (6 / 5) A (ne_of_gt hApos) (by linarith [hA.1])
    simpa only [oldProduct, eval_mul] using mul_ne_zero hfirst hVxi
  have hnew0 : 0 < 2 - A * (1 / 10 : ℝ) := by linarith [hA.2]
  have hnew1 : 0 < 1 - 2 * A * (1 / 10 : ℝ) := by linarith [hA.2]
  have hnew2 : 0 < 1 - A * (1 / 10 : ℝ) := by linarith [hA.2]
  refine {
    A_ne_zero := ne_of_gt hApos,
    b_ne_zero := ne_of_gt hb,
    ell_ne_zero := ne_of_gt hell,
    cScale_ne_zero := scheduleScale_ne_zero n alpha (fun i => (halpha i).1),
    z_ne_zero := by norm_num,
    xi_sub_z_ne_zero := ne_of_gt hxi,
    old_product_at_xi := hUxi,
    V_at_pole0 := ?_, V_at_pole1 := ?_, V_at_z := ?_,
    xi_numerator := ne_of_lt (xiNumerator_fixed_neg A hA.1),
    pole0_numerator := ne_of_lt (pole0Numerator_fixed_neg A hA.1),
    pole1_numerator := ne_of_lt (pole1Numerator_fixed_neg A hA.1),
    positive_factor := SourceWeakTransferInterpolation.positiveFactor_ne_zero
      (6 / 5) A (by norm_num) hApos,
    old_z_factor := by norm_num,
    new_z_factor0 := ne_of_gt hnew0,
    new_z_factor1 := ne_of_gt hnew1,
    new_z_factor2 := ne_of_gt hnew2,
    eta_ne_zero := ?_ }
  · apply scheduleProduct_eval_ne_zero
    intro i
    exact form2_eval_pole0_ne_zero (alpha i) A (halpha i).1 hApos hA.2
  · apply scheduleProduct_eval_ne_zero
    intro i
    exact form2_eval_pole1_ne_zero (alpha i) A (halpha i).2 hAone
  · apply scheduleProduct_eval_ne_zero
    intro i
    exact ne_of_gt (form2_eval_fixed_z_pos (alpha i) (halpha i).2)
  · exact ne_of_gt (add_pos (div_pos (mul_pos (by norm_num) hb) (by norm_num))
      (mul_pos hell hnew2))

def scheduledExtension (n : ℕ) (A B τ : ℝ) (alpha : Fin (n + 1) → ℝ) :
    ℝ × ℝ × ℝ × Polynomial ℝ → Polynomial ℝ :=
  combinedExtension (transferFactor A (1 / 10) (tailWeight A (1 / 10) τ))
    (transferCorrection n (6 / 5) A (1 / 10) (tailGap A B τ) (scheduleProduct alpha))
    (commonFactor n (tailGap A B τ) (scheduleScale n alpha) (scheduleProduct alpha) * n0 (6 / 5) A (1 / 10))
    (commonFactor n (tailGap A B τ) (scheduleScale n alpha) (scheduleProduct alpha) * n1 (6 / 5) A (1 / 10))
    (commonFactor n (tailGap A B τ) (scheduleScale n alpha) (scheduleProduct alpha) * barN2 (6 / 5) A (1 / 10))
    (xi A)

/-- Concrete polynomial injectivity with only interval, distinctness and
positive-weight assumptions; no unspecified nonzero factors remain. -/
theorem scheduledExtension_injective (n : ℕ) (A B τ : ℝ) (alpha : Fin (n + 1) → ℝ)
    (hA : (17 / 10 : ℝ) ≤ A ∧ A < 2) (hB : 1 < B ∧ B < 2)
    (hBA : B < A) (hτ : 0 < τ)
    (halpha : ∀ i, 1 < alpha i ∧ alpha i < 2) (hne : ∀ i, alpha i ≠ A) :
    Function.Injective (scheduledExtension n A B τ alpha) :=
  concreteExtension_injective n (6 / 5) A (1 / 10)
    (tailWeight A (1 / 10) τ) (tailGap A B τ) (scheduleScale n alpha) (scheduleProduct alpha)
    (tailUnits_of_intervals n A B τ alpha hA hB hBA hτ halpha hne)

/-- The bounded explicit extension is a linear equivalence on the tail region. -/
def scheduledBoundedEquiv (n : ℕ) (A B τ : ℝ) (alpha : Fin (n + 1) → ℝ)
    (hA : (17 / 10 : ℝ) ≤ A ∧ A < 2) (hB : 1 < B ∧ B < 2)
    (hBA : B < A) (hτ : 0 < τ)
    (halpha : ∀ i, 1 < alpha i ∧ alpha i < 2) (hne : ∀ i, alpha i ≠ A) :
    (ℝ × ℝ × ℝ × degreeLT ℝ (3 * n + 4)) ≃ₗ[ℝ] degreeLT ℝ (3 * n + 7) :=
  concreteBoundedEquiv n (6 / 5) A (1 / 10)
    (tailWeight A (1 / 10) τ) (tailGap A B τ) (scheduleScale n alpha) (scheduleProduct alpha)
    (tailUnits_of_intervals n A B τ alpha hA hB hBA hτ halpha hne)
    (scheduleProduct_natDegree_le alpha)

/-- Every target polynomial of degree at most 3n+6 has a unique input,
using only the displayed interval and distinctness assumptions. -/
theorem scheduled_existsUnique_boundedInput
    (n : ℕ) (A B τ : ℝ) (alpha : Fin (n + 1) → ℝ)
    (hA : (17 / 10 : ℝ) ≤ A ∧ A < 2) (hB : 1 < B ∧ B < 2)
    (hBA : B < A) (hτ : 0 < τ)
    (halpha : ∀ i, 1 < alpha i ∧ alpha i < 2) (hne : ∀ i, alpha i ≠ A)
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ 3 * n + 6) :
    ∃! input : ℝ × ℝ × ℝ × degreeLT ℝ (3 * n + 4),
      scheduledExtension n A B τ alpha
        (input.1, input.2.1, input.2.2.1, (input.2.2.2 : Polynomial ℝ)) = Q :=
  concrete_existsUnique_boundedInput n (6 / 5) A (1 / 10)
    (tailWeight A (1 / 10) τ) (tailGap A B τ) (scheduleScale n alpha) (scheduleProduct alpha)
    (tailUnits_of_intervals n A B τ alpha hA hB hBA hτ halpha hne)
    (scheduleProduct_natDegree_le alpha) Q hQ

end

end PanelMoments.SourceInvariantTailSchedule
