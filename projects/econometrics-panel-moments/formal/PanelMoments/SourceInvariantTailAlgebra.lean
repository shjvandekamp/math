import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Scalar algebra on the invariant tail-weight curve

The specialization b(A) = τ*A/(1+z*A) makes the weak difference Δ a
multiple of (r-z)/r. This module proves that rational identity, the
positive gauge-evaluation determinant, and the two endpoint multipliers
and evaluation pivot on the same curve. Every rational identity states
its denominator hypotheses.

The final three exact numerical identities check the proposed initial
endpoint kills and the following Δ(z) kill. These are scalar identities:
they do not identify an actual source-space invariant, establish a
transfer isomorphism, or prove paired/source independence.
-/

namespace PanelMoments.SourceInvariantTailAlgebra

noncomputable section

def tailWeight (A z τ : ℝ) : ℝ :=
  τ * A / (1 + z * A)

def weakDifference (A B bnew bold r : ℝ) : ℝ :=
  bnew * (1 + A * r) / (3 * A * r) -
    bold * (1 + B * r) / (3 * B * r)

def gaugeEvaluationDeterminant (A B bnew bold : ℝ) : ℝ :=
  (A * bold - B * bnew) * (bnew - bold) / (12 * A * B)

def kappaZero (A B bnew bold z : ℝ) : ℝ :=
  z / 2 * ((3 * B - 2 * A) * bnew - A * bold) / (A - B)

def kappaInfinity (A B bnew bold : ℝ) : ℝ :=
  (A * bold - (3 * A - 2 * B) * bnew) / (2 * A * (A - B))

def evaluationPivot (A B bnew bold : ℝ) : ℝ :=
  4 * bnew / 3 + weakDifference A B bnew bold (1 / A)

theorem tailUnit_pos (A z : ℝ) (hA : 0 < A) (hz : 0 < z) :
    0 < 1 + z * A :=
  add_pos (by norm_num) (mul_pos hz hA)

theorem tailUnit_ne_zero (A z : ℝ) (hA : 0 < A) (hz : 0 < z) :
    1 + z * A ≠ 0 :=
  ne_of_gt (tailUnit_pos A z hA hz)

theorem tailWeight_pos (A z τ : ℝ)
    (hA : 0 < A) (hz : 0 < z) (hτ : 0 < τ) :
    0 < tailWeight A z τ :=
  div_pos (mul_pos hτ hA) (tailUnit_pos A z hA hz)

theorem tailWeight_sub (A B z τ : ℝ)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    tailWeight A z τ - tailWeight B z τ =
      τ * (A - B) / ((1 + z * A) * (1 + z * B)) := by
  have hUA' : 1 + A * z ≠ 0 := by simpa only [mul_comm] using hUA
  have hUB' : 1 + B * z ≠ 0 := by simpa only [mul_comm] using hUB
  unfold tailWeight
  field_simp [hUA, hUB, hUA', hUB']
  ring

theorem tailWeight_ne (A B z τ : ℝ)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0)
    (hτ : τ ≠ 0) (hAB : A ≠ B) :
    tailWeight A z τ ≠ tailWeight B z τ := by
  apply sub_ne_zero.mp
  rw [tailWeight_sub A B z τ hUA hUB]
  exact div_ne_zero (mul_ne_zero hτ (sub_ne_zero.mpr hAB)) (mul_ne_zero hUA hUB)

/-- The tail curve forces the displayed factor r-z, under the original
weak-difference denominator hypotheses. -/
theorem weakDifference_tail (A B z τ r : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hr : r ≠ 0)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    weakDifference A B (tailWeight A z τ) (tailWeight B z τ) r =
      ((tailWeight A z τ - tailWeight B z τ) / 3) * (r - z) / r := by
  have hUA' : 1 + A * z ≠ 0 := by simpa only [mul_comm] using hUA
  have hUB' : 1 + B * z ≠ 0 := by simpa only [mul_comm] using hUB
  unfold weakDifference tailWeight
  field_simp [hA, hB, hr, hUA, hUB, hUA', hUB']
  ring

theorem weakDifference_tail_at_z (A B z τ : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hz : z ≠ 0)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    weakDifference A B (tailWeight A z τ) (tailWeight B z τ) z = 0 := by
  rw [weakDifference_tail A B z τ z hA hB hz hUA hUB]
  simp

theorem gaugeEvaluationDeterminant_tail (A B z τ : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    gaugeEvaluationDeterminant A B (tailWeight A z τ) (tailWeight B z τ) =
      τ ^ 2 * z * (A - B) ^ 2 /
        (12 * (1 + z * A) ^ 2 * (1 + z * B) ^ 2) := by
  have hUA' : 1 + A * z ≠ 0 := by simpa only [mul_comm] using hUA
  have hUB' : 1 + B * z ≠ 0 := by simpa only [mul_comm] using hUB
  unfold gaugeEvaluationDeterminant tailWeight
  field_simp [hA, hB, hUA, hUB, hUA', hUB']
  ring

theorem gaugeEvaluationDeterminant_tail_pos (A B z τ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) (hτ : 0 < τ)
    (hAB : A ≠ B) :
    0 < gaugeEvaluationDeterminant A B (tailWeight A z τ) (tailWeight B z τ) := by
  rw [gaugeEvaluationDeterminant_tail A B z τ (ne_of_gt hA) (ne_of_gt hB)
    (tailUnit_ne_zero A z hA hz) (tailUnit_ne_zero B z hB hz)]
  exact div_pos
    (mul_pos (mul_pos (sq_pos_of_ne_zero (ne_of_gt hτ)) hz)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hAB)))
    (mul_pos
      (mul_pos (by norm_num) (sq_pos_of_ne_zero (tailUnit_ne_zero A z hA hz)))
      (sq_pos_of_ne_zero (tailUnit_ne_zero B z hB hz)))

theorem gaugeEvaluationDeterminant_tail_ne_zero (A B z τ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) (hτ : 0 < τ)
    (hAB : A ≠ B) :
    gaugeEvaluationDeterminant A B (tailWeight A z τ) (tailWeight B z τ) ≠ 0 :=
  ne_of_gt (gaugeEvaluationDeterminant_tail_pos A B z τ hA hB hz hτ hAB)

theorem kappaZero_tail (A B z τ : ℝ)
    (hAB : A - B ≠ 0) (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    kappaZero A B (tailWeight A z τ) (tailWeight B z τ) z =
      -(τ * A * z * (2 + 3 * z * B) /
        (2 * (1 + z * A) * (1 + z * B))) := by
  unfold kappaZero tailWeight
  field_simp [hAB, hUA, hUB]
  ring

theorem kappaInfinity_tail (A B z τ : ℝ)
    (hA : A ≠ 0) (hAB : A - B ≠ 0)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    kappaInfinity A B (tailWeight A z τ) (tailWeight B z τ) =
      -(τ * (3 + 2 * z * B) /
        (2 * (1 + z * A) * (1 + z * B))) := by
  have hUA' : 1 + A * z ≠ 0 := by simpa only [mul_comm] using hUA
  have hUB' : 1 + B * z ≠ 0 := by simpa only [mul_comm] using hUB
  unfold kappaInfinity tailWeight
  field_simp [hA, hAB, hUA, hUB, hUA', hUB']
  ring

theorem kappaZero_tail_neg (A B z τ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) (hτ : 0 < τ)
    (hAB : A ≠ B) :
    kappaZero A B (tailWeight A z τ) (tailWeight B z τ) z < 0 := by
  rw [kappaZero_tail A B z τ (sub_ne_zero.mpr hAB)
    (tailUnit_ne_zero A z hA hz) (tailUnit_ne_zero B z hB hz)]
  apply neg_lt_zero.mpr
  exact div_pos
    (mul_pos (mul_pos (mul_pos hτ hA) hz)
      (add_pos (by norm_num) (mul_pos (mul_pos (by norm_num) hz) hB)))
    (mul_pos (mul_pos (by norm_num) (tailUnit_pos A z hA hz))
      (tailUnit_pos B z hB hz))

theorem kappaInfinity_tail_neg (A B z τ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) (hτ : 0 < τ)
    (hAB : A ≠ B) :
    kappaInfinity A B (tailWeight A z τ) (tailWeight B z τ) < 0 := by
  rw [kappaInfinity_tail A B z τ (ne_of_gt hA) (sub_ne_zero.mpr hAB)
    (tailUnit_ne_zero A z hA hz) (tailUnit_ne_zero B z hB hz)]
  apply neg_lt_zero.mpr
  exact div_pos
    (mul_pos hτ (add_pos (by norm_num) (mul_pos (mul_pos (by norm_num) hz) hB)))
    (mul_pos (mul_pos (by norm_num) (tailUnit_pos A z hA hz))
      (tailUnit_pos B z hB hz))

theorem evaluationPivot_tail (A B z τ : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0) :
    evaluationPivot A B (tailWeight A z τ) (tailWeight B z τ) =
      τ * (5 * A - B + A * z * (5 * B - A)) /
        (3 * (1 + z * A) * (1 + z * B)) := by
  have hUA' : 1 + A * z ≠ 0 := by simpa only [mul_comm] using hUA
  have hUB' : 1 + B * z ≠ 0 := by simpa only [mul_comm] using hUB
  unfold evaluationPivot weakDifference tailWeight
  field_simp [hA, hB, hUA, hUB, hUA', hUB']
  ring

theorem evaluationPivot_tail_ne_zero (A B z τ : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hτ : τ ≠ 0)
    (hUA : 1 + z * A ≠ 0) (hUB : 1 + z * B ≠ 0)
    (hN : 5 * A - B + A * z * (5 * B - A) ≠ 0) :
    evaluationPivot A B (tailWeight A z τ) (tailWeight B z τ) ≠ 0 := by
  rw [evaluationPivot_tail A B z τ hA hB hUA hUB]
  exact div_ne_zero (mul_ne_zero hτ hN)
    (mul_ne_zero (mul_ne_zero (by norm_num) hUA) hUB)

/-- The proposed third-step weight kills the zero-endpoint multiplier. -/
theorem kappaZero_initial_kill :
    kappaZero (3 / 2) (7 / 5) (5 / 2) 2 (1 / 10) = 0 := by
  norm_num [kappaZero]

/-- The proposed fourth-step weight kills the infinity-endpoint multiplier. -/
theorem kappaInfinity_initial_kill :
    kappaInfinity (8 / 5) (3 / 2) (20 / 9) (5 / 2) = 0 := by
  norm_num [kappaInfinity]

/-- The proposed fifth-step weight lies on the curve determined by the
previous step, so the weak difference vanishes at z=1/10. -/
theorem weakDifference_initial_kill :
    weakDifference (17 / 10) (8 / 5) (2465 / 1053) (20 / 9) (1 / 10) = 0 := by
  norm_num [weakDifference]

end

end PanelMoments.SourceInvariantTailAlgebra
