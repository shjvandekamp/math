import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# An explicit interpolation coefficient in the weak-transfer calculation

This module checks the displayed real polynomial interpolation identity and
the resulting reduced rational scalar. The positive factor is
4 * (a - A)^2 + 3 * a * A, so the reduced scalar is nonzero when
a,A > 0, h ≠ 0, and its two denominator numerators are nonzero.
At h = 0 the reduced scalar vanishes.

The rational interpolation formula states every denominator hypothesis it
uses. Its reduced form needs no unit hypotheses for 1 - A*h or
1 - 4*A*h. These algebraic statements do not identify an actual source
row, prove a transfer theorem, or establish paired/source independence.
-/

namespace PanelMoments.SourceWeakTransferInterpolation

noncomputable section

def nodeNumerator0 (a A h : ℝ) : ℝ :=
  2 * (a - A) + A * h * (4 * a - A)

def nodeNumerator1 (a A h : ℝ) : ℝ :=
  a - 4 * A + 8 * A * h * (a - A)

def positiveFactor (a A : ℝ) : ℝ :=
  4 * a ^ 2 - 5 * a * A + 4 * A ^ 2

def interpolationValue (a A h : ℝ) : ℝ :=
  1 - (A - 2 * a) * (1 - 4 * A * h) / nodeNumerator0 a A h +
    4 * (2 * A - a) * (1 - A * h) / nodeNumerator1 a A h

def scaledInterpolationValue (a A h : ℝ) : ℝ :=
  (6 * A * h ^ 2 / ((1 - A * h) * (1 - 4 * A * h))) *
    interpolationValue a A h

def reducedValue (a A h : ℝ) : ℝ :=
  -6 * A * h ^ 2 * positiveFactor a A /
    (nodeNumerator0 a A h * nodeNumerator1 a A h)

/-- The interpolation certificate after clearing its two node denominators. -/
theorem interpolation_numerator_factorization (a A h : ℝ) :
    nodeNumerator0 a A h * nodeNumerator1 a A h -
        (A - 2 * a) * (1 - 4 * A * h) * nodeNumerator1 a A h +
        4 * (2 * A - a) * (1 - A * h) * nodeNumerator0 a A h =
      -(1 - A * h) * (1 - 4 * A * h) * positiveFactor a A := by
  unfold nodeNumerator0 nodeNumerator1 positiveFactor
  ring

theorem positiveFactor_eq_sq (a A : ℝ) :
    positiveFactor a A = 4 * (a - A) ^ 2 + 3 * a * A := by
  unfold positiveFactor
  ring

theorem positiveFactor_pos (a A : ℝ) (ha : 0 < a) (hA : 0 < A) :
    0 < positiveFactor a A := by
  rw [positiveFactor_eq_sq]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (by norm_num) (sq_nonneg (a - A)))
    (mul_pos (mul_pos (by norm_num) ha) hA)

theorem positiveFactor_ne_zero (a A : ℝ) (ha : 0 < a) (hA : 0 < A) :
    positiveFactor a A ≠ 0 :=
  ne_of_gt (positiveFactor_pos a A ha hA)

/-- The rational interpolation identity requires only its two node units. -/
theorem interpolationValue_factorization (a A h : ℝ)
    (hN0 : nodeNumerator0 a A h ≠ 0) (hN1 : nodeNumerator1 a A h ≠ 0) :
    interpolationValue a A h =
      -(1 - A * h) * (1 - 4 * A * h) * positiveFactor a A /
        (nodeNumerator0 a A h * nodeNumerator1 a A h) := by
  unfold interpolationValue
  field_simp [hN0, hN1]
  unfold nodeNumerator0 nodeNumerator1 positiveFactor
  ring

/-- Cancelling the two interpolation factors gives the stated reduced scalar. -/
theorem scaledInterpolationValue_eq_reducedValue (a A h : ℝ)
    (hN0 : nodeNumerator0 a A h ≠ 0) (hN1 : nodeNumerator1 a A h ≠ 0)
    (hleft : 1 - A * h ≠ 0) (hright : 1 - 4 * A * h ≠ 0) :
    scaledInterpolationValue a A h = reducedValue a A h := by
  have hright' : 1 - A * h * 4 ≠ 0 := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hright
  unfold scaledInterpolationValue reducedValue
  rw [interpolationValue_factorization a A h hN0 hN1]
  field_simp [hN0, hN1, hleft, hright, hright']

/-- Nonvanishing of the reduced scalar does not need the canceled factors
1 - A*h and 1 - 4*A*h to be units. -/
theorem reducedValue_ne_zero (a A h : ℝ) (ha : 0 < a) (hA : 0 < A)
    (hh : h ≠ 0)
    (hN0 : nodeNumerator0 a A h ≠ 0) (hN1 : nodeNumerator1 a A h ≠ 0) :
    reducedValue a A h ≠ 0 := by
  unfold reducedValue
  apply div_ne_zero _ (mul_ne_zero hN0 hN1)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hA)) (pow_ne_zero 2 hh))
    (positiveFactor_ne_zero a A ha hA)

/-- The boundary value vanishes even when a node denominator also vanishes. -/
theorem reducedValue_at_zero (a A : ℝ) : reducedValue a A 0 = 0 := by
  simp [reducedValue]

end

end PanelMoments.SourceWeakTransferInterpolation
