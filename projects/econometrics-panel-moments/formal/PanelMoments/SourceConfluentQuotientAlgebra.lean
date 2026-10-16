import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Displayed determinant algebra for the confluent three-class quotient

The first matrix uses the corrected third-row first entry
(s - 2*e*s - 1)/(6*e). Its determinant at e=1 is positive for 0<s<1.
At e=-1 its second row vanishes. Replacing that row by the displayed
coefficient row gives a determinant whose positivity at s=(1/3)^m is
proved here for every natural m>=3, including the required length bound
by induction rather than as a hypothesis.

These are identities and inequalities for explicitly defined matrices.
No theorem here identifies them with actual source functions or asserts
that the replacement row is an analytic derivative. The actual quotient,
confluence, endpoint-section, and source-space bridges remain separate
paper arguments; this module does not prove Eq. (24).
-/

namespace PanelMoments.SourceConfluentQuotientAlgebra

noncomputable section

/-- Rows are the three quotient coordinates; columns are the three targets. -/
def quotientMatrix (e s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1 - 1 / (3 * s), 0, -9 / 2],
    ![(e + 1) / (6 * e), 0, 0],
    ![(s - 2 * e * s - 1) / (6 * e),
      (2 * e * s - e - s) / (6 * e),
      (4 * e * s + e - 2 * s) / (2 * e)]]

/-- The displayed replacement for the vanishing second row at e=-1. -/
def replacementRow (m s : ℝ) : Fin 3 → ℝ :=
  ![(2 * (1 - s) - m * (1 + s)) / 9,
    ((m + 2) * s - 1) / 9,
    2 * (m + 2) * s / 3]

def oddReplacementMatrix (m s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![(quotientMatrix (-1) s) 0, replacementRow m s, (quotientMatrix (-1) s) 2]

def oddCoefficient (m s : ℝ) : ℝ :=
  (3 * s - 1) * ((15 * m - 9) * s - 2) / (108 * s)

def thirdPower (m : ℕ) : ℝ := (1 / 3) ^ m

def coordinateConversionMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, -1, 1], ![1, 0, θ], ![0, 1, 2 - 2 * θ]]

/-- In fact the displayed determinant identity needs only e!=0;
the parity specializations are immediate consequences. -/
theorem quotientMatrix_det (e s : ℝ) (he : e ≠ 0) :
    (quotientMatrix e s).det = -(e + 1) * (2 * e * s - e - s) / (8 * e ^ 2) := by
  rw [Matrix.det_fin_three (quotientMatrix e s)]
  simp [quotientMatrix]
  field_simp [he]
  ring

theorem quotientMatrix_even_det (s : ℝ) :
    (quotientMatrix 1 s).det = (1 - s) / 4 := by
  rw [quotientMatrix_det 1 s (by norm_num)]
  ring

theorem quotientMatrix_even_det_pos (s : ℝ) (hs : s < 1) :
    0 < (quotientMatrix 1 s).det := by
  rw [quotientMatrix_even_det]
  exact div_pos (sub_pos.mpr hs) (by norm_num)

theorem quotientMatrix_odd_second_row (s : ℝ) :
    (quotientMatrix (-1) s) 1 = 0 := by
  funext j
  fin_cases j <;> norm_num [quotientMatrix]

theorem quotientMatrix_odd_det (s : ℝ) :
    (quotientMatrix (-1) s).det = 0 := by
  rw [quotientMatrix_det (-1) s (by norm_num)]
  norm_num

/-- This checks the determinant of the explicit replacement matrix;
it does not assert a derivative identity for an actual function family. -/
theorem oddReplacementMatrix_det (m s : ℝ) (hs : s ≠ 0) :
    (oddReplacementMatrix m s).det = oddCoefficient m s := by
  rw [Matrix.det_fin_three (oddReplacementMatrix m s)]
  simp [oddReplacementMatrix, quotientMatrix, replacementRow, oddCoefficient]
  field_simp [hs]
  ring

theorem coordinateConversionMatrix_det (θ : ℝ) :
    (coordinateConversionMatrix θ).det = 3 * (1 - θ) := by
  rw [Matrix.det_fin_three (coordinateConversionMatrix θ)]
  simp [coordinateConversionMatrix]
  ring

theorem coordinateConversionMatrix_det_ne_zero (θ : ℝ) (hθ : θ ≠ 1) :
    (coordinateConversionMatrix θ).det ≠ 0 := by
  rw [coordinateConversionMatrix_det]
  exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hθ))

theorem thirdPower_pos (m : ℕ) : 0 < thirdPower m :=
  pow_pos (by norm_num) m

theorem thirdPower_le_one_twenty_seven (m : ℕ) (hm : 3 ≤ m) :
    thirdPower m ≤ 1 / 27 := by
  unfold thirdPower
  calc
    (1 / 3 : ℝ) ^ m ≤ (1 / 3 : ℝ) ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = 1 / 27 := by norm_num

theorem thirdPower_lt_one (m : ℕ) (hm : 3 ≤ m) : thirdPower m < 1 := by
  have h := thirdPower_le_one_twenty_seven m hm
  linarith

theorem three_mul_thirdPower_lt_one (m : ℕ) (hm : 3 ≤ m) :
    3 * thirdPower m < 1 := by
  have h := thirdPower_le_one_twenty_seven m hm
  linarith

/-- The weighted geometric expression decreases from length three onward. -/
theorem weightedPower_succ_le (m : ℕ) (hm : 3 ≤ m) :
    (15 * ((m + 1 : ℕ) : ℝ) - 9) * thirdPower (m + 1) ≤
      (15 * (m : ℝ) - 9) * thirdPower m := by
  have hm_real : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnonneg : 0 ≤ (10 * (m : ℝ) - 11) * thirdPower m :=
    mul_nonneg (by linarith) (le_of_lt (thirdPower_pos m))
  unfold thirdPower at *
  rw [pow_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The all-natural-length estimate is proved by induction, not assumed. -/
theorem weightedPower_le_four_thirds (m : ℕ) (hm : 3 ≤ m) :
    (15 * (m : ℝ) - 9) * thirdPower m ≤ 4 / 3 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [thirdPower]
  | succ m hm ih => exact (weightedPower_succ_le m hm).trans ih

theorem weightedPower_lt_two (m : ℕ) (hm : 3 ≤ m) :
    (15 * (m : ℝ) - 9) * thirdPower m < 2 := by
  have h := weightedPower_le_four_thirds m hm
  linarith

theorem oddCoefficient_pos_at_length (m : ℕ) (hm : 3 ≤ m) :
    0 < oddCoefficient (m : ℝ) (thirdPower m) := by
  have hfirst : 3 * thirdPower m - 1 < 0 :=
    sub_neg.mpr (three_mul_thirdPower_lt_one m hm)
  have hsecond : (15 * (m : ℝ) - 9) * thirdPower m - 2 < 0 :=
    sub_neg.mpr (weightedPower_lt_two m hm)
  unfold oddCoefficient
  exact div_pos (mul_pos_of_neg_of_neg hfirst hsecond)
    (mul_pos (by norm_num) (thirdPower_pos m))

theorem oddCoefficient_ne_zero_at_length (m : ℕ) (hm : 3 ≤ m) :
    oddCoefficient (m : ℝ) (thirdPower m) ≠ 0 :=
  ne_of_gt (oddCoefficient_pos_at_length m hm)

theorem quotientMatrix_even_det_pos_at_length (m : ℕ) (hm : 3 ≤ m) :
    0 < (quotientMatrix 1 (thirdPower m)).det :=
  quotientMatrix_even_det_pos (thirdPower m) (thirdPower_lt_one m hm)

theorem quotientMatrix_even_det_ne_zero_at_length (m : ℕ) (hm : 3 ≤ m) :
    (quotientMatrix 1 (thirdPower m)).det ≠ 0 :=
  ne_of_gt (quotientMatrix_even_det_pos_at_length m hm)

theorem oddReplacementMatrix_det_pos_at_length (m : ℕ) (hm : 3 ≤ m) :
    0 < (oddReplacementMatrix (m : ℝ) (thirdPower m)).det := by
  rw [oddReplacementMatrix_det (m : ℝ) (thirdPower m) (ne_of_gt (thirdPower_pos m))]
  exact oddCoefficient_pos_at_length m hm

theorem oddReplacementMatrix_det_ne_zero_at_length (m : ℕ) (hm : 3 ≤ m) :
    (oddReplacementMatrix (m : ℝ) (thirdPower m)).det ≠ 0 :=
  ne_of_gt (oddReplacementMatrix_det_pos_at_length m hm)

end

end PanelMoments.SourceConfluentQuotientAlgebra
