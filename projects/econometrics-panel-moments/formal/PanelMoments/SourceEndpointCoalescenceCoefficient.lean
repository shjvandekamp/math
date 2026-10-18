import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Positive coefficient in the endpoint coalescence calculation

This module proves the finite real algebra of the displayed first coefficient
matrix. Its determinant is positive for `A > 1` and `B ≥ 3`, including
`A = 4^m`, `B = 3^m` for `m ≥ 1`. It does not identify the matrix as an actual
source asymptotic coefficient, extract residues, or prove source independence.
-/

namespace PanelMoments.SourceEndpointCoalescenceCoefficient

noncomputable section

def kappa (A : ℝ) : ℝ := 3 * A / (4 * (A - 1))

def p (A B : ℝ) : ℝ := B * (3 * kappa A - 2)

def chi (A B : ℝ) : ℝ := B - (3 * kappa A / 2) * (B - 1)

def ell (A B : ℝ) : ℝ := chi A B - kappa A

def d (A B : ℝ) : ℝ := chi A B - 2 * kappa A

/-- The explicit first coefficient matrix, with row and column states `0,1,2`. -/
def coefficientMatrix (A B : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, 4 * p A B / 3, 4 * p A B / 3],
    ![2 * d A B / 3, 0, 2 * ell A B / 3],
    ![2 * d A B / 3, 2 * ell A B / 3, 0]]

theorem ell_eq (A B : ℝ) : ell A B = (kappa A - p A B) / 2 := by
  unfold ell chi p
  ring

theorem d_eq (A B : ℝ) : d A B = -(kappa A + p A B) / 2 := by
  unfold d chi p
  ring

theorem p_eq (A B : ℝ) (hA : A ≠ 1) :
    p A B = B * (A + 8) / (4 * (A - 1)) := by
  unfold p kappa
  field_simp [sub_ne_zero.mpr hA]
  ring

theorem kappa_pos (A : ℝ) (hA : 1 < A) : 0 < kappa A := by
  unfold kappa
  exact div_pos (by linarith) (by linarith)

theorem kappa_lt_p (A B : ℝ) (hA : 1 < A) (hB : 3 ≤ B) :
    kappa A < p A B := by
  rw [p_eq A B (ne_of_gt hA)]
  unfold kappa
  apply (div_lt_div_iff_of_pos_right (by linarith : 0 < 4 * (A - 1))).2
  have h := mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ A + 8)
  nlinarith

theorem ell_neg (A B : ℝ) (hA : 1 < A) (hB : 3 ≤ B) : ell A B < 0 := by
  rw [ell_eq]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (kappa_lt_p A B hA hB)) (by norm_num)

theorem d_neg (A B : ℝ) (hA : 1 < A) (hB : 3 ≤ B) : d A B < 0 := by
  rw [d_eq]
  have hk := kappa_pos A hA
  have hp := kappa_lt_p A B hA hB
  exact div_neg_of_neg_of_pos (by linarith) (by norm_num)

theorem coefficientMatrix_det (A B : ℝ) :
    (coefficientMatrix A B).det = 32 * p A B * ell A B * d A B / 27 := by
  rw [Matrix.det_fin_three (coefficientMatrix A B)]
  simp [coefficientMatrix]
  ring

theorem coefficientMatrix_det_pos (A B : ℝ) (hA : 1 < A) (hB : 3 ≤ B) :
    0 < (coefficientMatrix A B).det := by
  rw [coefficientMatrix_det]
  have hp : 0 < p A B := lt_trans (kappa_pos A hA) (kappa_lt_p A B hA hB)
  have held : 0 < ell A B * d A B :=
    mul_pos_of_neg_of_neg (ell_neg A B hA hB) (d_neg A B hA hB)
  have hnum : 0 < (32 : ℝ) * p A B * (ell A B * d A B) :=
    mul_pos (mul_pos (by norm_num) hp) held
  simpa only [mul_assoc] using div_pos hnum (by norm_num : (0 : ℝ) < 27)

/-- The positive leading coefficient for every integer `m ≥ 1`. -/
theorem coefficientMatrix_det_pos_pow (m : ℕ) (hm : 1 ≤ m) :
    0 < (coefficientMatrix ((4 : ℝ) ^ m) ((3 : ℝ) ^ m)).det := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  apply coefficientMatrix_det_pos
  · exact one_lt_pow₀ (by norm_num) hm0
  · exact le_self_pow₀ (by norm_num) hm0

end

end PanelMoments.SourceEndpointCoalescenceCoefficient
