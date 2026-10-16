import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# The displayed two-block invariant-tail base, from its rational source rows

This module uses the actual formulas in IT10--IT13, over `ℚ`, at
`z = 1/10`, `(a₁,a₂) = (6/5,7/5)`, and `(b₁,b₂) = (1,2)`.
The binary kernels, completed H/J rows, retained heads, and normalized
weak rows are defined by those formulas, rather than supplied as data.
The explicit Γ is proved to annihilate all three completed binary outputs
on the six-pole regular domain. Its heads and four weak outputs are also
checked by field and polynomial arithmetic. Its final four rows are the
identity.

The weak outputs are displayed with the common denominator Λ₂; their
numerators are the common-denominator form of the four saved
`base.weak_kernel_functions` in `source24_invariant_tail_base.json`.
They are checked against the defining source expressions below, so no
external identity or saved certificate is assumed.

This is a bridge to the displayed two-block formulas only. Identifying
these formulas with the full source-family interface and an actual time
derivative, transporting them through later lengths, and identifying the
later coefficient matrices remain separate formal obligations.
-/

namespace PanelMoments.SourceInvariantTailActualBase

open scoped BigOperators

def z : ℚ := 1 / 10
def a : Fin 2 → ℚ := ![6 / 5, 7 / 5]
def b : Fin 2 → ℚ := ![1, 2]

def X (r : ℚ) : Fin 3 → ℚ := ![1, -r, r - z]
def v (r : ℚ) : Fin 3 → ℚ := ![z, -r, r - z]

def rowForms (A r : ℚ) : Fin 3 → ℚ :=
  ![2 - A * r, 1 - 2 * A * r, 1 - A * r]

def binaryScale (A r : ℚ) : Fin 3 → ℚ := ![1, -A * r, 0]

/-- The actual binary kernel `(1 + δᵢⱼ) scaleⱼ / lᵢ`. -/
def K (A r : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of (fun i j => (1 + if i = j then 1 else 0) *
    binaryScale A r j / rowForms A r i)

def mu (A r : ℚ) : Fin 3 → ℚ :=
  ![2 / rowForms A r 0, -r / rowForms A r 1, (r - z) / rowForms A r 2]

def u (A r : ℚ) : Fin 3 → ℚ :=
  ![1 / rowForms A r 0, 1 / rowForms A r 1, 2 / rowForms A r 2]

def completedH (A B r : ℚ) (c j : Fin 3) : ℚ :=
  X r c * ∑ i : Fin 3, K A r c i * K B r i j

def completedJ (A B r : ℚ) (c j : Fin 3) : ℚ :=
  mu A r c * Matrix.vecMul (v r) (K B r) j

/-- Source order: H10,H11,H12,H20,H21,H22,J10,J11,J12,J20,J21,J22. -/
def completedBinary (r : ℚ) : Matrix (Fin 12) (Fin 3) ℚ :=
  Matrix.of ![completedH (a 0) (a 1) r 0, completedH (a 0) (a 1) r 1,
    completedH (a 0) (a 1) r 2, completedH (a 1) (a 0) r 0,
    completedH (a 1) (a 0) r 1, completedH (a 1) (a 0) r 2,
    completedJ (a 0) (a 1) r 0, completedJ (a 0) (a 1) r 1,
    completedJ (a 0) (a 1) r 2, completedJ (a 1) (a 0) r 0,
    completedJ (a 1) (a 0) r 1, completedJ (a 1) (a 0) r 2]

def retainedH (r : ℚ) (c j : Fin 3) : ℚ := if c = j then X r c else 0

def retainedHeads (r : ℚ) : Matrix (Fin 12) (Fin 3) ℚ :=
  Matrix.of ![retainedH r 0, retainedH r 1, retainedH r 2,
    retainedH r 0, retainedH r 1, retainedH r 2, 0, 0, 0, 0, 0, 0]

/-- IT13: the weight belongs to the other (last) block. -/
def weakH (A B weight r : ℚ) (c : Fin 3) : ℚ :=
  weight * X r c * ∑ i : Fin 3, K A r c i * u B r i

def weakJ (A B weight r : ℚ) (c : Fin 3) : ℚ :=
  weight * mu A r c * ∑ i : Fin 3, v r i * u B r i

def weakRows (r : ℚ) : Fin 12 → ℚ :=
  ![weakH (a 0) (a 1) (b 1) r 0, weakH (a 0) (a 1) (b 1) r 1,
    weakH (a 0) (a 1) (b 1) r 2, weakH (a 1) (a 0) (b 0) r 0,
    weakH (a 1) (a 0) (b 0) r 1, weakH (a 1) (a 0) (b 0) r 2,
    weakJ (a 0) (a 1) (b 1) r 0, weakJ (a 0) (a 1) (b 1) r 1,
    weakJ (a 0) (a 1) (b 1) r 2, weakJ (a 1) (a 0) (b 0) r 0,
    weakJ (a 1) (a 0) (b 0) r 1, weakJ (a 1) (a 0) (b 0) r 2]

def suppliedM : Matrix (Fin 12) (Fin 4) ℤ :=
  Matrix.of ![![-12586, -2387, 217, -15841],
    ![777245, -3710, -31535, 1250270],
    ![197960, -15680, -9800, 344960],
    ![6048, 2016, 0, 6048],
    ![-842625, 0, 33705, -1348200],
    ![-263340, 11970, 11970, -442890],
    ![-28620, -18810, 1710, -50742],
    ![121086, -4788, -40698, 131796],
    ![176400, 0, 0, 0], ![0, 20580, 0, 0],
    ![0, 0, 49392, 0], ![0, 0, 0, 246960]]

def gammaScales : Fin 4 → ℚ := ![176400, 20580, 49392, 246960]

def gamma : Matrix (Fin 12) (Fin 4) ℚ :=
  Matrix.of ![![-899 / 12600, -341 / 2940, 31 / 7056, -2263 / 35280],
    ![22207 / 5040, -53 / 294, -4505 / 7056, 17861 / 3528],
    ![101 / 90, -16 / 21, -25 / 126, 88 / 63],
    ![6 / 175, 24 / 245, 0, 6 / 245],
    ![-535 / 112, 0, 535 / 784, -535 / 98],
    ![-209 / 140, 57 / 98, 95 / 392, -703 / 392],
    ![-159 / 980, -627 / 686, 95 / 2744, -2819 / 13720],
    ![961 / 1400, -57 / 245, -323 / 392, 523 / 980],
    ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

def theta : Fin 4 → ℚ := ![-467 / 1260, -53 / 294, 155 / 3528, -1399 / 3528]

def combinedBinary (r : ℚ) : Matrix (Fin 4) (Fin 3) ℚ :=
  Matrix.of (fun j c => ∑ i : Fin 12, gamma i j * completedBinary r i c)

def combinedHeads (r : ℚ) : Matrix (Fin 4) (Fin 3) ℚ :=
  Matrix.of (fun j c => ∑ i : Fin 12, gamma i j * retainedHeads r i c)

def combinedWeak (r : ℚ) (j : Fin 4) : ℚ :=
  ∑ i : Fin 12, gamma i j * weakRows r i

def Regular (r : ℚ) : Prop := ∀ s : Fin 2, ∀ c : Fin 3, rowForms (a s) r c ≠ 0

def commonDenominator (r : ℚ) : ℚ :=
  rowForms (a 0) r 0 * rowForms (a 0) r 1 * rowForms (a 0) r 2 *
    rowForms (a 1) r 0 * rowForms (a 1) r 1 * rowForms (a 1) r 2

/-- Ascending-coefficient polynomials obtained by multiplying IT13 by Λ₂. -/
def weakNumerators (r : ℚ) : Fin 4 → ℚ :=
  ![-257 / 4900 - 41159 / 5250 * r + 519757 / 6000 * r ^ 2 -
      1905674747 / 7350000 * r ^ 3 + 126847613 / 375000 * r ^ 4 -
      61211983 / 312500 * r ^ 5 + 1274427 / 31250 * r ^ 6,
    1431 / 3430 - 7337 / 980 * r + 41416 / 875 * r ^ 2 -
      54387757 / 428750 * r ^ 3 + 635863 / 4375 * r ^ 4 -
      1026294 / 15625 * r ^ 5 + 22572 / 3125 * r ^ 6,
    19 / 2744 + 7213 / 11760 * r - 53393 / 8400 * r ^ 2 +
      17526077 / 2058000 * r ^ 3 + 251749 / 105000 * r ^ 4 -
      101357 / 12500 * r ^ 5 + 3753 / 1250 * r ^ 6,
    -1387 / 13720 - 2273939 / 294000 * r + 1155289 / 13125 * r ^ 2 -
      6439258631 / 25725000 * r ^ 3 + 389797769 / 1312500 * r ^ 4 -
      4826327 / 31250 * r ^ 5 + 89343 / 3125 * r ^ 6]

def weakFunctions (r : ℚ) (j : Fin 4) : ℚ :=
  weakNumerators r j / commonDenominator r

theorem parameters_positive : 0 < z ∧ (∀ s, 0 < a s) ∧ (∀ s, 0 < b s) := by
  refine ⟨by norm_num [z], ?_, ?_⟩
  · intro s
    fin_cases s <;> norm_num [a]
  · intro s
    fin_cases s <;> norm_num [b]

theorem z_ne_zero : z ≠ 0 := ne_of_gt parameters_positive.1

theorem regular_at_z : Regular z := by
  intro s c
  fin_cases s <;> fin_cases c <;> norm_num [rowForms, a, z]

theorem gamma_eq_scaled_M :
    gamma = Matrix.of (fun i j => (suppliedM i j : ℚ) / gammaScales j) := by
  decide +kernel

theorem gamma_last_four_rows :
    Matrix.of ![gamma 8, gamma 9, gamma 10, gamma 11] =
      (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  decide +kernel

/-- The finite-sum formula uses the usual matrix product. -/
theorem completedH_eq_matrix_product (A B r : ℚ) (c j : Fin 3) :
    completedH A B r c j = X r c * (K A r * K B r) c j := rfl

theorem combinedBinary_eq_matrix_product (r : ℚ) :
    combinedBinary r = gamma.transpose * completedBinary r := rfl

theorem combinedHeads_eq_matrix_product (r : ℚ) :
    combinedHeads r = gamma.transpose * retainedHeads r := rfl

theorem commonDenominator_ne_zero (r : ℚ) (hr : Regular r) :
    commonDenominator r ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (hr 0 0) (hr 0 1)) (hr 0 2)) (hr 1 0)) (hr 1 1)) (hr 1 2)

private def integerRowForms (r : ℚ) : Fin 2 → Fin 3 → ℚ :=
  ![![10 - r * 6, 5 - r * 12, 5 - r * 6],
    ![10 - r * 7, 5 - r * 14, 5 - r * 7]]

private theorem rowForms_mul_five (r : ℚ) (s : Fin 2) (c : Fin 3) :
    rowForms (a s) r c * 5 = integerRowForms r s c := by
  fin_cases s <;> fin_cases c <;> norm_num [rowForms, a, integerRowForms] <;> ring

private theorem rowForms_eq_div_five (r : ℚ) (s : Fin 2) (c : Fin 3) :
    rowForms (a s) r c = integerRowForms r s c / 5 := by
  apply (eq_div_iff (by norm_num : (5 : ℚ) ≠ 0)).2
  exact rowForms_mul_five r s c

private theorem integerRowForms_ne_zero (r : ℚ) (hr : Regular r)
    (s : Fin 2) (c : Fin 3) : integerRowForms r s c ≠ 0 := by
  rw [← rowForms_mul_five]
  exact mul_ne_zero (hr s c) (by norm_num)

/-- Each retained head is checked against Γ's actual source coefficients. -/
theorem combinedHeads_eq (r : ℚ) (j : Fin 4) (c : Fin 3) :
    combinedHeads r j c = theta j * v r c := by
  fin_cases j <;> fin_cases c <;>
    norm_num [combinedHeads, Matrix.mul_apply, Matrix.transpose_apply, retainedHeads,
      retainedH, gamma, theta, v, X, z, Matrix.of_apply, Fin.sum_univ_succ] <;> ring

theorem combinedHeads_row_sum_zero (r : ℚ) (j : Fin 4) :
    (∑ c : Fin 3, combinedHeads r j c) = 0 := by
  simp_rw [combinedHeads_eq]
  simp [Fin.sum_univ_succ, v]
  ring

/-- The actual completed binary rows are annihilated, on all three outputs. -/
theorem combinedBinary_eq_zero (r : ℚ) (hr : Regular r) :
    combinedBinary r = 0 := by
  have h10 := integerRowForms_ne_zero r hr 0 0
  have h11 := integerRowForms_ne_zero r hr 0 1
  have h12 := integerRowForms_ne_zero r hr 0 2
  have h20 := integerRowForms_ne_zero r hr 1 0
  have h21 := integerRowForms_ne_zero r hr 1 1
  have h22 := integerRowForms_ne_zero r hr 1 2
  norm_num [integerRowForms] at h10 h11 h12 h20 h21 h22
  ext j c
  fin_cases j <;> fin_cases c <;>
    simp [combinedBinary, completedBinary, completedH, completedJ,
      Matrix.vecMul, dotProduct, K, mu, gamma, Matrix.of_apply, Fin.sum_univ_succ] <;>
    simp_rw [rowForms_eq_div_five, div_div_eq_mul_div] <;>
    norm_num [integerRowForms, binaryScale, a, X, v, z, gamma, Matrix.of_apply] <;>
    field_simp [h10, h11, h12, h20, h21, h22] <;> ring

theorem combinedBinary_row_sum_zero (r : ℚ) (hr : Regular r) (j : Fin 4) :
    (∑ c : Fin 3, combinedBinary r j c) = 0 := by
  simp [combinedBinary_eq_zero r hr]

/-- The actual IT13 weak rows have the displayed numerators after clearing Λ₂. -/
theorem combinedWeak_cleared (r : ℚ) (hr : Regular r) (j : Fin 4) :
    commonDenominator r * combinedWeak r j = weakNumerators r j := by
  have h10 := integerRowForms_ne_zero r hr 0 0
  have h11 := integerRowForms_ne_zero r hr 0 1
  have h12 := integerRowForms_ne_zero r hr 0 2
  have h20 := integerRowForms_ne_zero r hr 1 0
  have h21 := integerRowForms_ne_zero r hr 1 1
  have h22 := integerRowForms_ne_zero r hr 1 2
  norm_num [integerRowForms] at h10 h11 h12 h20 h21 h22
  fin_cases j <;>
    simp only [combinedWeak, weakRows, weakH, weakJ, commonDenominator,
      K, mu, u, Matrix.of_apply, Fin.sum_univ_succ] <;>
    simp_rw [rowForms_eq_div_five, div_div_eq_mul_div] <;>
    norm_num [weakNumerators, integerRowForms, binaryScale, a, b,
      X, v, z, gamma, Matrix.of_apply] <;>
    field_simp [h10, h11, h12, h20, h21, h22] <;> ring

/-- The four weak functions are derived from the IT13 H/J rows, not assumed. -/
theorem combinedWeak_eq (r : ℚ) (hr : Regular r) (j : Fin 4) :
    combinedWeak r j = weakFunctions r j := by
  apply (eq_div_iff (commonDenominator_ne_zero r hr)).2
  simpa [mul_comm] using combinedWeak_cleared r hr j

end PanelMoments.SourceInvariantTailActualBase
