import PanelMoments.SourceRelativeTimeJet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Actual algebra of the scalar preserving prepend

The common matrix is `G̃ = I + 11ᵀ`. The actual relative-time table
perturbation has factors `(1, 1 + ε, 1 + 2ε)` at the prepend block.
On `∑ a, X a = 0`, its baseline kernel preserves the starting row by
`X K(0) = 4 X`. The first derivative below is obtained from the existing
actual homogeneous-kernel derivative, with its denominator hypotheses.

The two concrete observation matrices from SP6 and SP14 have determinants
`1` and `-1/4`. Their diagonal scaling consequences retain the endpoint
values as explicit nonzero hypotheses. No principal-part extraction,
generic existence, or arbitrary-length independence theorem is asserted.
-/

namespace PanelMoments.SourceScalarPrependAlgebra

open scoped BigOperators
open SourceHomogeneous SourceRelativeTimeJet

noncomputable section

/-- The positive common matrix `I + 11ᵀ`, through the actual table interface. -/
def preservingTable : Table 2 :=
  fun _ a b => (if a = b then 1 else 0) + 1

/-- Only the prepend time block is varied, using the existing relative-time curve. -/
def prependTable (ε : ℝ) : Table 2 :=
  perturbTable preservingTable 0 (relativeDirection 1 2) ε

def ell (X : State 2 → ℝ) : ℝ := X 1 + 2 * X 2

/-- The polynomial row `3 X D - 3 X - ell · 1ᵀ`, with `D = diag(0,1,2)`. -/
def regularRow (X : State 2 → ℝ) : State 2 → ℝ :=
  fun b => 3 * X b * relativeDirection 1 2 b - 3 * X b - ell X

theorem prependTable_entry (ε : ℝ) (a b : State 2) :
    prependTable ε 0 a b =
      ((if a = b then 1 else 0) + 1) * (![1, 1 + ε, 1 + 2 * ε] : State 2 → ℝ) b := by
  have hd : 1 + ε * relativeDirection 1 2 b =
      (![1, 1 + ε, 1 + 2 * ε] : State 2 → ℝ) b := by
    fin_cases b <;> simp [relativeDirection, mul_comm]
  simp only [prependTable, perturbTable, ↓reduceIte, preservingTable, hd]

theorem preserving_rowForm (X : State 2 → ℝ) (a : State 2)
    (hplane : ∑ b : State 2, X b = 0) :
    rowForm preservingTable X 0 a = X a := by
  simp [rowForm, preservingTable, add_mul, Finset.sum_add_distrib, hplane]

theorem preserving_rowFormJet (X : State 2 → ℝ) (a : State 2) :
    rowFormJet preservingTable X 0 (relativeDirection 1 2) a =
      ell X + relativeDirection 1 2 a * X a := by
  fin_cases a <;>
    simp [rowFormJet, preservingTable, relativeDirection, ell, Fin.sum_univ_succ] <;> ring

/-- The exact row form for `(u,v) = (1+ε,1+2ε)` on the terminal plane. -/
theorem prepend_rowForm (ε : ℝ) (X : State 2 → ℝ) (a : State 2)
    (hplane : ∑ b : State 2, X b = 0) :
    rowForm (prependTable ε) X 0 a =
      X a + ε * (ell X + relativeDirection 1 2 a * X a) := by
  rw [prependTable, rowForm_perturbTable, preserving_rowForm X a hplane,
    preserving_rowFormJet]

/-- The limiting kernel is `I + (1/X) X`, not the identity matrix. -/
theorem prepend_kernel_zero (X : State 2 → ℝ)
    (hplane : ∑ a : State 2, X a = 0) (hX : ∀ a, X a ≠ 0) :
    kernel (prependTable 0) X 0 =
      1 + Matrix.of (fun a b : State 2 => X b / X a) := by
  rw [prependTable, perturbTable_zero]
  ext a b
  simp only [kernel, Matrix.of_apply, preserving_rowForm X a hplane,
    Matrix.add_apply, Matrix.one_apply, preservingTable]
  by_cases hab : a = b
  · subst b
    simp [hX a]
  · simp [hab]

/-- The actual prepend preserves the starting row by the scalar factor four. -/
theorem prepend_preserves_row (X : State 2 → ℝ)
    (hplane : ∑ a : State 2, X a = 0) (hX : ∀ a, X a ≠ 0) :
    Matrix.vecMul X (kernel (prependTable 0) X 0) = (4 : ℝ) • X := by
  rw [prepend_kernel_zero X hplane hX, Matrix.vecMul_add, Matrix.vecMul_one]
  funext b
  change X b + (∑ a : State 2, X a * (X b / X a)) = 4 * X b
  have hc (a : State 2) : X a * (X b / X a) = X b := by
    field_simp [hX a]
  simp_rw [hc]
  simp
  ring

private theorem weighted_kernelJet (X : State 2 → ℝ) (a b : State 2)
    (hplane : ∑ c : State 2, X c = 0) (hXa : X a ≠ 0) :
    X a * kernelJet preservingTable X 0 (relativeDirection 1 2) a b =
      ((if a = b then 1 else 0) + 1) * X b *
        (relativeDirection 1 2 b - relativeDirection 1 2 a - ell X / X a) := by
  simp only [kernelJet, Matrix.of_apply, kernel, preservingTable,
    preserving_rowForm X a hplane, preserving_rowFormJet]
  field_simp [hXa]
  ring

/-- The SP5 identity for the actual kernel derivative, with every reciprocal
coordinate factor retained. -/
theorem prepend_kernelJet_row (X : State 2 → ℝ)
    (hplane : ∑ a : State 2, X a = 0) (hX : ∀ a, X a ≠ 0) :
    Matrix.vecMul X (kernelJet preservingTable X 0 (relativeDirection 1 2)) =
      regularRow X - (ell X * ∑ a : State 2, 1 / X a) • X := by
  funext b
  simp only [Matrix.vecMul, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [weighted_kernelJet X _ _ hplane (hX _)]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, relativeDirection, regularRow, ell] <;>
    field_simp [hX 0, hX 1, hX 2] <;> ring

/-- The preceding identity is the real derivative of the actual perturbed
table kernel, rather than merely a formula assigned to a formal jet. -/
theorem prepend_row_hasDerivAt (X : State 2 → ℝ) (b : State 2)
    (hplane : ∑ a : State 2, X a = 0) (hX : ∀ a, X a ≠ 0) :
    HasDerivAt (fun ε : ℝ => Matrix.vecMul X (kernel (prependTable ε) X 0) b)
      (regularRow X b - (ell X * ∑ a : State 2, 1 / X a) * X b) 0 := by
  have h := vecMul_kernel_hasDerivAt preservingTable X X 0 (relativeDirection 1 2) b
    (fun a => by rw [preserving_rowForm X a hplane]; exact hX a)
  have hj := congrFun (prepend_kernelJet_row X hplane hX) b
  exact h.congr_deriv hj

/-- The numerical principal-part coefficient matrix displayed in SP6. -/
def firstObservationMatrix : Matrix (State 2) (State 2) ℝ :=
  ![![1, 1, 3], ![-1, 0, -1], ![0, -1, -1]]

/-- The numerical coefficient matrix `-I + 11ᵀ/4` displayed in SP14. -/
def symmetricObservationMatrix : Matrix (State 2) (State 2) ℝ :=
  -(1 : Matrix (State 2) (State 2) ℝ) +
    (1 / 4 : ℝ) • Matrix.of (fun _ _ : State 2 => (1 : ℝ))

theorem firstObservationMatrix_det : firstObservationMatrix.det = 1 := by
  rw [Matrix.det_fin_three firstObservationMatrix]
  norm_num [firstObservationMatrix]

theorem symmetricObservationMatrix_det : symmetricObservationMatrix.det = -(1 / 4 : ℝ) := by
  rw [Matrix.det_fin_three symmetricObservationMatrix]
  norm_num [symmetricObservationMatrix, Matrix.one_apply]

theorem firstObservation_scaled_det (β : State 2 → ℝ) :
    (Matrix.diagonal β * firstObservationMatrix).det = ∏ a : State 2, β a := by
  rw [Matrix.det_mul, Matrix.det_diagonal, firstObservationMatrix_det, mul_one]

theorem symmetricObservation_scaled_det (β : State 2 → ℝ) :
    (Matrix.diagonal β * symmetricObservationMatrix).det =
      (∏ a : State 2, β a) * -(1 / 4 : ℝ) := by
  rw [Matrix.det_mul, Matrix.det_diagonal, symmetricObservationMatrix_det]

theorem firstObservation_scaled_det_ne_zero (β : State 2 → ℝ) (hβ : ∀ a, β a ≠ 0) :
    (Matrix.diagonal β * firstObservationMatrix).det ≠ 0 := by
  rw [firstObservation_scaled_det]
  exact Finset.prod_ne_zero_iff.mpr (fun a _ => hβ a)

theorem symmetricObservation_scaled_det_ne_zero (β : State 2 → ℝ) (hβ : ∀ a, β a ≠ 0) :
    (Matrix.diagonal β * symmetricObservationMatrix).det ≠ 0 := by
  rw [symmetricObservation_scaled_det]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun a _ => hβ a)) (by norm_num)

end

end PanelMoments.SourceScalarPrependAlgebra
