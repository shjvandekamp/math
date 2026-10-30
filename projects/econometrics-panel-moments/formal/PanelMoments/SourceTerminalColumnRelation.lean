import PanelMoments.SourceFirstBlockCancellation

set_option autoImplicit false

/-!
# Exact terminal-column relation for the actual scaled kernel

For `firstTable u w = (I + 11ᵀ) diag(1,u,w)`, write
`x = X₀`, `y = u X₁`, `z = w X₂`, and `L₂ = x+y+2z`.
The actual kernel columns satisfy
`Kᵢ₂ = θ + η Kᵢ₁ + χ δᵢ₂`, where
`θ = z/(3x+z)`, `η = z(x-y)/(y(3x+z))`, and
`χ = 4xz/((3x+z)L₂)`.

The first theorem is a polynomial identity in the actual table numerators and
row forms, without unit hypotheses. The kernel, row, and ordered-tail formulas
then require the actual row-form units, `y ≠ 0`, and `3x+z ≠ 0` explicitly.
No plane equation, kernel inverse, or `X₀ ≠ 0` is used. No asymptotic or rank
statement is asserted.
-/

namespace PanelMoments.SourceTerminalColumnRelation

open scoped BigOperators
open SourceHomogeneous SourceFirstBlockCancellation

noncomputable section

def theta (w : ℝ) (X : State 2 → ℝ) : ℝ :=
  w * X 2 / (3 * X 0 + w * X 2)

def eta (u w : ℝ) (X : State 2 → ℝ) : ℝ :=
  (w * X 2) * (X 0 - u * X 1) / ((u * X 1) * (3 * X 0 + w * X 2))

def chi (u w : ℝ) (X : State 2 → ℝ) : ℝ :=
  4 * X 0 * (w * X 2) /
    ((3 * X 0 + w * X 2) * rowForm (firstTable u w) X 0 2)

/-- Clearing the column relation gives an identity of actual table polynomials. -/
theorem column_relation_cleared (u w : ℝ) (X : State 2 → ℝ) (i : State 2) :
    (u * X 1) * (3 * X 0 + w * X 2) * rowForm (firstTable u w) X 0 2 *
        (firstTable u w 0 i 2 * X 2) =
      (u * X 1) * (w * X 2) * rowForm (firstTable u w) X 0 2 *
        rowForm (firstTable u w) X 0 i +
      (w * X 2) * (X 0 - u * X 1) * rowForm (firstTable u w) X 0 2 *
        (firstTable u w 0 i 1 * X 1) +
      4 * X 0 * (u * X 1) * (w * X 2) * rowForm (firstTable u w) X 0 i *
        (if i = 2 then 1 else 0) := by
  fin_cases i <;>
    simp [rowForm, firstTable, SourceTimeScaling.scaledTable,
      SourceScalarPrependAlgebra.preservingTable, firstTime, Fin.sum_univ_succ] <;> ring

/-- The actual column relation, with exactly the denominator conditions used. -/
theorem kernel_column_relation (u w : ℝ) (X : State 2 → ℝ) (i : State 2)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0)
    (hy : u * X 1 ≠ 0) (hD : 3 * X 0 + w * X 2 ≠ 0) :
    kernel (firstTable u w) X 0 i 2 =
      theta w X + eta u w X * kernel (firstTable u w) X 0 i 1 +
        chi u w X * (if i = 2 then 1 else 0) := by
  have hc := column_relation_cleared u w X i
  have hu : u ≠ 0 := (mul_ne_zero_iff.mp hy).1
  have hX1 : X 1 ≠ 0 := (mul_ne_zero_iff.mp hy).2
  have hD' : 3 * X 0 + X 2 * w ≠ 0 := by simpa only [mul_comm] using hD
  simp only [kernel, Matrix.of_apply, theta, eta, chi]
  field_simp [hL i, hL 2, hy, hu, hX1, hD, hD']
  apply mul_left_cancel₀ hX1
  nlinarith only [hc]

/-- An arbitrary row retains the constant term through its row sum. -/
theorem vecMul_column_relation (u w : ℝ) (X R : State 2 → ℝ)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0)
    (hy : u * X 1 ≠ 0) (hD : 3 * X 0 + w * X 2 ≠ 0) :
    Matrix.vecMul R (kernel (firstTable u w) X 0) 2 =
      theta w X * (∑ i, R i) +
      eta u w X * Matrix.vecMul R (kernel (firstTable u w) X 0) 1 +
      chi u w X * R 2 := by
  simp only [Matrix.vecMul, dotProduct]
  simp_rw [kernel_column_relation u w X _ hL hy hD]
  simp [Fin.sum_univ_succ]
  ring

theorem vecMul_column_relation_zero_sum (u w : ℝ) (X R : State 2 → ℝ)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0)
    (hy : u * X 1 ≠ 0) (hD : 3 * X 0 + w * X 2 ≠ 0)
    (hR : ∑ i, R i = 0) :
    Matrix.vecMul R (kernel (firstTable u w) X 0) 2 =
      eta u w X * Matrix.vecMul R (kernel (firstTable u w) X 0) 1 +
      chi u w X * R 2 := by
  rw [vecMul_column_relation u w X R hL hy hD, hR, mul_zero, zero_add]

/-- Appending the actual terminal kernel to an actual ordered word gives this
two-output recurrence whenever the prefix row has zero sum. -/
theorem word_tail_column_relation_zero_sum {N : ℕ} (A : Table 2)
    (word : List (Fin N)) (u w : ℝ) (X R : State 2 → ℝ)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0)
    (hy : u * X 1 ≠ 0) (hD : 3 * X 0 + w * X 2 ≠ 0)
    (hprefix : ∑ i, Matrix.vecMul R (homogeneousWordProduct A X word) i = 0) :
    Matrix.vecMul R
        (homogeneousWordProduct A X word * kernel (firstTable u w) X 0) 2 =
      eta u w X * Matrix.vecMul R
        (homogeneousWordProduct A X word * kernel (firstTable u w) X 0) 1 +
      chi u w X * Matrix.vecMul R (homogeneousWordProduct A X word) 2 := by
  simpa only [Matrix.vecMul_vecMul] using
    vecMul_column_relation_zero_sum u w X
      (Matrix.vecMul R (homogeneousWordProduct A X word)) hL hy hD hprefix

end

end PanelMoments.SourceTerminalColumnRelation
