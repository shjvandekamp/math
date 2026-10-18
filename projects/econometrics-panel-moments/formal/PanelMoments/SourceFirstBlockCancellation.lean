import PanelMoments.SourceScalarPrependAlgebra
import PanelMoments.SourceTimeScaling
import PanelMoments.SourceTerminalPrefixExtraction

set_option autoImplicit false

/-!
# First-block cancellation on the fixed new-state line

The first actual table is `(I + 11ᵀ) diag(1,u,w)`. On
`2 X₀ + X₁ + X₂ = 0`, set `v = (2 X₀,X₁,X₂)` and
`d = (2(u+w-3),1-2w,1-2u)`. The denominator-cleared starting row
`l = 3(w-u) X₂(e₀-e₂) - (2u-w)v` satisfies
`l K = X₀(4e₀ + d K)`.

The proof clears the row forms of the existing actual kernel. It does not
invert that kernel or assume nonzero coordinates. Arbitrary right tails,
actual ordered word tails, and the divided-output formula follow. The
divided formula states its coordinate and `w-u` units explicitly. No
residue extraction, admissible specialization, or source rank is asserted.
-/

namespace PanelMoments.SourceFirstBlockCancellation

open scoped BigOperators
open SourceHomogeneous SourceTimeScaling SourceScalarPrependAlgebra

noncomputable section

def firstTime (u w : ℝ) : State 2 → ℝ := ![1, u, w]

/-- The existing positive common table with the actual first time scaling. -/
def firstTable (u w : ℝ) : Table 2 := scaledTable preservingTable (firstTime u w)

def firstBasis : State 2 → ℝ := ![1, 0, 0]

def newStateRow (X : State 2 → ℝ) : State 2 → ℝ := ![2 * X 0, X 1, X 2]

def correctionRow (u w : ℝ) : State 2 → ℝ :=
  ![2 * (u + w - 3), 1 - 2 * w, 1 - 2 * u]

def clearedStartingRow (u w : ℝ) (X : State 2 → ℝ) : State 2 → ℝ :=
  (3 * (w - u) * X 2) • (![1, 0, -1] : State 2 → ℝ) -
    (2 * u - w) • newStateRow X

def startingRow (u w : ℝ) (X : State 2 → ℝ) : State 2 → ℝ :=
  X 2 • (![1, 0, -1] : State 2 → ℝ) -
    ((2 * u - w) / (3 * (w - u))) • newStateRow X

theorem firstTable_rowForm (u w : ℝ) (X : State 2 → ℝ) (a : State 2) :
    rowForm (firstTable u w) X 0 a =
      X 0 + u * X 1 + w * X 2 + firstTime u w a * X a := by
  fin_cases a <;>
    simp [rowForm, firstTable, scaledTable, preservingTable, firstTime,
      Fin.sum_univ_succ] <;> ring

/-- This polynomial decomposition is the only use of the new-state plane. -/
theorem clearedStartingRow_decomposition (u w : ℝ) (X : State 2 → ℝ)
    (hplane : 2 * X 0 + X 1 + X 2 = 0) :
    clearedStartingRow u w X = X 0 • correctionRow u w +
      Matrix.vecMul (![3, -1, -1] : State 2 → ℝ)
        (Matrix.diagonal (rowForm (firstTable u w) X 0)) := by
  have hX1 : X 1 = -2 * X 0 - X 2 := by linarith
  funext a
  fin_cases a <;>
    simp [clearedStartingRow, correctionRow, newStateRow, Matrix.vecMul_diagonal,
      firstTable_rowForm, firstTime, hX1] <;> ring

/-- The signed row-form row cancels against the actual kernel. -/
theorem signedForms_kernel (u w : ℝ) (X : State 2 → ℝ)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0) :
    Matrix.vecMul
      (Matrix.vecMul (![3, -1, -1] : State 2 → ℝ)
        (Matrix.diagonal (rowForm (firstTable u w) X 0)))
      (kernel (firstTable u w) X 0) = (4 * X 0) • firstBasis := by
  rw [Matrix.vecMul_vecMul,
    SourceTerminalPrefixExtraction.rowForm_diagonal_mul_kernel (firstTable u w) X 0 hL,
    ← Matrix.vecMul_vecMul]
  have hrow : Matrix.vecMul (![3, -1, -1] : State 2 → ℝ)
      (Matrix.of (firstTable u w 0)) = (![4, 0, 0] : State 2 → ℝ) := by
    funext a
    fin_cases a <;>
      simp [Matrix.vecMul, dotProduct, firstTable, scaledTable, preservingTable,
        firstTime, Fin.sum_univ_succ] <;> ring
  rw [hrow]
  funext a
  fin_cases a <;> simp [Matrix.vecMul_diagonal, firstBasis]

/-- The first-block identity requires only the actual row-form units. -/
theorem clearedStartingRow_kernel (u w : ℝ) (X : State 2 → ℝ)
    (hplane : 2 * X 0 + X 1 + X 2 = 0)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0) :
    Matrix.vecMul (clearedStartingRow u w X) (kernel (firstTable u w) X 0) =
      X 0 • ((4 : ℝ) • firstBasis +
        Matrix.vecMul (correctionRow u w) (kernel (firstTable u w) X 0)) := by
  rw [clearedStartingRow_decomposition u w X hplane, Matrix.add_vecMul,
    Matrix.smul_vecMul, signedForms_kernel u w X hL]
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Right multiplication preserves the actual first kernel and the tail order. -/
theorem clearedStartingRow_kernel_tail (u w : ℝ) (X : State 2 → ℝ)
    (B : Matrix (State 2) (State 2) ℝ)
    (hplane : 2 * X 0 + X 1 + X 2 = 0)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0) :
    Matrix.vecMul (clearedStartingRow u w X) (kernel (firstTable u w) X 0 * B) =
      X 0 • ((4 : ℝ) • Matrix.vecMul firstBasis B +
        Matrix.vecMul (correctionRow u w) (kernel (firstTable u w) X 0 * B)) := by
  rw [← Matrix.vecMul_vecMul, clearedStartingRow_kernel u w X hplane hL,
    Matrix.smul_vecMul, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]

/-- The same identity for the existing actual ordered word product. -/
theorem clearedStartingRow_kernel_wordTail {N : ℕ} (u w : ℝ)
    (X : State 2 → ℝ) (A : Table 2) (word : List (Fin N))
    (hplane : 2 * X 0 + X 1 + X 2 = 0)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0) :
    Matrix.vecMul (clearedStartingRow u w X)
        (kernel (firstTable u w) X 0 * homogeneousWordProduct A X word) =
      X 0 • ((4 : ℝ) • Matrix.vecMul firstBasis (homogeneousWordProduct A X word) +
        Matrix.vecMul (correctionRow u w)
          (kernel (firstTable u w) X 0 * homogeneousWordProduct A X word)) :=
  clearedStartingRow_kernel_tail u w X (homogeneousWordProduct A X word) hplane hL

theorem clearedStartingRow_eq_scale (u w : ℝ) (X : State 2 → ℝ)
    (hgap : w - u ≠ 0) :
    clearedStartingRow u w X = (3 * (w - u)) • startingRow u w X := by
  funext a
  simp only [clearedStartingRow, startingRow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hgap]

/-- The scalar tail formula, with every division used by the research row explicit. -/
theorem startingRow_kernel_tail_divided (u w : ℝ) (X : State 2 → ℝ)
    (B : Matrix (State 2) (State 2) ℝ) (j : State 2)
    (hplane : 2 * X 0 + X 1 + X 2 = 0)
    (hL : ∀ a, rowForm (firstTable u w) X 0 a ≠ 0)
    (hgap : w - u ≠ 0) (hX0 : X 0 ≠ 0) (hXj : X j ≠ 0) :
    Matrix.vecMul (startingRow u w X) (kernel (firstTable u w) X 0 * B) j /
        (X 0 * X j) =
      (4 * B 0 j + Matrix.vecMul (correctionRow u w)
        (kernel (firstTable u w) X 0 * B) j) / (3 * (w - u) * X j) := by
  have h := clearedStartingRow_kernel_tail u w X B hplane hL
  rw [clearedStartingRow_eq_scale u w X hgap, Matrix.smul_vecMul] at h
  have hj := congrFun h j
  have he : Matrix.vecMul firstBasis B j = B 0 j := by
    simp [Matrix.vecMul, dotProduct, firstBasis, Fin.sum_univ_succ]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, he] at hj
  field_simp [hgap, hX0, hXj]
  nlinarith only [hj]

end

end PanelMoments.SourceFirstBlockCancellation
