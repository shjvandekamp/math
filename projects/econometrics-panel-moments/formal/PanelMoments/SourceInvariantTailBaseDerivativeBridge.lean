import PanelMoments.SourceInvariantTailActualBase
import PanelMoments.SourceInvariantTailWeakDerivative

set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# The actual two-block source derivatives give the displayed base functions

The rows below are the actual perturbed H/J expressions of
`SourceInvariantTailWeakDerivative`, assembled in the exact order used
by `SourceInvariantTailActualBase`. The parameters and constant Γ are
the checked real base's explicit rational constants.

At zero perturbation, Γ annihilates all completed outputs and leaves
the retained source heads `θⱼ v`. Its missing-output derivative is
`(r-z) weakFunctionsⱼ` for the completed rows and the negative of this
for the actual sources. Only the six displayed binary row-form units
are assumed; the normalized derivative additionally needs `r ≠ z`.

This identifies the displayed two-block source expressions and their
actual kernel derivatives, without a rank hypothesis or assumed
function identity. It does not identify later coefficient matrices or
the complete all-length source-family coefficient indexing.
-/

namespace PanelMoments.SourceInvariantTailBaseDerivativeBridge

open scoped BigOperators
open SourceInvariantTailActualBase

noncomputable section

/-- Preserve the source order H10,H11,H12,H20,H21,H22,J10,...,J22. -/
def assembleRows (H₁ H₂ J₁ J₂ : Fin 3 → Fin 3 → ℝ) :
    Matrix (Fin 12) (Fin 3) ℝ :=
  Matrix.of ![H₁ 0, H₁ 1, H₁ 2, H₂ 0, H₂ 1, H₂ 2,
    J₁ 0, J₁ 1, J₁ 2, J₂ 0, J₂ 1, J₂ 2]

def completedRows (r δ : ℝ) : Matrix (Fin 12) (Fin 3) ℝ :=
  assembleRows
    (SourceInvariantTailWeakDerivative.completedH (a 0) (a 1) (b 0) (b 1) z r δ)
    (SourceInvariantTailWeakDerivative.completedH (a 1) (a 0) (b 1) (b 0) z r δ)
    (SourceInvariantTailWeakDerivative.completedJ (a 0) (a 1) (b 0) (b 1) z r δ)
    (SourceInvariantTailWeakDerivative.completedJ (a 1) (a 0) (b 1) (b 0) z r δ)

/-- Actual sources use the retained head minus the completed kernel row. -/
def sourceRows (r δ : ℝ) : Matrix (Fin 12) (Fin 3) ℝ :=
  assembleRows
    (SourceInvariantTailWeakDerivative.sourceH (a 0) (a 1) (b 0) (b 1) z r δ)
    (SourceInvariantTailWeakDerivative.sourceH (a 1) (a 0) (b 1) (b 0) z r δ)
    (SourceInvariantTailWeakDerivative.sourceJ (a 0) (a 1) (b 0) (b 1) z r δ)
    (SourceInvariantTailWeakDerivative.sourceJ (a 1) (a 0) (b 1) (b 0) z r δ)

def combinedCompleted (r δ : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of (fun j c => ∑ i : Fin 12, gamma i j * completedRows r δ i c)

def combinedSource (r δ : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of (fun j c => ∑ i : Fin 12, gamma i j * sourceRows r δ i c)

theorem binaryK_eq (A r : ℝ) :
    SourceInvariantTailWeakDerivative.binaryK A r = K A r := rfl

theorem binaryMu_eq (A r : ℝ) (c : Fin 3) :
    SourceInvariantTailWeakDerivative.binaryMu A z r c = mu A r c := by
  fin_cases c <;>
    simp [SourceInvariantTailWeakDerivative.binaryMu,
      SourceInvariantTailWeakDerivative.prefixNumerator, mu,
      SourceInvariantTailWeakDerivative.rowForms, rowForms]

theorem weakH_eq (A B weight r : ℝ) (c : Fin 3) :
    SourceInvariantTailWeakDerivative.weakH A B weight z r c =
      weakH A B weight r c := rfl

theorem weakJ_eq (A B weight r : ℝ) (c : Fin 3) :
    SourceInvariantTailWeakDerivative.weakJ A B weight z r c =
      weakJ A B weight r c := by
  rw [SourceInvariantTailWeakDerivative.weakJ, binaryMu_eq]
  rfl

theorem actualCompletedH_zero (A B bA bB r : ℝ) (c j : Fin 3) :
    SourceInvariantTailWeakDerivative.completedH A B bA bB z r 0 c j =
      completedH A B r c j := by
  simp only [SourceInvariantTailWeakDerivative.completedH,
    SourceInvariantTailWeakDerivative.kernel_zero, binaryK_eq]
  rfl

theorem actualCompletedJ_zero (A B bA bB r : ℝ) (c j : Fin 3) :
    SourceInvariantTailWeakDerivative.completedJ A B bA bB z r 0 c j =
      completedJ A B r c j := by
  simp only [SourceInvariantTailWeakDerivative.completedJ,
    SourceInvariantTailWeakDerivative.mu_zero, binaryMu_eq,
    SourceInvariantTailWeakDerivative.kernel_zero, binaryK_eq]
  rfl

theorem completedRows_zero (r : ℝ) : completedRows r 0 = completedBinary r := by
  ext i c
  fin_cases i <;>
    simp [completedRows, assembleRows, completedBinary,
      actualCompletedH_zero, actualCompletedJ_zero]

theorem sourceRows_eq_head_sub_completed (r δ : ℝ) :
    sourceRows r δ = retainedHeads r - completedRows r δ := by
  ext i c
  fin_cases i <;>
    simp [sourceRows, completedRows, assembleRows, retainedHeads,
      SourceInvariantTailWeakDerivative.sourceH,
      SourceInvariantTailWeakDerivative.sourceJ,
      SourceInvariantTailWeakDerivative.retainedH, retainedH,
      SourceInvariantTailWeakDerivative.X, X]

theorem combinedCompleted_eq_matrix_product (r δ : ℝ) :
    combinedCompleted r δ = gamma.transpose * completedRows r δ := rfl

theorem combinedSource_eq_matrix_product (r δ : ℝ) :
    combinedSource r δ = gamma.transpose * sourceRows r δ := rfl

theorem combinedSource_eq_head_sub_completed (r δ : ℝ) :
    combinedSource r δ = combinedHeads r - combinedCompleted r δ := by
  ext j c
  simp [combinedSource, sourceRows_eq_head_sub_completed,
    combinedHeads, combinedCompleted, mul_sub, Finset.sum_sub_distrib]

/-- All three actual completed outputs vanish after Γ at the binary base. -/
theorem combinedCompleted_zero (r : ℝ) (hr : Regular r) :
    combinedCompleted r 0 = 0 := by
  simpa only [combinedCompleted, completedRows_zero, combinedBinary] using
    combinedBinary_eq_zero r hr

theorem combinedSource_zero (r : ℝ) (hr : Regular r) :
    combinedSource r 0 = combinedHeads r := by
  rw [combinedSource_eq_head_sub_completed, combinedCompleted_zero r hr, sub_zero]

theorem combinedSource_zero_eq (r : ℝ) (hr : Regular r) (j : Fin 4) (c : Fin 3) :
    combinedSource r 0 j c = theta j * v r c := by
  rw [combinedSource_zero r hr]
  exact combinedHeads_eq r j c

private theorem completedH_base_hasDerivAt (r : ℝ) (hr : Regular r)
    (s t : Fin 2) (c : Fin 3) :
    HasDerivAt (fun δ : ℝ =>
      SourceInvariantTailWeakDerivative.completedH (a s) (a t) (b s) (b t) z r δ c 2)
      ((r - z) * weakH (a s) (a t) (b t) r c) 0 := by
  simpa only [weakH_eq] using
    SourceInvariantTailWeakDerivative.completedH_missing_hasDerivAt
      (a s) (a t) (b s) (b t) z r c (hr s c) (hr t)

private theorem completedJ_base_hasDerivAt (r : ℝ) (hr : Regular r)
    (s t : Fin 2) (c : Fin 3) :
    HasDerivAt (fun δ : ℝ =>
      SourceInvariantTailWeakDerivative.completedJ (a s) (a t) (b s) (b t) z r δ c 2)
      ((r - z) * weakJ (a s) (a t) (b t) r c) 0 := by
  simpa only [weakJ_eq] using
    SourceInvariantTailWeakDerivative.completedJ_missing_hasDerivAt
      (a s) (a t) (b s) (b t) z r c (hr s c) (hr t)

theorem completedRows_missing_hasDerivAt (r : ℝ) (hr : Regular r) (i : Fin 12) :
    HasDerivAt (fun δ : ℝ => completedRows r δ i 2) ((r - z) * weakRows r i) 0 := by
  fin_cases i
  · simpa [completedRows, assembleRows, weakRows] using completedH_base_hasDerivAt r hr 0 1 0
  · simpa [completedRows, assembleRows, weakRows] using completedH_base_hasDerivAt r hr 0 1 1
  · simpa [completedRows, assembleRows, weakRows] using completedH_base_hasDerivAt r hr 0 1 2
  · simpa [completedRows, assembleRows, weakRows] using completedH_base_hasDerivAt r hr 1 0 0
  · simpa [completedRows, assembleRows, weakRows] using completedH_base_hasDerivAt r hr 1 0 1
  · simpa [completedRows, assembleRows, weakRows] using completedH_base_hasDerivAt r hr 1 0 2
  · simpa [completedRows, assembleRows, weakRows] using completedJ_base_hasDerivAt r hr 0 1 0
  · simpa [completedRows, assembleRows, weakRows] using completedJ_base_hasDerivAt r hr 0 1 1
  · simpa [completedRows, assembleRows, weakRows] using completedJ_base_hasDerivAt r hr 0 1 2
  · simpa [completedRows, assembleRows, weakRows] using completedJ_base_hasDerivAt r hr 1 0 0
  · simpa [completedRows, assembleRows, weakRows] using completedJ_base_hasDerivAt r hr 1 0 1
  · simpa [completedRows, assembleRows, weakRows] using completedJ_base_hasDerivAt r hr 1 0 2

/-- Constant Γ commutes with the actual finite sum of kernel derivatives. -/
theorem combinedCompleted_missing_hasDerivAt (r : ℝ) (hr : Regular r) (j : Fin 4) :
    HasDerivAt (fun δ : ℝ => combinedCompleted r δ j 2)
      ((r - z) * weakFunctions r j) 0 := by
  have hs : HasDerivAt
      (fun δ : ℝ => ∑ i : Fin 12, gamma i j * completedRows r δ i 2)
      (∑ i : Fin 12, gamma i j * ((r - z) * weakRows r i)) 0 :=
    HasDerivAt.fun_sum (fun i _ =>
      (completedRows_missing_hasDerivAt r hr i).const_mul (gamma i j))
  have hc : (∑ i : Fin 12, gamma i j * ((r - z) * weakRows r i)) =
      (r - z) * weakFunctions r j := by
    rw [← combinedWeak_eq r hr j]
    simp only [combinedWeak, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact hs.congr_deriv hc

/-- The displayed actual source has the opposite sign to its completed row. -/
theorem combinedSource_missing_hasDerivAt (r : ℝ) (hr : Regular r) (j : Fin 4) :
    HasDerivAt (fun δ : ℝ => combinedSource r δ j 2)
      (-((r - z) * weakFunctions r j)) 0 := by
  apply ((combinedCompleted_missing_hasDerivAt r hr j).const_sub
    (combinedHeads r j 2)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun δ =>
    congrArg (fun M : Matrix (Fin 4) (Fin 3) ℝ => M j 2)
      (combinedSource_eq_head_sub_completed r δ))

theorem combinedSource_missing_deriv (r : ℝ) (hr : Regular r) (j : Fin 4) :
    deriv (fun δ : ℝ => combinedSource r δ j 2) 0 =
      -(r - z) * weakFunctions r j := by
  rw [(combinedSource_missing_hasDerivAt r hr j).deriv]
  ring

theorem combinedCompleted_normalized_deriv (r : ℝ) (hr : Regular r)
    (hrz : r ≠ z) (j : Fin 4) :
    deriv (fun δ : ℝ => combinedCompleted r δ j 2) 0 / (r - z) = weakFunctions r j := by
  rw [(combinedCompleted_missing_hasDerivAt r hr j).deriv]
  field_simp [sub_ne_zero.mpr hrz]

theorem combinedSource_normalized_deriv (r : ℝ) (hr : Regular r)
    (hrz : r ≠ z) (j : Fin 4) :
    deriv (fun δ : ℝ => combinedSource r δ j 2) 0 / (r - z) = -weakFunctions r j := by
  rw [(combinedSource_missing_hasDerivAt r hr j).deriv]
  field_simp [sub_ne_zero.mpr hrz]

/-- Binary annihilation, exact retained heads, and signed actual derivatives. -/
theorem actual_two_block_base (r : ℝ) (hr : Regular r) :
    combinedCompleted r 0 = 0 ∧
    (∀ j c, combinedSource r 0 j c = theta j * v r c) ∧
    (∀ j, HasDerivAt (fun δ : ℝ => combinedSource r δ j 2)
      (-((r - z) * weakFunctions r j)) 0) :=
  ⟨combinedCompleted_zero r hr, combinedSource_zero_eq r hr,
    combinedSource_missing_hasDerivAt r hr⟩

end

end PanelMoments.SourceInvariantTailBaseDerivativeBridge
