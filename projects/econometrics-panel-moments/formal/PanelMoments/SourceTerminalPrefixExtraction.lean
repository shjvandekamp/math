import PanelMoments.SourceHomogeneous
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

/-!
# Finite algebra of terminal-prefix extraction

For the actual terminal table matrix `A`, its inverse `B`, and its existing
row forms `L`, set `T_K = B diag(L) - diag(X)`. The component identity and
its own-line and coordinate-edge restrictions give the local data in
LC69--LC70. Two other components of `g B`, together with `g a`, recover
the entire row when `A a a` is nonzero.

The final theorem uses the actual nonsingular matrix inverse and three
explicit observation points. All line, coordinate, and denominator
conditions remain hypotheses. The kernel bridge is proved directly from
`SourceHomogeneous.kernel`. No residue operator, ambient-membership
statement, generic existence, or source-family independence is asserted.
-/

namespace PanelMoments.SourceTerminalPrefixExtraction

open scoped BigOperators
open SourceHomogeneous

noncomputable section

/-- `T_K` with an explicit candidate inverse, using the actual table row forms. -/
def terminalCorrection (A : Table 2) (X : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) : Matrix (State 2) (State 2) ℝ :=
  B * Matrix.diagonal (rowForm A X t) - Matrix.diagonal X

theorem terminalCorrection_component (A : Table 2) (X g : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (j : State 2) :
    Matrix.vecMul g (terminalCorrection A X t B) j =
      rowForm A X t j * Matrix.vecMul g B j - X j * g j := by
  rw [terminalCorrection, Matrix.vecMul_sub, ← Matrix.vecMul_vecMul]
  simp only [Pi.sub_apply, Matrix.vecMul_diagonal]
  ring

theorem terminalCorrection_own_line (A : Table 2) (X g : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (a : State 2)
    (hL : rowForm A X t a = 0) :
    Matrix.vecMul g (terminalCorrection A X t B) a = -(X a * g a) := by
  rw [terminalCorrection_component, hL]
  ring

theorem terminalCorrection_coordinate_edge (A : Table 2) (X g : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (j : State 2) (hX : X j = 0) :
    Matrix.vecMul g (terminalCorrection A X t B) j =
      rowForm A X t j * Matrix.vecMul g B j := by
  rw [terminalCorrection_component, hX]
  ring

/-- Clearing the actual kernel's row denominators requires only their units. -/
theorem rowForm_diagonal_mul_kernel (A : Table 2) (X : State 2 → ℝ) (t : ℕ)
    (hL : ∀ a, rowForm A X t a ≠ 0) :
    Matrix.diagonal (rowForm A X t) * kernel A X t =
      Matrix.of (A t) * Matrix.diagonal X := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  change rowForm A X t a * (A t a b * X b / rowForm A X t a) = A t a b * X b
  field_simp [hL a]

/-- The correction matrix is tied to the actual append kernel. -/
theorem terminalCorrection_mul_kernel (A : Table 2) (X : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hBA : B * Matrix.of (A t) = 1)
    (hL : ∀ a, rowForm A X t a ≠ 0) :
    terminalCorrection A X t B * kernel A X t =
      Matrix.diagonal X * (1 - kernel A X t) := by
  rw [terminalCorrection, sub_mul, Matrix.mul_assoc,
    rowForm_diagonal_mul_kernel A X t hL, ← Matrix.mul_assoc, hBA,
    one_mul, mul_sub, mul_one]

/-- Multiplying by an actual table row yields `L_a e_a - v_a`. -/
theorem table_row_terminalCorrection (A : Table 2) (X : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hAB : Matrix.of (A t) * B = 1) (a : State 2) :
    Matrix.vecMul (A t a) (terminalCorrection A X t B) =
      fun j => rowForm A X t a * (if a = j then 1 else 0) - A t a j * X j := by
  funext j
  rw [terminalCorrection_component]
  have hrow : Matrix.vecMul (A t a) B j = if a = j then 1 else 0 := by
    have h := congrArg (fun M : Matrix (State 2) (State 2) ℝ => M a j) hAB
    simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
      Matrix.vecMul, dotProduct] using h
  rw [hrow]
  by_cases haj : a = j
  · subst j
    simp only [↓reduceIte]
    ring
  · simp only [haj, ↓reduceIte, mul_zero, zero_sub]
    ring

/-- The exact LC69 coefficient shift absorbs the terminal `E` contribution. -/
theorem prefix_shift_on_own_line (A : Table 2) (X h : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hAB : Matrix.of (A t) * B = 1)
    (a : State 2) (scalar : ℝ) (hL : rowForm A X t a = 0) :
    Matrix.vecMul (h + scalar • A t a) (terminalCorrection A X t B) =
      Matrix.vecMul h (terminalCorrection A X t B) -
        scalar • (fun j => A t a j * X j) := by
  rw [Matrix.add_vecMul, Matrix.smul_vecMul, table_row_terminalCorrection A X t B hAB a]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hL, zero_mul, zero_sub]
  ring

theorem row_reconstruction (A : Table 2) (g : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hBA : B * Matrix.of (A t) = 1) :
    Matrix.vecMul (Matrix.vecMul g B) (Matrix.of (A t)) = g := by
  rw [Matrix.vecMul_vecMul, hBA, Matrix.vecMul_one]

/-- The missing component in LC70, keeping the actual diagonal coefficient. -/
theorem missing_coordinate (A : Table 2) (g : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hBA : B * Matrix.of (A t) = 1)
    (a : State 2) (haa : A t a a ≠ 0) :
    Matrix.vecMul g B a =
      (g a - ∑ j ∈ Finset.univ.erase a, Matrix.vecMul g B j * A t j a) / A t a a := by
  have hsum : (∑ j ∈ Finset.univ.erase a, Matrix.vecMul g B j * A t j a) +
      Matrix.vecMul g B a * A t a a = g a := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    exact congrFun (row_reconstruction A g t B hBA) a
  apply (eq_div_iff haa).2
  linarith

/-- The own entry of `g`, together with the other two entries of `g B`. -/
def extractedCoordinates (B : Matrix (State 2) (State 2) ℝ)
    (g : State 2 → ℝ) (a : State 2) : State 2 → ℝ :=
  fun j => if j = a then g a else Matrix.vecMul g B j

/-- Complete the three inverse coordinates from the local data. -/
def completeCoordinates (A : Table 2) (t : ℕ) (a : State 2)
    (data : State 2 → ℝ) : State 2 → ℝ :=
  fun j => if j = a then
    (data a - ∑ k ∈ Finset.univ.erase a, data k * A t k a) / A t a a
  else data j

theorem completeCoordinates_extracted (A : Table 2) (g : State 2 → ℝ) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hBA : B * Matrix.of (A t) = 1)
    (a : State 2) (haa : A t a a ≠ 0) :
    completeCoordinates A t a (extractedCoordinates B g a) = Matrix.vecMul g B := by
  have hown : extractedCoordinates B g a a = g a := by simp [extractedCoordinates]
  have hsum : (∑ j ∈ Finset.univ.erase a, extractedCoordinates B g a j * A t j a) =
      ∑ j ∈ Finset.univ.erase a, Matrix.vecMul g B j * A t j a := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [extractedCoordinates, (Finset.mem_erase.mp hj).1]
  funext j
  by_cases hja : j = a
  · subst j
    simp only [completeCoordinates, ↓reduceIte, hown, hsum]
    exact (missing_coordinate A g t B hBA a haa).symm
  · simp [completeCoordinates, extractedCoordinates, hja]

/-- Coordinate-edge ratios and the own-line ratio, evaluated before reconstruction. -/
def terminalObservations (A : Table 2) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (g : State 2 → ℝ) (a : State 2)
    (points : State 2 → State 2 → ℝ) : State 2 → ℝ :=
  fun j => if j = a then
    -Matrix.vecMul g (terminalCorrection A (points j) t B) a / points j a
  else Matrix.vecMul g (terminalCorrection A (points j) t B) j / rowForm A (points j) t j

theorem terminalObservations_eq_extracted (A : Table 2) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (g : State 2 → ℝ) (a : State 2)
    (points : State 2 → State 2 → ℝ)
    (hline : ∀ j, rowForm A (points j) t a = 0) (hown : points a a ≠ 0)
    (hedge : ∀ j, j ≠ a → points j j = 0)
    (hunit : ∀ j, j ≠ a → rowForm A (points j) t j ≠ 0) :
    terminalObservations A t B g a points = extractedCoordinates B g a := by
  funext j
  by_cases hja : j = a
  · subst j
    simp only [terminalObservations, extractedCoordinates, ↓reduceIte]
    rw [terminalCorrection_own_line A (points a) g t B a (hline a)]
    field_simp [hown]
  · simp only [terminalObservations, extractedCoordinates, hja, ↓reduceIte]
    rw [terminalCorrection_coordinate_edge A (points j) g t B j (hedge j hja)]
    field_simp [hunit j hja]

/-- Three genuine local values recover the constant terminal prefix row. -/
theorem reconstruct_from_terminalObservations (A : Table 2) (t : ℕ)
    (B : Matrix (State 2) (State 2) ℝ) (hBA : B * Matrix.of (A t) = 1)
    (g : State 2 → ℝ) (a : State 2) (haa : A t a a ≠ 0)
    (points : State 2 → State 2 → ℝ)
    (hline : ∀ j, rowForm A (points j) t a = 0) (hown : points a a ≠ 0)
    (hedge : ∀ j, j ≠ a → points j j = 0)
    (hunit : ∀ j, j ≠ a → rowForm A (points j) t j ≠ 0) :
    Matrix.vecMul
      (completeCoordinates A t a (terminalObservations A t B g a points))
      (Matrix.of (A t)) = g := by
  rw [terminalObservations_eq_extracted A t B g a points hline hown hedge hunit,
    completeCoordinates_extracted A g t B hBA a haa, row_reconstruction A g t B hBA]

theorem actual_inverse_terminalCorrection_mul_kernel (A : Table 2)
    (X : State 2 → ℝ) (t : ℕ) (hdet : (Matrix.of (A t)).det ≠ 0)
    (hL : ∀ a, rowForm A X t a ≠ 0) :
    terminalCorrection A X t (Matrix.of (A t))⁻¹ * kernel A X t =
      Matrix.diagonal X * (1 - kernel A X t) := by
  exact terminalCorrection_mul_kernel A X t _
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)) hL

theorem actual_inverse_prefix_shift (A : Table 2) (X h : State 2 → ℝ) (t : ℕ)
    (hdet : (Matrix.of (A t)).det ≠ 0) (a : State 2) (scalar : ℝ)
    (hL : rowForm A X t a = 0) :
    Matrix.vecMul (h + scalar • A t a) (terminalCorrection A X t (Matrix.of (A t))⁻¹) =
      Matrix.vecMul h (terminalCorrection A X t (Matrix.of (A t))⁻¹) -
        scalar • (fun j => A t a j * X j) := by
  exact prefix_shift_on_own_line A X h t _
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)) a scalar hL

/-- The LC70 reconstruction for the actual inverse of the terminal table. -/
theorem actual_inverse_terminalPrefix_reconstruction (A : Table 2) (t : ℕ)
    (hdet : (Matrix.of (A t)).det ≠ 0) (g : State 2 → ℝ) (a : State 2)
    (haa : A t a a ≠ 0) (points : State 2 → State 2 → ℝ)
    (hline : ∀ j, rowForm A (points j) t a = 0) (hown : points a a ≠ 0)
    (hedge : ∀ j, j ≠ a → points j j = 0)
    (hunit : ∀ j, j ≠ a → rowForm A (points j) t j ≠ 0) :
    Matrix.vecMul
      (completeCoordinates A t a
        (terminalObservations A t (Matrix.of (A t))⁻¹ g a points))
      (Matrix.of (A t)) = g := by
  exact reconstruct_from_terminalObservations A t _
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet))
    g a haa points hline hown hedge hunit

end

end PanelMoments.SourceTerminalPrefixExtraction
