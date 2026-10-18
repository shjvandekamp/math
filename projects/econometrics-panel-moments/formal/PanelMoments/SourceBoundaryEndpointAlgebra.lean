import PanelMoments.SourceWeightedPrependAlgebra
import PanelMoments.SourceTimeScaling

set_option autoImplicit false

/-!
# Actual weighted-kernel algebra at coordinate endpoints

For the actual table `(diag(r) + 11ᵀ) diag(b)`, cancel the output coordinate
in `(Z diag(X)) K` before restricting to a coordinate edge. The resulting
row `U` satisfies the endpoint relation with coefficients
`(b k / b i) * (w i / (S - w k))`, where `w i = 1/r i` and `S = 1 + ∑ w i`.

The finite recovery matrix has diagonal one and these negated off-diagonal
coefficients. Its determinant is `S² / ∏ k, (S - w k)`, independent of the
nonzero time factors, and is positive when the diagonal weights are positive.
The coordinate is canceled algebraically, never by evaluating `0/0`.
No source independence, residue interpolation, or generic-existence claim
is made here.
-/

namespace PanelMoments.SourceBoundaryEndpointAlgebra

open scoped BigOperators
open SourceHomogeneous SourceWeightedPrependAlgebra SourceTimeScaling

noncomputable section

/-- The output coordinate is absent from this actual-kernel numerator. -/
def canceledOutput {Q : ℕ} (A : Table Q) (X Z : State Q → ℝ) (t : ℕ) : State Q → ℝ :=
  fun j => ∑ i : State Q, Z i * X i * A t i j / rowForm A X t i

/-- Exact finite algebra, valid before any coordinate-edge restriction. -/
theorem canceledOutput_kernel {Q : ℕ} (A : Table Q) (X Z : State Q → ℝ) (t : ℕ) :
    Matrix.vecMul (Matrix.vecMul Z (Matrix.diagonal X)) (kernel A X t) =
      Matrix.vecMul (canceledOutput A X Z t) (Matrix.diagonal X) := by
  have hdiag : Matrix.vecMul Z (Matrix.diagonal X) = fun i => Z i * X i := by
    funext i
    simp only [Matrix.vecMul_diagonal]
  rw [hdiag]
  funext j
  simp only [Matrix.vecMul_diagonal]
  change (∑ i : State Q, (Z i * X i) * (A t i j * X j / rowForm A X t i)) =
    (∑ i : State Q, Z i * X i * A t i j / rowForm A X t i) * X j
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem canceledOutput_eq_divided_output {Q : ℕ} (A : Table Q)
    (X Z : State Q → ℝ) (t : ℕ) (j : State Q) (hX : X j ≠ 0) :
    canceledOutput A X Z t j =
      Matrix.vecMul (Matrix.vecMul Z (Matrix.diagonal X)) (kernel A X t) j / X j := by
  rw [canceledOutput_kernel, Matrix.vecMul_diagonal]
  field_simp [hX]

/-- The existing weighted common table with the actual column time factors. -/
def weightedTimeTable (r b : State 2 → ℝ) : Table 2 :=
  scaledTable (weightedTable r) b

theorem weightedTime_rowForm (r b X : State 2 → ℝ) (t : ℕ) (a : State 2) :
    rowForm (weightedTimeTable r b) X t a =
      (∑ i : State 2, b i * X i) + r a * b a * X a := by
  simp [rowForm, weightedTimeTable, scaledTable, weightedTable,
    add_mul, Finset.sum_add_distrib]
  ring

theorem weightedTime_canceledOutput (r b X Z : State 2 → ℝ) (t : ℕ) (j : State 2) :
    canceledOutput (weightedTimeTable r b) X Z t j =
      b j * ((∑ i : State 2, Z i * X i / rowForm (weightedTimeTable r b) X t i) +
        r j * (Z j * X j / rowForm (weightedTimeTable r b) X t j)) := by
  let f : State 2 → ℝ := fun i => Z i * X i / rowForm (weightedTimeTable r b) X t i
  have hterm (i : State 2) :
      Z i * X i * weightedTimeTable r b t i j / rowForm (weightedTimeTable r b) X t i =
        b j * (f i + if i = j then r j * f j else 0) := by
    by_cases hij : i = j
    · subst i
      simp only [weightedTimeTable, scaledTable, weightedTable, ↓reduceIte, f]
      ring
    · simp only [weightedTimeTable, scaledTable, weightedTable, hij, ↓reduceIte,
        zero_add, add_zero, f]
      ring
  change (∑ i : State 2, Z i * X i * weightedTimeTable r b t i j /
    rowForm (weightedTimeTable r b) X t i) = b j * ((∑ i : State 2, f i) + r j * f j)
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp

theorem weight_pos {r : State 2 → ℝ} (hr : ∀ i, 0 < r i) (i : State 2) :
    0 < weight r i := one_div_pos.mpr (hr i)

theorem preservingScale_pos {r : State 2 → ℝ} (hr : ∀ i, 0 < r i) :
    0 < preservingScale r :=
  add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => le_of_lt (weight_pos hr i)))

theorem preservingScale_sub_weight_eq (r : State 2 → ℝ) (k : State 2) :
    preservingScale r - weight r k = 1 + ∑ i ∈ Finset.univ.erase k, weight r i := by
  have hsum : (∑ i ∈ Finset.univ.erase k, weight r i) + weight r k =
      ∑ i : State 2, weight r i :=
    Finset.sum_erase_add _ _ (Finset.mem_univ k)
  unfold preservingScale
  linarith

theorem preservingScale_sub_weight_pos {r : State 2 → ℝ} (hr : ∀ i, 0 < r i)
    (k : State 2) : 0 < preservingScale r - weight r k := by
  rw [preservingScale_sub_weight_eq]
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => le_of_lt (weight_pos hr i)))

def endpointCoefficient (r b : State 2 → ℝ) (k i : State 2) : ℝ :=
  (b k / b i) * (weight r i / (preservingScale r - weight r k))

/-- The endpoint relation follows from the actual weighted kernel output. -/
theorem weighted_endpoint_relation (r b X Z : State 2 → ℝ) (t : ℕ) (k : State 2)
    (hr : ∀ i, 0 < r i) (hb : ∀ i, b i ≠ 0) (hX : X k = 0) :
    canceledOutput (weightedTimeTable r b) X Z t k =
      ∑ i ∈ Finset.univ.erase k,
        endpointCoefficient r b k i * canceledOutput (weightedTimeTable r b) X Z t i := by
  let f : State 2 → ℝ := fun i => Z i * X i / rowForm (weightedTimeTable r b) X t i
  let T : ℝ := ∑ i : State 2, f i
  have hU (i : State 2) : canceledOutput (weightedTimeTable r b) X Z t i =
      b i * (T + r i * f i) := weightedTime_canceledOutput r b X Z t i
  have hfk : f k = 0 := by simp [f, hX]
  have hsumf : (∑ i ∈ Finset.univ.erase k, f i) = T := by
    have hsum : (∑ i ∈ Finset.univ.erase k, f i) + f k = T :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k)
    simpa only [hfk, add_zero] using hsum
  have hterm (i : State 2) :
      (weight r i / b i) * canceledOutput (weightedTimeTable r b) X Z t i =
        weight r i * T + f i := by
    rw [hU]
    unfold weight
    field_simp [hb i, ne_of_gt (hr i)]
  have hsum : (∑ i ∈ Finset.univ.erase k,
      (weight r i / b i) * canceledOutput (weightedTimeTable r b) X Z t i) =
      (preservingScale r - weight r k) * T := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumf,
      preservingScale_sub_weight_eq]
    ring
  have heta : (∑ i ∈ Finset.univ.erase k,
      endpointCoefficient r b k i * canceledOutput (weightedTimeTable r b) X Z t i) =
      (b k / (preservingScale r - weight r k)) *
        ∑ i ∈ Finset.univ.erase k,
          (weight r i / b i) * canceledOutput (weightedTimeTable r b) X Z t i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold endpointCoefficient
    ring
  rw [heta, hsum, hU, hfk, mul_zero, add_zero]
  field_simp [ne_of_gt (preservingScale_sub_weight_pos hr k)]

/-- The finite endpoint recovery matrix, with the paper's row/column convention. -/
def endpointMatrix (r b : State 2 → ℝ) : Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun k i => if k = i then 1 else -endpointCoefficient r b k i)

def endpointCore (r : State 2 → ℝ) : Matrix (State 2) (State 2) ℝ :=
  preservingScale r • (1 : Matrix (State 2) (State 2) ℝ) -
    Matrix.of (fun _ i : State 2 => weight r i)

/-- Row and column scaling expose the cancellation of all time factors. -/
theorem endpointMatrix_factorization (r b : State 2 → ℝ)
    (hb : ∀ i, b i ≠ 0) (hgap : ∀ i, preservingScale r - weight r i ≠ 0) :
    endpointMatrix r b =
      Matrix.diagonal (fun k => b k / (preservingScale r - weight r k)) *
        endpointCore r * Matrix.diagonal (fun i => 1 / b i) := by
  ext k i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [endpointMatrix, endpointCore, Matrix.of_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hki : k = i
  · subst i
    simp only [↓reduceIte, mul_one]
    field_simp [hb k, hgap k]
  · simp only [hki, ↓reduceIte, mul_zero, zero_sub, endpointCoefficient]
    ring

theorem endpointCore_det (r : State 2 → ℝ) :
    (endpointCore r).det = preservingScale r ^ 2 := by
  rw [Matrix.det_fin_three (endpointCore r)]
  simp [endpointCore, preservingScale, Fin.sum_univ_succ]
  ring

theorem endpointMatrix_det (r b : State 2 → ℝ)
    (hb : ∀ i, b i ≠ 0) (hgap : ∀ i, preservingScale r - weight r i ≠ 0) :
    (endpointMatrix r b).det =
      preservingScale r ^ 2 / ∏ k : State 2, (preservingScale r - weight r k) := by
  rw [endpointMatrix_factorization r b hb hgap, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, endpointCore_det]
  simp [Fin.prod_univ_succ]
  field_simp [hb 0, hb 1, hb 2, hgap 0, hgap 1, hgap 2]

theorem endpointMatrix_det_pos (r b : State 2 → ℝ)
    (hr : ∀ i, 0 < r i) (hb : ∀ i, b i ≠ 0) : 0 < (endpointMatrix r b).det := by
  rw [endpointMatrix_det r b hb (fun i => ne_of_gt (preservingScale_sub_weight_pos hr i))]
  exact div_pos (sq_pos_of_pos (preservingScale_pos hr))
    (Finset.prod_pos (fun i _ => preservingScale_sub_weight_pos hr i))

theorem endpointMatrix_det_ne_zero (r b : State 2 → ℝ)
    (hr : ∀ i, 0 < r i) (hb : ∀ i, b i ≠ 0) : (endpointMatrix r b).det ≠ 0 :=
  ne_of_gt (endpointMatrix_det_pos r b hr hb)

end

end PanelMoments.SourceBoundaryEndpointAlgebra
