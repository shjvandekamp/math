import PanelMoments.SourceScalarPrependAlgebra

set_option autoImplicit false

/-!
# Actual algebra of the weighted preserving prepend

The common matrix is `G̃ = diag(r) + 11ᵀ`, and the actual relative-time
perturbation has factors `(1, 1 + ε, 1 + 2ε)` at the prepend block.
On `∑ a, X a = 0`, write `w a = 1 / r a` and `S = 1 + ∑ a, w a`.
The baseline kernel preserves the starting row by `X K(0) = S X`.
Its derivative is proved through the existing actual kernel interface,
assuming nonzero `r a` and coordinates `X a`.

The finite matrix calculations below are the two rank-one determinants
and the concrete quadratic coefficient determinant from SP16–SP22.
No residue extraction, generic existence, or source-family independence
is asserted here.
-/

namespace PanelMoments.SourceWeightedPrependAlgebra

open scoped BigOperators
open SourceHomogeneous SourceRelativeTimeJet
open SourceScalarPrependAlgebra (ell)

noncomputable section

/-- The common matrix `diag(r) + 11ᵀ` through the actual table interface. -/
def weightedTable (r : State 2 → ℝ) : Table 2 :=
  fun _ a b => (if a = b then r a else 0) + 1

def weightedPrependTable (r : State 2 → ℝ) (ε : ℝ) : Table 2 :=
  perturbTable (weightedTable r) 0 (relativeDirection 1 2) ε

def weight (r : State 2 → ℝ) (a : State 2) : ℝ := 1 / r a

def preservingScale (r : State 2 → ℝ) : ℝ := 1 + ∑ a : State 2, weight r a

/-- The part of the weighted row derivative without reciprocal coordinates. -/
def weightedRegularRow (r X : State 2 → ℝ) : State 2 → ℝ :=
  fun b => (preservingScale r - 1) * X b * relativeDirection 1 2 b -
    (∑ a : State 2, weight r a * relativeDirection 1 2 a) * X b - ell X * weight r b

theorem weightedPrependTable_entry (r : State 2 → ℝ) (ε : ℝ) (a b : State 2) :
    weightedPrependTable r ε 0 a b =
      ((if a = b then r a else 0) + 1) *
        (![1, 1 + ε, 1 + 2 * ε] : State 2 → ℝ) b := by
  have hd : 1 + ε * relativeDirection 1 2 b =
      (![1, 1 + ε, 1 + 2 * ε] : State 2 → ℝ) b := by
    fin_cases b <;> simp [relativeDirection, mul_comm]
  simp only [weightedPrependTable, perturbTable, ↓reduceIte, weightedTable, hd]

theorem weighted_rowForm (r X : State 2 → ℝ) (a : State 2)
    (hplane : ∑ b : State 2, X b = 0) :
    rowForm (weightedTable r) X 0 a = r a * X a := by
  simp [rowForm, weightedTable, add_mul, Finset.sum_add_distrib, hplane]

theorem weighted_rowFormJet (r X : State 2 → ℝ) (a : State 2) :
    rowFormJet (weightedTable r) X 0 (relativeDirection 1 2) a =
      ell X + r a * relativeDirection 1 2 a * X a := by
  fin_cases a <;>
    simp [rowFormJet, weightedTable, relativeDirection, ell, Fin.sum_univ_succ] <;> ring

/-- The exact row form on the terminal plane, before any limiting operation. -/
theorem weighted_prepend_rowForm (r X : State 2 → ℝ) (ε : ℝ) (a : State 2)
    (hplane : ∑ b : State 2, X b = 0) :
    rowForm (weightedPrependTable r ε) X 0 a =
      r a * X a + ε * (ell X + r a * relativeDirection 1 2 a * X a) := by
  rw [weightedPrependTable, rowForm_perturbTable, weighted_rowForm r X a hplane,
    weighted_rowFormJet]

theorem weighted_prepend_kernel_zero (r X : State 2 → ℝ)
    (hplane : ∑ a : State 2, X a = 0)
    (hr : ∀ a, r a ≠ 0) (hX : ∀ a, X a ≠ 0) :
    kernel (weightedPrependTable r 0) X 0 =
      1 + Matrix.of (fun a b : State 2 => (weight r a / X a) * X b) := by
  rw [weightedPrependTable, perturbTable_zero]
  ext a b
  simp only [kernel, Matrix.of_apply, weighted_rowForm r X a hplane,
    Matrix.add_apply, Matrix.one_apply, weightedTable, weight]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    field_simp [hr a, hX a]
  · simp only [hab, ↓reduceIte, zero_add]
    field_simp [hr a, hX a]

theorem weighted_prepend_preserves_row (r X : State 2 → ℝ)
    (hplane : ∑ a : State 2, X a = 0)
    (hr : ∀ a, r a ≠ 0) (hX : ∀ a, X a ≠ 0) :
    Matrix.vecMul X (kernel (weightedPrependTable r 0) X 0) = preservingScale r • X := by
  rw [weighted_prepend_kernel_zero r X hplane hr hX, Matrix.vecMul_add, Matrix.vecMul_one]
  funext b
  change X b + (∑ a : State 2, X a * ((weight r a / X a) * X b)) =
    preservingScale r * X b
  have hc (a : State 2) : X a * ((weight r a / X a) * X b) = weight r a * X b := by
    field_simp [hX a]
  simp_rw [hc]
  rw [← Finset.sum_mul]
  simp only [preservingScale]
  ring

/-- An entrywise identity for the actual kernel derivative. -/
theorem weighted_kernelJet_entry (r X : State 2 → ℝ) (a b : State 2)
    (hplane : ∑ c : State 2, X c = 0) (hra : r a ≠ 0) (hXa : X a ≠ 0) :
    X a * kernelJet (weightedTable r) X 0 (relativeDirection 1 2) a b =
      ((if a = b then 1 else 0) + weight r a) * X b *
        (relativeDirection 1 2 b - relativeDirection 1 2 a - ell X * weight r a / X a) := by
  simp only [kernelJet, Matrix.of_apply, kernel,
    weighted_rowForm r X a hplane, weighted_rowFormJet, weightedTable, weight]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    field_simp [hra, hXa]
    ring
  · simp only [hab, ↓reduceIte, zero_add]
    field_simp [hra, hXa]
    ring

private theorem weighted_kernelJet_summand (r X : State 2 → ℝ) (a b : State 2)
    (hplane : ∑ c : State 2, X c = 0) (hra : r a ≠ 0) (hXa : X a ≠ 0) :
    X a * kernelJet (weightedTable r) X 0 (relativeDirection 1 2) a b =
      (if a = b then -(ell X * weight r b) else 0) +
        weight r a * X b * relativeDirection 1 2 b -
        (weight r a * relativeDirection 1 2 a) * X b -
        (weight r a ^ 2 / X a) * (ell X * X b) := by
  rw [weighted_kernelJet_entry r X a b hplane hra hXa]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    field_simp [hXa]
    ring
  · simp only [hab, ↓reduceIte, zero_add]
    ring

/-- The weighted prepend identity, retaining all reciprocal coordinate factors. -/
theorem weighted_prepend_kernelJet_row (r X : State 2 → ℝ)
    (hplane : ∑ a : State 2, X a = 0)
    (hr : ∀ a, r a ≠ 0) (hX : ∀ a, X a ≠ 0) :
    Matrix.vecMul X (kernelJet (weightedTable r) X 0 (relativeDirection 1 2)) =
      weightedRegularRow r X - (ell X * ∑ a : State 2, weight r a ^ 2 / X a) • X := by
  funext b
  simp only [Matrix.vecMul, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [weighted_kernelJet_summand r X _ _ hplane (hr _) (hX _)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    weightedRegularRow, preservingScale]
  ring

/-- This row formula is the derivative of the actual perturbed kernel. -/
theorem weighted_prepend_row_hasDerivAt (r X : State 2 → ℝ) (b : State 2)
    (hplane : ∑ a : State 2, X a = 0)
    (hr : ∀ a, r a ≠ 0) (hX : ∀ a, X a ≠ 0) :
    HasDerivAt
      (fun ε : ℝ => Matrix.vecMul X (kernel (weightedPrependTable r ε) X 0) b)
      (weightedRegularRow r X b -
        (ell X * ∑ a : State 2, weight r a ^ 2 / X a) * X b) 0 := by
  have h := vecMul_kernel_hasDerivAt (weightedTable r) X X 0 (relativeDirection 1 2) b
    (fun a => by rw [weighted_rowForm r X a hplane]; exact mul_ne_zero (hr a) (hX a))
  have hj := congrFun (weighted_prepend_kernelJet_row r X hplane hr hX) b
  exact h.congr_deriv hj

/-- The finite coefficient matrix `I + w 1ᵀ`. -/
def weightedObservationMatrix (r : State 2 → ℝ) : Matrix (State 2) (State 2) ℝ :=
  1 + Matrix.of (fun a _ : State 2 => weight r a)

/-- The finite coefficient matrix `I - w 1ᵀ / S`. -/
def weightedCorrectionMatrix (r : State 2 → ℝ) : Matrix (State 2) (State 2) ℝ :=
  1 - Matrix.of (fun a _ : State 2 => weight r a / preservingScale r)

private theorem rankOne_det (w : State 2 → ℝ) :
    (1 + Matrix.of (fun a _ : State 2 => w a)).det = 1 + ∑ a : State 2, w a := by
  rw [Matrix.det_fin_three (1 + Matrix.of (fun a _ : State 2 => w a))]
  simp [Fin.sum_univ_succ]
  ring

theorem weightedObservationMatrix_det (r : State 2 → ℝ) :
    (weightedObservationMatrix r).det = preservingScale r := by
  exact rankOne_det (weight r)

theorem weightedCorrectionMatrix_det (r : State 2 → ℝ) (hS : preservingScale r ≠ 0) :
    (weightedCorrectionMatrix r).det = 1 / preservingScale r := by
  have hm : weightedCorrectionMatrix r =
      1 + Matrix.of (fun a _ : State 2 => -(weight r a / preservingScale r)) := by
    ext a b
    simp [weightedCorrectionMatrix, sub_eq_add_neg]
  rw [hm, rankOne_det]
  simp only [Finset.sum_neg_distrib, div_eq_mul_inv, ← Finset.sum_mul]
  have hs : ∑ a : State 2, weight r a = preservingScale r - 1 := by
    simp [preservingScale]
  rw [hs]
  field_simp [hS]
  ring

theorem weightedObservationMatrix_det_ne_zero (r : State 2 → ℝ)
    (hS : preservingScale r ≠ 0) : (weightedObservationMatrix r).det ≠ 0 := by
  rw [weightedObservationMatrix_det]
  exact hS

theorem weightedCorrectionMatrix_det_ne_zero (r : State 2 → ℝ)
    (hS : preservingScale r ≠ 0) : (weightedCorrectionMatrix r).det ≠ 0 := by
  rw [weightedCorrectionMatrix_det r hS]
  exact one_div_ne_zero hS

/-- Coefficients in the basis `(L₁², L₁L₂, L₂²)` of the three quadratic
columns in SP18, with all five scalar factors left explicit. -/
def quadraticCoefficientMatrix (κ B12 B21 h k : ℝ) : Matrix (State 2) (State 2) ℝ :=
  ![![0, 0, -B21 * h], ![κ, B12 * h, -B21 * k], ![0, B12 * k, 0]]

theorem quadraticCoefficientMatrix_det (κ B12 B21 h k : ℝ) :
    (quadraticCoefficientMatrix κ B12 B21 h k).det = -κ * B12 * B21 * h * k := by
  rw [Matrix.det_fin_three (quadraticCoefficientMatrix κ B12 B21 h k)]
  simp [quadraticCoefficientMatrix]
  ring

theorem quadraticCoefficientMatrix_det_ne_zero (κ B12 B21 h k : ℝ)
    (hκ : κ ≠ 0) (h12 : B12 ≠ 0) (h21 : B21 ≠ 0) (hh : h ≠ 0) (hk : k ≠ 0) :
    (quadraticCoefficientMatrix κ B12 B21 h k).det ≠ 0 := by
  rw [quadraticCoefficientMatrix_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hκ) h12) h21) hh) hk

end

end PanelMoments.SourceWeightedPrependAlgebra
