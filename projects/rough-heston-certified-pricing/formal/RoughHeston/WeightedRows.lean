module

public import RoughHeston.ProductIntegration
public import RoughHeston.WeightedKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exponentially weighted rows of the concrete fractional Adams scheme

The predictor row is bounded by the full fractional Laplace integral. The
complete corrector row is obtained by assembling the actual affine cell
weights. Moving each cell's mass to its right endpoint costs at most one
mesh-step exponential factor. These bounds retain the complete history and
do not impose a smallness condition on the maturity.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Finset

namespace RoughHeston

/-- A left-endpoint exponential factor is bounded by the factor at every
point of its predictor cell, including the integrable singular final cell. -/
theorem predictorWeight_exp_cell_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 ≤ rate)
    {j n : ℕ} (hj : j < n) :
    predictorWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) ≤
      (Real.Gamma α)⁻¹ * ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
        weightedFractionalKernel α rate ((n : ℝ) * dt) r := by
  have hcell : (j : ℝ) * dt ≤ ((j + 1 : ℕ) : ℝ) * dt :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hdt.le
  have hend : ((j + 1 : ℕ) : ℝ) * dt ≤ (n : ℝ) * dt :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hdt.le
  have hk := intervalIntegrable_fractionalKernel hα ((n : ℝ) * dt)
    ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)
  have hw := intervalIntegrable_weightedFractionalKernel hα rate ((n : ℝ) * dt)
    ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)
  rw [predictorWeight_eq_kernel_cell hα hdt hj]
  calc
    _ = (Real.Gamma α)⁻¹ *
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r *
            Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
      apply intervalIntegral.integral_mono_on hcell (hk.mul_const _) hw
      intro r hr
      unfold weightedFractionalKernel
      apply mul_le_mul_of_nonneg_left _ (fractionalKernel_nonneg (hr.2.trans hend))
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (sub_le_sub_left hr.1 _)
        (neg_nonpos.mpr hrate)

/-- The exponentially damped predictor row is bounded independently of its
length. This includes the empty row. -/
theorem predictorWeight_exp_row_range_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) (n : ℕ) :
    (∑ j ∈ range n, predictorWeight α dt j n *
      Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt))) ≤ rate ^ (-α) := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ) * dt) (n := n)
    (fun j _ => intervalIntegrable_weightedFractionalKernel hα rate ((n : ℝ) * dt)
      ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt))
  simp only [Nat.cast_zero, zero_mul] at hsplit
  calc
    _ ≤ ∑ j ∈ range n, (Real.Gamma α)⁻¹ *
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          weightedFractionalKernel α rate ((n : ℝ) * dt) r :=
      sum_le_sum (fun j hj => predictorWeight_exp_cell_le hα hdt hrate.le (mem_range.mp hj))
    _ = weightedKernelMass α rate ((n : ℝ) * dt) := by
      rw [← mul_sum, hsplit]
      rfl
    _ ≤ rate ^ (-α) := weightedKernelMass_le hα hrate
      (mul_nonneg (Nat.cast_nonneg n) hdt.le)

theorem predictorWeight_exp_row_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) (n : ℕ) :
    (∑ j : Fin n, predictorWeight α dt j.val n *
      Real.exp (-rate * ((n : ℝ) * dt - (j.val : ℝ) * dt))) ≤ rate ^ (-α) := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => predictorWeight α dt j n *
    Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt))) n]
  exact predictorWeight_exp_row_range_le hα hdt hrate n

private theorem exp_mesh_successor (rate dt : ℝ) (n j : ℕ) :
    Real.exp (-rate * ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt)) =
      Real.exp (rate * dt) * Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) := by
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The two exact affine cell weights can be bounded by putting all the
cell's mass at its right endpoint. -/
theorem correctorWeight_exp_cell_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 ≤ rate)
    {j n : ℕ} (hj : j < n) :
    correctorLeftCellWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) +
      correctorRightCellWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt)) ≤
      Real.exp (rate * dt) * (predictorWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt))) := by
  have hcell : (j : ℝ) * dt ≤ ((j + 1 : ℕ) : ℝ) * dt :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hdt.le
  have hmono : Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) ≤
      Real.exp (-rate * ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (sub_le_sub_left hcell _)
      (neg_nonpos.mpr hrate)
  calc
    _ ≤ correctorLeftCellWeight α dt j n *
          Real.exp (-rate * ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt)) +
        correctorRightCellWeight α dt j n *
          Real.exp (-rate * ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmono
        (correctorLeftCellWeight_nonneg hα hdt hj)) le_rfl
    _ = predictorWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt)) := by
      rw [← add_mul, correctorCellWeight_sum hα hdt hj]
    _ = _ := by
      rw [exp_mesh_successor]
      ring

/-- The complete corrector row, including its endpoint, retains the same
full-history bound up to one exponential mesh-step factor. -/
theorem correctorWeight_exp_row_range_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ range (n + 1), correctorWeight α dt j n *
      Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt))) ≤
        Real.exp (rate * dt) * rate ^ (-α) := by
  have hassemble := correctorWeights_assemble hα hdt hn
    (fun j => Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)))
  simp only [smul_eq_mul] at hassemble
  rw [← hassemble]
  calc
    _ ≤ ∑ j ∈ range n, Real.exp (rate * dt) * (predictorWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt))) :=
      sum_le_sum (fun j hj => correctorWeight_exp_cell_le hα hdt hrate.le (mem_range.mp hj))
    _ = Real.exp (rate * dt) * ∑ j ∈ range n, predictorWeight α dt j n *
        Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (predictorWeight_exp_row_range_le hα hdt hrate n)
      (Real.exp_pos _).le

theorem correctorWeight_exp_row_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (∑ j : Fin (n + 1), correctorWeight α dt j.val n *
      Real.exp (-rate * ((n : ℝ) * dt - (j.val : ℝ) * dt))) ≤
        Real.exp (rate * dt) * rate ^ (-α) := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => correctorWeight α dt j n *
    Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt))) (n + 1)]
  exact correctorWeight_exp_row_range_le hα hdt hrate hn

/-- The corrector history row is bounded by its complete nonnegative row. -/
theorem correctorWeight_exp_history_row_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (∑ j : Fin n, correctorWeight α dt j.val n *
      Real.exp (-rate * ((n : ℝ) * dt - (j.val : ℝ) * dt))) ≤
        Real.exp (rate * dt) * rate ^ (-α) := by
  have h := correctorWeight_exp_row_le hα hdt hrate hn
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last] at h
  have hend := mul_nonneg (correctorWeight_nonneg hα hdt (Nat.le_refl n))
    (Real.exp_pos (-rate * ((n : ℝ) * dt - (n : ℝ) * dt))).le
  linarith

private theorem exp_mesh_growth (rate dt : ℝ) (n j : ℕ) :
    Real.exp (rate * ((j : ℝ) * dt)) = Real.exp (rate * ((n : ℝ) * dt)) *
      Real.exp (-rate * ((n : ℝ) * dt - (j : ℝ) * dt)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Unnormalized exponential weights, in the form used by continuation
estimates for the predictor history row. -/
theorem predictorWeight_exp_growth_row_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) (n : ℕ) :
    (∑ j : Fin n, predictorWeight α dt j.val n * Real.exp (rate * ((j.val : ℝ) * dt))) ≤
      Real.exp (rate * ((n : ℝ) * dt)) * rate ^ (-α) := by
  calc
    _ = Real.exp (rate * ((n : ℝ) * dt)) *
        ∑ j : Fin n, predictorWeight α dt j.val n *
          Real.exp (-rate * ((n : ℝ) * dt - (j.val : ℝ) * dt)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [exp_mesh_growth rate dt n j.val]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (predictorWeight_exp_row_le hα hdt hrate n)
      (Real.exp_pos _).le

/-- Unnormalized exponential weights for the complete corrector row. -/
theorem correctorWeight_exp_growth_row_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (∑ j : Fin (n + 1), correctorWeight α dt j.val n * Real.exp (rate * ((j.val : ℝ) * dt))) ≤
      Real.exp (rate * ((n : ℝ) * dt)) * (Real.exp (rate * dt) * rate ^ (-α)) := by
  calc
    _ = Real.exp (rate * ((n : ℝ) * dt)) *
        ∑ j : Fin (n + 1), correctorWeight α dt j.val n *
          Real.exp (-rate * ((n : ℝ) * dt - (j.val : ℝ) * dt)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [exp_mesh_growth rate dt n j.val]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (correctorWeight_exp_row_le hα hdt hrate hn)
      (Real.exp_pos _).le

theorem correctorWeight_exp_growth_history_row_le {α dt rate : ℝ}
    (hα : 0 < α) (hdt : 0 < dt) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (∑ j : Fin n, correctorWeight α dt j.val n * Real.exp (rate * ((j.val : ℝ) * dt))) ≤
      Real.exp (rate * ((n : ℝ) * dt)) * (Real.exp (rate * dt) * rate ^ (-α)) := by
  calc
    _ = Real.exp (rate * ((n : ℝ) * dt)) *
        ∑ j : Fin n, correctorWeight α dt j.val n *
          Real.exp (-rate * ((n : ℝ) * dt - (j.val : ℝ) * dt)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [exp_mesh_growth rate dt n j.val]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (correctorWeight_exp_history_row_le hα hdt hrate hn)
      (Real.exp_pos _).le

end RoughHeston

#print axioms RoughHeston.predictorWeight_exp_row_le
#print axioms RoughHeston.correctorWeight_exp_row_le
#print axioms RoughHeston.correctorWeight_exp_growth_history_row_le
