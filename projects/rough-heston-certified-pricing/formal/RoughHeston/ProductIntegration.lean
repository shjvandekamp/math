module

public import RoughHeston.WeightProperties
public import RoughHeston.FractionalIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fractional Adams weights as actual product integration

The predictor coefficients are the exact integrals of the fractional kernel
over the uniform mesh cells. This identifies the numerical weighted sum with
product integration and gives a consistency estimate for Hölder inputs.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Finset

namespace RoughHeston

/-- A concrete predictor coefficient is the normalized mass of its mesh cell. -/
theorem predictorWeight_eq_kernel_cell {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) :
    predictorWeight α dt j n = (Real.Gamma α)⁻¹ *
      ∫ r in (j : ℝ) * dt..(j + 1 : ℕ) * dt, fractionalKernel α ((n : ℝ) * dt) r := by
  have hleft : (n : ℝ) * dt - (j : ℝ) * dt = ((n - j : ℕ) : ℝ) * dt := by
    rw [Nat.cast_sub hj.le]
    ring
  have hright : (n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt =
      ((n - j - 1 : ℕ) : ℝ) * dt := by
    rw [Nat.cast_sub (show 1 ≤ n - j by omega), Nat.cast_sub hj.le]
    push_cast
    ring
  rw [integral_fractionalKernel hα, hleft, hright,
    Real.mul_rpow (Nat.cast_nonneg _) hdt.le,
    Real.mul_rpow (Nat.cast_nonneg _) hdt.le]
  unfold predictorWeight
  rw [Real.Gamma_add_one hα.ne']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem mesh_cell_bounds {dt : ℝ} (hdt : 0 ≤ dt) {j n : ℕ} (hj : j < n) :
    0 ≤ (j : ℝ) * dt ∧
      (j : ℝ) * dt ≤ ((j + 1 : ℕ) : ℝ) * dt ∧
      ((j + 1 : ℕ) : ℝ) * dt ≤ (n : ℝ) * dt := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hdt, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hdt
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hdt

/-- Local defect on one cell of the concrete predictor. The Hölder condition
is imposed on the original continuous integrand, not on the numerical error. -/
theorem predictor_cell_defect_le {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) {j n : ℕ} (hj : j < n) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((n : ℝ) * dt)))
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α) :
    ‖(Real.Gamma α)⁻¹ •
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r • (f r - f ((j : ℝ) * dt))‖ ≤
      (H * dt ^ α) * predictorWeight α dt j n := by
  obtain ⟨hleft, hcell, hright⟩ := mesh_cell_bounds hdt.le hj
  have hfc : ContinuousOn f (Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)) :=
    hf.mono (Icc_subset_Icc hleft hright)
  have hbound : ∀ r ∈ Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt),
      ‖f r - f ((j : ℝ) * dt)‖ ≤ H * dt ^ α := by
    intro r hr
    apply (hholder _ _ hleft hr.1 (hr.2.trans hright)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow (sub_nonneg.mpr hr.1) _ hα.le
    have hupper := hr.2
    push_cast at hupper
    nlinarith
  have hraw := norm_integral_fractionalKernel_smul_le hα hcell hright
    (fun r => f r - f ((j : ℝ) * dt)) (hfc.sub continuousOn_const) hbound
  have hg : 0 ≤ (Real.Gamma α)⁻¹ := (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hg]
  apply (mul_le_mul_of_nonneg_left hraw hg).trans_eq
  rw [predictorWeight_eq_kernel_cell hα hdt hj, integral_fractionalKernel hα]
  ring

/-- The concrete predictor is consistent with the actual fractional integral
with the explicit `H * t_n^α / Γ(α+1) * dt^α` error constant. -/
theorem predictor_consistency {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) (n : ℕ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((n : ℝ) * dt)))
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α) :
    ‖fractionalIntegral α f ((n : ℝ) * dt) -
      ∑ j ∈ range n, predictorWeight α dt j n • f ((j : ℝ) * dt)‖ ≤
      H * ((n : ℝ) * dt) ^ α / Real.Gamma (α + 1) * dt ^ α := by
  have hcell : ∀ j < n, IntervalIntegrable
      (fun r => fractionalKernel α ((n : ℝ) * dt) r • f r) volume
      ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt) := by
    intro j hj
    obtain ⟨hleft, hmid, hright⟩ := mesh_cell_bounds hdt.le hj
    exact intervalIntegrable_fractionalKernel_smul hα hmid _ f
      (hf.mono (Icc_subset_Icc hleft hright))
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ) * dt) hcell
  simp only [Nat.cast_zero, zero_mul] at hsplit
  have herror : fractionalIntegral α f ((n : ℝ) * dt) -
        ∑ j ∈ range n, predictorWeight α dt j n • f ((j : ℝ) * dt) =
      ∑ j ∈ range n, (Real.Gamma α)⁻¹ •
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r • (f r - f ((j : ℝ) * dt)) := by
    unfold fractionalIntegral fractionalIntegralRaw
    rw [← hsplit, smul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    have hconst := intervalIntegrable_fractionalKernel_smul hα
      (mesh_cell_bounds hdt.le (mem_range.mp hj)).2.1 ((n : ℝ) * dt)
      (fun _ => f ((j : ℝ) * dt)) continuousOn_const
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (hcell j (mem_range.mp hj)) hconst,
      smul_sub, intervalIntegral.integral_smul_const, smul_smul,
      ← predictorWeight_eq_kernel_cell hα hdt (mem_range.mp hj)]
  rw [herror]
  calc
    ‖∑ j ∈ range n, (Real.Gamma α)⁻¹ •
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r • (f r - f ((j : ℝ) * dt))‖ ≤
        ∑ j ∈ range n, ‖(Real.Gamma α)⁻¹ •
          ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
            fractionalKernel α ((n : ℝ) * dt) r • (f r - f ((j : ℝ) * dt))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ range n, (H * dt ^ α) * predictorWeight α dt j n := by
      exact sum_le_sum (fun j hj => predictor_cell_defect_le hα hdt hH
        (mem_range.mp hj) f hf hholder)
    _ = H * ((n : ℝ) * dt) ^ α / Real.Gamma (α + 1) * dt ^ α := by
      rw [← mul_sum, predictorWeight_row_sum hα,
        Real.mul_rpow (Nat.cast_nonneg _) hdt.le]
      ring

/-- Left and right affine basis functions on a uniform mesh cell. -/
def cellLeftHat (dt : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  (((j + 1 : ℕ) : ℝ) * dt - r) / dt

def cellRightHat (dt : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  (r - (j : ℝ) * dt) / dt

def correctorLeftCellWeight (α dt : ℝ) (j n : ℕ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
    fractionalKernel α ((n : ℝ) * dt) r * cellLeftHat dt j r

def correctorRightCellWeight (α dt : ℝ) (j n : ℕ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
    fractionalKernel α ((n : ℝ) * dt) r * cellRightHat dt j r

theorem cellLeftHat_nonneg {dt r : ℝ} (hdt : 0 < dt) (j : ℕ)
    (hr : r ≤ ((j + 1 : ℕ) : ℝ) * dt) : 0 ≤ cellLeftHat dt j r :=
  div_nonneg (sub_nonneg.mpr hr) hdt.le

theorem cellRightHat_nonneg {dt r : ℝ} (hdt : 0 < dt) (j : ℕ)
    (hr : (j : ℝ) * dt ≤ r) : 0 ≤ cellRightHat dt j r :=
  div_nonneg (sub_nonneg.mpr hr) hdt.le

theorem cellHat_sum {dt : ℝ} (hdt : dt ≠ 0) (j : ℕ) (r : ℝ) :
    cellLeftHat dt j r + cellRightHat dt j r = 1 := by
  unfold cellLeftHat cellRightHat
  push_cast
  field_simp
  ring

private theorem kernel_mul_time_sub {α t r : ℝ} (hα : 0 < α) (hr : r ≤ t) :
    fractionalKernel α t r * (t - r) = fractionalKernel (α + 1) t r := by
  unfold fractionalKernel
  have h := Real.rpow_add_one' (sub_nonneg.mpr hr)
    (show α - 1 + 1 ≠ 0 by linarith)
  simpa only [sub_add_cancel, add_sub_cancel_right] using h.symm

private theorem integral_kernel_leftHat {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) :
    (∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
      fractionalKernel α ((n : ℝ) * dt) r * cellLeftHat dt j r) =
    (((((n : ℝ) * dt - (j : ℝ) * dt) ^ (α + 1) -
        ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt) ^ (α + 1)) / (α + 1)) -
      ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt) *
        ((((n : ℝ) * dt - (j : ℝ) * dt) ^ α -
          ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt) ^ α) / α)) / dt := by
  obtain ⟨_, hcell, hright⟩ := mesh_cell_bounds hdt.le hj
  have hk := intervalIntegrable_fractionalKernel hα ((n : ℝ) * dt)
    ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)
  have hk1 := intervalIntegrable_fractionalKernel (show 0 < α + 1 by linarith)
    ((n : ℝ) * dt) ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)
  calc
    _ = ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
      (fractionalKernel (α + 1) ((n : ℝ) * dt) r -
        ((n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt) *
          fractionalKernel α ((n : ℝ) * dt) r) / dt := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hcell] at hr
      dsimp only
      rw [← kernel_mul_time_sub hα (hr.2.trans hright)]
      unfold cellLeftHat
      ring
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub hk1 (hk.const_mul _),
        intervalIntegral.integral_const_mul,
        integral_fractionalKernel (show 0 < α + 1 by linarith),
        integral_fractionalKernel hα]

/-- Exact affine-cell formula for the left corrector hat. -/
theorem correctorLeftCellWeight_formula {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) :
    correctorLeftCellWeight α dt j n = dt ^ α / Real.Gamma (α + 2) *
      (((n - j - 1 : ℕ) : ℝ) ^ (α + 1) -
        (((n - j - 1 : ℕ) : ℝ) - α) * ((n - j : ℕ) : ℝ) ^ α) := by
  have hleft : (n : ℝ) * dt - (j : ℝ) * dt = ((n - j : ℕ) : ℝ) * dt := by
    rw [Nat.cast_sub hj.le]
    ring
  have hright : (n : ℝ) * dt - ((j + 1 : ℕ) : ℝ) * dt =
      ((n - j - 1 : ℕ) : ℝ) * dt := by
    rw [Nat.cast_sub (show 1 ≤ n - j by omega), Nat.cast_sub hj.le]
    push_cast
    ring
  have hgap : ((n - j : ℕ) : ℝ) = ((n - j - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (show 1 ≤ n - j by omega)]
    push_cast
    ring
  have hGamma : Real.Gamma (α + 2) = (α + 1) * (α * Real.Gamma α) := by
    rw [show α + 2 = (α + 1) + 1 by ring,
      Real.Gamma_add_one (show α + 1 ≠ 0 by linarith), Real.Gamma_add_one hα.ne']
  unfold correctorLeftCellWeight
  rw [integral_kernel_leftHat hα hdt hj, hleft, hright,
    Real.mul_rpow (Nat.cast_nonneg _) hdt.le,
    Real.mul_rpow (Nat.cast_nonneg _) hdt.le,
    Real.mul_rpow (Nat.cast_nonneg _) hdt.le,
    Real.mul_rpow (Nat.cast_nonneg _) hdt.le,
    Real.rpow_add_one hdt.ne',
    Real.rpow_add_one' (Nat.cast_nonneg (n - j)) (show α + 1 ≠ 0 by linarith),
    Real.rpow_add_one' (Nat.cast_nonneg (n - j - 1)) (show α + 1 ≠ 0 by linarith),
    hGamma]
  field_simp
  rw [hgap]
  ring

theorem correctorCellWeight_sum {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) :
    correctorLeftCellWeight α dt j n + correctorRightCellWeight α dt j n =
      predictorWeight α dt j n := by
  have hk := intervalIntegrable_fractionalKernel hα ((n : ℝ) * dt)
    ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)
  have hl : Continuous (cellLeftHat dt j) := by
    unfold cellLeftHat
    fun_prop
  have hr : Continuous (cellRightHat dt j) := by
    unfold cellRightHat
    fun_prop
  unfold correctorLeftCellWeight correctorRightCellWeight
  rw [← mul_add, ← intervalIntegral.integral_add
    (hk.mul_continuousOn hl.continuousOn) (hk.mul_continuousOn hr.continuousOn)]
  simp_rw [← mul_add, cellHat_sum hdt.ne', mul_one]
  exact (predictorWeight_eq_kernel_cell hα hdt hj).symm

/-- Exact affine-cell formula for the right corrector hat. -/
theorem correctorRightCellWeight_formula {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) :
    correctorRightCellWeight α dt j n = dt ^ α / Real.Gamma (α + 2) *
      (((n - j : ℕ) : ℝ) ^ (α + 1) -
        (((n - j : ℕ) : ℝ) + α) * ((n - j - 1 : ℕ) : ℝ) ^ α) := by
  have hsum := correctorCellWeight_sum hα hdt hj
  rw [correctorLeftCellWeight_formula hα hdt hj, predictorWeight] at hsum
  have hgap : ((n - j : ℕ) : ℝ) = ((n - j - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (show 1 ≤ n - j by omega)]
    push_cast
    ring
  have hGamma : Real.Gamma (α + 2) = (α + 1) * Real.Gamma (α + 1) := by
    rw [show α + 2 = (α + 1) + 1 by ring]
    exact Real.Gamma_add_one (by linarith)
  apply eq_sub_of_add_eq' at hsum
  rw [hsum, hGamma,
    Real.rpow_add_one' (Nat.cast_nonneg (n - j)) (show α + 1 ≠ 0 by linarith),
    Real.rpow_add_one' (Nat.cast_nonneg (n - j - 1)) (show α + 1 ≠ 0 by linarith)]
  field_simp
  rw [hgap]
  ring


/-- The first corrector coefficient is the left hat on the first cell. -/
theorem correctorWeight_zero_eq_left {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {n : ℕ} (hn : 0 < n) :
    correctorWeight α dt 0 n = correctorLeftCellWeight α dt 0 n := by
  rw [correctorLeftCellWeight_formula hα hdt hn]
  simp [correctorWeight, (Nat.ne_of_gt hn).symm]

/-- The endpoint corrector coefficient is the right hat on the last cell. -/
theorem correctorWeight_last_eq_right {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (n : ℕ) :
    correctorWeight α dt (n + 1) (n + 1) =
      correctorRightCellWeight α dt n (n + 1) := by
  rw [correctorRightCellWeight_formula hα hdt (Nat.lt_succ_self n)]
  simp [correctorWeight, Real.zero_rpow hα.ne']

/-- At an interior node, the two neighboring cell hats add to exactly the
source's corrector coefficient. -/
theorem correctorWeight_interior_eq_cells {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) :
    correctorWeight α dt (j + 1) (n + 1) =
      correctorLeftCellWeight α dt (j + 1) (n + 1) +
        correctorRightCellWeight α dt j (n + 1) := by
  rw [correctorLeftCellWeight_formula hα hdt (by omega),
    correctorRightCellWeight_formula hα hdt (by omega)]
  have hsub : n + 1 - (j + 1) = n - j := by omega
  have hsub1 : n + 1 - j = n - j + 1 := by omega
  have hsub2 : n - j + 1 - 1 = n - j := by omega
  have hne : j + 1 ≠ n + 1 := by omega
  simp only [correctorWeight, hne, Nat.add_one_ne_zero, ite_false, hsub, hsub1, hsub2]
  rw [Real.rpow_add_one' (Nat.cast_nonneg (n - j)) (show α + 1 ≠ 0 by linarith)]
  rw [Nat.cast_sub (show 1 ≤ n - j by omega)]
  push_cast
  ring

/-- Cellwise linear product integration assembles into the exact original
corrector row. The identity applies to both real and complex nodal data. -/
theorem correctorWeights_assemble {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt) {n : ℕ} (hn : 0 < n) (v : ℕ → E) :
    (∑ j ∈ range n, (correctorLeftCellWeight α dt j n • v j +
      correctorRightCellWeight α dt j n • v (j + 1))) =
      ∑ j ∈ range (n + 1), correctorWeight α dt j n • v j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [sum_add_distrib,
    sum_range_succ' (fun j => correctorLeftCellWeight α dt j (m + 1) • v j),
    sum_range_succ (fun j => correctorRightCellWeight α dt j (m + 1) • v (j + 1))]
  calc
    _ = (∑ j ∈ range m, (correctorLeftCellWeight α dt (j + 1) (m + 1) • v (j + 1) +
        correctorRightCellWeight α dt j (m + 1) • v (j + 1))) +
        correctorLeftCellWeight α dt 0 (m + 1) • v 0 +
        correctorRightCellWeight α dt m (m + 1) • v (m + 1) := by
      rw [sum_add_distrib]
      ac_rfl
    _ = (∑ j ∈ range m, correctorWeight α dt (j + 1) (m + 1) • v (j + 1)) +
        correctorWeight α dt 0 (m + 1) • v 0 +
        correctorWeight α dt (m + 1) (m + 1) • v (m + 1) := by
      rw [correctorWeight_zero_eq_left hα hdt (Nat.succ_pos m),
        correctorWeight_last_eq_right hα hdt]
      congr 2
      apply sum_congr rfl
      intro j hj
      rw [← add_smul, ← correctorWeight_interior_eq_cells hα hdt (mem_range.mp hj)]
    _ = _ := by
      rw [sum_range_succ, sum_range_succ']

/-- The continuous affine interpolant used on a corrector cell. -/
def cellLinearInterpolant (dt : ℝ) (j : ℕ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  cellLeftHat dt j r • f ((j : ℝ) * dt) +
    cellRightHat dt j r • f (((j + 1 : ℕ) : ℝ) * dt)

theorem continuous_cellLinearInterpolant (dt : ℝ) (j : ℕ) (f : ℝ → ℂ) :
    Continuous (cellLinearInterpolant dt j f) := by
  unfold cellLinearInterpolant cellLeftHat cellRightHat
  fun_prop

/-- Each corrector cell is the actual kernel integral of its affine interpolant. -/
theorem corrector_cell_integral {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) (f : ℝ → ℂ) :
    (Real.Gamma α)⁻¹ •
      (∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
        fractionalKernel α ((n : ℝ) * dt) r • cellLinearInterpolant dt j f r) =
      correctorLeftCellWeight α dt j n • f ((j : ℝ) * dt) +
        correctorRightCellWeight α dt j n • f (((j + 1 : ℕ) : ℝ) * dt) := by
  have hl := intervalIntegrable_fractionalKernel_smul hα
    (mesh_cell_bounds hdt.le hj).2.1 ((n : ℝ) * dt)
    (fun r => cellLeftHat dt j r • f ((j : ℝ) * dt)) (by
      unfold cellLeftHat
      fun_prop)
  have hr := intervalIntegrable_fractionalKernel_smul hα
    (mesh_cell_bounds hdt.le hj).2.1 ((n : ℝ) * dt)
    (fun r => cellRightHat dt j r • f (((j + 1 : ℕ) : ℝ) * dt)) (by
      unfold cellRightHat
      fun_prop)
  unfold cellLinearInterpolant
  simp_rw [smul_add]
  rw [intervalIntegral.integral_add hl hr, smul_add]
  simp_rw [smul_smul, intervalIntegral.integral_smul_const, smul_smul]
  rfl

/-- Exact identification of the full corrector sum with product integration. -/
theorem corrector_productIntegration {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {n : ℕ} (hn : 0 < n) (f : ℝ → ℂ) :
    (∑ j ∈ range n, (Real.Gamma α)⁻¹ •
      ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
        fractionalKernel α ((n : ℝ) * dt) r • cellLinearInterpolant dt j f r) =
      ∑ j ∈ range (n + 1), correctorWeight α dt j n • f ((j : ℝ) * dt) := by
  calc
    _ = ∑ j ∈ range n, (correctorLeftCellWeight α dt j n • f ((j : ℝ) * dt) +
        correctorRightCellWeight α dt j n • f (((j + 1 : ℕ) : ℝ) * dt)) := by
      apply sum_congr rfl
      intro j hj
      exact corrector_cell_integral hα hdt (mem_range.mp hj) f
    _ = _ := correctorWeights_assemble hα hdt hn (fun j => f ((j : ℝ) * dt))

/-- An affine interpolant of Hölder data differs from the input by at most
the common endpoint error on every mesh cell. -/
theorem cellLinearInterpolant_error_le {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) {j n : ℕ} (hj : j < n) (f : ℝ → ℂ)
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α)
    {r : ℝ} (hr : r ∈ Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)) :
    ‖f r - cellLinearInterpolant dt j f r‖ ≤ H * dt ^ α := by
  obtain ⟨hleft, _, hright⟩ := mesh_cell_bounds hdt.le hj
  have hlen : ((j + 1 : ℕ) : ℝ) * dt - (j : ℝ) * dt = dt := by
    push_cast
    ring
  have hl : ‖f r - f ((j : ℝ) * dt)‖ ≤ H * dt ^ α := by
    apply (hholder _ _ hleft hr.1 (hr.2.trans hright)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    exact Real.rpow_le_rpow (sub_nonneg.mpr hr.1) (by linarith [hr.2]) hα.le
  have hu : ‖f r - f (((j + 1 : ℕ) : ℝ) * dt)‖ ≤ H * dt ^ α := by
    rw [norm_sub_rev]
    apply (hholder _ _ (hleft.trans hr.1) hr.2 hright).trans
    apply mul_le_mul_of_nonneg_left _ hH
    exact Real.rpow_le_rpow (sub_nonneg.mpr hr.2) (by linarith [hr.1]) hα.le
  have hl0 := cellLeftHat_nonneg hdt j hr.2
  have hr0 := cellRightHat_nonneg hdt j hr.1
  have hdecomp : f r - cellLinearInterpolant dt j f r =
      cellLeftHat dt j r • (f r - f ((j : ℝ) * dt)) +
        cellRightHat dt j r • (f r - f (((j + 1 : ℕ) : ℝ) * dt)) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, cellHat_sum hdt.ne', one_smul]
    rfl
  rw [hdecomp]
  calc
    _ ≤ ‖cellLeftHat dt j r • (f r - f ((j : ℝ) * dt))‖ +
        ‖cellRightHat dt j r • (f r - f (((j + 1 : ℕ) : ℝ) * dt))‖ := norm_add_le _ _
    _ = cellLeftHat dt j r * ‖f r - f ((j : ℝ) * dt)‖ +
        cellRightHat dt j r * ‖f r - f (((j + 1 : ℕ) : ℝ) * dt)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hl0, abs_of_nonneg hr0]
    _ ≤ cellLeftHat dt j r * (H * dt ^ α) + cellRightHat dt j r * (H * dt ^ α) :=
      add_le_add (mul_le_mul_of_nonneg_left hl hl0) (mul_le_mul_of_nonneg_left hu hr0)
    _ = H * dt ^ α := by rw [← add_mul, cellHat_sum hdt.ne', one_mul]

/-- Local consistency of the actual corrector product integral. -/
theorem corrector_cell_defect_le {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) {j n : ℕ} (hj : j < n) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((n : ℝ) * dt)))
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α) :
    ‖(Real.Gamma α)⁻¹ •
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r • (f r - cellLinearInterpolant dt j f r)‖ ≤
      (H * dt ^ α) * predictorWeight α dt j n := by
  obtain ⟨hleft, hcell, hright⟩ := mesh_cell_bounds hdt.le hj
  have hfc : ContinuousOn f (Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt)) :=
    hf.mono (Icc_subset_Icc hleft hright)
  have hbound : ∀ r ∈ Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt),
      ‖f r - cellLinearInterpolant dt j f r‖ ≤ H * dt ^ α :=
    fun _ hr => cellLinearInterpolant_error_le hα hdt hH hj f hholder hr
  have hraw := norm_integral_fractionalKernel_smul_le hα hcell hright
    (fun r => f r - cellLinearInterpolant dt j f r)
    (hfc.sub (continuous_cellLinearInterpolant dt j f).continuousOn) hbound
  have hg : 0 ≤ (Real.Gamma α)⁻¹ := (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hg]
  apply (mul_le_mul_of_nonneg_left hraw hg).trans_eq
  rw [predictorWeight_eq_kernel_cell hα hdt hj, integral_fractionalKernel hα]
  ring

/-- The source's complete corrector row has the same explicit consistency
bound as the predictor, proved by integrating the actual affine interpolant. -/
theorem corrector_consistency {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) {n : ℕ} (hn : 0 < n) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((n : ℝ) * dt)))
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α) :
    ‖fractionalIntegral α f ((n : ℝ) * dt) -
      ∑ j ∈ range (n + 1), correctorWeight α dt j n • f ((j : ℝ) * dt)‖ ≤
      H * ((n : ℝ) * dt) ^ α / Real.Gamma (α + 1) * dt ^ α := by
  have hcell : ∀ j < n, IntervalIntegrable
      (fun r => fractionalKernel α ((n : ℝ) * dt) r • f r) volume
      ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt) := by
    intro j hj
    obtain ⟨hleft, hmid, hright⟩ := mesh_cell_bounds hdt.le hj
    exact intervalIntegrable_fractionalKernel_smul hα hmid _ f
      (hf.mono (Icc_subset_Icc hleft hright))
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ) * dt) hcell
  simp only [Nat.cast_zero, zero_mul] at hsplit
  have herror : fractionalIntegral α f ((n : ℝ) * dt) -
        ∑ j ∈ range (n + 1), correctorWeight α dt j n • f ((j : ℝ) * dt) =
      ∑ j ∈ range n, (Real.Gamma α)⁻¹ •
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r • (f r - cellLinearInterpolant dt j f r) := by
    rw [← corrector_productIntegration hα hdt hn]
    unfold fractionalIntegral fractionalIntegralRaw
    rw [← hsplit, smul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    have hint := intervalIntegrable_fractionalKernel_smul hα
      (mesh_cell_bounds hdt.le (mem_range.mp hj)).2.1 ((n : ℝ) * dt)
      (cellLinearInterpolant dt j f) (continuous_cellLinearInterpolant dt j f).continuousOn
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (hcell j (mem_range.mp hj)) hint, smul_sub]
  rw [herror]
  calc
    ‖∑ j ∈ range n, (Real.Gamma α)⁻¹ •
        ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
          fractionalKernel α ((n : ℝ) * dt) r • (f r - cellLinearInterpolant dt j f r)‖ ≤
        ∑ j ∈ range n, ‖(Real.Gamma α)⁻¹ •
          ∫ r in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt,
            fractionalKernel α ((n : ℝ) * dt) r • (f r - cellLinearInterpolant dt j f r)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ range n, (H * dt ^ α) * predictorWeight α dt j n := by
      exact sum_le_sum (fun j hj => corrector_cell_defect_le hα hdt hH
        (mem_range.mp hj) f hf hholder)
    _ = H * ((n : ℝ) * dt) ^ α / Real.Gamma (α + 1) * dt ^ α := by
      rw [← mul_sum, predictorWeight_row_sum hα,
        Real.mul_rpow (Nat.cast_nonneg _) hdt.le]
      ring

theorem correctorLeftCellWeight_nonneg {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) : 0 ≤ correctorLeftCellWeight α dt j n := by
  obtain ⟨_, hcell, hright⟩ := mesh_cell_bounds hdt.le hj
  apply mul_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  apply intervalIntegral.integral_nonneg hcell
  intro r hr
  exact mul_nonneg (fractionalKernel_nonneg (hr.2.trans hright))
    (cellLeftHat_nonneg hdt j hr.2)

theorem correctorRightCellWeight_nonneg {α dt : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    {j n : ℕ} (hj : j < n) : 0 ≤ correctorRightCellWeight α dt j n := by
  obtain ⟨_, hcell, hright⟩ := mesh_cell_bounds hdt.le hj
  apply mul_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  apply intervalIntegral.integral_nonneg hcell
  intro r hr
  exact mul_nonneg (fractionalKernel_nonneg (hr.2.trans hright))
    (cellRightHat_nonneg hdt j hr.1)

theorem predictor_consistency_fin {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) (n : ℕ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((n : ℝ) * dt)))
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α) :
    ‖fractionalIntegral α f ((n : ℝ) * dt) -
      ∑ j : Fin n, predictorWeight α dt j.val n • f ((j.val : ℝ) * dt)‖ ≤
      H * ((n : ℝ) * dt) ^ α / Real.Gamma (α + 1) * dt ^ α := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => predictorWeight α dt j n • f ((j : ℝ) * dt)) n]
  exact predictor_consistency hα hdt hH n f hf hholder

theorem corrector_consistency_fin {α dt H : ℝ} (hα : 0 < α) (hdt : 0 < dt)
    (hH : 0 ≤ H) {n : ℕ} (hn : 0 < n) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((n : ℝ) * dt)))
    (hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖f r - f s‖ ≤ H * (r - s) ^ α) :
    ‖fractionalIntegral α f ((n : ℝ) * dt) -
      ∑ j : Fin (n + 1), correctorWeight α dt j.val n • f ((j.val : ℝ) * dt)‖ ≤
      H * ((n : ℝ) * dt) ^ α / Real.Gamma (α + 1) * dt ^ α := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => correctorWeight α dt j n • f ((j : ℝ) * dt)) (n + 1)]
  exact corrector_consistency hα hdt hH hn f hf hholder

end RoughHeston

#print axioms RoughHeston.predictorWeight_eq_kernel_cell
#print axioms RoughHeston.predictor_consistency
#print axioms RoughHeston.corrector_productIntegration
#print axioms RoughHeston.corrector_consistency
