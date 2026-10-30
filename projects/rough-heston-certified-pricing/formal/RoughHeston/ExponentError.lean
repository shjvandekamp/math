module

public import RoughHeston.Exponent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual composite trapezoidal error and nodal perturbation

The weights are precisely `trapezoidWeight` from the transform exponent.
The quadrature estimate follows by splitting the actual interval integral
into mesh cells and bounding each cell's two endpoint defects.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Finset

namespace RoughHeston

theorem trapezoidWeight_nonneg {dt : ℝ} (ht : 0 ≤ dt) (N j : ℕ) :
    0 ≤ trapezoidWeight dt N j := by
  unfold trapezoidWeight
  split_ifs <;> positivity

private theorem trapezoidWeight_eq_endpoint_corrections (dt : ℝ) {N : ℕ}
    (hN : 0 < N) (j : ℕ) :
    trapezoidWeight dt N j =
      dt - (if j = 0 then dt / 2 else 0) - (if j = N then dt / 2 else 0) := by
  by_cases hj0 : j = 0
  · subst j
    simp [trapezoidWeight, (Nat.ne_of_gt hN).symm]
    ring
  · by_cases hjN : j = N
    · subst j
      simp [trapezoidWeight, Nat.ne_of_gt hN]
      ring
    · simp [trapezoidWeight, hj0, hjN]

theorem trapezoidWeight_row_sum (dt : ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ range (N + 1), trapezoidWeight dt N j = (N : ℝ) * dt := by
  simp only [trapezoidWeight_eq_endpoint_corrections dt hN,
    sum_sub_distrib, sum_const, sum_ite_eq', Finset.mem_range,
    Nat.zero_lt_succ, Nat.lt_succ_self, ite_true, nsmul_eq_mul, card_range]
  push_cast
  ring

theorem trapezoidWeight_sum_fin (dt : ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ j : Fin (N + 1), trapezoidWeight dt N j.val = (N : ℝ) * dt := by
  exact (Fin.sum_univ_eq_sum_range (trapezoidWeight dt N) (N + 1)).trans
    (trapezoidWeight_row_sum dt hN)

/-- The implemented endpoint weights equal the sum of the trapezoids on
the mesh cells. This is an algebraic identity, not a quadrature assumption. -/
theorem trapezoid_sum_eq_cells (dt : ℝ) {N : ℕ} (hN : 0 < N) (z : ℕ → ℂ) :
    (∑ j ∈ range (N + 1), (trapezoidWeight dt N j : ℂ) * z j) =
      ∑ j ∈ range N, ((dt / 2 : ℝ) : ℂ) * (z j + z (j + 1)) := by
  have hterm (j : ℕ) : (trapezoidWeight dt N j : ℂ) * z j =
      (dt : ℂ) * z j - (if j = 0 then ((dt / 2 : ℝ) : ℂ) * z 0 else 0) -
        (if j = N then ((dt / 2 : ℝ) : ℂ) * z N else 0) := by
    by_cases hj0 : j = 0
    · subst j
      simp [trapezoidWeight, (Nat.ne_of_gt hN).symm]
      ring
    · by_cases hjN : j = N
      · subst j
        simp [trapezoidWeight, hj0]
        ring
      · simp [trapezoidWeight, hj0, hjN]
  simp only [hterm, sum_sub_distrib, sum_ite_eq', Finset.mem_range,
    Nat.zero_lt_succ, Nat.lt_succ_self, ite_true, ← mul_sum]
  have hleft := sum_range_succ z N
  have hright := sum_range_succ' z N
  rw [sum_add_distrib]
  rw [eq_sub_iff_add_eq.mpr hleft.symm, eq_sub_iff_add_eq.mpr hright.symm]
  push_cast
  ring

/-- Bounded changes in the values at the nodes change the actual weighted
trapezoidal sum by at most the interval length times that bound. -/
theorem trapezoid_nodal_perturbation {dt E : ℝ} (ht : 0 ≤ dt) {N : ℕ}
    (hN : 0 < N) (x y : ℕ → ℂ) (hxy : ∀ j ≤ N, ‖x j - y j‖ ≤ E) :
    ‖(∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) * x j.val) -
      (∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) * y j.val)‖ ≤
        ((N : ℝ) * dt) * E := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    ‖∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) * (x j.val - y j.val)‖ ≤
        ∑ j : Fin (N + 1), ‖(trapezoidWeight dt N j.val : ℂ) * (x j.val - y j.val)‖ :=
      norm_sum_le _ _
    _ = ∑ j : Fin (N + 1), trapezoidWeight dt N j.val * ‖x j.val - y j.val‖ := by
      apply sum_congr rfl
      intro j _
      simp [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (trapezoidWeight_nonneg ht N j.val)]
    _ ≤ ∑ j : Fin (N + 1), trapezoidWeight dt N j.val * E := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hxy j.val (by omega)) (trapezoidWeight_nonneg ht N j.val)
    _ = _ := by rw [← sum_mul, trapezoidWeight_sum_fin dt hN]

private theorem integral_endpoint_defect {a b C : ℝ} (hab : a ≤ b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f volume a b) (z : ℂ)
    (hbound : ∀ t ∈ Icc a b, ‖f t - z‖ ≤ C) :
    ‖(∫ t in a..b, f t) - ((b - a : ℝ) : ℂ) * z‖ ≤ C * (b - a) := by
  have hid : (∫ t in a..b, f t) - ((b - a : ℝ) : ℂ) * z =
      ∫ t in a..b, f t - z := by
    rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
      intervalIntegral.integral_const, Complex.real_smul]
  rw [hid]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun t => f t - z) (C := C) (fun t ht => by
      rw [uIoc_of_le hab] at ht
      exact hbound t ⟨ht.1.le, ht.2⟩)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

private theorem trapezoid_mesh_cell_bounds {dt : ℝ} (ht : 0 ≤ dt) {j N : ℕ} (hj : j < N) :
    0 ≤ (j : ℝ) * dt ∧ (j : ℝ) * dt ≤ ((j + 1 : ℕ) : ℝ) * dt ∧
      ((j + 1 : ℕ) : ℝ) * dt ≤ (N : ℝ) * dt := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) ht, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) ht
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ht

/-- The error on one actual mesh cell follows from the two endpoint
Hölder bounds and the norm inequality for its integral. -/
theorem trapezoid_cell_defect_le {alpha dt H : ℝ} (ha : 0 < alpha)
    (ht : 0 < dt) (hH : 0 ≤ H) {j N : ℕ} (hj : j < N) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((N : ℝ) * dt)))
    (hholder : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ (N : ℝ) * dt →
      ‖f t - f s‖ ≤ H * (t - s) ^ alpha) :
    ‖(∫ t in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt, f t) -
      ((dt / 2 : ℝ) : ℂ) * (f ((j : ℝ) * dt) + f (((j + 1 : ℕ) : ℝ) * dt))‖ ≤
        dt * H * dt ^ alpha := by
  obtain ⟨hleft, hcell, hright⟩ := trapezoid_mesh_cell_bounds ht.le hj
  have hlen : ((j + 1 : ℕ) : ℝ) * dt - (j : ℝ) * dt = dt := by push_cast; ring
  have hfi : IntervalIntegrable f volume ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt) :=
    (hf.mono (Icc_subset_Icc hleft hright)).intervalIntegrable_of_Icc hcell
  have hleftbound : ∀ t ∈ Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt),
      ‖f t - f ((j : ℝ) * dt)‖ ≤ H * dt ^ alpha := by
    intro t hmem
    apply (hholder _ _ hleft hmem.1 (hmem.2.trans hright)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow (sub_nonneg.mpr hmem.1) _ ha.le
    linarith [hmem.2]
  have hrightbound : ∀ t ∈ Icc ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt),
      ‖f t - f (((j + 1 : ℕ) : ℝ) * dt)‖ ≤ H * dt ^ alpha := by
    intro t hmem
    rw [norm_sub_rev]
    apply (hholder _ _ (hleft.trans hmem.1) hmem.2 hright).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow (sub_nonneg.mpr hmem.2) _ ha.le
    linarith [hmem.1]
  have hl := integral_endpoint_defect hcell f hfi (f ((j : ℝ) * dt)) hleftbound
  have hr := integral_endpoint_defect hcell f hfi (f (((j + 1 : ℕ) : ℝ) * dt)) hrightbound
  rw [hlen] at hl hr
  let I : ℂ := ∫ t in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt, f t
  have hid : I - ((dt / 2 : ℝ) : ℂ) * (f ((j : ℝ) * dt) + f (((j + 1 : ℕ) : ℝ) * dt)) =
      (1 / 2 : ℂ) * ((I - (dt : ℂ) * f ((j : ℝ) * dt)) +
        (I - (dt : ℂ) * f (((j + 1 : ℕ) : ℝ) * dt))) := by push_cast; ring
  change ‖I - _‖ ≤ _
  rw [hid, norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
  rw [hhalf]
  calc
    (1 / 2 : ℝ) * ‖(I - (dt : ℂ) * f ((j : ℝ) * dt)) +
        (I - (dt : ℂ) * f (((j + 1 : ℕ) : ℝ) * dt))‖ ≤
      (1 / 2 : ℝ) * (‖I - (dt : ℂ) * f ((j : ℝ) * dt)‖ +
        ‖I - (dt : ℂ) * f (((j + 1 : ℕ) : ℝ) * dt)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ((H * dt ^ alpha) * dt + (H * dt ^ alpha) * dt) :=
      mul_le_mul_of_nonneg_left (add_le_add hl hr) (by norm_num)
    _ = _ := by ring

/-- The actual composite trapezoidal rule has an `alpha`-order bound for
an ordered `alpha`-Hölder integrand on the maturity interval. -/
theorem trapezoid_consistency {alpha dt H : ℝ} (ha : 0 < alpha) (ht : 0 < dt)
    (hH : 0 ≤ H) {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 ((N : ℝ) * dt)))
    (hholder : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ (N : ℝ) * dt →
      ‖f t - f s‖ ≤ H * (t - s) ^ alpha) :
    ‖(∫ t in 0..(N : ℝ) * dt, f t) -
      ∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) * f ((j.val : ℝ) * dt)‖ ≤
        ((N : ℝ) * dt) * H * dt ^ alpha := by
  have hfi : ∀ j < N, IntervalIntegrable f volume ((j : ℝ) * dt) (((j + 1 : ℕ) : ℝ) * dt) := by
    intro j hj
    obtain ⟨hleft, hcell, hright⟩ := trapezoid_mesh_cell_bounds ht.le hj
    exact (hf.mono (Icc_subset_Icc hleft hright)).intervalIntegrable_of_Icc hcell
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ) * dt) hfi
  simp only [Nat.cast_zero, zero_mul] at hsplit
  rw [Fin.sum_univ_eq_sum_range (fun j => (trapezoidWeight dt N j : ℂ) * f ((j : ℝ) * dt)),
    trapezoid_sum_eq_cells dt hN, ← hsplit, ← sum_sub_distrib]
  calc
    ‖∑ j ∈ range N, ((∫ t in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt, f t) -
        ((dt / 2 : ℝ) : ℂ) * (f ((j : ℝ) * dt) + f (((j + 1 : ℕ) : ℝ) * dt)))‖ ≤
      ∑ j ∈ range N, ‖(∫ t in (j : ℝ) * dt..((j + 1 : ℕ) : ℝ) * dt, f t) -
        ((dt / 2 : ℝ) : ℂ) * (f ((j : ℝ) * dt) + f (((j + 1 : ℕ) : ℝ) * dt))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ range N, dt * H * dt ^ alpha :=
      sum_le_sum (fun j hj => trapezoid_cell_defect_le ha ht hH (Finset.mem_range.mp hj) f hf hholder)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

end RoughHeston
