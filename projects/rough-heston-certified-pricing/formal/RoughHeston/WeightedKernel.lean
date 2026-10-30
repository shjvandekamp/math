module

public import RoughHeston.FractionalIntegral

/-!
# Exponentially weighted fractional-kernel mass

The full positive-half-line Laplace integral gives a bound independent of the
maturity. No smallness restriction on the maturity is imposed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

/-- The fractional power kernel with exponential decay, expressed in elapsed
time from the kernel endpoint. -/
def laplaceFractionalKernel (α rate x : ℝ) : ℝ :=
  x ^ (α - 1) * Real.exp (-rate * x)

/-- The exponentially weighted fractional kernel in the integration variable. -/
def weightedFractionalKernel (α rate t r : ℝ) : ℝ :=
  fractionalKernel α t r * Real.exp (-rate * (t - r))

/-- Normalized weighted row mass on the complete history `[0,t]`. -/
def weightedKernelMass (α rate t : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ r in 0..t, weightedFractionalKernel α rate t r

/-- Exact infinite Laplace integral. -/
theorem integral_laplaceFractionalKernel {α rate : ℝ} (hα : 0 < α) (hrate : 0 < rate) :
    (∫ x : ℝ in Ioi 0, laplaceFractionalKernel α rate x) =
      rate ^ (-α) * Real.Gamma α := by
  simpa only [laplaceFractionalKernel, neg_mul, one_div, Real.rpow_neg_eq_inv_rpow]
    using Real.integral_rpow_mul_exp_neg_mul_Ioi hα hrate

/-- The positive infinite Laplace integral is genuinely integrable. This also
follows from its exact positive value, since a nonintegrable Bochner integral
has value zero. -/
theorem integrableOn_laplaceFractionalKernel {α rate : ℝ}
    (hα : 0 < α) (hrate : 0 < rate) :
    IntegrableOn (laplaceFractionalKernel α rate) (Ioi 0) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_laplaceFractionalKernel hα hrate] at hz
  exact (ne_of_gt (mul_pos (Real.rpow_pos_of_pos hrate (-α))
    (Real.Gamma_pos_of_pos hα))) hz

/-- Finite-history integrability includes the singular endpoint. Positivity
of the exponential damping parameter is not needed for this finite interval. -/
theorem intervalIntegrable_weightedFractionalKernel {α : ℝ} (hα : 0 < α)
    (rate t a b : ℝ) :
    IntervalIntegrable (weightedFractionalKernel α rate t) volume a b := by
  unfold weightedFractionalKernel
  apply (intervalIntegrable_fractionalKernel hα t a b).mul_continuousOn
  exact ((continuous_const.mul (continuous_const.sub continuous_id)).rexp).continuousOn

theorem weightedFractionalKernel_nonneg {α rate t r : ℝ} (hr : r ≤ t) :
    0 ≤ weightedFractionalKernel α rate t r :=
  mul_nonneg (fractionalKernel_nonneg hr) (Real.exp_pos _).le

/-- Reflecting the history variable turns the weighted mass into a finite
Laplace integral. -/
theorem weightedKernelMass_eq_laplaceIntegral (α rate t : ℝ) :
    weightedKernelMass α rate t =
      (Real.Gamma α)⁻¹ * ∫ x in 0..t, laplaceFractionalKernel α rate x := by
  unfold weightedKernelMass weightedFractionalKernel fractionalKernel
  change (Real.Gamma α)⁻¹ *
    (∫ r in 0..t, laplaceFractionalKernel α rate (t - r)) =
      (Real.Gamma α)⁻¹ * ∫ x in 0..t, laplaceFractionalKernel α rate x
  rw [intervalIntegral.integral_comp_sub_left (laplaceFractionalKernel α rate) t]
  simp only [sub_self, sub_zero]

theorem weightedKernelMass_nonneg {α rate t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    0 ≤ weightedKernelMass α rate t := by
  apply mul_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  apply intervalIntegral.integral_nonneg ht
  intro r hr
  exact weightedFractionalKernel_nonneg hr.2

/-- The finite-history Laplace mass is bounded by the full positive-half-line
integral, without a restriction on the history length. -/
theorem integral_laplaceFractionalKernel_le {α rate t : ℝ}
    (hα : 0 < α) (hrate : 0 < rate) (ht : 0 ≤ t) :
    (∫ x in 0..t, laplaceFractionalKernel α rate x) ≤
      rate ^ (-α) * Real.Gamma α := by
  rw [intervalIntegral.integral_of_le ht]
  calc
    (∫ x in Ioc 0 t, laplaceFractionalKernel α rate x) ≤
        ∫ x in Ioi 0, laplaceFractionalKernel α rate x := by
      apply setIntegral_mono_set (integrableOn_laplaceFractionalKernel hα hrate)
      · apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro x hx
        exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
      · exact Filter.Eventually.of_forall (fun x hx => hx.1)
    _ = rate ^ (-α) * Real.Gamma α := integral_laplaceFractionalKernel hα hrate

/-- The weighted fractional-history mass is at most `rate^(-α)`, for every
nonnegative maturity. This is the analytic constant for exponentially weighted
Adams row estimates. -/
theorem weightedKernelMass_le {α rate t : ℝ} (hα : 0 < α) (hrate : 0 < rate) (ht : 0 ≤ t) :
    weightedKernelMass α rate t ≤ rate ^ (-α) := by
  rw [weightedKernelMass_eq_laplaceIntegral]
  calc
    (Real.Gamma α)⁻¹ * (∫ x in 0..t, laplaceFractionalKernel α rate x) ≤
        (Real.Gamma α)⁻¹ * (rate ^ (-α) * Real.Gamma α) :=
      mul_le_mul_of_nonneg_left (integral_laplaceFractionalKernel_le hα hrate ht)
        (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
    _ = rate ^ (-α) := by
      rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt (Real.Gamma_pos_of_pos hα)), mul_one]

/-- The same bound with the full integral exposed in the statement. -/
theorem normalized_weighted_fractional_integral_le {α rate t : ℝ}
    (hα : 0 < α) (hrate : 0 < rate) (ht : 0 ≤ t) :
    (Real.Gamma α)⁻¹ *
      (∫ r in 0..t, (t - r) ^ (α - 1) * Real.exp (-rate * (t - r))) ≤ rate ^ (-α) :=
  weightedKernelMass_le hα hrate ht

end RoughHeston

#print axioms RoughHeston.integrableOn_laplaceFractionalKernel
#print axioms RoughHeston.intervalIntegrable_weightedFractionalKernel
#print axioms RoughHeston.normalized_weighted_fractional_integral_le
