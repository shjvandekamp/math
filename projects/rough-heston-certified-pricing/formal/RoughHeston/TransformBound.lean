module

public import RoughHeston.FractionalSemigroup
public import RoughHeston.Volterra
public import RoughHeston.TransformError
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transform bounds from an actual real-part barrier

The Volterra equation and fractional semigroup law rewrite the force
integral in the exact Riccati exponent as a complementary fractional
integral of the solution. Positivity of the real kernel then turns a
real-part barrier into an exponential-transform bound. Neither existence
of such a solution nor the barrier nor a stochastic transform identity is
asserted by these deterministic results.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

theorem fractionalIntegral_congr_on {α T : ℝ} (hT : 0 ≤ T) {f g : ℝ → ℂ}
    (hfg : ∀ r ∈ Icc 0 T, f r = g r) :
    fractionalIntegral α f T = fractionalIntegral α g T := by
  unfold fractionalIntegral fractionalIntegralRaw
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hT] at hr
  dsimp only
  rw [hfg r hr]

/-- The real part of an ordinary integral inherits a one-sided real-part
bound. A norm bound on the complex integrand is not required. -/
theorem re_intervalIntegral_le {T B : ℝ} (hT : 0 ≤ T) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 T)) (hbound : ∀ r ∈ Icc 0 T, (f r).re ≤ B) :
    (∫ r in 0..T, f r).re ≤ B * T := by
  have hf' : ContinuousOn f (uIcc 0 T) := by simpa only [uIcc_of_le hT] using hf
  have hre : (∫ r in 0..T, f r).re = ∫ r in 0..T, (f r).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hf'.intervalIntegrable).symm
  rw [hre]
  calc
    _ ≤ ∫ _r in 0..T, B := intervalIntegral.integral_mono_on hT
      (Complex.continuous_re.comp_continuousOn hf').intervalIntegrable
      intervalIntegrable_const hbound
    _ = B * T := by simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- Positivity of the fractional kernel preserves one-sided real-part
bounds, with its exact Gamma-normalized mass. -/
theorem re_fractionalIntegral_le {α T B : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 T))
    (hbound : ∀ r ∈ Icc 0 T, (f r).re ≤ B) :
    (fractionalIntegral α f T).re ≤ B * T ^ α / Real.Gamma (α + 1) := by
  have hfi := intervalIntegrable_fractionalKernel_smul hα hT T f hf
  have hk := intervalIntegrable_fractionalKernel hα T 0 T
  have hfr : ContinuousOn (fun r => (f r).re) (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn hf
  have hkir : IntervalIntegrable
      (fun r => fractionalKernel α T r * (f r).re) volume 0 T :=
    hk.mul_continuousOn (by simpa only [uIcc_of_le hT] using hfr)
  have hre : (∫ r in 0..T, fractionalKernel α T r • f r).re =
      ∫ r in 0..T, fractionalKernel α T r * (f r).re := by
    have h := (Complex.reCLM.intervalIntegral_comp_comm hfi).symm
    simpa only [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul] using h
  have hraw : (∫ r in 0..T, fractionalKernel α T r • f r).re ≤ B * T ^ α / α := by
    rw [hre]
    calc
      _ ≤ ∫ r in 0..T, B * fractionalKernel α T r := by
        apply intervalIntegral.integral_mono_on hT hkir (hk.const_mul B)
        intro r hr
        simpa only [mul_comm B] using
          mul_le_mul_of_nonneg_left (hbound r hr) (fractionalKernel_nonneg hr.2)
      _ = B * T ^ α / α := by
        rw [intervalIntegral.integral_const_mul, integral_fractionalKernel hα]
        simp only [sub_zero, sub_self, Real.zero_rpow hα.ne', sub_zero]
        ring
  unfold fractionalIntegral fractionalIntegralRaw
  rw [Complex.smul_re, smul_eq_mul]
  calc
    _ ≤ (Real.Gamma α)⁻¹ * (B * T ^ α / α) :=
      mul_le_mul_of_nonneg_left hraw (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
    _ = B * T ^ α / Real.Gamma (α + 1) := by
      rw [Real.Gamma_add_one hα.ne']
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The actual Volterra equation identifies the time integral of its force
with the complementary fractional integral of the solution. -/
theorem IsRiccatiSolution.integral_force_eq_complementary
    {α R gamma rho nu u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) :
    (∫ r in 0..T, riccati R gamma rho nu u (h r)) = fractionalIntegral (1 - α) h T := by
  calc
    _ = fractionalIntegral (1 - α)
        (fractionalIntegral α (fun r => riccati R gamma rho nu u (h r))) T :=
      (fractionalIntegral_complementary hα hα1 hT
        (fun r => riccati R gamma rho nu u (h r)) hh.force_continuous).symm
    _ = _ := fractionalIntegral_congr_on hT (fun r hr => (hh.2 r hr).symm)

/-- Exact Riccati exponent in terms of the solution itself. This identity
comes from the integral equation, not from a stochastic transform formula. -/
theorem IsRiccatiSolution.exactExponent_eq_complementary
    {α R gamma rho nu u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (theta V0 : ℝ) :
    exactRiccatiExponent R gamma rho nu theta V0 u T h =
      (theta * gamma) • (∫ r in 0..T, h r) + V0 • fractionalIntegral (1 - α) h T := by
  have hhi : IntervalIntegrable h volume 0 T :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hh.1)
  have hFi : IntervalIntegrable (fun r => riccati R gamma rho nu u (h r)) volume 0 T :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hh.force_continuous)
  unfold exactRiccatiExponent riccatiExponentIntegrand
  rw [intervalIntegral.integral_add (hhi.const_mul _) (hFi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hh.integral_force_eq_complementary hα hα1 hT]
  simp only [Complex.real_smul]

/-- A real-part barrier for the actual solution bounds the real part of its
exact exponent, without an assumed norm bound on the solution. -/
theorem IsRiccatiSolution.exponent_re_le_of_re_le
    {α R gamma rho nu theta V0 u T B : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (htheta : 0 ≤ theta * gamma) (hV0 : 0 ≤ V0)
    (hbound : ∀ r ∈ Icc 0 T, (h r).re ≤ B) :
    (exactRiccatiExponent R gamma rho nu theta V0 u T h).re ≤
      B * (theta * gamma * T + V0 * T ^ (1 - α) / Real.Gamma (2 - α)) := by
  rw [hh.exactExponent_eq_complementary hα hα1 hT theta V0]
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hord := re_intervalIntegral_le hT h hh.1 hbound
  have hfrac := re_fractionalIntegral_le (sub_pos.mpr hα1) hT h hh.1 hbound
  rw [show 1 - α + 1 = 2 - α by ring] at hfrac
  calc
    _ ≤ (theta * gamma) * (B * T) + V0 * (B * T ^ (1 - α) / Real.Gamma (2 - α)) :=
      add_le_add (mul_le_mul_of_nonneg_left hord htheta)
        (mul_le_mul_of_nonneg_left hfrac hV0)
    _ = _ := by ring

/-- The exponential transform of the exact Riccati exponent is bounded by
the exponential of the derived real-part estimate. -/
theorem IsRiccatiSolution.norm_exp_exponent_le_of_re_le
    {α R gamma rho nu theta V0 u T B : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (htheta : 0 ≤ theta * gamma) (hV0 : 0 ≤ V0)
    (hbound : ∀ r ∈ Icc 0 T, (h r).re ≤ B) :
    ‖Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T h)‖ ≤
      Real.exp (B * (theta * gamma * T + V0 * T ^ (1 - α) / Real.Gamma (2 - α))) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (hh.exponent_re_le_of_re_le hα hα1 hT htheta hV0 hbound)

/-- An additional deterministic drift with bounded real part is included
without imposing any condition on its imaginary part. -/
theorem IsRiccatiSolution.norm_exp_drift_add_exponent_le_of_re_le
    {α R gamma rho nu theta V0 u T B C : ℝ} {h : ℝ → ℂ} {drift : ℂ}
    (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (htheta : 0 ≤ theta * gamma) (hV0 : 0 ≤ V0)
    (hbound : ∀ r ∈ Icc 0 T, (h r).re ≤ B) (hdrift : drift.re ≤ C) :
    ‖Complex.exp (drift + exactRiccatiExponent R gamma rho nu theta V0 u T h)‖ ≤
      Real.exp (C + B * (theta * gamma * T + V0 * T ^ (1 - α) / Real.Gamma (2 - α))) := by
  rw [Complex.norm_exp, Complex.add_re]
  exact Real.exp_le_exp.mpr
    (add_le_add hdrift (hh.exponent_re_le_of_re_le hα hα1 hT htheta hV0 hbound))

end RoughHeston

#print axioms RoughHeston.IsRiccatiSolution.integral_force_eq_complementary
#print axioms RoughHeston.IsRiccatiSolution.exactExponent_eq_complementary
#print axioms RoughHeston.IsRiccatiSolution.norm_exp_exponent_le_of_re_le
