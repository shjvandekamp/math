module

public import RoughHeston.Approximation
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Frequency continuity from certified uniform approximation

The bounded exact-solution family is not assumed continuous in frequency.
Its exact exponent is a uniform limit of the actual polynomial Adams
exponents; the same is true of their exponentials. Thus the exact objects
needed in a finite-band Fourier integral are continuous on the band.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology

namespace RoughHeston

theorem continuous_polynomial_eval_real (p : Polynomial ℂ) :
    Continuous (fun u : ℝ => p.eval (u : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add, Pi.add_def] using hp.add hq
  | monomial n c =>
      simpa only [Polynomial.eval_monomial, Pi.mul_def, Pi.pow_def] using
        (continuous_const.mul (Complex.continuous_ofReal.pow n))

theorem continuous_roughExponent_eval
    (alpha dt R gamma rho nu theta V0 : ℝ) (N : ℕ) :
    Continuous (fun u : ℝ =>
      (roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ)) :=
  continuous_polynomial_eval_real _

theorem continuous_roughTransform_eval
    (alpha dt R gamma rho nu theta V0 : ℝ) (N : ℕ) :
    Continuous (fun u : ℝ =>
      Complex.exp ((roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ))) :=
  Complex.continuous_exp.comp (continuous_roughExponent_eval alpha dt R gamma rho nu theta V0 N)

/-- Every positive-order power of the original dyadic step tends to zero. -/
theorem dyadic_step_power_tendsto_zero (alpha T : ℝ) (M0 : ℕ) (ha : 0 < alpha) :
    Tendsto (fun ell : ℕ => (T / ((2 ^ ell * M0 : ℕ) : ℝ)) ^ alpha) atTop (𝓝 0) := by
  have hgeom : Tendsto (fun ell : ℕ => ((2 : ℝ)⁻¹) ^ ell) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hid : (fun ell : ℕ => T / ((2 ^ ell * M0 : ℕ) : ℝ)) =
      fun ell : ℕ => (T / (M0 : ℝ)) * ((2 : ℝ)⁻¹) ^ ell := by
    funext ell
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have hdt : Tendsto (fun ell : ℕ => T / ((2 ^ ell * M0 : ℕ) : ℝ)) atTop (𝓝 0) := by
    rw [hid]
    simpa only [mul_zero] using hgeom.const_mul (T / (M0 : ℝ))
  exact hdt.rpow_const_nhds_zero ha

/-- A uniform norm error bounded by a vanishing real sequence gives actual
uniform convergence. No measurability or continuity of the limit is assumed. -/
theorem tendstoUniformlyOn_of_norm_error {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    {s : Set ℝ} {w : ℕ → ℝ} (hw : Tendsto w atTop (𝓝 0))
    (hb : ∀ ell, ∀ u ∈ s, ‖F ell u - f u‖ ≤ w ell) :
    TendstoUniformlyOn F f atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : ∀ᶠ ell in atTop, w ell < eps := (tendsto_order.mp hw).2 eps heps
  filter_upwards [he] with ell hell
  intro u hu
  simpa only [dist_eq_norm, norm_sub_rev] using (hb ell u hu).trans_lt hell

/-- One validated dyadic family uniformly approximates both exact objects
on the frequency band. The only exact-family hypotheses concern the time
equation and a common state bound. -/
theorem riccati_band_uniform_exponent_and_transform
    (alpha T R gamma rho nu theta V0 U Q0 : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha R gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ∃ M0 : ℕ, 0 < M0 ∧
      TendstoUniformlyOn
        (fun (ell : ℕ) (u : ℝ) => (roughExponent alpha (T / ((2 ^ ell * M0 : ℕ) : ℝ))
          R gamma rho nu theta V0 (2 ^ ell * M0)).eval (u : ℂ))
        (fun u => exactRiccatiExponent R gamma rho nu theta V0 u T (h u)) atTop (Icc 0 U) ∧
      TendstoUniformlyOn
        (fun (ell : ℕ) (u : ℝ) => Complex.exp ((roughExponent alpha (T / ((2 ^ ell * M0 : ℕ) : ℝ))
          R gamma rho nu theta V0 (2 ^ ell * M0)).eval (u : ℂ)))
        (fun u => Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T (h u)))
        atTop (Icc 0 U) := by
  obtain ⟨M0, hM0, herr⟩ := riccati_dyadic_band_transform_error
    alpha T R gamma rho nu theta V0 U Q0 1 h ha ha1 hT hU hQ0 (by norm_num) hsol hbound
  have hpow := dyadic_step_power_tendsto_zero alpha T M0 ha
  refine ⟨M0, hM0, ?_, ?_⟩
  · apply tendstoUniformlyOn_of_norm_error
      (w := fun ell => finiteBandExponentConstant alpha T R gamma rho nu theta V0 U (Q0 + 1) *
        (T / ((2 ^ ell * M0 : ℕ) : ℝ)) ^ alpha)
    · simpa only [mul_zero] using hpow.const_mul
        (finiteBandExponentConstant alpha T R gamma rho nu theta V0 U (Q0 + 1))
    · exact fun ell u hu => (herr ell u hu).1
  · apply tendstoUniformlyOn_of_norm_error
      (w := fun ell => finiteBandTransformConstant alpha T R gamma rho nu theta V0 U (Q0 + 1) *
        (T / ((2 ^ ell * M0 : ℕ) : ℝ)) ^ alpha)
    · simpa only [mul_zero] using hpow.const_mul
        (finiteBandTransformConstant alpha T R gamma rho nu theta V0 U (Q0 + 1))
    · exact fun ell u hu => (herr ell u hu).2

/-- Frequency continuity of the exact exponent is derived from the
validated approximants, without any frequency-regularity assumption on `h`. -/
theorem continuousOn_exactRiccatiExponent_band
    (alpha T R gamma rho nu theta V0 U Q0 : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha R gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ContinuousOn (fun u => exactRiccatiExponent R gamma rho nu theta V0 u T (h u)) (Icc 0 U) := by
  obtain ⟨M0, _, he, _⟩ := riccati_band_uniform_exponent_and_transform
    alpha T R gamma rho nu theta V0 U Q0 h ha ha1 hT hU hQ0 hsol hbound
  apply he.continuousOn
  exact (Filter.Eventually.of_forall (fun ell =>
    (continuous_roughExponent_eval alpha (T / ((2 ^ ell * M0 : ℕ) : ℝ))
      R gamma rho nu theta V0 (2 ^ ell * M0)).continuousOn)).frequently

/-- The exact deterministic transform is therefore continuous and hence
integrable against every continuous weight on the compact frequency band. -/
theorem continuousOn_exactRiccatiTransform_band
    (alpha T R gamma rho nu theta V0 U Q0 : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha R gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ContinuousOn
      (fun u => Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T (h u))) (Icc 0 U) :=
  Complex.continuous_exp.comp_continuousOn
    (continuousOn_exactRiccatiExponent_band alpha T R gamma rho nu theta V0 U Q0 h
      ha ha1 hT hU hQ0 hsol hbound)

end RoughHeston

#print axioms RoughHeston.riccati_band_uniform_exponent_and_transform
#print axioms RoughHeston.continuousOn_exactRiccatiExponent_band
#print axioms RoughHeston.continuousOn_exactRiccatiTransform_band
