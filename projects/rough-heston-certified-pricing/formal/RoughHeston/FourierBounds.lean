module

public import RoughHeston.Payoff
public import RoughHeston.BandContinuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic call Fourier error estimates

These estimates use the genuine strike-one call factor on `R = -2`.
They bound Fourier integrals, without identifying them with expectations
under a stochastic model.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory

namespace RoughHeston

theorem callDenominator_factor (u : ℝ) :
    callDenominator u = ((u : ℂ) - 2 * Complex.I) * ((u : ℂ) - Complex.I) := by
  unfold callDenominator
  ring

theorem norm_callDenominator_ge_two (u : ℝ) : 2 ≤ ‖callDenominator u‖ := by
  have h2 : 2 ≤ ‖(u : ℂ) - 2 * Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((u : ℂ) - 2 * Complex.I)
  have h1 : 1 ≤ ‖(u : ℂ) - Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((u : ℂ) - Complex.I)
  rw [callDenominator_factor, norm_mul]
  nlinarith

theorem norm_callDenominator_ge_sq (u : ℝ) : u ^ 2 ≤ ‖callDenominator u‖ := by
  have h2 : |u| ≤ ‖(u : ℂ) - 2 * Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((u : ℂ) - 2 * Complex.I)
  have h1 : |u| ≤ ‖(u : ℂ) - Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((u : ℂ) - Complex.I)
  rw [callDenominator_factor, norm_mul]
  have h := mul_le_mul h2 h1 (abs_nonneg u) (norm_nonneg _)
  simpa only [← sq, sq_abs] using h

theorem norm_callPayoffTransform_le_half (u : ℝ) :
    ‖callPayoffTransform u‖ ≤ 1 / 2 := by
  simp only [callPayoffTransform, norm_div, norm_neg, norm_one]
  exact one_div_le_one_div_of_le (by norm_num) (norm_callDenominator_ge_two u)

theorem norm_callPayoffTransform_le_inv_sq {u : ℝ} (hu : 0 < u) :
    ‖callPayoffTransform u‖ ≤ 1 / u ^ 2 := by
  simp only [callPayoffTransform, norm_div, norm_neg, norm_one]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hu) (norm_callDenominator_ge_sq u)

theorem continuous_callPayoffTransform : Continuous callPayoffTransform := by
  apply Continuous.div continuous_const
    (show Continuous callDenominator by unfold callDenominator; fun_prop)
  exact callDenominator_ne_zero

/-- A uniform transform error controls the integral of its genuine call
factor over a finite band. The integrand is the difference itself. -/
theorem call_band_integral_error {U E : ℝ} (hU : 0 ≤ U)
    (Phi Psi : ℝ → ℂ) (he : ∀ u ∈ Icc 0 U, ‖Phi u - Psi u‖ ≤ E) :
    ‖∫ u in 0..U, callPayoffTransform u * (Phi u - Psi u)‖ ≤ U / 2 * E := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := U)
    (f := fun u => callPayoffTransform u * (Phi u - Psi u))
    (C := (1 / 2) * E) (fun u hu => by
      rw [uIoc_of_le hU] at hu
      rw [norm_mul]
      exact mul_le_mul (norm_callPayoffTransform_le_half u)
        (he u ⟨hu.1.le, hu.2⟩) (norm_nonneg _) (by norm_num))
  simpa only [sub_zero, abs_of_nonneg hU, div_eq_mul_inv, one_mul, mul_assoc, mul_comm,
    mul_left_comm] using hb

/-- The tail majorant is integrable and its integral is exactly `1/U`. -/
theorem integral_Ioi_inv_sq {U : ℝ} (hU : 0 < U) :
    IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ioi U) ∧
      (∫ u : ℝ in Ioi U, 1 / u ^ 2) = 1 / U := by
  have heq : (fun u : ℝ => 1 / u ^ 2) = (fun u : ℝ => u ^ (-2 : ℝ)) := by
    funext u
    simp
  rw [heq]
  refine ⟨integrableOn_Ioi_rpow_of_lt (by norm_num) hU, ?_⟩
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hU]
  norm_num [Real.rpow_neg_one]

/-- Absolute integrability and a quantitative tail estimate follow from a
measurable bounded comparison, using the actual call transform. -/
theorem call_fourier_tail_bound {U B : ℝ} (hU : 0 < U)
    (Phi : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable Phi (volume.restrict (Ioi U)))
    (hbound : ∀ u ∈ Ioi U, ‖Phi u‖ ≤ B) :
    IntegrableOn (fun u => callPayoffTransform u * Phi u) (Ioi U) ∧
      ‖∫ u in Ioi U, callPayoffTransform u * Phi u‖ ≤ B / U := by
  have hmajor := (integral_Ioi_inv_sq hU).1.const_mul B
  have hdom : ∀ᵐ u ∂volume.restrict (Ioi U),
      ‖callPayoffTransform u * Phi u‖ ≤ B * (1 / u ^ 2) := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    exact Filter.Eventually.of_forall (fun u hu => by
      rw [norm_mul, mul_comm B]
      exact mul_le_mul (norm_callPayoffTransform_le_inv_sq (hU.trans hu))
        (hbound u hu) (norm_nonneg _) (by positivity))
  refine ⟨hmajor.mono'
    (continuous_callPayoffTransform.aestronglyMeasurable.restrict.mul hmeas) hdom, ?_⟩
  calc
    _ ≤ ∫ u in Ioi U, B * (1 / u ^ 2) := norm_integral_le_of_norm_le hmajor hdom
    _ = B / U := by
      rw [integral_const_mul, (integral_Ioi_inv_sq hU).2]
      ring

/-- When both band integrands are integrable, the preceding estimate is
an error between their integrals rather than merely the integral of a
difference. -/
theorem call_band_difference_bound {U E : ℝ} (hU : 0 ≤ U)
    (Phi Psi : ℝ → ℂ)
    (hPhi : IntervalIntegrable (fun u => callPayoffTransform u * Phi u) volume 0 U)
    (hPsi : IntervalIntegrable (fun u => callPayoffTransform u * Psi u) volume 0 U)
    (he : ∀ u ∈ Icc 0 U, ‖Phi u - Psi u‖ ≤ E) :
    ‖(∫ u in 0..U, callPayoffTransform u * Phi u) -
      ∫ u in 0..U, callPayoffTransform u * Psi u‖ ≤ U / 2 * E := by
  rw [← intervalIntegral.integral_sub hPhi hPsi]
  simpa only [mul_sub] using call_band_integral_error hU Phi Psi he

/-- A cutoff error estimate for a genuine call Fourier integral. Its exact
comparison is explicitly measurable and bounded on the tail; identification
of this integral with a financial expectation is a separate obligation. -/
theorem call_cutoff_error {U B E : ℝ} (hU : 0 < U)
    (Phi Psi : ℝ → ℂ)
    (hPhi : IntervalIntegrable (fun u => callPayoffTransform u * Phi u) volume 0 U)
    (hPsi : IntervalIntegrable (fun u => callPayoffTransform u * Psi u) volume 0 U)
    (hmeas : AEStronglyMeasurable Phi (volume.restrict (Ioi U)))
    (hbound : ∀ u ∈ Ioi U, ‖Phi u‖ ≤ B)
    (he : ∀ u ∈ Icc 0 U, ‖Phi u - Psi u‖ ≤ E) :
    IntegrableOn (fun u => callPayoffTransform u * Phi u) (Ioi 0) ∧
      ‖(∫ u in Ioi 0, callPayoffTransform u * Phi u) -
        ∫ u in 0..U, callPayoffTransform u * Psi u‖ ≤ U / 2 * E + B / U := by
  have htail := call_fourier_tail_bound hU Phi hmeas hbound
  have hall : IntegrableOn (fun u => callPayoffTransform u * Phi u) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hU.le]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hU.le).1 hPhi).union htail.1
  refine ⟨hall, ?_⟩
  rw [← intervalIntegral.integral_interval_add_Ioi' hPhi htail.1]
  calc
    _ = ‖((∫ u in 0..U, callPayoffTransform u * Phi u) -
        ∫ u in 0..U, callPayoffTransform u * Psi u) +
        ∫ u in Ioi U, callPayoffTransform u * Phi u‖ := by congr 1; abel
    _ ≤ ‖(∫ u in 0..U, callPayoffTransform u * Phi u) -
        ∫ u in 0..U, callPayoffTransform u * Psi u‖ +
        ‖∫ u in Ioi U, callPayoffTransform u * Phi u‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (call_band_difference_bound hU.le Phi Psi hPhi hPsi he) htail.2

/-- The derived actual Adams transform error controls its call-weighted
band integral, on one uniform dyadic family. No compactly supported payoff
is substituted: only the integration domain is truncated. -/
theorem riccati_dyadic_call_band_error (alpha T gamma rho nu theta V0 U Q0 eta : ℝ)
    (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0) (heta : 0 < eta)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha (-2) gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ‖∫ u in 0..U, callPayoffTransform u *
        (Complex.exp ((roughExponent alpha dt (-2) gamma rho nu theta V0 N).eval (u : ℂ)) -
          Complex.exp (exactRiccatiExponent (-2) gamma rho nu theta V0 u T (h u)))‖ ≤
        U / 2 * finiteBandTransformConstant alpha T (-2) gamma rho nu theta V0 U (Q0 + eta) *
          dt ^ alpha := by
  obtain ⟨M0, hM0, herr⟩ := riccati_dyadic_band_transform_error
    alpha T (-2) gamma rho nu theta V0 U Q0 eta h ha ha1 hT hU hQ0 heta hsol hbound
  refine ⟨M0, hM0, fun ell => ?_⟩
  dsimp only
  have hi := call_band_integral_error hU
    (fun u => Complex.exp ((roughExponent alpha (T / (2 ^ ell * M0 : ℕ))
      (-2) gamma rho nu theta V0 (2 ^ ell * M0)).eval (u : ℂ)))
    (fun u => Complex.exp (exactRiccatiExponent (-2) gamma rho nu theta V0 u T (h u)))
    (fun u hu => (herr ell u hu).2)
  simpa only [mul_assoc] using hi

/-- Both actual call-weighted band integrands are integrable, and their
integrals converge at the derived rate. Continuity of the exact transform
is obtained from uniform numerical convergence, not assumed for `h`. -/
theorem riccati_dyadic_call_band_difference_error
    (alpha T gamma rho nu theta V0 U Q0 eta : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0) (heta : 0 < eta)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha (-2) gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      let PhiN := fun u : ℝ => Complex.exp
        ((roughExponent alpha dt (-2) gamma rho nu theta V0 N).eval (u : ℂ))
      let Phi := fun u : ℝ => Complex.exp
        (exactRiccatiExponent (-2) gamma rho nu theta V0 u T (h u))
      IntervalIntegrable (fun u => callPayoffTransform u * PhiN u) volume 0 U ∧
      IntervalIntegrable (fun u => callPayoffTransform u * Phi u) volume 0 U ∧
      ‖(∫ u in 0..U, callPayoffTransform u * PhiN u) -
        ∫ u in 0..U, callPayoffTransform u * Phi u‖ ≤
        U / 2 * finiteBandTransformConstant alpha T (-2) gamma rho nu theta V0 U (Q0 + eta) *
          dt ^ alpha := by
  have hce := continuousOn_exactRiccatiTransform_band alpha T (-2) gamma rho nu theta V0
    U Q0 h ha ha1 hT hU hQ0 hsol hbound
  have hie : IntervalIntegrable (fun u => callPayoffTransform u *
      Complex.exp (exactRiccatiExponent (-2) gamma rho nu theta V0 u T (h u))) volume 0 U :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le hU, Pi.mul_def] using continuous_callPayoffTransform.continuousOn.mul hce)
  obtain ⟨M0, hM0, herr⟩ := riccati_dyadic_band_transform_error
    alpha T (-2) gamma rho nu theta V0 U Q0 eta h ha ha1 hT hU hQ0 heta hsol hbound
  refine ⟨M0, hM0, fun ell => ?_⟩
  dsimp only
  have hin : IntervalIntegrable (fun u => callPayoffTransform u *
      Complex.exp ((roughExponent alpha (T / (2 ^ ell * M0 : ℕ))
        (-2) gamma rho nu theta V0 (2 ^ ell * M0)).eval (u : ℂ))) volume 0 U :=
    (continuous_callPayoffTransform.mul
      (continuous_roughTransform_eval _ _ _ _ _ _ _ _ _)).intervalIntegrable _ _
  refine ⟨hin, hie, ?_⟩
  have hi := call_band_difference_bound hU _ _ hin hie (fun u hu => (herr ell u hu).2)
  simpa only [mul_assoc] using hi

end RoughHeston

#print axioms RoughHeston.call_cutoff_error
#print axioms RoughHeston.riccati_dyadic_call_band_error
#print axioms RoughHeston.riccati_dyadic_call_band_difference_error
