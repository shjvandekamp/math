module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Mapping estimates for the actual fractional integral

The kernel is integrated as a Lebesgue interval integral, including its
integrable singularity at the upper endpoint. Its value at that single point
follows Mathlib's convention for real powers and does not affect the integral.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

/-- The unnormalized Riemann-Liouville kernel. -/
def fractionalKernel (α t r : ℝ) : ℝ := (t - r) ^ (α - 1)

/-- The unnormalized fractional integral of a complex-valued function. -/
def fractionalIntegralRaw (α : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r in 0..t, fractionalKernel α t r • f r

/-- The Riemann-Liouville fractional integral, with its Gamma normalization. -/
def fractionalIntegral (α : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.Gamma α)⁻¹ • fractionalIntegralRaw α f t

/-- The singular kernel is interval integrable whenever `α > 0`. -/
theorem intervalIntegrable_fractionalKernel {α : ℝ} (hα : 0 < α)
    (t a b : ℝ) : IntervalIntegrable (fractionalKernel α t) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_rpow'
    (a := t - a) (b := t - b) (r := α - 1) (by linarith)).comp_sub_left t
  unfold fractionalKernel
  simpa only [sub_sub_cancel] using h

/-- Exact kernel mass, including intervals that touch the singularity. -/
theorem integral_fractionalKernel {α : ℝ} (hα : 0 < α) (t a b : ℝ) :
    (∫ r in a..b, fractionalKernel α t r) =
      ((t - a) ^ α - (t - b) ^ α) / α := by
  unfold fractionalKernel
  rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r ^ (α - 1)),
    integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  simp only [sub_add_cancel]

theorem fractionalKernel_nonneg {α t r : ℝ} (hr : r ≤ t) :
    0 ≤ fractionalKernel α t r := Real.rpow_nonneg (sub_nonneg.mpr hr) _

/-- Multiplication by a continuous bounded-path integrand preserves actual
kernel integrability; no quadrature or assumed defect is used. -/
theorem intervalIntegrable_fractionalKernel_smul {α a b : ℝ} (hα : 0 < α)
    (hab : a ≤ b) (t : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable (fun r => fractionalKernel α t r • f r) volume a b := by
  exact (intervalIntegrable_fractionalKernel hα t a b).smul_continuousOn
    (by simpa only [uIcc_of_le hab] using hf)

/-- A norm estimate on any subinterval lying before the kernel endpoint. -/
theorem norm_integral_fractionalKernel_smul_le {α a b t M : ℝ}
    (hα : 0 < α) (hab : a ≤ b) (hbt : b ≤ t) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc a b)) (hbound : ∀ r ∈ Icc a b, ‖f r‖ ≤ M) :
    ‖∫ r in a..b, fractionalKernel α t r • f r‖ ≤
      M * ((t - a) ^ α - (t - b) ^ α) / α := by
  have hi := intervalIntegrable_fractionalKernel_smul hα hab t f hf
  have hk := intervalIntegrable_fractionalKernel hα t a b
  calc
    ‖∫ r in a..b, fractionalKernel α t r • f r‖ ≤
        ∫ r in a..b, ‖fractionalKernel α t r • f r‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ r in a..b, M * fractionalKernel α t r := by
      apply intervalIntegral.integral_mono_on hab hi.norm (hk.const_mul M)
      intro r hr
      have hk0 := fractionalKernel_nonneg (α := α) (hr.2.trans hbt)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
      simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hbound r hr) hk0
    _ = M * ((t - a) ^ α - (t - b) ^ α) / α := by
      rw [intervalIntegral.integral_const_mul, integral_fractionalKernel hα]
      ring

/-- The actual fractional integral is well-defined by an integrable kernel
times the continuous input, including at `t = 0`. -/
theorem fractionalIntegral_integrable {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t)) :
    IntervalIntegrable (fun r => fractionalKernel α t r • f r) volume 0 t :=
  intervalIntegrable_fractionalKernel_smul hα ht t f hf

/-- Supremum-norm mapping estimate for the actual fractional integral.
The hypotheses only require continuity and the bound on the relevant interval. -/
theorem norm_fractionalIntegral_le {α t M : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t))
    (hbound : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ M) :
    ‖fractionalIntegral α f t‖ ≤ M * t ^ α / Real.Gamma (α + 1) := by
  have hraw := norm_integral_fractionalKernel_smul_le hα ht (le_refl t) f hf hbound
  simp only [sub_zero, sub_self, Real.zero_rpow (ne_of_gt hα), sub_zero] at hraw
  have hgamma : 0 ≤ (Real.Gamma α)⁻¹ := (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  unfold fractionalIntegral fractionalIntegralRaw
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgamma]
  calc
    (Real.Gamma α)⁻¹ * ‖∫ r in 0..t, fractionalKernel α t r • f r‖ ≤
        (Real.Gamma α)⁻¹ * (M * t ^ α / α) :=
      mul_le_mul_of_nonneg_left hraw hgamma
    _ = M * t ^ α / Real.Gamma (α + 1) := by
      rw [Real.Gamma_add_one (ne_of_gt hα)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- For order at most one, increasing the endpoint decreases the kernel at
every point strictly before the earlier endpoint. -/
theorem fractionalKernel_le_of_time_le {α r s t : ℝ} (hα : α ≤ 1)
    (hrs : r < s) (hst : s ≤ t) :
    fractionalKernel α t r ≤ fractionalKernel α s r := by
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hrs)
    (sub_le_sub_right hst r) (sub_nonpos.mpr hα)

/-- Hölder bound before Gamma normalization. The proof uses actual
integrability and kernel cancellation on the interior of `[0,s]`. -/
theorem norm_fractionalIntegralRaw_sub_le {α s t M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t))
    (hbound : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ M) :
    ‖fractionalIntegralRaw α f t - fractionalIntegralRaw α f s‖ ≤
      2 * M * (t - s) ^ α / α := by
  have ht : 0 ≤ t := hs.trans hst
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hbound 0 ⟨le_rfl, ht⟩)
  have hf0s : ContinuousOn f (Icc 0 s) := hf.mono (Icc_subset_Icc le_rfl hst)
  have hfst : ContinuousOn f (Icc s t) := hf.mono (Icc_subset_Icc hs le_rfl)
  have hit0s := intervalIntegrable_fractionalKernel_smul hα hs t f hf0s
  have his0s := intervalIntegrable_fractionalKernel_smul hα hs s f hf0s
  have hitst := intervalIntegrable_fractionalKernel_smul hα hst t f hfst
  have hkt := intervalIntegrable_fractionalKernel hα t 0 s
  have hks := intervalIntegrable_fractionalKernel hα s 0 s
  have hidiff : IntervalIntegrable
      (fun r => (fractionalKernel α t r - fractionalKernel α s r) • f r) volume 0 s := by
    simpa only [sub_smul] using hit0s.sub his0s
  have hsplit : fractionalIntegralRaw α f t - fractionalIntegralRaw α f s =
      (∫ r in 0..s, (fractionalKernel α t r - fractionalKernel α s r) • f r) +
        (∫ r in s..t, fractionalKernel α t r • f r) := by
    unfold fractionalIntegralRaw
    simp_rw [sub_smul]
    rw [intervalIntegral.integral_sub hit0s his0s,
      ← intervalIntegral.integral_add_adjacent_intervals hit0s hitst]
    exact add_sub_right_comm _ _ _
  have hfirst :
      ‖∫ r in 0..s, (fractionalKernel α t r - fractionalKernel α s r) • f r‖ ≤
        M * (s ^ α - t ^ α + (t - s) ^ α) / α := by
    calc
      ‖∫ r in 0..s, (fractionalKernel α t r - fractionalKernel α s r) • f r‖ ≤
          ∫ r in 0..s, ‖(fractionalKernel α t r - fractionalKernel α s r) • f r‖ :=
        intervalIntegral.norm_integral_le_integral_norm hs
      _ ≤ ∫ r in 0..s, M * (fractionalKernel α s r - fractionalKernel α t r) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hs hidiff.norm
          ((hks.sub hkt).const_mul M)
        intro r hr
        have hkorder := fractionalKernel_le_of_time_le hα1.le hr.2 hst
        have hkdiff : fractionalKernel α t r - fractionalKernel α s r ≤ 0 :=
          sub_nonpos.mpr hkorder
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hkdiff]
        calc
          -(fractionalKernel α t r - fractionalKernel α s r) * ‖f r‖ ≤
              -(fractionalKernel α t r - fractionalKernel α s r) * M :=
            mul_le_mul_of_nonneg_left (hbound r ⟨hr.1.le, hr.2.le.trans hst⟩)
              (neg_nonneg.mpr hkdiff)
          _ = M * (fractionalKernel α s r - fractionalKernel α t r) := by ring
      _ = M * (s ^ α - t ^ α + (t - s) ^ α) / α := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hks hkt,
          integral_fractionalKernel hα, integral_fractionalKernel hα]
        simp only [sub_zero, sub_self, Real.zero_rpow (ne_of_gt hα), sub_zero]
        ring
  have hsecond : ‖∫ r in s..t, fractionalKernel α t r • f r‖ ≤
      M * (t - s) ^ α / α := by
    have h := norm_integral_fractionalKernel_smul_le hα hst (le_refl t) f hfst
      (fun r hr => hbound r ⟨hs.trans hr.1, hr.2⟩)
    simpa only [sub_self, Real.zero_rpow (ne_of_gt hα), sub_zero] using h
  rw [hsplit]
  calc
    ‖(∫ r in 0..s, (fractionalKernel α t r - fractionalKernel α s r) • f r) +
        (∫ r in s..t, fractionalKernel α t r • f r)‖ ≤
      ‖∫ r in 0..s, (fractionalKernel α t r - fractionalKernel α s r) • f r‖ +
        ‖∫ r in s..t, fractionalKernel α t r • f r‖ := norm_add_le _ _
    _ ≤ M * (s ^ α - t ^ α + (t - s) ^ α) / α +
        M * (t - s) ^ α / α := add_le_add hfirst hsecond
    _ = (M * (s ^ α - t ^ α + (t - s) ^ α) + M * (t - s) ^ α) / α := by ring
    _ ≤ 2 * M * (t - s) ^ α / α := by
      apply div_le_div_of_nonneg_right _ hα.le
      have hpow := Real.rpow_le_rpow hs hst hα.le
      nlinarith [mul_nonneg hM (sub_nonneg.mpr hpow)]

/-- The actual fractional integral maps bounded continuous inputs to
`α`-Hölder functions, with the explicit constant `2M / Γ(α+1)`. -/
theorem norm_fractionalIntegral_sub_le {α s t M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t))
    (hbound : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ M) :
    ‖fractionalIntegral α f t - fractionalIntegral α f s‖ ≤
      2 * M / Real.Gamma (α + 1) * (t - s) ^ α := by
  have hraw := norm_fractionalIntegralRaw_sub_le hα hα1 hs hst f hf hbound
  have hgamma : 0 ≤ (Real.Gamma α)⁻¹ := (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le
  unfold fractionalIntegral
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hgamma]
  calc
    (Real.Gamma α)⁻¹ * ‖fractionalIntegralRaw α f t - fractionalIntegralRaw α f s‖ ≤
        (Real.Gamma α)⁻¹ * (2 * M * (t - s) ^ α / α) :=
      mul_le_mul_of_nonneg_left hraw hgamma
    _ = 2 * M / Real.Gamma (α + 1) * (t - s) ^ α := by
      rw [Real.Gamma_add_one (ne_of_gt hα)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The mapping estimate on a prescribed maturity interval. -/
theorem norm_fractionalIntegral_le_on {α t T M : ℝ} (hα : 0 < α)
    (ht : 0 ≤ t) (htT : t ≤ T) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 T)) (hbound : ∀ r ∈ Icc 0 T, ‖f r‖ ≤ M) :
    ‖fractionalIntegral α f t‖ ≤ M * t ^ α / Real.Gamma (α + 1) :=
  norm_fractionalIntegral_le hα ht f (hf.mono (Icc_subset_Icc le_rfl htT))
    (fun r hr => hbound r ⟨hr.1, hr.2.trans htT⟩)

/-- The Hölder estimate on a prescribed maturity interval, including both
endpoints and the case of coincident evaluation times. -/
theorem norm_fractionalIntegral_sub_le_on {α s t T M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 T))
    (hbound : ∀ r ∈ Icc 0 T, ‖f r‖ ≤ M) :
    ‖fractionalIntegral α f t - fractionalIntegral α f s‖ ≤
      2 * M / Real.Gamma (α + 1) * (t - s) ^ α :=
  norm_fractionalIntegral_sub_le hα hα1 hs hst f
    (hf.mono (Icc_subset_Icc le_rfl htT))
    (fun r hr => hbound r ⟨hr.1, hr.2.trans htT⟩)

end RoughHeston

#print axioms RoughHeston.intervalIntegrable_fractionalKernel
#print axioms RoughHeston.integral_fractionalKernel
#print axioms RoughHeston.norm_fractionalIntegral_le
#print axioms RoughHeston.norm_fractionalIntegral_sub_le_on
