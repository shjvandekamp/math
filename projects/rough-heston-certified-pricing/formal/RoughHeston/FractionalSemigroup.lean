module

public import RoughHeston.FractionalIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convolution of the actual fractional kernels

The Beta integral identifies the convolution of the two singular power
kernels, including its normalization by Gamma functions.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

/-- The actual convolution mass of two fractional power kernels. -/
theorem integral_fractionalKernel_convolution {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    (∫ r in 0..t, fractionalKernel β t r * r ^ (α - 1)) =
      t ^ (α + β - 1) * Real.Gamma α * Real.Gamma β / Real.Gamma (α + β) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    _ = ∫ r in 0..t, (r : ℂ) ^ ((α : ℂ) - 1) *
        ((t : ℂ) - r) ^ ((β : ℂ) - 1) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.le] at hr
      dsimp only
      unfold fractionalKernel
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (sub_nonneg.mpr hr.2),
        Complex.ofReal_cpow hr.1]
      push_cast
      ring
    _ = (t : ℂ) ^ ((α : ℂ) + β - 1) * Complex.betaIntegral α β :=
      Complex.betaIntegral_scaled α β ht
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div α β (by simpa using hα) (by simpa using hβ)]
      have hp : (t : ℂ) ^ ((α : ℂ) + β - 1) = ((t ^ (α + β - 1) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow ht.le]
        push_cast
        rfl
      rw [hp, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        Complex.Gamma_ofReal]
      push_cast
      ring

/-- Both endpoint singularities in the convolution mass are integrable. The
positive exact Beta integral rules out the undefined-integral value zero. -/
theorem intervalIntegrable_fractionalKernel_convolution {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => fractionalKernel β t r * r ^ (α - 1)) volume 0 t := by
  rcases ht.eq_or_lt with rfl | ht
  · exact IntervalIntegrable.refl
  · apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [integral_fractionalKernel_convolution hα hβ ht]
    apply ne_of_gt
    exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos ht _)
      (Real.Gamma_pos_of_pos hα)) (Real.Gamma_pos_of_pos hβ))
      (Real.Gamma_pos_of_pos (add_pos hα hβ))

/-- Gamma-normalized convolution is the fractional kernel of the sum of the
two positive orders. -/
theorem normalized_fractionalKernel_convolution {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    (Real.Gamma β)⁻¹ * (Real.Gamma α)⁻¹ *
        (∫ r in 0..t, fractionalKernel β t r * r ^ (α - 1)) =
      t ^ (α + β - 1) / Real.Gamma (α + β) := by
  rw [integral_fractionalKernel_convolution hα hβ ht]
  have hGa : Real.Gamma α ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hα)
  have hGb : Real.Gamma β ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hβ)
  field_simp

/-- Complementary orders have normalized convolution mass one. -/
theorem complementary_fractionalKernel_convolution {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t) :
    (Real.Gamma (1 - α))⁻¹ * (Real.Gamma α)⁻¹ *
        (∫ r in 0..t, fractionalKernel (1 - α) t r * r ^ (α - 1)) = 1 := by
  rw [normalized_fractionalKernel_convolution hα (sub_pos.mpr hα1) ht]
  simp only [add_sub_cancel, sub_self, Real.rpow_zero, Real.Gamma_one, div_one]

private def truncatedKernel (α T : ℝ) : ℝ → ℝ :=
  (Ioc 0 T).indicator (fun r => (Real.Gamma α)⁻¹ * r ^ (α - 1))

private def truncatedPath (T : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Icc 0 T).indicator f

private theorem integrable_truncatedKernel {α : ℝ} (hα : 0 < α) (T : ℝ) :
    Integrable (truncatedKernel α T) := by
  have h : IntervalIntegrable (fun r : ℝ => r ^ (α - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  exact (h.const_mul (Real.Gamma α)⁻¹).1.integrable_indicator measurableSet_Ioc

private theorem truncatedKernel_nonneg {α T : ℝ} (hα : 0 < α) (r : ℝ) :
    0 ≤ truncatedKernel α T r := by
  by_cases hr : r ∈ Ioc 0 T
  · simpa only [truncatedKernel, indicator_of_mem hr] using
      mul_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le (Real.rpow_nonneg hr.1.le _)
  · simp only [truncatedKernel, indicator_of_notMem hr, le_refl]

private theorem fractionalIntegral_reflect (α t : ℝ) (f : ℝ → ℂ) :
    fractionalIntegral α f t =
      ∫ r in 0..t, ((Real.Gamma α)⁻¹ * r ^ (α - 1)) • f (t - r) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun r => (Real.Gamma α)⁻¹ • (fractionalKernel α t r • f r)) t (a := 0) (b := t)
  simp only [sub_self, sub_zero] at h
  unfold fractionalIntegral fractionalIntegralRaw
  rw [← intervalIntegral.integral_smul, ← h]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only [fractionalKernel]
  rw [sub_sub_cancel, smul_smul]

private theorem convolution_truncatedKernel_eq (α T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℂ) :
    convolution (truncatedKernel α T) f (ContinuousLinearMap.lsmul ℝ ℝ) volume T =
      fractionalIntegral α f T := by
  rw [fractionalIntegral_reflect]
  change (∫ r : ℝ, truncatedKernel α T r • f (T - r)) = _
  have hfun : (fun r => truncatedKernel α T r • f (T - r)) =
      (Ioc 0 T).indicator (fun r => ((Real.Gamma α)⁻¹ * r ^ (α - 1)) • f (T - r)) := by
    funext r
    by_cases hr : r ∈ Ioc 0 T <;> simp [truncatedKernel, hr]
  rw [hfun, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hT]

private theorem convolution_truncatedKernel_path_eq (α T t : ℝ)
    (ht : 0 ≤ t) (htT : t ≤ T) (f : ℝ → ℂ) :
    convolution (truncatedKernel α T) (truncatedPath T f)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume t = fractionalIntegral α f t := by
  rw [fractionalIntegral_reflect]
  change (∫ r : ℝ, truncatedKernel α T r • truncatedPath T f (t - r)) = _
  have hfun : (fun r => truncatedKernel α T r • truncatedPath T f (t - r)) =
      (Ioc 0 t).indicator (fun r => ((Real.Gamma α)⁻¹ * r ^ (α - 1)) • f (t - r)) := by
    funext r
    by_cases hr : r ∈ Ioc 0 t
    · have hrT : r ∈ Ioc 0 T := ⟨hr.1, hr.2.trans htT⟩
      have hsT : t - r ∈ Icc 0 T := ⟨sub_nonneg.mpr hr.2, by linarith [hr.1]⟩
      simp [truncatedKernel, truncatedPath, hr, hrT, hsT]
    · by_cases hr0 : 0 < r
      · have hrt : t < r := lt_of_not_ge (fun h => hr ⟨hr0, h⟩)
        have hsT : t - r ∉ Icc 0 T := fun h => (not_le_of_gt hrt) (sub_nonneg.mp h.1)
        simp [truncatedPath, hr, hsT]
      · have hrT : r ∉ Ioc 0 T := fun h => hr0 h.1
        simp [truncatedKernel, hr, hrT]
  rw [hfun, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le ht]

private theorem convolution_truncatedPath_eq (T : ℝ) (hT : 0 ≤ T)
    (k : ℝ → ℝ) (f : ℝ → ℂ) :
    convolution k (truncatedPath T f) (ContinuousLinearMap.lsmul ℝ ℝ) volume T =
      ∫ r in 0..T, k r • f (T - r) := by
  change (∫ r : ℝ, k r • truncatedPath T f (T - r)) = _
  have hfun : (fun r => k r • truncatedPath T f (T - r)) =
      (Icc 0 T).indicator (fun r => k r • f (T - r)) := by
    funext r
    by_cases hr : r ∈ Icc 0 T
    · have hs : T - r ∈ Icc 0 T := ⟨sub_nonneg.mpr hr.2, by linarith [hr.1]⟩
      simp [truncatedPath, hr, hs]
    · have hs : T - r ∉ Icc 0 T := by
        intro hs
        exact hr ⟨by linarith [hs.2], sub_nonneg.mp hs.1⟩
      simp [truncatedPath, hr, hs]
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hT]

private theorem convolution_truncatedKernels {α β T t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) (htT : t ≤ T) :
    convolution (truncatedKernel β T) (truncatedKernel α T)
      (ContinuousLinearMap.mul ℝ ℝ) volume t = t ^ (α + β - 1) / Real.Gamma (α + β) := by
  change (∫ r : ℝ, truncatedKernel β T r * truncatedKernel α T (t - r)) = _
  have hfun : (fun r => truncatedKernel β T r * truncatedKernel α T (t - r)) =
      (Ioo 0 t).indicator (fun r => ((Real.Gamma β)⁻¹ * r ^ (β - 1)) *
        ((Real.Gamma α)⁻¹ * (t - r) ^ (α - 1))) := by
    funext r
    by_cases hr : r ∈ Ioo 0 t
    · have hrT : r ∈ Ioc 0 T := ⟨hr.1, hr.2.le.trans htT⟩
      have hsT : t - r ∈ Ioc 0 T := ⟨sub_pos.mpr hr.2, by linarith [hr.1]⟩
      simp [truncatedKernel, hr, hrT, hsT]
    · by_cases hr0 : 0 < r
      · have hrt : t ≤ r := le_of_not_gt (fun h => hr ⟨hr0, h⟩)
        have hsT : t - r ∉ Ioc 0 T := fun h => (not_lt_of_ge hrt) (sub_pos.mp h.1)
        simp [truncatedKernel, hr, hsT]
      · have hrT : r ∉ Ioc 0 T := fun h => hr0 h.1
        simp [truncatedKernel, hr, hrT]
  rw [hfun, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.le]
  calc
    _ = (Real.Gamma β)⁻¹ * (Real.Gamma α)⁻¹ *
        ∫ r in 0..t, fractionalKernel α t r * r ^ (β - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only [fractionalKernel]
      ring
    _ = t ^ (β + α - 1) / Real.Gamma (β + α) := by
      rw [mul_comm (Real.Gamma β)⁻¹ (Real.Gamma α)⁻¹]
      exact normalized_fractionalKernel_convolution hβ hα ht
    _ = _ := by rw [add_comm β α]

private theorem convolution_truncatedKernels_path {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 ≤ T) (f : ℝ → ℂ) :
    convolution
      (convolution (truncatedKernel β T) (truncatedKernel α T) (ContinuousLinearMap.mul ℝ ℝ) volume)
      (truncatedPath T f) (ContinuousLinearMap.lsmul ℝ ℝ) volume T =
      fractionalIntegral (α + β) f T := by
  rw [convolution_truncatedPath_eq T hT, fractionalIntegral_reflect,
    intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp only
  rw [convolution_truncatedKernels hα hβ hr.1 hr.2]
  simp only [div_eq_mul_inv, mul_comm]

/-- The actual fractional integral satisfies the semigroup law for every
continuous complex path on a finite nonnegative interval. Absolute
integrability of the double kernel is established before using Fubini. -/
theorem fractionalIntegral_semigroup {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 ≤ T) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 T)) :
    fractionalIntegral β (fractionalIntegral α f) T = fractionalIntegral (α + β) f T := by
  have ha := integrable_truncatedKernel hα T
  have hb := integrable_truncatedKernel hβ T
  have hp : Integrable (truncatedPath T f) :=
    hf.integrableOn_Icc.integrable_indicator measurableSet_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 ⟨le_rfl, hT⟩)
  have hpbound (r : ℝ) : ‖truncatedPath T f r‖ ≤ M := by
    by_cases hr : r ∈ Icc 0 T
    · simpa only [truncatedPath, indicator_of_mem hr] using hM r hr
    · simpa only [truncatedPath, indicator_of_notMem hr, norm_zero] using hM0
  have hk := hb.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) ha
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => truncatedKernel β T p.2 •
        (truncatedKernel α T (p.1 - p.2) • truncatedPath T f (T - p.1)))
      (volume.prod volume) := by
    have hprod := hk.aestronglyMeasurable.smul (hp.comp_sub_left T).aestronglyMeasurable.comp_fst
    simpa only [ContinuousLinearMap.mul_apply', Pi.smul_def', smul_smul] using hprod
  have hi : Integrable
      (fun p : ℝ × ℝ => truncatedKernel β T p.2 •
        (truncatedKernel α T (p.1 - p.2) • truncatedPath T f (T - p.1)))
      (volume.prod volume) := by
    apply (hk.const_mul M).mono' hm
    apply Filter.Eventually.of_forall
    intro p
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (truncatedKernel_nonneg hβ p.2),
      abs_of_nonneg (truncatedKernel_nonneg hα (p.1 - p.2)), ContinuousLinearMap.mul_apply']
    calc
      _ ≤ truncatedKernel β T p.2 * (truncatedKernel α T (p.1 - p.2) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpbound _)
          (truncatedKernel_nonneg hα _)) (truncatedKernel_nonneg hβ _)
      _ = _ := by ring
  have hassoc := convolution_assoc'
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x y z => by simp only [ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.lsmul_apply, smul_smul])
    (hb.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) ha)
    (ha.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hp) hi
  have hright : convolution (truncatedKernel β T)
      (convolution (truncatedKernel α T) (truncatedPath T f)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume T =
      fractionalIntegral β (fractionalIntegral α f) T := by
    rw [convolution_truncatedKernel_eq β T hT]
    change (Real.Gamma β)⁻¹ •
        (∫ r in 0..T, fractionalKernel β T r •
          convolution (truncatedKernel α T) (truncatedPath T f)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume r) =
      (Real.Gamma β)⁻¹ • ∫ r in 0..T, fractionalKernel β T r • fractionalIntegral α f r
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hT] at hr
    dsimp only
    rw [convolution_truncatedKernel_path_eq α T r hr.1 hr.2]
  calc
    _ = convolution (truncatedKernel β T)
        (convolution (truncatedKernel α T) (truncatedPath T f)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume T := hright.symm
    _ = _ := hassoc.symm.trans (convolution_truncatedKernels_path hα hβ hT f)

/-- Complementary fractional orders recover the ordinary integral of the
original continuous path. -/
theorem fractionalIntegral_complementary {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 T)) :
    fractionalIntegral (1 - α) (fractionalIntegral α f) T = ∫ r in 0..T, f r := by
  rw [fractionalIntegral_semigroup hα (sub_pos.mpr hα1) hT f hf]
  simp [fractionalIntegral, fractionalIntegralRaw, fractionalKernel]

end RoughHeston

#print axioms RoughHeston.intervalIntegrable_fractionalKernel_convolution
#print axioms RoughHeston.complementary_fractionalKernel_convolution
#print axioms RoughHeston.fractionalIntegral_semigroup
#print axioms RoughHeston.fractionalIntegral_complementary
