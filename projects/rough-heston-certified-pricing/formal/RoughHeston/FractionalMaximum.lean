module

public import RoughHeston.TransformBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A finite-difference inequality at a maximum

The actual fractional integral has a one-sided finite-difference bound at
a maximum of the real part. The proof retains the complete old history;
its kernel difference has the sign needed to use the maximum hypothesis.
Only continuity and the explicitly stated recent-interval deficit are
assumed. No fractional derivative formula is assumed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

/-- A finite-difference lower bound for the actual fractional integral at
a maximum of the real part. The separate recent-interval deficit makes
the regularity needed by a subsequent maximum principle explicit. -/
theorem re_fractionalIntegral_sub_ge_at_max {β s t ω : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (v : ℝ → ℂ) (hv : ContinuousOn v (Icc 0 t))
    (hmax : ∀ r ∈ Icc 0 t, (v r).re ≤ (v t).re)
    (hrecent : ∀ r ∈ Icc s t, (v t).re - ω ≤ (v r).re) :
    ((v t).re * (t ^ β - s ^ β) - ω * (t - s) ^ β) /
        Real.Gamma (β + 1) ≤
      (fractionalIntegral β v t - fractionalIntegral β v s).re := by
  have hv0s : ContinuousOn v (Icc 0 s) := hv.mono (Icc_subset_Icc le_rfl hst)
  have hvst : ContinuousOn v (Icc s t) := hv.mono (Icc_subset_Icc hs le_rfl)
  have hit0s := intervalIntegrable_fractionalKernel_smul hβ hs t v hv0s
  have his0s := intervalIntegrable_fractionalKernel_smul hβ hs s v hv0s
  have hitst := intervalIntegrable_fractionalKernel_smul hβ hst t v hvst
  have hkt := intervalIntegrable_fractionalKernel hβ t 0 s
  have hks := intervalIntegrable_fractionalKernel hβ s 0 s
  have hkst := intervalIntegrable_fractionalKernel hβ t s t
  have hidiff : IntervalIntegrable
      (fun r => (fractionalKernel β t r - fractionalKernel β s r) • v r) volume 0 s := by
    simpa only [sub_smul] using hit0s.sub his0s
  have hvre0s : ContinuousOn (fun r => (v r).re) (Icc 0 s) :=
    Complex.continuous_re.comp_continuousOn hv0s
  have hvrest : ContinuousOn (fun r => (v r).re) (Icc s t) :=
    Complex.continuous_re.comp_continuousOn hvst
  have hire0s : IntervalIntegrable
      (fun r => (fractionalKernel β t r - fractionalKernel β s r) * (v r).re)
      volume 0 s :=
    (hkt.sub hks).mul_continuousOn (by simpa only [uIcc_of_le hs] using hvre0s)
  have hirest : IntervalIntegrable
      (fun r => fractionalKernel β t r * (v r).re) volume s t :=
    hkst.mul_continuousOn (by simpa only [uIcc_of_le hst] using hvrest)
  have hsplit : fractionalIntegralRaw β v t - fractionalIntegralRaw β v s =
      (∫ r in 0..s, (fractionalKernel β t r - fractionalKernel β s r) • v r) +
        (∫ r in s..t, fractionalKernel β t r • v r) := by
    unfold fractionalIntegralRaw
    simp_rw [sub_smul]
    rw [intervalIntegral.integral_sub hit0s his0s,
      ← intervalIntegral.integral_add_adjacent_intervals hit0s hitst]
    exact add_sub_right_comm _ _ _
  have hreold : (∫ r in 0..s,
      (fractionalKernel β t r - fractionalKernel β s r) • v r).re =
      ∫ r in 0..s, (fractionalKernel β t r - fractionalKernel β s r) * (v r).re := by
    have h := (Complex.reCLM.intervalIntegral_comp_comm hidiff).symm
    simpa only [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul] using h
  have hrenew : (∫ r in s..t, fractionalKernel β t r • v r).re =
      ∫ r in s..t, fractionalKernel β t r * (v r).re := by
    have h := (Complex.reCLM.intervalIntegral_comp_comm hitst).symm
    simpa only [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul] using h
  have hold : (v t).re * (t ^ β - (t - s) ^ β - s ^ β) / β ≤
      (∫ r in 0..s, (fractionalKernel β t r - fractionalKernel β s r) • v r).re := by
    rw [hreold]
    calc
      _ = ∫ r in 0..s, (v t).re *
          (fractionalKernel β t r - fractionalKernel β s r) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hkt hks,
          integral_fractionalKernel hβ, integral_fractionalKernel hβ]
        simp only [sub_zero, sub_self, Real.zero_rpow hβ.ne', sub_zero]
        ring
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hs
          ((hkt.sub hks).const_mul (v t).re) hire0s
        intro r hr
        have hsign : fractionalKernel β t r - fractionalKernel β s r ≤ 0 :=
          sub_nonpos.mpr (fractionalKernel_le_of_time_le hβ1.le hr.2 hst)
        simpa only [mul_comm (v t).re] using
          mul_le_mul_of_nonpos_left (hmax r ⟨hr.1.le, hr.2.le.trans hst⟩) hsign
  have hnew : ((v t).re - ω) * (t - s) ^ β / β ≤
      (∫ r in s..t, fractionalKernel β t r • v r).re := by
    rw [hrenew]
    calc
      _ = ∫ r in s..t, ((v t).re - ω) * fractionalKernel β t r := by
        rw [intervalIntegral.integral_const_mul, integral_fractionalKernel hβ]
        simp only [sub_self, Real.zero_rpow hβ.ne', sub_zero]
        ring
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hst
          (hkst.const_mul ((v t).re - ω)) hirest
        intro r hr
        simpa only [mul_comm ((v t).re - ω)] using
          mul_le_mul_of_nonneg_left (hrecent r hr) (fractionalKernel_nonneg hr.2)
  have hraw : ((v t).re * (t ^ β - s ^ β) - ω * (t - s) ^ β) / β ≤
      (fractionalIntegralRaw β v t - fractionalIntegralRaw β v s).re := by
    rw [hsplit, Complex.add_re]
    calc
      _ = (v t).re * (t ^ β - (t - s) ^ β - s ^ β) / β +
          ((v t).re - ω) * (t - s) ^ β / β := by ring
      _ ≤ _ := add_le_add hold hnew
  unfold fractionalIntegral
  rw [← smul_sub, Complex.smul_re, smul_eq_mul]
  calc
    _ = (Real.Gamma β)⁻¹ *
        (((v t).re * (t ^ β - s ^ β) - ω * (t - s) ^ β) / β) := by
      rw [Real.Gamma_add_one hβ.ne']
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hraw
      (inv_pos.mpr (Real.Gamma_pos_of_pos hβ)).le

/-- The complementary-order version used for a fractional equation of
order `α`. The old history is controlled by the maximum; only the final
interval of length `ε` contributes a possible deficit. -/
theorem re_complementary_fractionalIntegral_sub_ge_at_max {α t ε ω : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hεt : ε < t)
    (v : ℝ → ℂ) (hv : ContinuousOn v (Icc 0 t))
    (hmax : ∀ r ∈ Icc 0 t, (v r).re ≤ (v t).re)
    (hrecent : ∀ r ∈ Icc (t - ε) t, (v t).re - ω ≤ (v r).re) :
    ((v t).re * (t ^ (1 - α) - (t - ε) ^ (1 - α)) - ω * ε ^ (1 - α)) /
        Real.Gamma (2 - α) ≤
      (fractionalIntegral (1 - α) v t - fractionalIntegral (1 - α) v (t - ε)).re := by
  have h := re_fractionalIntegral_sub_ge_at_max (sub_pos.mpr hα1)
    (by linarith : 1 - α < 1) (sub_nonneg.mpr hεt.le) (by linarith : t - ε ≤ t)
    v hv hmax hrecent
  simpa only [sub_sub_cancel, show 1 - α + 1 = 2 - α by ring] using h

/-- The power increment has a positive linear lower bound. This follows
from the actual kernel integral, without differentiating the path. -/
theorem rpow_increment_ge {β t ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hε : 0 < ε) (hεt : ε < t) :
    β * t ^ (β - 1) * ε ≤ t ^ β - (t - ε) ^ β := by
  have hmass : t ^ (β - 1) * ε ≤ (t ^ β - (t - ε) ^ β) / β := by
    calc
      _ = ∫ _r in 0..ε, t ^ (β - 1) := by
        simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ r in 0..ε, fractionalKernel β t r := by
        apply intervalIntegral.integral_mono_on hε.le intervalIntegrable_const
          (intervalIntegrable_fractionalKernel hβ t 0 ε)
        intro r hr
        exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr (hr.2.trans_lt hεt))
          (sub_le_self t hr.1) (sub_nonpos.mpr hβ1.le)
      _ = _ := by rw [integral_fractionalKernel hβ]; simp only [sub_zero]
  have h := (le_div_iff₀ hβ).mp hmass
  nlinarith

/-- A strict maximum principle conditional on the explicitly stated
local little-Hölder property. The relation `v = I^α f` and the actual
semigroup law identify the finite difference with an ordinary integral
of `f`; no fractional derivative hypothesis is used.

Proving the local regularity for a given equation is a separate task. -/
theorem re_force_pos_at_positive_max_of_littleHolder {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t)
    (v f : ℝ → ℂ) (hv : ContinuousOn v (Icc 0 t))
    (hf : ContinuousOn f (Icc 0 t))
    (heq : ∀ r ∈ Icc 0 t, v r = fractionalIntegral α f r)
    (hmax : ∀ r ∈ Icc 0 t, (v r).re ≤ (v t).re)
    (hpos : 0 < (v t).re)
    (hsmall : ∀ η > 0, ∃ δ > 0, ∀ r ∈ Icc (t - δ) t,
      ‖v t - v r‖ ≤ η * (t - r) ^ α) :
    0 < (f t).re := by
  by_contra hnot
  have hft : (f t).re ≤ 0 := le_of_not_gt hnot
  let K := (v t).re * (1 - α) * t ^ (-α)
  let G := Real.Gamma (2 - α)
  let B := K / (4 * G)
  have hK : 0 < K := mul_pos (mul_pos hpos (sub_pos.mpr hα1))
    (Real.rpow_pos_of_pos ht _)
  have hG : 0 < G := Real.Gamma_pos_of_pos (by linarith)
  have hB : 0 < B := div_pos hK (mul_pos (by norm_num) hG)
  obtain ⟨δv, hδv, hδvbound⟩ := hsmall (K / 2) (by positivity)
  obtain ⟨δf, hδf, hδfbound⟩ :=
    (Metric.continuousWithinAt_iff.mp (hf t ⟨ht.le, le_rfl⟩)) B hB
  let ε := min t (min δv δf) / 2
  have hε : 0 < ε := div_pos (lt_min ht (lt_min hδv hδf)) (by norm_num)
  have hεt : ε < t := by
    have h := min_le_left t (min δv δf)
    dsimp only [ε] at *
    linarith
  have hεδv : ε < δv := by
    have h := (min_le_right t (min δv δf)).trans (min_le_left δv δf)
    dsimp only [ε] at *
    linarith
  have hεδf : ε < δf := by
    have h := (min_le_right t (min δv δf)).trans (min_le_right δv δf)
    dsimp only [ε] at *
    linarith
  have hrecent : ∀ r ∈ Icc (t - ε) t,
      (v t).re - (K / 2) * ε ^ α ≤ (v r).re := by
    intro r hr
    have hrδ : r ∈ Icc (t - δv) t := ⟨by linarith [hr.1], hr.2⟩
    have hnorm := hδvbound r hrδ
    have hpow : (t - r) ^ α ≤ ε ^ α :=
      Real.rpow_le_rpow (sub_nonneg.mpr hr.2) (by linarith [hr.1]) hα.le
    have hnorm' : ‖v t - v r‖ ≤ (K / 2) * ε ^ α :=
      hnorm.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hre := Complex.re_le_norm (v t - v r)
    simp only [Complex.sub_re] at hre
    linarith
  have hfd := re_complementary_fractionalIntegral_sub_ge_at_max
    hα hα1 hε hεt v hv hmax hrecent
  have hcomp (x : ℝ) (hx : x ∈ Icc 0 t) :
      fractionalIntegral (1 - α) v x = ∫ r in 0..x, f r := by
    calc
      _ = fractionalIntegral (1 - α) (fractionalIntegral α f) x :=
        fractionalIntegral_congr_on hx.1 (fun r hr => heq r ⟨hr.1, hr.2.trans hx.2⟩)
      _ = _ := fractionalIntegral_complementary hα hα1 hx.1 f
        (hf.mono (Icc_subset_Icc le_rfl hx.2))
  have hts0 : 0 ≤ t - ε := sub_nonneg.mpr hεt.le
  have htst : t - ε ≤ t := sub_le_self t hε.le
  have hf0s := hf.mono (Icc_subset_Icc le_rfl htst)
  have hfst := hf.mono (Icc_subset_Icc hts0 le_rfl)
  have hf0su : ContinuousOn f (uIcc 0 (t - ε)) := by
    simpa only [uIcc_of_le hts0] using hf0s
  have hfstu : ContinuousOn f (uIcc (t - ε) t) := by
    simpa only [uIcc_of_le htst] using hfst
  have hid : fractionalIntegral (1 - α) v t - fractionalIntegral (1 - α) v (t - ε) =
      ∫ r in (t - ε)..t, f r := by
    rw [hcomp t ⟨ht.le, le_rfl⟩, hcomp (t - ε) ⟨hts0, htst⟩,
      ← intervalIntegral.integral_add_adjacent_intervals hf0su.intervalIntegrable
        hfstu.intervalIntegrable]
    simp only [add_sub_cancel_left]
  rw [hid] at hfd
  have hpowmul : ε ^ α * ε ^ (1 - α) = ε := by
    rw [← Real.rpow_add hε, add_sub_cancel, Real.rpow_one]
  have hpow := rpow_increment_ge (sub_pos.mpr hα1) (by linarith : 1 - α < 1) hε hεt
  rw [show 1 - α - 1 = -α by ring] at hpow
  have hmain : K * ε ≤ (v t).re * (t ^ (1 - α) - (t - ε) ^ (1 - α)) := by
    have h := mul_le_mul_of_nonneg_left hpow hpos.le
    dsimp only [K]
    nlinarith
  have hlow : K / 2 * ε ≤ G * (∫ r in (t - ε)..t, f r).re := by
    have h := (div_le_iff₀ hG).mp hfd
    rw [mul_assoc (K / 2), hpowmul] at h
    nlinarith
  have hforce : ∀ r ∈ Icc (t - ε) t, (f r).re ≤ B := by
    intro r hr
    have hr0t : r ∈ Icc 0 t := ⟨hts0.trans hr.1, hr.2⟩
    have hdist : dist r t < δf := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hr.2)]
      linarith [hr.1]
    have hclose := hδfbound hr0t hdist
    rw [dist_eq_norm] at hclose
    have hre := Complex.re_le_norm (f r - f t)
    simp only [Complex.sub_re] at hre
    linarith
  have hupper : (∫ r in (t - ε)..t, f r).re ≤ B * ε := by
    have hre : (∫ r in (t - ε)..t, f r).re = ∫ r in (t - ε)..t, (f r).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hfstu.intervalIntegrable).symm
    rw [hre]
    calc
      _ ≤ ∫ _r in (t - ε)..t, B := by
        apply intervalIntegral.integral_mono_on htst
          (Complex.continuous_re.comp_continuousOn hfstu).intervalIntegrable
          intervalIntegrable_const
        exact hforce
      _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have hquarter : G * (B * ε) = K / 4 * ε := by
    dsimp only [B]
    field_simp
  have hbound := hlow.trans (mul_le_mul_of_nonneg_left hupper hG.le)
  rw [hquarter] at hbound
  nlinarith [mul_pos hK hε]

end RoughHeston

#print axioms RoughHeston.re_fractionalIntegral_sub_ge_at_max
#print axioms RoughHeston.re_complementary_fractionalIntegral_sub_ge_at_max
#print axioms RoughHeston.rpow_increment_ge
#print axioms RoughHeston.re_force_pos_at_positive_max_of_littleHolder
