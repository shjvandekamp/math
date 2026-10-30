module

public import RoughHeston.FractionalIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local little-Hölder regularity of fractional integrals

Continuity of the original input makes its recent-history remainder
arbitrarily small. The old history and the frozen constant contribution
are Lipschitz away from the singular endpoint.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

private theorem rpow_increment_div_le {α c x y : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hc : 0 < c) (hcx : c ≤ x) (hxy : x ≤ y) :
    (y ^ α - x ^ α) / α ≤ c ^ (α - 1) * (y - x) := by
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (α - 1)) volume x y :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hmass : (∫ r in x..y, r ^ (α - 1)) = (y ^ α - x ^ α) / α := by
    rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
    simp only [sub_add_cancel]
  rw [← hmass]
  calc
    _ ≤ ∫ _r in x..y, c ^ (α - 1) := by
      apply intervalIntegral.integral_mono_on hxy hi intervalIntegrable_const
      intro r hr
      exact Real.rpow_le_rpow_of_nonpos hc (hcx.trans hr.1) (by linarith)
    _ = c ^ (α - 1) * (y - x) := by
      simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- The old-history part changes at most linearly when the moving endpoint
stays a positive distance from the old-history interval. -/
theorem norm_fractional_old_history_sub_le {α a s t c M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a) (has : a < s) (hst : s ≤ t)
    (hc : 0 < c) (hcs : c ≤ s - a) (hM : 0 ≤ M)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 a))
    (hbound : ∀ r ∈ Icc 0 a, ‖f r‖ ≤ M) :
    ‖(∫ r in 0..a, fractionalKernel α t r • f r) -
      ∫ r in 0..a, fractionalKernel α s r • f r‖ ≤
        M * c ^ (α - 1) * (t - s) := by
  have hkt := intervalIntegrable_fractionalKernel hα t 0 a
  have hks := intervalIntegrable_fractionalKernel hα s 0 a
  have hft := intervalIntegrable_fractionalKernel_smul hα ha t f hf
  have hfs := intervalIntegrable_fractionalKernel_smul hα ha s f hf
  have hdiff : IntervalIntegrable
      (fun r => (fractionalKernel α t r - fractionalKernel α s r) • f r) volume 0 a :=
    (hkt.sub hks).smul_continuousOn (by simpa only [uIcc_of_le ha] using hf)
  have heq : (∫ r in 0..a, fractionalKernel α t r • f r) -
      (∫ r in 0..a, fractionalKernel α s r • f r) =
      ∫ r in 0..a, (fractionalKernel α t r - fractionalKernel α s r) • f r := by
    simp_rw [sub_smul]
    rw [intervalIntegral.integral_sub hft hfs]
  rw [heq]
  calc
    _ ≤ ∫ r in 0..a, ‖(fractionalKernel α t r - fractionalKernel α s r) • f r‖ :=
      intervalIntegral.norm_integral_le_integral_norm ha
    _ ≤ ∫ r in 0..a, M * (fractionalKernel α s r - fractionalKernel α t r) := by
      apply intervalIntegral.integral_mono_on ha hdiff.norm ((hks.sub hkt).const_mul M)
      intro r hr
      have hkorder := fractionalKernel_le_of_time_le hα1.le (hr.2.trans_lt has) hst
      have hkdiff : fractionalKernel α t r - fractionalKernel α s r ≤ 0 :=
        sub_nonpos.mpr hkorder
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hkdiff]
      calc
        _ ≤ -(fractionalKernel α t r - fractionalKernel α s r) * M :=
          mul_le_mul_of_nonneg_left (hbound r hr) (neg_nonneg.mpr hkdiff)
        _ = _ := by ring
    _ = M * ((s ^ α - t ^ α + (t - a) ^ α - (s - a) ^ α) / α) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hks hkt,
        integral_fractionalKernel hα, integral_fractionalKernel hα]
      simp only [sub_zero]
      ring
    _ ≤ M * (((t - a) ^ α - (s - a) ^ α) / α) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply div_le_div_of_nonneg_right _ hα.le
      have hp := Real.rpow_le_rpow (ha.trans has.le) hst hα.le
      linarith
    _ ≤ M * (c ^ (α - 1) * (t - s)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only [sub_sub_sub_cancel_right] using
        rpow_increment_div_le hα hα1 hc hcs (sub_le_sub_right hst a)
    _ = _ := by ring

private theorem fractionalIntegralRaw_translate (α a q : ℝ) (f : ℝ → ℂ) :
    (∫ r in a..q, fractionalKernel α q r • f r) =
      fractionalIntegralRaw α (fun r => f (r + a)) (q - a) := by
  have h := intervalIntegral.integral_comp_add_right
    (fun r => fractionalKernel α q r • f r) a (a := 0) (b := q - a)
  simp only [zero_add, sub_add_cancel] at h
  rw [← h]
  unfold fractionalIntegralRaw
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only [fractionalKernel]
  rw [show q - (r + a) = q - a - r by ring]

/-- The actual Hölder estimate on a translated recent-history interval. -/
theorem norm_fractional_recent_history_sub_le {α a s t M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (has : a ≤ s) (hst : s ≤ t)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a t))
    (hbound : ∀ r ∈ Icc a t, ‖f r‖ ≤ M) :
    ‖(∫ r in a..t, fractionalKernel α t r • f r) -
      ∫ r in a..s, fractionalKernel α s r • f r‖ ≤
        2 * M * (t - s) ^ α / α := by
  have hmem (r : ℝ) (hr : r ∈ Icc 0 (t - a)) : r + a ∈ Icc a t := by
    constructor <;> linarith [hr.1, hr.2]
  have hfc : ContinuousOn (fun r => f (r + a)) (Icc 0 (t - a)) :=
    hf.comp (continuous_id.add continuous_const).continuousOn hmem
  rw [fractionalIntegralRaw_translate, fractionalIntegralRaw_translate]
  have h := norm_fractionalIntegralRaw_sub_le hα hα1 (sub_nonneg.mpr has)
    (sub_le_sub_right hst a) (fun r => f (r + a)) hfc
    (fun r hr => hbound (r + a) (hmem r hr))
  simpa only [sub_sub_sub_cancel_right] using h

private theorem integral_fractionalKernel_smul_const {α : ℝ} (hα : 0 < α)
    (q : ℝ) (z : ℂ) :
    (∫ r in 0..q, fractionalKernel α q r • z) = (q ^ α / α) • z := by
  rw [intervalIntegral.integral_smul_const, integral_fractionalKernel hα]
  simp only [sub_zero, sub_self, Real.zero_rpow hα.ne', sub_zero]

private theorem fractionalIntegralRaw_eq_split_sub_const {α a q : ℝ}
    (hα : 0 < α) (ha : 0 ≤ a) (haq : a ≤ q)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 q)) (z : ℂ) :
    fractionalIntegralRaw α f q =
      (∫ r in 0..a, fractionalKernel α q r • (f r - z)) +
      (∫ r in a..q, fractionalKernel α q r • (f r - z)) + (q ^ α / α) • z := by
  have hq : 0 ≤ q := ha.trans haq
  have hfc : ContinuousOn (fun r => f r - z) (Icc 0 q) := hf.sub continuousOn_const
  have hi0 := intervalIntegrable_fractionalKernel_smul hα ha q
    (fun r => f r - z) (hfc.mono (Icc_subset_Icc le_rfl haq))
  have hia := intervalIntegrable_fractionalKernel_smul hα haq q
    (fun r => f r - z) (hfc.mono (Icc_subset_Icc ha le_rfl))
  rw [intervalIntegral.integral_add_adjacent_intervals hi0 hia,
    ← integral_fractionalKernel_smul_const hα q z]
  have hic := intervalIntegrable_fractionalKernel_smul hα hq q (fun _ => z) continuousOn_const
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_fractionalKernel_smul hα hq q (fun r => f r - z) hfc) hic]
  unfold fractionalIntegralRaw
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [← smul_add, sub_add_cancel]

private theorem norm_fractionalIntegral_sub_le_local {α a s t c M eps : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a) (has : a < s) (hst : s ≤ t)
    (hc : 0 < c) (hcs : c ≤ s - a) (hM : 0 ≤ M)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t))
    (hglobal : ∀ r ∈ Icc 0 a, ‖f r - f t‖ ≤ M)
    (hrecent : ∀ r ∈ Icc a t, ‖f r - f t‖ ≤ eps) :
    ‖fractionalIntegral α f t - fractionalIntegral α f s‖ ≤
      (Real.Gamma α)⁻¹ * ((M + ‖f t‖) * c ^ (α - 1) * (t - s) +
        2 * eps * (t - s) ^ α / α) := by
  have hs : 0 ≤ s := ha.trans has.le
  have hat : a ≤ t := has.le.trans hst
  have hfc : ContinuousOn (fun r => f r - f t) (Icc 0 t) := hf.sub continuousOn_const
  let A : ℂ := (∫ r in 0..a, fractionalKernel α t r • (f r - f t)) -
    ∫ r in 0..a, fractionalKernel α s r • (f r - f t)
  let P : ℂ := (∫ r in a..t, fractionalKernel α t r • (f r - f t)) -
    ∫ r in a..s, fractionalKernel α s r • (f r - f t)
  let C : ℂ := ((t ^ α - s ^ α) / α) • f t
  have hold : ‖A‖ ≤ M * c ^ (α - 1) * (t - s) :=
    norm_fractional_old_history_sub_le hα hα1 ha has hst hc hcs hM
      (fun r => f r - f t) (hfc.mono (Icc_subset_Icc le_rfl hat)) hglobal
  have hnew : ‖P‖ ≤ 2 * eps * (t - s) ^ α / α :=
    norm_fractional_recent_history_sub_le hα hα1 has.le hst
      (fun r => f r - f t) (hfc.mono (Icc_subset_Icc ha le_rfl)) hrecent
  have hcon : ‖C‖ ≤ ‖f t‖ * c ^ (α - 1) * (t - s) := by
    have hpow : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs hst hα.le
    have hdiv : 0 ≤ (t ^ α - s ^ α) / α := div_nonneg (sub_nonneg.mpr hpow) hα.le
    dsimp only [C]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiv]
    calc
      _ ≤ (c ^ (α - 1) * (t - s)) * ‖f t‖ :=
        mul_le_mul_of_nonneg_right (rpow_increment_div_le hα hα1 hc (by linarith) hst)
          (norm_nonneg _)
      _ = _ := by ring
  have heq : fractionalIntegralRaw α f t - fractionalIntegralRaw α f s = A + P + C := by
    rw [fractionalIntegralRaw_eq_split_sub_const hα ha hat f hf (f t),
      fractionalIntegralRaw_eq_split_sub_const hα ha has.le f
        (hf.mono (Icc_subset_Icc le_rfl hst)) (f t)]
    dsimp only [A, P, C]
    rw [sub_div, sub_smul]
    ring
  have hraw : ‖fractionalIntegralRaw α f t - fractionalIntegralRaw α f s‖ ≤
      (M + ‖f t‖) * c ^ (α - 1) * (t - s) + 2 * eps * (t - s) ^ α / α := by
    rw [heq]
    calc
      ‖A + P + C‖ ≤ ‖A + P‖ + ‖C‖ := norm_add_le _ _
      _ ≤ (‖A‖ + ‖P‖) + ‖C‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (M * c ^ (α - 1) * (t - s) + 2 * eps * (t - s) ^ α / α) +
          ‖f t‖ * c ^ (α - 1) * (t - s) := add_le_add (add_le_add hold hnew) hcon
      _ = _ := by ring
  unfold fractionalIntegral
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le]
  exact mul_le_mul_of_nonneg_left hraw (inv_pos.mpr (Real.Gamma_pos_of_pos hα)).le

/-- At every strictly positive time, an actual fractional integral of a
continuous input is locally little-Hölder of order `α` from the left. The
neighborhood can be chosen inside the nonnegative time axis. -/
theorem fractionalIntegral_littleHolder_left {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 t)) :
    ∀ eta > 0, ∃ d > 0, d ≤ t ∧ ∀ s : ℝ, 0 ≤ s → t - d ≤ s → s < t →
      ‖fractionalIntegral α f t - fractionalIntegral α f s‖ ≤ eta * (t - s) ^ α := by
  intro eta heta
  let eps : ℝ := eta * α * Real.Gamma α / 4
  have hGamma : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have heps : 0 < eps := by dsimp only [eps]; positivity
  obtain ⟨d0, hd0, hcont⟩ := (Metric.continuousWithinAt_iff.mp (hf t ⟨ht.le, le_rfl⟩)) eps heps
  let a : ℝ := max 0 (t - d0 / 2)
  have ha : 0 ≤ a := le_max_left _ _
  have hat : a < t := by
    apply max_lt
    · exact ht
    · linarith
  have hrecent : ∀ r ∈ Icc a t, ‖f r - f t‖ ≤ eps := by
    intro r hr
    have hr0 : r ∈ Icc 0 t := ⟨ha.trans hr.1, hr.2⟩
    have hdist : dist r t < d0 := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hr.2)]
      have ha' : t - d0 / 2 ≤ a := le_max_right _ _
      linarith [hr.1]
    simpa only [dist_eq_norm] using (hcont hr0 hdist).le
  have hfc : ContinuousOn (fun r => f r - f t) (Icc 0 t) := hf.sub continuousOn_const
  obtain ⟨M, hglobal⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  have hM : 0 ≤ M := (norm_nonneg _).trans (hglobal 0 ⟨le_rfl, ht.le⟩)
  let c : ℝ := (t - a) / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  let C : ℝ := (Real.Gamma α)⁻¹ * (M + ‖f t‖) * c ^ (α - 1)
  have hmax : (0 : ℝ) < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let b : ℝ := (eta / (2 * max 1 C)) ^ (1 / (1 - α))
  have hb : 0 < b := Real.rpow_pos_of_pos (div_pos heta (by positivity)) _
  let d : ℝ := min c b
  have hd : 0 < d := lt_min hc hb
  have hdc : d ≤ c := min_le_left _ _
  have hdb : d ≤ b := min_le_right _ _
  have hdt : d ≤ t := by dsimp only [c] at hdc; linarith
  refine ⟨d, hd, hdt, ?_⟩
  intro s hs hnear hst
  have has : a < s := by dsimp only [c] at hdc; linarith
  have hcs : c ≤ s - a := by dsimp only [c] at *; linarith
  have hgap : 0 < t - s := sub_pos.mpr hst
  have hgapb : t - s ≤ b := (by linarith : t - s ≤ d).trans hdb
  have hpow : (t - s) ^ (1 - α) ≤ eta / (2 * max 1 C) := by
    apply (Real.le_rpow_inv_iff_of_pos hgap.le (div_pos heta (by positivity)).le
      (sub_pos.mpr hα1)).mp
    simpa only [b, one_div] using hgapb
  have hsmall : C * (t - s) ^ (1 - α) ≤ eta / 2 := by
    calc
      _ ≤ max 1 C * (t - s) ^ (1 - α) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hgap.le _)
      _ ≤ max 1 C * (eta / (2 * max 1 C)) :=
        mul_le_mul_of_nonneg_left hpow hmax.le
      _ = eta / 2 := by field_simp
  have hfactor : (t - s) ^ (1 - α) * (t - s) ^ α = t - s := by
    rw [← Real.rpow_add hgap, sub_add_cancel, Real.rpow_one]
  have hlinear : C * (t - s) ≤ eta / 2 * (t - s) ^ α := by
    calc
      _ = C * ((t - s) ^ (1 - α) * (t - s) ^ α) :=
        congrArg (fun x : ℝ => C * x) hfactor.symm
      _ = (C * (t - s) ^ (1 - α)) * (t - s) ^ α := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hgap.le _)
  have hcoeff : (Real.Gamma α)⁻¹ * (2 * eps / α) = eta / 2 := by
    dsimp only [eps]
    field_simp
    ring
  have hlocal := norm_fractionalIntegral_sub_le_local hα hα1 ha has hst.le hc hcs hM f hf
    (fun r hr => hglobal r ⟨hr.1, hr.2.trans hat.le⟩) hrecent
  calc
    _ ≤ (Real.Gamma α)⁻¹ * ((M + ‖f t‖) * c ^ (α - 1) * (t - s) +
        2 * eps * (t - s) ^ α / α) := hlocal
    _ = C * (t - s) + ((Real.Gamma α)⁻¹ * (2 * eps / α)) * (t - s) ^ α := by
      dsimp only [C]
      ring
    _ = C * (t - s) + (eta / 2) * (t - s) ^ α := by rw [hcoeff]
    _ ≤ (eta / 2) * (t - s) ^ α + (eta / 2) * (t - s) ^ α := add_le_add hlinear le_rfl
    _ = eta * (t - s) ^ α := by ring

/-- Closed-neighborhood formulation, including the coincident endpoint,
for direct use in a finite-difference fractional maximum principle. -/
theorem fractionalIntegral_littleHolder_left_Icc {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 t)) :
    ∀ eta > 0, ∃ d > 0, ∀ s ∈ Icc (t - d) t,
      ‖fractionalIntegral α f t - fractionalIntegral α f s‖ ≤ eta * (t - s) ^ α := by
  intro eta heta
  obtain ⟨d, hd, hdt, hbound⟩ := fractionalIntegral_littleHolder_left hα hα1 ht f hf eta heta
  refine ⟨d, hd, ?_⟩
  intro s hs
  rcases hs.2.eq_or_lt with rfl | hst
  · simp [Real.zero_rpow hα.ne']
  · exact hbound s (by linarith [hs.1]) hs.1 hst

end RoughHeston

#print axioms RoughHeston.fractionalIntegral_littleHolder_left
#print axioms RoughHeston.fractionalIntegral_littleHolder_left_Icc
