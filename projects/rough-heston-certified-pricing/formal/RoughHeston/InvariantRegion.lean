module

public import RoughHeston.FractionalMaximum
public import RoughHeston.LocalRegularity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Invariant-region bounds for an existing concrete Riccati solution

A continuous path that reaches a barrier has a first positive contact.
At that contact the strict fractional maximum principle conflicts with
the inward sign of the concrete Riccati force. These results bound an
existing solution; they do not assert global existence.
-/

@[expose] public section

noncomputable section

open Set

namespace RoughHeston

/-- A continuous real path starting below a barrier and reaching it has
a first positive contact, with its complete prior history below it. -/
theorem exists_first_barrier_contact {T B : ℝ} (hT : 0 ≤ T)
    (v : ℝ → ℝ) (hv : ContinuousOn v (Icc 0 T))
    (hzero : v 0 < B) (hreach : B ≤ v T) :
    ∃ t ∈ Ioc 0 T, v t = B ∧ ∀ s ∈ Icc 0 t, v s ≤ B := by
  let S := Icc 0 T ∩ v ⁻¹' Ici B
  have hclosed : IsClosed S :=
    hv.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  have hnonempty : S.Nonempty := ⟨T, ⟨⟨hT, le_rfl⟩, hreach⟩⟩
  obtain ⟨t, ht⟩ := hcompact.exists_isLeast hnonempty
  have ht0 : 0 < t := by
    by_contra hnot
    have htz : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1.1.1
    have h := ht.1.2
    change B ≤ v t at h
    rw [htz] at h
    exact (not_le_of_gt hzero) h
  have htT : t ≤ T := ht.1.1.2
  obtain ⟨r, hr, hreq⟩ := intermediate_value_Icc ht0.le
    (hv.mono (Icc_subset_Icc le_rfl htT)) ⟨hzero.le, ht.1.2⟩
  have hrS : r ∈ S := ⟨⟨hr.1, hr.2.trans htT⟩, by change B ≤ v r; rw [hreq]⟩
  have hrt : r = t := le_antisymm hr.2 (ht.2 hrS)
  have hvalue : v t = B := by simpa only [hrt] using hreq
  refine ⟨t, ⟨ht0, htT⟩, hvalue, ?_⟩
  intro s hs
  by_contra hnot
  have hBs : B < v s := lt_of_not_ge hnot
  have hsS : s ∈ S := ⟨⟨hs.1, hs.2.trans htT⟩, hBs.le⟩
  have hst : s = t := le_antisymm hs.2 (ht.2 hsS)
  rw [hst, hvalue] at hBs
  exact (lt_irrefl B) hBs

/-- The concrete Riccati solution cannot reach `Re h = 1`, conditional
only on its explicit local little-Hölder property. -/
theorem IsRiccatiSolution.concrete_re_lt_one_of_littleHolder
    {α u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Ioc 0 T, ∀ η > 0, ∃ δ > 0,
      ∀ r ∈ Icc (t - δ) t, ‖h t - h r‖ ≤ η * (t - r) ^ α) :
    ∀ t ∈ Icc 0 T, (h t).re < 1 := by
  intro t ht
  by_contra hnot
  obtain ⟨s, hs, hsvalue, hsmax⟩ := exists_first_barrier_contact ht.1
    (fun r => (h r).re)
    (Complex.continuous_re.comp_continuousOn
      (hh.1.mono (Icc_subset_Icc le_rfl ht.2)))
    (by rw [hh.zero hT]; norm_num) (le_of_not_gt hnot)
  have hsT : s ≤ T := hs.2.trans ht.2
  have hstrict := re_force_pos_at_positive_max_of_littleHolder hα hα1 hs.1
    h (fun r => riccati (-2) 1 (-1 / 2) 1 u (h r))
    (hh.1.mono (Icc_subset_Icc le_rfl hsT))
    (hh.force_continuous.mono (Icc_subset_Icc le_rfl hsT))
    (fun r hr => hh.2 r ⟨hr.1, hr.2.trans hsT⟩)
    (by intro r hr; simpa only [hsvalue] using hsmax r hr)
    (by simpa only [hsvalue] using (zero_lt_one : (0 : ℝ) < 1))
    (hsmall s ⟨hs.1, hsT⟩)
  have hrepr : h s = 1 + Complex.I * ((h s).im : ℂ) := by
    apply Complex.ext
    · simpa using hsvalue
    · simp
  rw [hrepr] at hstrict
  have hforce := concrete_riccati_halfplane_neg u (h s).im
  linarith

/-- A fixed complex linear functional commutes with the actual fractional
integral. This lets the maximum principle control a norm at first contact. -/
theorem fractionalIntegral_const_mul (α t : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    fractionalIntegral α (fun r => c * f r) t = c * fractionalIntegral α f t := by
  unfold fractionalIntegral fractionalIntegralRaw
  simp only [Complex.real_smul, Complex.ofReal_inv]
  calc
    _ = ((Real.Gamma α)⁻¹ : ℂ) *
        (c * ∫ r in 0..t, (fractionalKernel α t r : ℂ) * f r) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      ring
    _ = _ := by ring

theorem littleHolder_const_mul {α t : ℝ} {v : ℝ → ℂ}
    (hsmall : ∀ η > 0, ∃ δ > 0, ∀ r ∈ Icc (t - δ) t,
      ‖v t - v r‖ ≤ η * (t - r) ^ α) (c : ℂ) :
    ∀ η > 0, ∃ δ > 0, ∀ r ∈ Icc (t - δ) t,
      ‖c * v t - c * v r‖ ≤ η * (t - r) ^ α := by
  intro η hη
  by_cases hc : c = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro r hr
    simp only [hc, zero_mul, sub_self, norm_zero]
    exact mul_nonneg hη.le (Real.rpow_nonneg (sub_nonneg.mpr hr.2) _)
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨δ, hδ, hbound⟩ := hsmall (η / ‖c‖) (div_pos hη hcnorm)
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ ‖c‖ * (η / ‖c‖ * (t - r) ^ α) :=
      mul_le_mul_of_nonneg_left (hbound r hr) hcnorm.le
    _ = _ := by field_simp

/-- A finite-frequency norm barrier for the concrete solution, conditional
on the same explicit local regularity as the real-part barrier. The
maximum principle is applied to a fixed linear projection, so no chain
rule for a fractional derivative of the squared norm is assumed. -/
theorem IsRiccatiSolution.concrete_norm_lt_band_of_littleHolder
    {α u T U : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hu : |u| ≤ U)
    (hsmall : ∀ t ∈ Ioc 0 T, ∀ η > 0, ∃ δ > 0,
      ∀ r ∈ Icc (t - δ) t, ‖h t - h r‖ ≤ η * (t - r) ^ α) :
    ∀ t ∈ Icc 0 T, ‖h t‖ < bandConstantBound (-2) U + 1 := by
  let A := bandConstantBound (-2) U
  have hq : ‖riccatiConstant (-2) u‖ ≤ A := riccatiConstant_norm_le hu
  have hA : 0 ≤ A := (norm_nonneg _).trans hq
  have hB : 0 < A + 1 := by linarith
  have hre := hh.concrete_re_lt_one_of_littleHolder hα hα1 hT hsmall
  intro t ht
  by_contra hnot
  obtain ⟨s, hs, hsvalue, hsmax⟩ := exists_first_barrier_contact ht.1
    (fun r => ‖h r‖) (hh.1.norm.mono (Icc_subset_Icc le_rfl ht.2))
    (by rw [hh.zero hT, norm_zero]; exact hB) (le_of_not_gt hnot)
  have hsT : s ≤ T := hs.2.trans ht.2
  have hnormsq : (star (h s) * h s).re = ‖h s‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.mul_re, Complex.normSq_apply]
  have hmaximum : ∀ r ∈ Icc 0 s,
      (star (h s) * h r).re ≤ (star (h s) * h s).re := by
    intro r hr
    calc
      _ ≤ ‖star (h s) * h r‖ := Complex.re_le_norm _
      _ = ‖h s‖ * ‖h r‖ := by simp
      _ ≤ ‖h s‖ * (A + 1) := mul_le_mul_of_nonneg_left (hsmax r hr) (norm_nonneg _)
      _ = _ := by rw [hnormsq, hsvalue]; ring
  have hpositive : 0 < (star (h s) * h s).re := by
    rw [hnormsq, hsvalue]
    exact pow_pos hB _
  have hstrict := re_force_pos_at_positive_max_of_littleHolder hα hα1 hs.1
    (fun r => star (h s) * h r)
    (fun r => star (h s) * riccati (-2) 1 (-1 / 2) 1 u (h r))
    (continuousOn_const.mul (hh.1.mono (Icc_subset_Icc le_rfl hsT)))
    (continuousOn_const.mul (hh.force_continuous.mono (Icc_subset_Icc le_rfl hsT)))
    (by intro r hr; rw [fractionalIntegral_const_mul, ← hh.2 r ⟨hr.1, hr.2.trans hsT⟩])
    hmaximum hpositive (littleHolder_const_mul (hsmall s ⟨hs.1, hsT⟩) (star (h s)))
  have hradial := concrete_riccati_radial_bound u (h s) (hre s ⟨hs.1.le, hsT⟩).le
  have hqmul := mul_le_mul_of_nonneg_right hq (norm_nonneg (h s))
  rw [hsvalue] at hradial hqmul
  nlinarith [sq_nonneg A]

/-- The actual fractional equation transfers the proved local regularity
of the fractional integral to its solution. -/
theorem fractionalEquation_littleHolder_left {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t)
    (v f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t))
    (heq : ∀ r ∈ Icc 0 t, v r = fractionalIntegral α f r) :
    ∀ η > 0, ∃ δ > 0, ∀ r ∈ Icc (t - δ) t,
      ‖v t - v r‖ ≤ η * (t - r) ^ α := by
  intro η hη
  obtain ⟨δ, hδ, hδt, hbound⟩ :=
    fractionalIntegral_littleHolder_left hα hα1 ht f hf η hη
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  rcases hr.2.eq_or_lt with rfl | hrt
  · simp [Real.zero_rpow hα.ne']
  · rw [heq t ⟨ht.le, le_rfl⟩, heq r ⟨hr0, hrt.le⟩]
    exact hbound r hr0 hr.1 hrt

/-- The strict maximum principle for an actual fractional equation with
continuous forcing. Its local little-Hölder regularity is derived rather
than assumed. -/
theorem re_force_pos_at_positive_max {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t)
    (v f : ℝ → ℂ) (hv : ContinuousOn v (Icc 0 t))
    (hf : ContinuousOn f (Icc 0 t))
    (heq : ∀ r ∈ Icc 0 t, v r = fractionalIntegral α f r)
    (hmax : ∀ r ∈ Icc 0 t, (v r).re ≤ (v t).re)
    (hpos : 0 < (v t).re) :
    0 < (f t).re :=
  re_force_pos_at_positive_max_of_littleHolder hα hα1 ht v f hv hf heq hmax hpos
    (fractionalEquation_littleHolder_left hα hα1 ht v f hf heq)

theorem IsRiccatiSolution.littleHolder_left {α R gamma rho nu u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hα : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Ioc 0 T, ∀ η > 0, ∃ δ > 0, ∀ r ∈ Icc (t - δ) t,
      ‖h t - h r‖ ≤ η * (t - r) ^ α := by
  intro t ht
  exact fractionalEquation_littleHolder_left hα hα1 ht.1 h
    (fun r => riccati R gamma rho nu u (h r))
    (hh.force_continuous.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => hh.2 r ⟨hr.1, hr.2.trans ht.2⟩)

/-- Every existing solution of the concrete fractional Riccati equation
stays strictly to the left of `Re z = 1`, at every finite maturity. -/
theorem IsRiccatiSolution.concrete_re_lt_one {α u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, (h t).re < 1 :=
  hh.concrete_re_lt_one_of_littleHolder hα hα1 hT (hh.littleHolder_left hα hα1)

/-- Every existing solution has an explicit norm bound uniform on a
finite frequency band and every finite maturity. Existence remains a
separate assertion. -/
theorem IsRiccatiSolution.concrete_norm_lt_band {α u T U : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hu : |u| ≤ U) :
    ∀ t ∈ Icc 0 T, ‖h t‖ < bandConstantBound (-2) U + 1 :=
  hh.concrete_norm_lt_band_of_littleHolder hα hα1 hT hu (hh.littleHolder_left hα hα1)

end RoughHeston

#print axioms RoughHeston.exists_first_barrier_contact
#print axioms RoughHeston.IsRiccatiSolution.concrete_re_lt_one_of_littleHolder
#print axioms RoughHeston.fractionalIntegral_const_mul
#print axioms RoughHeston.littleHolder_const_mul
#print axioms RoughHeston.IsRiccatiSolution.concrete_norm_lt_band_of_littleHolder
#print axioms RoughHeston.fractionalEquation_littleHolder_left
#print axioms RoughHeston.re_force_pos_at_positive_max
#print axioms RoughHeston.IsRiccatiSolution.concrete_re_lt_one
#print axioms RoughHeston.IsRiccatiSolution.concrete_norm_lt_band
