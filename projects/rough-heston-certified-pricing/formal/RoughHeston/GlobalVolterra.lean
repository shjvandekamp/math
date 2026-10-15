module

public import RoughHeston.VolterraExistence
public import RoughHeston.WeightedKernel
public import RoughHeston.MeshConditions
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global-in-time existence for a globally Lipschitz Volterra force

An exponentially rescaled continuous-path operator is a contraction on any
finite maturity interval. The original full-history integral is retained.
The quadratic Riccati force is not globally Lipschitz; applying this theorem
to it requires a cutoff and a proof that the cutoff never activates.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory

namespace RoughHeston

theorem norm_fractionalIntegral_exp_bound {alpha rate t M : ℝ}
    (ha : 0 < alpha) (hr : 0 < rate) (ht : 0 ≤ t) (hM : 0 ≤ M)
    (f : ℝ → ℂ) (_hf : ContinuousOn f (Icc 0 t))
    (hb : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ M * Real.exp (rate * s)) :
    Real.exp (-rate * t) * ‖fractionalIntegral alpha f t‖ ≤ rate ^ (-alpha) * M := by
  have hk := intervalIntegrable_fractionalKernel ha t 0 t
  have hmajor : IntervalIntegrable
      (fun s => fractionalKernel alpha t s * (M * Real.exp (rate * s))) volume 0 t :=
    hk.mul_continuousOn (by fun_prop)
  have hnorm : ‖∫ s in 0..t, fractionalKernel alpha t s • f s‖ ≤
      ∫ s in 0..t, fractionalKernel alpha t s * (M * Real.exp (rate * s)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht _ hmajor
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fractionalKernel_nonneg hs.2)]
      exact mul_le_mul_of_nonneg_left (hb s ⟨hs.1.le, hs.2⟩) (fractionalKernel_nonneg hs.2))
  have hidentity : Real.exp (-rate * t) * (Real.Gamma alpha)⁻¹ *
      (∫ s in 0..t, fractionalKernel alpha t s * (M * Real.exp (rate * s))) =
      weightedKernelMass alpha rate t * M := by
    unfold weightedKernelMass weightedFractionalKernel
    rw [← intervalIntegral.integral_const_mul]
    conv_rhs => rw [mul_assoc, ← intervalIntegral.integral_mul_const]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hexp : Real.exp (-rate * t) * Real.exp (rate * s) =
        Real.exp (-rate * (t - s)) := by rw [← Real.exp_add]; congr 1; ring
    dsimp only
    calc
      _ = (Real.Gamma alpha)⁻¹ * (fractionalKernel alpha t s *
          (Real.exp (-rate * t) * Real.exp (rate * s))) * M := by ring
      _ = _ := by rw [hexp]; ring
  unfold fractionalIntegral fractionalIntegralRaw
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos ha)).le, ← mul_assoc]
  calc
    _ ≤ Real.exp (-rate * t) * (Real.Gamma alpha)⁻¹ *
        (∫ s in 0..t, fractionalKernel alpha t s * (M * Real.exp (rate * s))) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity [Real.Gamma_pos_of_pos ha])
    _ = weightedKernelMass alpha rate t * M := hidentity
    _ ≤ _ := mul_le_mul_of_nonneg_right (weightedKernelMass_le ha hr ht) hM

/-- Exponential change of variables on the same continuous path space. -/
def scaleVolterraPath {T : ℝ} (rate : ℝ) (h : VolterraPath T) : VolterraPath T where
  toFun t := Real.exp (rate * (t : ℝ)) • h t
  continuous_toFun := by fun_prop

def weightedVolterraMap {alpha T : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (hT : 0 ≤ T) (rate : ℝ) (F : ℂ → ℂ) (hF : Continuous F)
    (h : VolterraPath T) : VolterraPath T :=
  scaleVolterraPath (-rate) (fractionalVolterraMap ha ha1 hT F hF (scaleVolterraPath rate h))

theorem weightedVolterraMap_dist_le {alpha T rate L : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 ≤ T) (hr : 0 < rate) (hL : 0 ≤ L)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hLip : ∀ z w : ℂ, ‖F z - F w‖ ≤ L * ‖z - w‖)
    (h g : VolterraPath T) :
    dist (weightedVolterraMap ha ha1 hT rate F hF h)
      (weightedVolterraMap ha ha1 hT rate F hF g) ≤ (rate ^ (-alpha) * L) * dist h g := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  let fh := fun s => F (extendVolterraPath hT (scaleVolterraPath rate h) s)
  let fg := fun s => F (extendVolterraPath hT (scaleVolterraPath rate g) s)
  have hfc : Continuous fh := hF.comp (continuous_extendVolterraPath hT _)
  have hgc : Continuous fg := hF.comp (continuous_extendVolterraPath hT _)
  have hb : ∀ s ∈ Icc 0 (t : ℝ), ‖fh s - fg s‖ ≤ (L * dist h g) * Real.exp (rate * s) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans t.property.2⟩
    apply (hLip _ _).trans
    rw [extendVolterraPath_on hT _ hsT, extendVolterraPath_on hT _ hsT]
    change L * ‖Real.exp (rate * s) • h ⟨s, hsT⟩ - Real.exp (rate * s) • g ⟨s, hsT⟩‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ L * (Real.exp (rate * s) * dist h g) := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := h) (g := g) ⟨s, hsT⟩
      _ = _ := by ring
  rw [dist_eq_norm]
  change ‖Real.exp (-rate * (t : ℝ)) • fractionalIntegral alpha fh t -
      Real.exp (-rate * (t : ℝ)) • fractionalIntegral alpha fg t‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← fractionalIntegral_sub_inputs ha t.property.1 fh fg hfc.continuousOn hgc.continuousOn]
  have hn := norm_fractionalIntegral_exp_bound ha hr t.property.1 (mul_nonneg hL dist_nonneg)
    (fun s => fh s - fg s) (hfc.sub hgc).continuousOn hb
  simpa only [mul_assoc] using hn

/-- Every continuous globally Lipschitz force has an actual full-history
Volterra solution on every finite nonnegative maturity interval. There is
no smallness condition on `T`. -/
theorem exists_fractionalVolterraSolution_global_lipschitz {alpha T L : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hLip : ∀ z w : ℂ, ‖F z - F w‖ ≤ L * ‖z - w‖) :
    ∃ h : ℝ → ℂ, Continuous h ∧
      ∀ t ∈ Icc 0 T, h t = fractionalIntegral alpha (fun s => F (h s)) t := by
  let rate := continuationRate alpha L
  have hr : 0 < rate := continuationRate_pos alpha L
  have hc : 0 ≤ rate ^ (-alpha) * L := mul_nonneg (Real.rpow_nonneg hr.le _) hL
  have hsmall : rate ^ (-alpha) * L < 1 := by
    have hb := continuationRate_contraction (L := L) ha
    change L * rate ^ (-alpha) ≤ 1 / 8 at hb
    nlinarith
  let op := weightedVolterraMap ha ha1 hT rate F hF
  have hcontr : ContractingWith ⟨rate ^ (-alpha) * L, hc⟩ op := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
    exact fun h g => weightedVolterraMap_dist_le ha ha1 hT hr hL F hF hLip h g
  obtain ⟨x, hfixed, _⟩ := hcontr.exists_fixedPoint (0 : VolterraPath T)
    (edist_ne_top _ _)
  let h := scaleVolterraPath rate x
  refine ⟨extendVolterraPath hT h, continuous_extendVolterraPath hT h, ?_⟩
  intro t ht
  have heq := congrArg (fun v : VolterraPath T => v ⟨t, ht⟩) hfixed
  change Real.exp (-rate * t) •
      fractionalIntegral alpha (fun s => F (extendVolterraPath hT h s)) t = x ⟨t, ht⟩ at heq
  rw [extendVolterraPath_on hT h ht]
  change Real.exp (rate * t) • x ⟨t, ht⟩ = _
  rw [← heq, smul_smul]
  have he : Real.exp (rate * t) * Real.exp (-rate * t) = 1 := by
    rw [← Real.exp_add]
    rw [show rate * t + -rate * t = 0 by ring, Real.exp_zero]
  rw [he, one_smul]

end RoughHeston

#print axioms RoughHeston.exists_fractionalVolterraSolution_global_lipschitz
