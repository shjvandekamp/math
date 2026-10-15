module

public import RoughHeston.Volterra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local existence for the actual fractional Volterra equation

The operator acts on continuous paths over the full maturity interval. Its
definition uses the Lebesgue fractional integral, including the initial-time
singularity. The closed-ball hypotheses provide an invariant complete metric
space and a strict contraction.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace RoughHeston

/-- Continuous paths on the prescribed maturity interval, with the sup norm. -/
abbrev VolterraPath (T : ℝ) := C(Icc (0 : ℝ) T, ℂ)

/-- A path is extended by clamping time to its prescribed interval. -/
def extendVolterraPath {T : ℝ} (hT : 0 ≤ T) (h : VolterraPath T) (t : ℝ) : ℂ :=
  h (projIcc 0 T hT t)

theorem continuous_extendVolterraPath {T : ℝ} (hT : 0 ≤ T) (h : VolterraPath T) :
    Continuous (extendVolterraPath hT h) := h.continuous.comp continuous_projIcc

theorem extendVolterraPath_on {T : ℝ} (hT : 0 ≤ T) (h : VolterraPath T)
    {t : ℝ} (ht : t ∈ Icc 0 T) : extendVolterraPath hT h t = h ⟨t, ht⟩ := by
  simp [extendVolterraPath, projIcc_of_mem _ ht]

theorem norm_extendVolterraPath_le {T : ℝ} (hT : 0 ≤ T) (h : VolterraPath T) (t : ℝ) :
    ‖extendVolterraPath hT h t‖ ≤ ‖h‖ := h.norm_coe_le_norm _

/-- Continuity of the actual fractional integral follows from the previously
proved Hölder estimate, rather than being postulated as an operator property. -/
theorem continuousOn_fractionalIntegral {α T M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hM : 0 ≤ M) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) :
    ContinuousOn (fractionalIntegral α f) (Icc 0 T) := by
  let C : ℝ≥0 := ⟨2 * M / Real.Gamma (α + 1),
    div_nonneg (mul_nonneg (by norm_num) hM)
      (Real.Gamma_pos_of_pos (by linarith)).le⟩
  have hd : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      dist (fractionalIntegral α f s) (fractionalIntegral α f t) ≤
        (C : ℝ) * dist s t ^ α := by
    intro s hs t ht
    change dist (fractionalIntegral α f s) (fractionalIntegral α f t) ≤
      (2 * M / Real.Gamma (α + 1)) * dist s t ^ α
    rw [dist_eq_norm, Real.dist_eq]
    rcases le_total s t with hst | hts
    · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      exact norm_fractionalIntegral_sub_le_on hα hα1 hs.1 hst ht.2 f hf hbound
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact norm_fractionalIntegral_sub_le_on hα hα1 ht.1 hts hs.2 f hf hbound
  have hh : HolderOnWith C ⟨α, hα.le⟩ (fractionalIntegral α f) (Icc 0 T) := by
    intro s hs t ht
    have he := ENNReal.ofReal_le_ofReal (hd s hs t ht)
    change edist (fractionalIntegral α f s) (fractionalIntegral α f t) ≤
      (C : ℝ≥0∞) * edist s t ^ α
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using he
  exact hh.continuousOn hα

def volterraForcePath {T : ℝ} (F : ℂ → ℂ) (hF : Continuous F)
    (h : VolterraPath T) : VolterraPath T := ⟨fun t => F (h t), hF.comp h.continuous⟩

/-- The actual normalized Volterra integral operator on continuous paths. -/
def fractionalVolterraMap {α T : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (F : ℂ → ℂ) (hF : Continuous F) (h : VolterraPath T) : VolterraPath T where
  toFun t := fractionalIntegral α (fun s => F (extendVolterraPath hT h s)) t
  continuous_toFun := by
    apply (continuousOn_iff_continuous_domRestrict
      (f := fractionalIntegral α (fun s => F (extendVolterraPath hT h s)))
      (s := Icc 0 T)).mp
    apply continuousOn_fractionalIntegral hα hα1 (norm_nonneg (volterraForcePath F hF h))
      (fun s => F (extendVolterraPath hT h s))
      (hF.comp (continuous_extendVolterraPath hT h)).continuousOn
    intro t _
    exact (volterraForcePath F hF h).norm_coe_le_norm (projIcc 0 T hT t)

/-- The actual Volterra map preserves the closed supnorm ball under the
explicit fractional-kernel mass condition. -/
theorem fractionalVolterraMap_mapsTo_ball {α T Q M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ Q → ‖F z‖ ≤ M)
    (hself : M * T ^ α / Real.Gamma (α + 1) ≤ Q) :
    MapsTo (fractionalVolterraMap hα hα1 hT F hF)
      (Metric.closedBall 0 Q) (Metric.closedBall 0 Q) := by
  intro h hh
  rw [mem_closedBall_zero_iff] at hh ⊢
  apply (ContinuousMap.norm_le _ hQ).mpr
  intro t
  have hb : ∀ s ∈ Icc 0 T, ‖F (extendVolterraPath hT h s)‖ ≤ M := by
    intro s _
    exact hbound _ ((norm_extendVolterraPath_le hT h s).trans hh)
  have hn := norm_fractionalIntegral_le_on hα t.property.1 t.property.2
    (fun s => F (extendVolterraPath hT h s))
    (hF.comp (continuous_extendVolterraPath hT h)).continuousOn hb
  apply hn.trans
  apply le_trans _ hself
  apply div_le_div_of_nonneg_right _ (Real.Gamma_pos_of_pos (by linarith)).le
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow t.property.1 t.property.2 hα.le) hM

/-- Linearity in the continuous input is proved directly from the Bochner
interval integral; it is used to establish the operator contraction. -/
theorem fractionalIntegral_sub_inputs {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (f g : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 t)) (hg : ContinuousOn g (Icc 0 t)) :
    fractionalIntegral α (fun s => f s - g s) t =
      fractionalIntegral α f t - fractionalIntegral α g t := by
  unfold fractionalIntegral fractionalIntegralRaw
  simp_rw [smul_sub]
  rw [intervalIntegral.integral_sub
    (fractionalIntegral_integrable hα ht f hf) (fractionalIntegral_integrable hα ht g hg),
    smul_sub]

theorem fractionalVolterraMap_dist_le {α T Q L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q → ‖F z - F w‖ ≤ L * ‖z - w‖)
    (h g : VolterraPath T) (hh : ‖h‖ ≤ Q) (hg : ‖g‖ ≤ Q) :
    dist (fractionalVolterraMap hα hα1 hT F hF h)
      (fractionalVolterraMap hα hα1 hT F hF g) ≤
      (T ^ α / Real.Gamma (α + 1) * L) * dist h g := by
  have hgamma := (Real.Gamma_pos_of_pos (by linarith : 0 < α + 1)).le
  have hc : 0 ≤ T ^ α / Real.Gamma (α + 1) * L :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hT _) hgamma) hL
  apply (ContinuousMap.dist_le (mul_nonneg hc dist_nonneg)).mpr
  intro t
  have hfc : Continuous (fun s => F (extendVolterraPath hT h s)) :=
    hF.comp (continuous_extendVolterraPath hT h)
  have hgc : Continuous (fun s => F (extendVolterraPath hT g s)) :=
    hF.comp (continuous_extendVolterraPath hT g)
  have hb : ∀ s ∈ Icc 0 T,
      ‖F (extendVolterraPath hT h s) - F (extendVolterraPath hT g s)‖ ≤ L * dist h g := by
    intro s _
    apply (hlip _ _ ((norm_extendVolterraPath_le hT h s).trans hh)
      ((norm_extendVolterraPath_le hT g s).trans hg)).trans
    apply mul_le_mul_of_nonneg_left _ hL
    simpa only [dist_eq_norm, extendVolterraPath] using
      (ContinuousMap.dist_apply_le_dist (f := h) (g := g) (projIcc 0 T hT s))
  rw [dist_eq_norm]
  change ‖fractionalIntegral α (fun s => F (extendVolterraPath hT h s)) t -
    fractionalIntegral α (fun s => F (extendVolterraPath hT g s)) t‖ ≤ _
  rw [← fractionalIntegral_sub_inputs hα t.property.1 _ _ hfc.continuousOn hgc.continuousOn]
  apply (norm_fractionalIntegral_le_on hα t.property.1 t.property.2 _
    (hfc.sub hgc).continuousOn hb).trans
  calc
    _ ≤ (L * dist h g) * T ^ α / Real.Gamma (α + 1) := by
      apply div_le_div_of_nonneg_right _ hgamma
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow t.property.1 t.property.2 hα.le) (mul_nonneg hL dist_nonneg)
    _ = _ := by ring

/-- Banach's theorem produces a path satisfying the actual integral equation.
The input bounds are solely bounds on the force in the prescribed state ball. -/
theorem exists_fractionalVolterraSolution {α T Q M L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ Q → ‖F z‖ ≤ M)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q → ‖F z - F w‖ ≤ L * ‖z - w‖)
    (hself : M * T ^ α / Real.Gamma (α + 1) ≤ Q)
    (hcontract : T ^ α / Real.Gamma (α + 1) * L < 1) :
    ∃ h : ℝ → ℂ, Continuous h ∧
      (∀ t ∈ Icc 0 T, h t = fractionalIntegral α (fun s => F (h s)) t) ∧
      (∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q) := by
  let op := fractionalVolterraMap hα hα1 hT F hF
  let S : Set (VolterraPath T) := Metric.closedBall 0 Q
  have hmaps : MapsTo op S S :=
    fractionalVolterraMap_mapsTo_ball hα hα1 hT hQ hM F hF hbound hself
  have hc : 0 ≤ T ^ α / Real.Gamma (α + 1) * L :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hT _)
      (Real.Gamma_pos_of_pos (by linarith)).le) hL
  have hcontr : ContractingWith ⟨T ^ α / Real.Gamma (α + 1) * L, hc⟩
      (hmaps.restrict op S S) := by
    refine ⟨hcontract, LipschitzWith.of_dist_le_mul ?_⟩
    intro h g
    exact fractionalVolterraMap_dist_le hα hα1 hT hL F hF hlip h.val g.val
      (mem_closedBall_zero_iff.mp h.property) (mem_closedBall_zero_iff.mp g.property)
  have hzero : (0 : VolterraPath T) ∈ S := by
    exact mem_closedBall_zero_iff.mpr (by simpa using hQ)
  obtain ⟨h, hh, hfixed, _⟩ := ContractingWith.exists_fixedPoint'
    (show IsComplete S from Metric.isClosed_closedBall.isComplete) hmaps hcontr hzero
    (edist_ne_top (0 : VolterraPath T) (op 0))
  refine ⟨extendVolterraPath hT h, continuous_extendVolterraPath hT h, ?_, ?_⟩
  · intro t ht
    have heq := congrArg (fun v : VolterraPath T => v ⟨t, ht⟩) hfixed
    rw [extendVolterraPath_on hT h ht]
    exact heq.symm
  · intro t _
    exact (norm_extendVolterraPath_le hT h t).trans (mem_closedBall_zero_iff.mp hh)

/-- Local existence for the concrete fractional Riccati equation used by the
pricing transform. Neither a solution nor a numerical defect is assumed. -/
theorem exists_riccatiSolution {α R gamma rho nu u T Q M L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ Q → ‖riccati R gamma rho nu u z‖ ≤ M)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (hself : M * T ^ α / Real.Gamma (α + 1) ≤ Q)
    (hcontract : T ^ α / Real.Gamma (α + 1) * L < 1) :
    ∃ h : ℝ → ℂ, IsRiccatiSolution α R gamma rho nu u T h ∧
      ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q := by
  obtain ⟨h, hc, heq, hb⟩ := exists_fractionalVolterraSolution hα hα1 hT hQ hM hL
    (riccati R gamma rho nu u) (continuous_riccati R gamma rho nu u) hbound hlip hself hcontract
  exact ⟨h, ⟨hc.continuousOn, heq⟩, hb⟩

/-- Restriction of an ordinary function with interval continuity to a path. -/
def restrictVolterraPath {T : ℝ} (h : ℝ → ℂ) (hh : ContinuousOn h (Icc 0 T)) :
    VolterraPath T := ⟨fun t => h t, hh.domRestrict⟩

private theorem fractionalIntegral_congr_on {α t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℂ}
    (hfg : ∀ s ∈ Icc 0 t, f s = g s) : fractionalIntegral α f t = fractionalIntegral α g t := by
  unfold fractionalIntegral fractionalIntegralRaw
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [hfg s hs]

theorem fractionalVolterraMap_fixed_of_solution {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (F : ℂ → ℂ) (hF : Continuous F)
    (h : ℝ → ℂ) (hh : ContinuousOn h (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, h t = fractionalIntegral α (fun s => F (h s)) t) :
    fractionalVolterraMap hα hα1 hT F hF (restrictVolterraPath h hh) =
      restrictVolterraPath h hh := by
  apply ContinuousMap.ext
  intro t
  change fractionalIntegral α (fun s => F (extendVolterraPath hT (restrictVolterraPath h hh) s)) t = h t
  rw [heq t t.property]
  apply fractionalIntegral_congr_on t.property.1
  intro s hs
  rw [extendVolterraPath_on hT _ ⟨hs.1, hs.2.trans t.property.2⟩]
  rfl

/-- Any two actual continuous solutions staying in the prescribed ball agree
on the whole interval whenever the explicit contraction condition holds. -/
theorem fractionalVolterraSolution_unique {α T Q L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q → ‖F z - F w‖ ≤ L * ‖z - w‖)
    (hcontract : T ^ α / Real.Gamma (α + 1) * L < 1)
    (h g : ℝ → ℂ) (hh : ContinuousOn h (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hheq : ∀ t ∈ Icc 0 T, h t = fractionalIntegral α (fun s => F (h s)) t)
    (hgeq : ∀ t ∈ Icc 0 T, g t = fractionalIntegral α (fun s => F (g s)) t)
    (hhbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q) (hgbound : ∀ t ∈ Icc 0 T, ‖g t‖ ≤ Q) :
    EqOn h g (Icc 0 T) := by
  have hhNorm : ‖restrictVolterraPath h hh‖ ≤ Q :=
    (ContinuousMap.norm_le _ hQ).mpr (fun t => hhbound t t.property)
  have hgNorm : ‖restrictVolterraPath g hg‖ ≤ Q :=
    (ContinuousMap.norm_le _ hQ).mpr (fun t => hgbound t t.property)
  have hd := fractionalVolterraMap_dist_le hα hα1 hT hL F hF hlip
    (restrictVolterraPath h hh) (restrictVolterraPath g hg) hhNorm hgNorm
  rw [fractionalVolterraMap_fixed_of_solution hα hα1 hT F hF h hh hheq,
    fractionalVolterraMap_fixed_of_solution hα hα1 hT F hF g hg hgeq] at hd
  have hd0 : dist (restrictVolterraPath h hh) (restrictVolterraPath g hg) = 0 := by
    nlinarith [dist_nonneg (x := restrictVolterraPath h hh) (y := restrictVolterraPath g hg)]
  have heq := dist_eq_zero.mp hd0
  intro t ht
  exact congrArg (fun v : VolterraPath T => v ⟨t, ht⟩) heq

theorem IsRiccatiSolution.unique_in_ball {α R gamma rho nu u T Q L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (hcontract : T ^ α / Real.Gamma (α + 1) * L < 1)
    {h g : ℝ → ℂ} (hh : IsRiccatiSolution α R gamma rho nu u T h)
    (hg : IsRiccatiSolution α R gamma rho nu u T g)
    (hhbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q) (hgbound : ∀ t ∈ Icc 0 T, ‖g t‖ ≤ Q) :
    EqOn h g (Icc 0 T) :=
  fractionalVolterraSolution_unique hα hα1 hT hQ hL
    (riccati R gamma rho nu u) (continuous_riccati R gamma rho nu u)
    hlip hcontract h g hh.1 hg.1 hh.2 hg.2 hhbound hgbound

/-- Finite-band local existence with the explicit polynomial force constants.
The same hypotheses provide a solution at every frequency in `[-U,U]`. -/
theorem exists_riccatiSolution_on_band {α R gamma rho nu T Q U : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hU : 0 ≤ U)
    (hself : (bandConstantBound R U + bandLinearBound R gamma rho nu U * Q +
      (gamma * nu) ^ 2 / 2 * Q ^ 2) * T ^ α / Real.Gamma (α + 1) ≤ Q)
    (hcontract : T ^ α / Real.Gamma (α + 1) *
      (bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * Q) < 1)
    {u : ℝ} (hu : |u| ≤ U) :
    ∃ h : ℝ → ℂ, IsRiccatiSolution α R gamma rho nu u T h ∧
      ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q := by
  have hM : 0 ≤ bandConstantBound R U + bandLinearBound R gamma rho nu U * Q +
      (gamma * nu) ^ 2 / 2 * Q ^ 2 := by
    unfold bandConstantBound bandLinearBound
    positivity
  have hL : 0 ≤ bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * Q := by
    unfold bandLinearBound
    positivity
  exact exists_riccatiSolution hα hα1 hT hQ hM hL
    (fun _ hz => riccati_band_norm_le hu hQ hz)
    (fun _ _ hz hw => riccati_band_lipschitz hu hz hw) hself hcontract

end RoughHeston

#print axioms RoughHeston.fractionalVolterraMap
#print axioms RoughHeston.exists_fractionalVolterraSolution
#print axioms RoughHeston.exists_riccatiSolution
#print axioms RoughHeston.IsRiccatiSolution.unique_in_ball
#print axioms RoughHeston.exists_riccatiSolution_on_band
