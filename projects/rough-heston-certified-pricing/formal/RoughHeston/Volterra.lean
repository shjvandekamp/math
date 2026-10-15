module

public import RoughHeston.FractionalIntegral
public import RoughHeston.RiccatiBounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The deterministic fractional Riccati equation and its regularity

`IsRiccatiSolution` states the actual integral equation and continuity. It
does not include existence, a bound, or a numerical error as a field.
-/

@[expose] public section
noncomputable section
open Set

namespace RoughHeston

def IsRiccatiSolution (alpha R gamma rho nu u T : ℝ) (h : ℝ → ℂ) : Prop :=
  ContinuousOn h (Icc 0 T) ∧
  ∀ t ∈ Icc 0 T, h t = fractionalIntegral alpha (fun s => riccati R gamma rho nu u (h s)) t

theorem continuous_riccati (R gamma rho nu u : ℝ) :
    Continuous (riccati R gamma rho nu u) := by
  unfold riccati
  fun_prop

theorem IsRiccatiSolution.zero {alpha R gamma rho nu u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u T h) (hT : 0 ≤ T) : h 0 = 0 := by
  rw [hh.2 0 ⟨le_rfl, hT⟩]
  simp [fractionalIntegral, fractionalIntegralRaw]

theorem IsRiccatiSolution.force_continuous {alpha R gamma rho nu u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u T h) :
    ContinuousOn (fun t => riccati R gamma rho nu u (h t)) (Icc 0 T) :=
  (continuous_riccati R gamma rho nu u).comp_continuousOn hh.1

/-- Regularity is derived from the actual Volterra equation, including at
zero. No ordinary time derivative is assumed. -/
theorem IsRiccatiSolution.holder {alpha R gamma rho nu u T M : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u T h)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hbound : ∀ t ∈ Icc 0 T, ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖h t - h s‖ ≤ 2 * M / Real.Gamma (alpha + 1) * (t - s) ^ alpha := by
  rw [hh.2 t ⟨hs.trans hst, htT⟩, hh.2 s ⟨hs, hst.trans htT⟩]
  exact norm_fractionalIntegral_sub_le_on ha ha1 hs hst htT
    (fun r => riccati R gamma rho nu u (h r)) hh.force_continuous hbound

theorem IsRiccatiSolution.force_holder {alpha R gamma rho nu u T M L Q : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u T h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hL : 0 ≤ L)
    (hbound : ∀ t ∈ Icc 0 T, ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    (hhbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖riccati R gamma rho nu u (h t) - riccati R gamma rho nu u (h s)‖ ≤
      L * (2 * M / Real.Gamma (alpha + 1) * (t - s) ^ alpha) :=
  (hlip _ _ (hhbound t ⟨hs.trans hst, htT⟩) (hhbound s ⟨hs, hst.trans htT⟩)).trans
    (mul_le_mul_of_nonneg_left (hh.holder ha ha1 hbound hs hst htT) hL)

end RoughHeston
