module

public import RoughHeston.GlobalVolterra
public import RoughHeston.InvariantRegion
public import RoughHeston.Cutoff
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Global deterministic existence for the concrete fractional Riccati equation

A globally Lipschitz cutoff equation has a solution on every finite
maturity interval. A first norm contact would give a solution of the
original equation on the complete preceding interval, contradicting its
strict invariant-region bound. The cutoff therefore never activates.
-/

@[expose] public section

noncomputable section

open Set

namespace RoughHeston

/-- A globally Lipschitz extension of the concrete force from its explicit
invariant ball gives an actual solution of the original equation on any
finite maturity interval. -/
theorem exists_concrete_global_riccati_of_cutoff {α u T U L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hu : |u| ≤ U) (hL : 0 ≤ L)
    (F : ℂ → ℂ) (hF : Continuous F)
    (hLip : ∀ z w : ℂ, ‖F z - F w‖ ≤ L * ‖z - w‖)
    (hid : ∀ z : ℂ, ‖z‖ ≤ bandConstantBound (-2) U + 1 →
      F z = riccati (-2) 1 (-1 / 2) 1 u z) :
    ∃ h : ℝ → ℂ, IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h ∧
      (∀ t ∈ Icc 0 T, ‖h t‖ < bandConstantBound (-2) U + 1) ∧
      (∀ t ∈ Icc 0 T, (h t).re < 1) := by
  obtain ⟨h, hc, heq⟩ := exists_fractionalVolterraSolution_global_lipschitz
    hα hα1 hT hL F hF hLip
  have hq := riccatiConstant_norm_le (R := -2) hu
  have hQ : 0 < bandConstantBound (-2) U + 1 := by
    have hA := (norm_nonneg _).trans hq
    linarith
  have hz : h 0 = 0 := by
    rw [heq 0 ⟨le_rfl, hT⟩]
    simp [fractionalIntegral, fractionalIntegralRaw]
  have hbound : ∀ t ∈ Icc 0 T, ‖h t‖ < bandConstantBound (-2) U + 1 := by
    intro t ht
    by_contra hnot
    obtain ⟨s, hs, hsvalue, hsmax⟩ := exists_first_barrier_contact ht.1
      (fun r => ‖h r‖) hc.norm.continuousOn
      (by rw [hz, norm_zero]; exact hQ) (le_of_not_gt hnot)
    have hsT : s ≤ T := hs.2.trans ht.2
    have hactual : IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u s h := by
      refine ⟨hc.continuousOn, ?_⟩
      intro r hr
      rw [heq r ⟨hr.1, hr.2.trans hsT⟩]
      exact fractionalIntegral_congr_on hr.1
        (fun x hx => hid (h x) (hsmax x ⟨hx.1, hx.2.trans hr.2⟩))
    have hstrict := hactual.concrete_norm_lt_band hα hα1 hs.1.le hu s ⟨hs.1.le, le_rfl⟩
    rw [hsvalue] at hstrict
    exact (lt_irrefl _) hstrict
  have hactual : IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h := by
    refine ⟨hc.continuousOn, ?_⟩
    intro t ht
    rw [heq t ht]
    exact fractionalIntegral_congr_on ht.1
      (fun r hr => hid (h r) (hbound r ⟨hr.1, hr.2.trans ht.2⟩).le)
  exact ⟨h, hactual, hbound, hactual.concrete_re_lt_one hα hα1 hT⟩

/-- The concrete fractional Riccati equation has an actual solution on
every finite nonnegative maturity interval. Its norm bound is uniform
over any prescribed finite frequency band, and its real part stays
strictly below one. All cutoff hypotheses are discharged. -/
theorem exists_concrete_global_riccati {α u T U : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hu : |u| ≤ U) :
    ∃ h : ℝ → ℂ, IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T h ∧
      (∀ t ∈ Icc 0 T, ‖h t‖ < bandConstantBound (-2) U + 1) ∧
      (∀ t ∈ Icc 0 T, (h t).re < 1) := by
  have hU : 0 ≤ U := (abs_nonneg u).trans hu
  have hq := riccatiConstant_norm_le (R := -2) hu
  have hQ : 0 ≤ bandConstantBound (-2) U + 1 := by
    have hA := (norm_nonneg _).trans hq
    linarith
  exact exists_concrete_global_riccati_of_cutoff hα hα1 hT hu
    (cutoffRiccatiLipschitz_nonneg hQ hU)
    (cutoffRiccati (bandConstantBound (-2) U + 1) (-2) 1 (-1 / 2) 1 u)
    (continuous_cutoffRiccati _ _ _ _ _ _)
    (cutoffRiccati_norm_sub_le hQ hu)
    (fun _ hz => cutoffRiccati_eq_of_norm_le hQ hz)

/-- A single family of actual solutions exists at every real frequency.
The finite-band bound applies to that same family for every band. The
choice is a deterministic existence statement, not a stochastic transform
identity or a pricing formula. -/
theorem exists_concrete_global_riccati_family {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) :
    ∃ h : ℝ → ℝ → ℂ,
      (∀ u : ℝ, IsRiccatiSolution α (-2) 1 (-1 / 2) 1 u T (h u)) ∧
      (∀ u : ℝ, ∀ t ∈ Icc 0 T, (h u t).re < 1) ∧
      (∀ U u : ℝ, |u| ≤ U → ∀ t ∈ Icc 0 T,
        ‖h u t‖ < bandConstantBound (-2) U + 1) := by
  classical
  have hex (u : ℝ) := exists_concrete_global_riccati hα hα1 hT (le_refl |u|)
  choose h hsolution _hbound hre using hex
  refine ⟨h, hsolution, hre, ?_⟩
  intro U u hu
  exact (hsolution u).concrete_norm_lt_band hα hα1 hT hu

end RoughHeston

#print axioms RoughHeston.exists_concrete_global_riccati_of_cutoff
#print axioms RoughHeston.exists_concrete_global_riccati
#print axioms RoughHeston.exists_concrete_global_riccati_family
