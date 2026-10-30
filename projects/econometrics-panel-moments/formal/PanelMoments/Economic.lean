import PanelMoments.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# Bridge to the normalized economic specification

Alternative zero has zero common coefficients and zero fixed effect. The table is
`exp (γ[q,r] + Σ k, x[t,k] β[q,k])` for nonbaseline alternatives and one for the baseline.
This module connects the polynomial restriction theorem to that actual specification.
It does not transfer a generic rank claim from free tables to the economic parameter space.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

def economicIndex {Q K : ℕ} (γ : Fin Q → State Q → ℝ)
    (β : Fin Q → Fin K → ℝ) (x : ℕ → Fin K → ℝ) (t : ℕ) (r : State Q) :
    State Q → ℝ :=
  Fin.cons 0 (fun q => γ q r + ∑ k, x t k * β q k)

def economicTable {Q K : ℕ} (γ : Fin Q → State Q → ℝ)
    (β : Fin Q → Fin K → ℝ) (x : ℕ → Fin K → ℝ) : Table Q :=
  fun t r q => Real.exp (economicIndex γ β x t r q)

@[simp] theorem economicTable_baseline {Q K : ℕ} (γ : Fin Q → State Q → ℝ)
    (β : Fin Q → Fin K → ℝ) (x : ℕ → Fin K → ℝ) (t : ℕ) (r : State Q) :
    economicTable γ β x t r 0 = 1 := by
  simp [economicTable, economicIndex]

theorem economicTable_pos {Q K : ℕ} (γ : Fin Q → State Q → ℝ)
    (β : Fin Q → Fin K → ℝ) (x : ℕ → Fin K → ℝ) :
    PositiveTable (economicTable γ β x) := by
  intro t r q
  exact Real.exp_pos _

def expEffects {Q : ℕ} (α : Fin Q → ℝ) : Fin Q → ℝ := fun q => Real.exp (α q)

def additiveEffect {Q : ℕ} (α : Fin Q → ℝ) : State Q → ℝ := Fin.cons 0 α

theorem expEffects_pos {Q : ℕ} (α : Fin Q → ℝ) : PositiveEffects (expEffects α) :=
  fun q => Real.exp_pos (α q)

theorem effect_expEffects {Q : ℕ} (α : Fin Q → ℝ) (q : State Q) :
    effect (expEffects α) q = Real.exp (additiveEffect α q) := by
  refine Fin.cases ?_ (fun i => ?_) q <;> simp [effect, expEffects, additiveEffect]

theorem transition_economic_logit {Q K : ℕ} (γ : Fin Q → State Q → ℝ)
    (β : Fin Q → Fin K → ℝ) (x : ℕ → Fin K → ℝ) (α : Fin Q → ℝ)
    (t : ℕ) (r q : State Q) :
    transition (economicTable γ β x) (expEffects α) t r q =
      Real.exp (economicIndex γ β x t r q + additiveEffect α q) /
        ∑ s, Real.exp (economicIndex γ β x t r s + additiveEffect α s) := by
  simp only [transition, denominator, economicTable, effect_expEffects, Real.exp_add]

/-- Quantifying over positive multipliers is exactly quantifying over unrestricted
normalized additive fixed effects. -/
theorem isMoment_iff_additive_effects {Q : ℕ} (A : Table Q) (T : ℕ)
    (r : State Q) (m : Path Q T → ℝ) :
    IsMoment A T r m ↔ ∀ α : Fin Q → ℝ,
      ∑ y, m y * likelihood A (expEffects α) T r y = 0 := by
  constructor
  · intro h α
    exact h (expEffects α) (expEffects_pos α)
  · intro h η hη
    have he : expEffects (fun q => Real.log (η q)) = η := by
      funext q
      exact Real.exp_log (hη q)
    simpa only [he] using h (fun q => Real.log (η q))

/-- Exact coefficient restrictions for the normalized covariate specification. -/
theorem economic_moment_iff_coefficient_kernel {Q K : ℕ}
    (γ : Fin Q → State Q → ℝ) (β : Fin Q → Fin K → ℝ)
    (x : ℕ → Fin K → ℝ) (T : ℕ) (r : State Q) (m : Path Q T → ℝ) :
    (∀ α : Fin Q → ℝ,
      ∑ y, m y * likelihood (economicTable γ β x) (expEffects α) T r y = 0) ↔
    ∀ d : Fin Q →₀ ℕ,
      ∑ y, m y * (clearedPathPoly (economicTable γ β x) T r y).coeff d = 0 := by
  rw [← isMoment_iff_additive_effects]
  exact isMoment_iff_coefficient_kernel (economicTable_pos γ β x) T r m

end

end PanelMoments
