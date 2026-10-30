import PanelMoments.StructuralMoments
import PanelMoments.StructuralGenericity

/-!
# The generic dimension of all three-choice panel moments

For every positive panel length, the explicit geometric economic region is
nonempty, open, and dense. On this region the actual fixed-effect-free moment
space has the dimension stated below, for every initial state. The dimension
formula concerns the whole moment space; it does not identify a particular
moment family as a basis for arbitrary panel lengths.
-/

namespace PanelMoments.StructuralCompleteness

noncomputable section

/-- The additive dimension identity avoids truncated subtraction in the
natural numbers. -/
theorem economic_moment_dimension_add_choose {T : ℕ} (hT : 1 ≤ T)
    {θ : EconomicFamily.EconomicParameter T}
    (hθ : θ ∈ StructuralGenericity.genericRegion T) (r : State 2) :
    Module.finrank ℝ (momentSubmodule (EconomicFamily.parameterTable θ) T r) +
        (3 * T).choose 2 =
      3 ^ T + 6 * (T - 1) := by
  cases T with
  | zero => omega
  | succ m =>
    have hdim := StructuralMoments.finrank_moment_add_choose
      (A := EconomicFamily.parameterTable θ)
      (EconomicFamily.parameterTable_positive θ)
      (fun t s => EconomicFamily.parameterTable_baseline θ t s) m r
      (fun t => StructuralGenericity.region_lineConditions hθ t)
      (fun t => StructuralGenericity.region_localNondegenerate hθ t)
      (StructuralGenericity.region_crossNonincident hθ)
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one] using hdim

/-- The sum is formed before natural-number subtraction. -/
theorem economic_moment_dimension {T : ℕ} (hT : 1 ≤ T)
    {θ : EconomicFamily.EconomicParameter T}
    (hθ : θ ∈ StructuralGenericity.genericRegion T) (r : State 2) :
    Module.finrank ℝ (momentSubmodule (EconomicFamily.parameterTable θ) T r) =
      (3 ^ T + 6 * (T - 1)) - (3 * T).choose 2 := by
  have hdim := economic_moment_dimension_add_choose hT hθ r
  omega

/-- A single declaration packages the generic economic domain and the
dimension of all fixed-effect-free moments, simultaneously for every initial
state and for an arbitrary positive panel length. -/
theorem three_choice_generic_moment_dimension (T : ℕ) (hT : 1 ≤ T) :
    (StructuralGenericity.genericRegion T).Nonempty ∧
      IsOpen (StructuralGenericity.genericRegion T) ∧
      Dense (StructuralGenericity.genericRegion T) ∧
      ∀ θ ∈ StructuralGenericity.genericRegion T, ∀ r : State 2,
        Module.finrank ℝ (momentSubmodule (EconomicFamily.parameterTable θ) T r) =
          (3 ^ T + 6 * (T - 1)) - (3 * T).choose 2 :=
  ⟨StructuralGenericity.genericRegion_nonempty T,
    StructuralGenericity.genericRegion_open T,
    StructuralGenericity.genericRegion_dense T,
    fun _ hθ r => economic_moment_dimension hT hθ r⟩

/-- At four periods the structural formula gives 33 moments on every initial
state, in agreement with the finite-case dimension. -/
theorem four_period_moment_dimension {θ : EconomicFamily.EconomicParameter 4}
    (hθ : θ ∈ StructuralGenericity.genericRegion 4) (r : State 2) :
    Module.finrank ℝ (momentSubmodule (EconomicFamily.parameterTable θ) 4 r) = 33 := by
  have hnum : (3 ^ 4 + 6 * (4 - 1)) - (3 * 4).choose 2 = 33 := by decide
  exact (economic_moment_dimension (T := 4) (by decide) hθ r).trans hnum

end

end PanelMoments.StructuralCompleteness
