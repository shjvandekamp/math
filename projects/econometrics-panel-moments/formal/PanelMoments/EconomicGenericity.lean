import PanelMoments.ModelAnalytic
import PanelMoments.FiniteCompleteness
import PanelMoments.Witness

/-!
An explicit open dense region in the joint normalized economic parameter space.
The defining analytic function is a product of fixed primitive minors, and its
nonzero value is proved at the concrete logarithmic parameter witness.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

theorem sourceMinor_parameter_analytic (r : State 2) :
    AnalyticOnNhd ℝ (fun θ => (Witness.sourceMinor (parameterTable θ) r).det)
      Set.univ := by
  intro θ _
  apply analyticAt_matrix_det
  intro i j
  exact parameter_sourceNumerator_analytic r (Witness.sourceRows i)
    (Witness.sourcePaths r j) θ (Set.mem_univ θ)

/-- This function is constructed from fixed rows, columns and evaluation points;
it is not defined by any independence or completeness predicate. -/
def exceptionalDeterminant (θ : EconomicParameter) : ℝ :=
  (Witness.evaluationMinor (parameterTable θ)).det *
    ∏ r : State 2, (Witness.sourceMinor (parameterTable θ) r).det

def genericEconomicRegion : Set EconomicParameter := {θ | exceptionalDeterminant θ ≠ 0}

theorem exceptionalDeterminant_analytic :
    AnalyticOnNhd ℝ exceptionalDeterminant Set.univ := by
  intro θ _
  apply AnalyticAt.mul (evaluationMinor_parameter_analytic θ (Set.mem_univ θ))
  apply Finset.analyticAt_fun_prod
  intro r _
  exact sourceMinor_parameter_analytic r θ (Set.mem_univ θ)

theorem parameterWitness_table_congr :
    ∀ t < 4, ∀ r q, parameterTable parameterWitness t r q =
      Witness.table (R := ℝ) t r q := by
  intro t ht r q
  exact parameterWitness_table ⟨t, ht⟩ r q

theorem exceptionalDeterminant_witness : exceptionalDeterminant parameterWitness ≠ 0 := by
  unfold exceptionalDeterminant
  rw [Witness.evaluationMinor_congr _ _ parameterWitness_table_congr]
  apply mul_ne_zero Witness.evaluationMinor_real_det_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  have he : Witness.sourceMinor (parameterTable parameterWitness) r =
      Witness.sourceMinor (Witness.table (R := ℝ)) r := by
    ext i j
    exact sourceNumerator_congr _ _ parameterWitness_table_congr r
      (Witness.sourceRows i) (Witness.sourcePaths r j)
  rw [he]
  exact Witness.sourceMinor_real_det_ne_zero r

theorem genericEconomicRegion_nonempty : genericEconomicRegion.Nonempty :=
  ⟨parameterWitness, exceptionalDeterminant_witness⟩

theorem genericEconomicRegion_open : IsOpen genericEconomicRegion :=
  analytic_nonzero_open exceptionalDeterminant_analytic

theorem genericEconomicRegion_dense : Dense genericEconomicRegion :=
  analytic_nonzero_dense exceptionalDeterminant_analytic exceptionalDeterminant_witness

/-- The full finite source-basis assertion, simultaneously for every initial
state, on an explicit nonempty open dense economic parameter region. -/
theorem economic_source_basis {θ : EconomicParameter} (hθ : θ ∈ genericEconomicRegion)
    (r : State 2) :
    LinearIndependent ℝ (sourceMoment (parameterTable θ) r) ∧
      momentSubmodule (parameterTable θ) 4 r =
        Submodule.span ℝ (Set.range (sourceMoment (parameterTable θ) r)) ∧
      Module.finrank ℝ (momentSubmodule (parameterTable θ) 4 r) = 33 := by
  have h := mul_ne_zero_iff.mp hθ
  have hK : (Witness.sourceMinor (parameterTable θ) r).det ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h.2) r (Finset.mem_univ r)
  exact source_basis_of_minors (parameterTable_positive θ) r Witness.sourceRows
    Witness.sourceRows_bijective (Witness.sourcePaths r) h.1 hK

/-- One declaration packages the generic-domain and complete finite basis claims. -/
theorem three_choice_four_period_generic_completeness :
    genericEconomicRegion.Nonempty ∧ IsOpen genericEconomicRegion ∧
      Dense genericEconomicRegion ∧
      ∀ θ ∈ genericEconomicRegion, ∀ r : State 2,
        LinearIndependent ℝ (sourceMoment (parameterTable θ) r) ∧
          momentSubmodule (parameterTable θ) 4 r =
            Submodule.span ℝ (Set.range (sourceMoment (parameterTable θ) r)) ∧
          Module.finrank ℝ (momentSubmodule (parameterTable θ) 4 r) = 33 :=
  ⟨genericEconomicRegion_nonempty, genericEconomicRegion_open,
    genericEconomicRegion_dense, fun _ hθ r => economic_source_basis hθ r⟩

end

end PanelMoments
