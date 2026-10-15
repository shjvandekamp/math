import PanelMoments.Genericity
import PanelMoments.WitnessCore
import PanelMoments.SourceAnalytic

/-! Analytic dependence of the actual restriction and source-numerator formulas. -/

namespace PanelMoments

open scoped BigOperators

noncomputable section

theorem ringDenominator_analyticAt
    (A : EconomicParameter → Witness.RingTable ℝ) (x : EconomicParameter)
    (hA : ∀ t r q, AnalyticAt ℝ (fun z => A z t r q) x)
    (η : Fin 2 → ℝ) (t : ℕ) (r : State 2) :
    AnalyticAt ℝ (fun z => Witness.ringDenominator (A z) η t r) x := by
  unfold Witness.ringDenominator
  apply Finset.analyticAt_fun_sum
  intro q _
  exact (hA t r q).mul analyticAt_const

theorem fullyReducedEval_analyticAt
    (A : EconomicParameter → Witness.RingTable ℝ) (x : EconomicParameter)
    (hA : ∀ t r q, AnalyticAt ℝ (fun z => A z t r q) x)
    (η : Fin 2 → ℝ) (T : ℕ) (r : State 2) (y : Path 2 T) :
    AnalyticAt ℝ (fun z => Witness.fullyReducedEval (A z) η T r y) x := by
  induction T generalizing A r with
  | zero => exact analyticAt_const
  | succ T ih =>
    simp only [Witness.fullyReducedEval]
    apply AnalyticAt.mul
    · apply AnalyticAt.mul analyticAt_const
      apply Finset.analyticAt_fun_prod
      intro s _
      exact ringDenominator_analyticAt A x hA η 0 s
    · exact ih (fun z t => A z (t + 1))
        (fun t r q => hA (t + 1) r q) (y 0) (Fin.tail y)

theorem reducedEval_analyticAt
    (A : EconomicParameter → Witness.RingTable ℝ) (x : EconomicParameter)
    (hA : ∀ t r q, AnalyticAt ℝ (fun z => A z t r q) x)
    (η : Fin 2 → ℝ) (T : ℕ) (y : Path 2 T) :
    AnalyticAt ℝ (fun z => Witness.reducedEval (A z) η T y) x := by
  cases T with
  | zero => exact analyticAt_const
  | succ T =>
    exact AnalyticAt.mul analyticAt_const
      (fullyReducedEval_analyticAt (fun z t => A z (t + 1)) x
        (fun t r q => hA (t + 1) r q) η T (y 0) (Fin.tail y))

theorem evaluationMinor_parameter_analytic :
    AnalyticOnNhd ℝ (fun θ => (Witness.evaluationMinor (parameterTable θ)).det) Set.univ := by
  intro θ _
  apply analyticAt_matrix_det
  intro i j
  exact reducedEval_analyticAt parameterTable θ
    (fun t r q => parameterTable_analytic t r q θ (Set.mem_univ θ)) _ 4 _

end

end PanelMoments
