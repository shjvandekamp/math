import PanelMoments.SourceMoments
import PanelMoments.Genericity

set_option autoImplicit false

/-! Analyticity and finite-time congruence of the shared source numerators. -/

namespace PanelMoments

noncomputable section

theorem originalScale_congr {R : Type*} [CommRing R] {Q : ℕ}
    (A B : ℕ → State Q → State Q → R)
    (hAB : ∀ t < 4, ∀ r q, A t r q = B t r q) (r : State Q) (y : Path Q 4) :
    originalScale A r y = originalScale B r y := by
  simp [originalScale, hAB]

theorem transformedScale_congr {R : Type*} [CommRing R] {Q : ℕ}
    (A B : ℕ → State Q → State Q → R)
    (hAB : ∀ t < 4, ∀ r q, A t r q = B t r q)
    (r : State Q) (o : Fin 6) (y : Path Q 4) :
    transformedScale A r o y = transformedScale B r o y := by
  fin_cases o <;>
    simp [transformedScale, orderPerm, Equiv.swap_apply_def, hAB]

theorem sourceNumerator_congr {R : Type*} [CommRing R] {Q : ℕ}
    (A B : ℕ → State Q → State Q → R)
    (hAB : ∀ t < 4, ∀ r q, A t r q = B t r q)
    (r : State Q) (i : SourceIndex Q) (y : Path Q 4) :
    sourceNumerator A r i y = sourceNumerator B r i y := by
  simp only [sourceNumerator, transformedScale_congr A B hAB]

theorem analyticAt_transformedScale {n Q : ℕ} (A : (Fin n → ℝ) → Table Q)
    (θ : Fin n → ℝ)
    (hA : ∀ t r q, AnalyticAt ℝ (fun z => A z t r q) θ)
    (r : State Q) (o : Fin 6) (y : Path Q 4) :
    AnalyticAt ℝ (fun z => transformedScale (A z) r o y) θ := by
  exact (((hA _ _ _).mul (hA _ _ _)).mul (hA _ _ _)).mul (hA _ _ _)

theorem analyticAt_sourceNumerator {n Q : ℕ} (A : (Fin n → ℝ) → Table Q)
    (θ : Fin n → ℝ)
    (hA : ∀ t r q, AnalyticAt ℝ (fun z => A z t r q) θ)
    (r : State Q) (i : SourceIndex Q) (y : Path Q 4) :
    AnalyticAt ℝ (fun z => sourceNumerator (A z) r i y) θ := by
  exact (analyticAt_const.mul (analyticAt_transformedScale A θ hA r (sourceFirstOrder i) y)).sub
    (analyticAt_const.mul (analyticAt_transformedScale A θ hA r (sourceSecondOrder i) y))

theorem parameter_sourceNumerator_analytic (r : State 2) (i : SourceIndex 2)
    (y : Path 2 4) :
    AnalyticOnNhd ℝ (fun θ => sourceNumerator (parameterTable θ) r i y) Set.univ := by
  intro θ _
  exact analyticAt_sourceNumerator parameterTable θ
    (fun t s q => parameterTable_analytic t s q θ (Set.mem_univ θ)) r i y

end

end PanelMoments
