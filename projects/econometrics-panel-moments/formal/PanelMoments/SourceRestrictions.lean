import PanelMoments.SourceMoments
import PanelMoments.WitnessCore

set_option autoImplicit false

/-!
# Bridge from moments to executable evaluation restrictions

The witness module's reduced evaluations remove the nonzero path-amplitude factor.
The restrictions below hold at every real evaluation vector, including points outside
the positive orthant: polynomial vanishing has already been proved from that orthant.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

theorem pathAmplitude_four_eq_originalScale {R : Type*} [CommRing R]
    (A : Witness.RingTable R) (r : State 2) (y : Path 2 4) :
    Witness.pathAmplitude A 4 r y = originalScale A r y := by
  change A 0 r (y 0) * (A 1 (y 0) (y 1) *
    (A 2 (y 1) (y 2) * (A 3 (y 2) (y 3) * 1))) =
      A 0 r (y 0) * A 1 (y 0) (y 1) * A 2 (y 1) (y 2) * A 3 (y 2) (y 3)
  ring

/-- Any true moment is killed by every executable, amplitude-weighted evaluation row. -/
theorem isMoment_reducedEval_zero {A : Table 2} (hA : PositiveTable A)
    (T : ℕ) (r : State 2) {m : Path 2 T → ℝ} (hm : IsMoment A T r m)
    (η : Fin 2 → ℝ) :
    ∑ y, m y * (Witness.pathAmplitude A T r y * Witness.reducedEval A η T y) = 0 := by
  have hp := (isMoment_iff_momentPoly_eq_zero hA T r m).mp hm
  have he := congrArg (MvPolynomial.eval η) hp
  simpa only [momentPoly, map_sum, map_mul, MvPolynomial.eval_C,
    Witness.eval_clearedPathPoly, map_zero] using he

/-- The shared source numerators annihilate the reduced evaluations. This is the exact
`C0 Kᵀ = 0` identity used by the finite certificates, for arbitrary positive tables. -/
theorem sourceNumerator_reducedEval_zero {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (i : SourceIndex 2) (η : Fin 2 → ℝ) :
    ∑ y, sourceNumerator A r i y * Witness.reducedEval A η 4 y = 0 := by
  calc
    _ = ∑ y, sourceMoment A r i y *
        (Witness.pathAmplitude A 4 r y * Witness.reducedEval A η 4 y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [sourceMoment_eq_numerator_div, pathAmplitude_four_eq_originalScale]
      field_simp [ne_of_gt (originalScale_pos hA r y)]
    _ = 0 := isMoment_reducedEval_zero hA 4 r (sourceMoment_isMoment hA r i) η

end

end PanelMoments
