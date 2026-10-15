import PanelMoments.BasisCertificate
import PanelMoments.SourceRestrictions

/-!
The finite model argument. The only exceptional conditions are determinants of
the explicitly defined primitive evaluation and source-numerator matrices.
EconomicGenericity supplies their nonvanishing witness and proves density.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

/-- Forty-eight actual polynomial restrictions on path moments. -/
def evaluationRestrictions (A : Table 2) (r : State 2) :
    Matrix (Fin 48) (Path 2 4) ℝ := fun i y =>
  Witness.pathAmplitude A 4 r y *
    Witness.reducedEval A (fun q => (Witness.evaluationPoints i q : ℝ)) 4 y

theorem momentSubmodule_le_evaluation_kernel {A : Table 2} (hA : PositiveTable A)
    (r : State 2) :
    momentSubmodule A 4 r ≤ LinearMap.ker (evaluationRestrictions A r).mulVecLin := by
  intro m hm
  apply LinearMap.mem_ker.mpr
  funext i
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    evaluationRestrictions, Pi.zero_apply, mul_comm] using
    isMoment_reducedEval_zero hA 4 r hm
      (fun q => (Witness.evaluationPoints i q : ℝ))

theorem evaluationRestrictions_minor_ne_zero {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hE : (Witness.evaluationMinor A).det ≠ 0) :
    ((evaluationRestrictions A r).submatrix id Witness.evaluationPaths).det ≠ 0 := by
  have he : ((evaluationRestrictions A r).submatrix id Witness.evaluationPaths).det =
      (∏ j, Witness.pathAmplitude A 4 r (Witness.evaluationPaths j)) *
        (Witness.evaluationMinor A).det := by
    exact Matrix.det_mul_row _ _
  rw [he]
  apply mul_ne_zero _ hE
  exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
    ne_of_gt (Witness.pathAmplitude_pos hA 4 r (Witness.evaluationPaths j)))

theorem sourceMoment_minor_ne_zero {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (rows : Fin 33 → SourceIndex 2) (cols : Fin 33 → Path 2 4)
    (hK : Matrix.det (fun i j => sourceNumerator A r (rows i) (cols j)) ≠ 0) :
    Matrix.det (fun i j => sourceMoment A r (rows i) (cols j)) ≠ 0 := by
  intro h
  apply hK
  have he : (fun i j => sourceNumerator A r (rows i) (cols j)) =
      (fun i j => originalScale A r (cols j) * sourceMoment A r (rows i) (cols j)) := by
    funext i j
    rw [sourceMoment_eq_numerator_div]
    field_simp [ne_of_gt (originalScale_pos hA r (cols j))]
  rw [he]
  calc
    _ = (∏ j, originalScale A r (cols j)) *
        Matrix.det (fun i j => sourceMoment A r (rows i) (cols j)) :=
      Matrix.det_mul_row _ _
    _ = 0 := by rw [h, mul_zero]

/-- Explicit nonzero minors imply the complete source-basis assertion for this
positive table. No desired rank is assumed. -/
theorem source_basis_of_minors {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (rows : Fin 33 → SourceIndex 2) (hrows : Function.Bijective rows)
    (cols : Fin 33 → Path 2 4)
    (hE : (Witness.evaluationMinor A).det ≠ 0)
    (hK : Matrix.det (fun i j => sourceNumerator A r (rows i) (cols j)) ≠ 0) :
    LinearIndependent ℝ (sourceMoment A r) ∧
      momentSubmodule A 4 r = Submodule.span ℝ (Set.range (sourceMoment A r)) ∧
      Module.finrank ℝ (momentSubmodule A 4 r) = 33 := by
  have hb := finite_basis_certificate three_choice_four_period_path_count
    (fun i => sourceMoment A r (rows i)) cols (evaluationRestrictions A r)
    Witness.evaluationPaths (momentSubmodule A 4 r)
    (fun i => sourceMoment_isMoment hA r (rows i))
    (momentSubmodule_le_evaluation_kernel hA r)
    (sourceMoment_minor_ne_zero hA r rows cols hK)
    (evaluationRestrictions_minor_ne_zero hA r hE)
  have hli : LinearIndependent ℝ (sourceMoment A r) :=
    (linearIndependent_equiv (Equiv.ofBijective rows hrows)).mp hb.1
  have hrange : Set.range (fun i => sourceMoment A r (rows i)) =
      Set.range (sourceMoment A r) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rows i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := hrows.surjective i
      exact ⟨j, rfl⟩
  exact ⟨hli, hrange ▸ hb.2.1, hb.2.2⟩

end

end PanelMoments
