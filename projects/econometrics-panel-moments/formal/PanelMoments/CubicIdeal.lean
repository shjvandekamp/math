import PanelMoments.CubicRelations
import PanelMoments.GeneralGeometry

/-!
In every homogeneous degree at least four, the three cubic generators span
exactly the polynomials vanishing on their six base points. Both sides have
codimension six, proved separately by cubic relation reduction and explicit
point separators.
-/

namespace PanelMoments.CubicIdeal

open scoped BigOperators
open MvPolynomial CubicRelations HomogeneousInterpolation

noncomputable section

def coefficientVectors (a b : Fin 3 → ℝ) (i : Fin 3) : GeneralGeometry.Point :=
  ![1, a i, b i]

theorem linearForm_coefficientVectors (a b : Fin 3 → ℝ) (i : Fin 3) :
    GeneralGeometry.linearForm (coefficientVectors a b i) = lines a b i := by
  simp [GeneralGeometry.linearForm, coefficientVectors, lines,
    LinearFormAlgebra.normalizedLine]

theorem blockFactor_zero (a b : Fin 3 → ℝ) (i : Fin 6) (r : Fin 3) :
    eval (GeneralGeometry.sixPoints (coefficientVectors a b) i)
      (Geometry.blockFactor (lines a b) r) = 0 := by
  simpa only [linearForm_coefficientVectors] using
    GeneralGeometry.blockFactor_zero (coefficientVectors a b) i r

theorem cubic_range_le_vanishing (a b : Fin 3 → ℝ) (n : ℕ) :
    LinearMap.range (cubicLinearMap a b n) ≤
      vanishingSubmodule (GeneralGeometry.sixPoints (coefficientVectors a b)) (n + 4) := by
  rintro f ⟨c, rfl⟩
  rw [mem_vanishingSubmodule]
  intro i
  change eval (GeneralGeometry.sixPoints (coefficientVectors a b) i)
    (cubicCombination a b (fun j => (c j).1)) = 0
  simp only [cubicCombination, map_sum, map_mul, blockFactor_zero, mul_zero, Finset.sum_const_zero]

/-- Equality of the cubic-generated and six-point vanishing subspaces, using
only explicit line and separator nonvanishing conditions. -/
theorem cubic_range_eq_vanishing (a b : Fin 3 → ℝ) (hL : LineConditions a b)
    (hP : GeneralGeometry.LocalNondegenerate (coefficientVectors a b)) (n : ℕ) :
    LinearMap.range (cubicLinearMap a b n) =
      vanishingSubmodule (GeneralGeometry.sixPoints (coefficientVectors a b)) (n + 4) := by
  classical
  let p := GeneralGeometry.sixPoints (coefficientVectors a b)
  let s := GeneralGeometry.separatingFamily (coefficientVectors a b) hP
  let c (i : Fin 6) := Classical.choose
    (GeneralGeometry.sixPoints_coordinate_nonzero (coefficientVectors a b) hP i)
  have hn (i : Fin 6) : p i (c i) ≠ 0 := Classical.choose_spec
    (GeneralGeometry.sixPoints_coordinate_nonzero (coefficientVectors a b) hP i)
  have hV : Module.finrank ℝ (vanishingSubmodule p (n + 4)) =
      (n + 6).choose 2 - 6 := by
    simpa only [Nat.add_assoc, Fintype.card_fin] using
      s.finrank_vanishing_of_le c hn (by omega : 2 ≤ n + 4)
  have hJ := finrank_range_cubicLinearMap_add_six a b hL n
  apply Submodule.eq_of_le_of_finrank_eq (cubic_range_le_vanishing a b n)
  change Module.finrank ℝ (LinearMap.range (cubicLinearMap a b n)) =
    Module.finrank ℝ (vanishingSubmodule p (n + 4))
  omega

/-- A vanishing polynomial has homogeneous cubic coefficients in the exact
degree required for the block-extension induction. -/
theorem exists_homogeneous_cubic_decomposition (a b : Fin 3 → ℝ)
    (hL : LineConditions a b)
    (hP : GeneralGeometry.LocalNondegenerate (coefficientVectors a b))
    {n : ℕ} {f : MvPolynomial (Fin 3) ℝ} (hf : f.IsHomogeneous (n + 4))
    (hz : ∀ i, eval (GeneralGeometry.sixPoints (coefficientVectors a b) i) f = 0) :
    ∃ c : Fin 3 → MvPolynomial (Fin 3) ℝ,
      (∀ i, (c i).IsHomogeneous (n + 1)) ∧ f = cubicCombination a b c := by
  have hm : (⟨f, hf⟩ : HomogeneousInterpolation.Homogeneous (n + 4)) ∈
      LinearMap.range (cubicLinearMap a b n) := by
    rw [cubic_range_eq_vanishing a b hL hP n, mem_vanishingSubmodule]
    exact hz
  obtain ⟨c, hc⟩ := hm
  refine ⟨fun i => (c i).1, fun i => (c i).2, ?_⟩
  exact (congrArg Subtype.val hc).symm

end

end PanelMoments.CubicIdeal
