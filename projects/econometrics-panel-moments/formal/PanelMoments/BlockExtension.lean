import PanelMoments.CubicIdeal
import PanelMoments.PointSyzygies
import Mathlib.Tactic.Choose

set_option autoImplicit false

/-!
# Extending the cubic span by one block

Interpolation at the old points turns pointwise cubic relations into one
polynomial relation. Subtracting that relation from an initial decomposition
makes every coefficient vanish on the old points while preserving the
decomposed polynomial and the coefficient degrees.
-/

namespace PanelMoments.BlockExtension

open scoped BigOperators
open MvPolynomial CubicRelations

noncomputable section

abbrev Point := Fin 3 → ℝ
abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- Add one three-line block while retaining vanishing of all coefficients
at the old points. The interpolation hypothesis concerns degree `k`; the
corrected coefficients have degree `k + 2`, and `F` has degree `k + 5`. -/
theorem exists_corrected_cubic_decomposition {ι : Type*}
    (p : ι → Point) (k : ℕ) (hp : ∀ j, p j ≠ 0)
    (heval : Function.Surjective (HomogeneousInterpolation.evaluation p k))
    (a b : Fin 3 → ℝ) (hL : LineConditions a b)
    (hP : GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors a b))
    (hcross : ∀ j i, eval (p j) (lines a b i) ≠ 0)
    {F : Poly} (hF : F.IsHomogeneous (k + 5))
    (hOld : ∀ j, eval (p j) F = 0)
    (hNew : ∀ i,
      eval (GeneralGeometry.sixPoints (CubicIdeal.coefficientVectors a b) i) F = 0) :
    ∃ c : Fin 3 → Poly,
      (∀ i, (c i).IsHomogeneous (k + 2)) ∧
      (∀ i j, eval (p j) (c i) = 0) ∧
      F = cubicCombination a b c := by
  classical
  have hF' : F.IsHomogeneous ((k + 1) + 4) := by
    simpa only [Nat.add_assoc] using hF
  obtain ⟨d, hd_hom, hd⟩ :=
    CubicIdeal.exists_homogeneous_cubic_decomposition a b hL hP (n := k + 1) hF' hNew
  have hd_hom' : ∀ i, (d i).IsHomogeneous (k + 2) := by
    intro i
    simpa only [Nat.add_assoc] using hd_hom i
  have hpoint (j : ι) :
      ∃ u₀₁ u₀₂ u₁₂ : ℝ,
        eval (p j) (d 0) = eval (p j) (lines a b 0) *
          (-p j 1 * u₀₁ - p j 2 * u₀₂) ∧
        eval (p j) (d 1) = eval (p j) (lines a b 1) *
          (p j 0 * u₀₁ - p j 2 * u₁₂) ∧
        eval (p j) (d 2) = eval (p j) (lines a b 2) *
          (p j 0 * u₀₂ + p j 1 * u₁₂) := by
    have hzero : eval (p j) (cubicCombination a b d) = 0 := by
      rw [← hd]
      exact hOld j
    have hscalar :
        ∑ i, eval (p j) (d i) *
          PointSyzygies.blockValue (p j) (fun r => eval (p j) (lines a b r)) i = 0 := by
      simpa only [cubicCombination, Geometry.blockFactor, PointSyzygies.blockValue,
        map_sum, map_mul, map_prod, eval_X] using hzero
    exact PointSyzygies.scaled_coordinate_syzygy (p j)
      (fun i => eval (p j) (lines a b i)) (fun i => eval (p j) (d i))
      (hp j) (hcross j) hscalar
  choose u₀₁ u₀₂ u₁₂ hu₀ hu₁ hu₂ using hpoint
  obtain ⟨B₀₁, hB₀₁⟩ := heval u₀₁
  obtain ⟨B₀₂, hB₀₂⟩ := heval u₀₂
  obtain ⟨B₁₂, hB₁₂⟩ := heval u₁₂
  have hB₀₁' (j : ι) : eval (p j) B₀₁.1 = u₀₁ j :=
    congrFun hB₀₁ j
  have hB₀₂' (j : ι) : eval (p j) B₀₂.1 = u₀₂ j :=
    congrFun hB₀₂ j
  have hB₁₂' (j : ι) : eval (p j) B₁₂.1 = u₁₂ j :=
    congrFun hB₁₂ j
  let g : Fin 3 → Poly :=
    ![-X 1 * B₀₁.1 - X 2 * B₀₂.1,
      X 0 * B₀₁.1 - X 2 * B₁₂.1,
      X 0 * B₀₂.1 + X 1 * B₁₂.1]
  let correction : Fin 3 → Poly := fun i => lines a b i * g i
  have hg_hom : ∀ i, (g i).IsHomogeneous (k + 1) := by
    intro i
    fin_cases i
    · change (-X 1 * B₀₁.1 - X 2 * B₀₂.1).IsHomogeneous (k + 1)
      simpa only [neg_mul, Nat.add_comm] using
        (((isHomogeneous_X ℝ (1 : Fin 3)).mul B₀₁.2).neg).sub
          ((isHomogeneous_X ℝ (2 : Fin 3)).mul B₀₂.2)
    · change (X 0 * B₀₁.1 - X 2 * B₁₂.1).IsHomogeneous (k + 1)
      simpa only [Nat.add_comm] using
        ((isHomogeneous_X ℝ (0 : Fin 3)).mul B₀₁.2).sub
          ((isHomogeneous_X ℝ (2 : Fin 3)).mul B₁₂.2)
    · change (X 0 * B₀₂.1 + X 1 * B₁₂.1).IsHomogeneous (k + 1)
      simpa only [Nat.add_comm] using
        ((isHomogeneous_X ℝ (0 : Fin 3)).mul B₀₂.2).add
          ((isHomogeneous_X ℝ (1 : Fin 3)).mul B₁₂.2)
  have hcorrection_hom (i : Fin 3) :
      (correction i).IsHomogeneous (k + 2) := by
    change (LinearFormAlgebra.normalizedLine (a i) (b i) * g i).IsHomogeneous (k + 2)
    convert (normalizedLine_isHomogeneous (a i) (b i)).mul (hg_hom i) using 1 <;> omega
  have hg_zero : coordinateCombination g = 0 := by
    simp only [coordinateCombination, Fin.sum_univ_three]
    dsimp [g]
    ring
  have hcorrection_zero : cubicCombination a b correction = 0 := by
    change cubicCombination a b (fun i => lines a b i * g i) = 0
    rw [cubicCombination_multiply_lines, hg_zero, mul_zero]
  have hmatches (j : ι) (i : Fin 3) :
      eval (p j) (correction i) = eval (p j) (d i) := by
    fin_cases i
    · change eval (p j) (lines a b 0 * (-X 1 * B₀₁.1 - X 2 * B₀₂.1)) =
        eval (p j) (d 0)
      simpa only [map_mul, map_sub, map_neg, eval_X, hB₀₁' j, hB₀₂' j] using (hu₀ j).symm
    · change eval (p j) (lines a b 1 * (X 0 * B₀₁.1 - X 2 * B₁₂.1)) =
        eval (p j) (d 1)
      simpa only [map_mul, map_sub, eval_X, hB₀₁' j, hB₁₂' j] using (hu₁ j).symm
    · change eval (p j) (lines a b 2 * (X 0 * B₀₂.1 + X 1 * B₁₂.1)) =
        eval (p j) (d 2)
      simpa only [map_mul, map_add, eval_X, hB₀₂' j, hB₁₂' j] using (hu₂ j).symm
  refine ⟨fun i => d i - correction i, ?_, ?_, ?_⟩
  · intro i
    exact (hd_hom' i).sub (hcorrection_hom i)
  · intro i j
    simp only [map_sub, hmatches j i, sub_self]
  · calc
      F = cubicCombination a b d := hd
      _ = cubicCombination a b d - cubicCombination a b correction := by
        rw [hcorrection_zero, sub_zero]
      _ = cubicCombination a b (fun i => d i - correction i) := by
        simp only [cubicCombination, sub_mul, Finset.sum_sub_distrib]

end

end PanelMoments.BlockExtension
