import PanelMoments.HomogeneousLikelihood
import PanelMoments.CubicProducts
import PanelMoments.BasisCertificate
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
The homogeneous likelihood map has the actual fixed-effect-free moment space
as its kernel. Positive path weights preserve its range, which is precisely
the cubic product span. Rank-nullity then transfers the structural polynomial
dimension to the model's moment dimension.
-/

namespace PanelMoments.StructuralMoments

open scoped BigOperators
open MvPolynomial HomogeneousLikelihood

noncomputable section

abbrev Poly := MvPolynomial (Fin 3) ℝ

def restrictionMap (A : Table 2) (m : ℕ) (r : State 2) :
    (Path 2 (m + 1) → ℝ) →ₗ[ℝ] Poly :=
  Fintype.linearCombination ℝ
    (fun y => pathWeight A (m + 1) r y • reducedPath A m y)

theorem restrictionMap_apply (A : Table 2) (m : ℕ) (r : State 2)
    (μ : Path 2 (m + 1) → ℝ) : restrictionMap A m r μ = homogeneousMoment A m r μ := by
  simp only [restrictionMap, Fintype.linearCombination_apply,
    MvPolynomial.smul_eq_C_mul, homogeneousMoment, map_mul, mul_assoc]

theorem momentSubmodule_eq_ker {A : Table 2} (hA : PositiveTable A)
    (m : ℕ) (r : State 2) :
    momentSubmodule A (m + 1) r = LinearMap.ker (restrictionMap A m r) := by
  ext μ
  rw [mem_momentSubmodule, LinearMap.mem_ker, restrictionMap_apply]
  exact isMoment_iff_homogeneousMoment_eq_zero hA m r μ

theorem restrictionMap_range {A : Table 2} (hA : PositiveTable A)
    (m : ℕ) (r : State 2) :
    LinearMap.range (restrictionMap A m r) = Submodule.span ℝ (Set.range (reducedPath A m)) := by
  rw [restrictionMap, Fintype.range_linearCombination]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨y, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro f ⟨y, rfl⟩
    have hw : pathWeight A (m + 1) r y ≠ 0 := ne_of_gt (pathWeight_pos hA _ r y)
    have hm := Submodule.smul_mem
      (Submodule.span ℝ (Set.range (fun z => pathWeight A (m + 1) r z • reducedPath A m z)))
      (pathWeight A (m + 1) r y)⁻¹ (Submodule.subset_span ⟨y, rfl⟩)
    rw [smul_smul, inv_mul_cancel₀ hw, one_smul] at hm
    exact hm

def tableA (A : Table 2) (t : ℕ) (r : Fin 3) : ℝ := A (t + 1) r 1
def tableB (A : Table 2) (t : ℕ) (r : Fin 3) : ℝ := A (t + 1) r 2

theorem homogeneousDenominator_eq_lines (A : Table 2)
    (hN : ∀ t r, A t r 0 = 1) (t : ℕ) :
    homogeneousDenominator A (t + 1) = CubicRelations.lines (tableA A t) (tableB A t) := by
  funext r
  change (∑ q : Fin 3, C (A (t + 1) r q) * X q) =
    X 0 + C (A (t + 1) r 1) * X 1 + C (A (t + 1) r 2) * X 2
  rw [Fin.sum_univ_three, hN]
  simp

theorem reducedPath_eq_pureProduct (A : Table 2) (hN : ∀ t r, A t r 0 = 1)
    (m : ℕ) (y : Path 2 (m + 1)) :
    reducedPath A m y = CubicProducts.pureProduct (tableA A) (tableB A) m y := by
  induction m generalizing A with
  | zero => rfl
  | succ m ih =>
    simp only [reducedPath, CubicProducts.pureProduct]
    rw [homogeneousDenominator_eq_lines A hN 0]
    rw [ih (shift A) (fun t r => hN (t + 1) r) (Fin.tail y)]
    rfl

theorem restrictionMap_range_eq_productSpan {A : Table 2} (hA : PositiveTable A)
    (hN : ∀ t r, A t r 0 = 1) (m : ℕ) (r : State 2) :
    LinearMap.range (restrictionMap A m r) =
      CubicProducts.productSpan (tableA A) (tableB A) m := by
  rw [restrictionMap_range hA]
  have hfun : reducedPath A m =
      CubicProducts.pureProduct (tableA A) (tableB A) m :=
    funext (reducedPath_eq_pureProduct A hN m)
  exact congrArg (fun f : Path 2 (m + 1) → Poly => Submodule.span ℝ (Set.range f)) hfun

theorem finrank_moment_add_range {A : Table 2} (hA : PositiveTable A)
    (m : ℕ) (r : State 2) :
    Module.finrank ℝ (momentSubmodule A (m + 1) r) +
      Module.finrank ℝ (LinearMap.range (restrictionMap A m r)) = 3 ^ (m + 1) := by
  rw [momentSubmodule_eq_ker hA]
  have h := (restrictionMap A m r).finrank_range_add_finrank_ker
  simpa [Module.finrank_pi, Path, State, Nat.add_comm] using h

/-- The structural dimension identity for the actual moment space. The
additive form keeps all arithmetic in the natural numbers without truncation. -/
theorem finrank_moment_add_choose {A : Table 2} (hA : PositiveTable A)
    (hN : ∀ t r, A t r 0 = 1) (m : ℕ) (r : State 2)
    (hL : ∀ t : Fin m, CubicRelations.LineConditions (tableA A t) (tableB A t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate
        (CubicIdeal.coefficientVectors (tableA A t) (tableB A t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (tableA A t) (tableB A t))) :
    Module.finrank ℝ (momentSubmodule A (m + 1) r) + (3 * m + 3).choose 2 =
      3 ^ (m + 1) + 6 * m := by
  have hmoment := finrank_moment_add_range hA m r
  rw [restrictionMap_range_eq_productSpan hA hN] at hmoment
  have hproduct := CubicProducts.finrank_productSpan_add_six_mul
    (tableA A) (tableB A) m hL hP hcross
  calc
    Module.finrank ℝ (momentSubmodule A (m + 1) r) + (3 * m + 3).choose 2 =
        Module.finrank ℝ (momentSubmodule A (m + 1) r) +
          (Module.finrank ℝ (CubicProducts.productSpan (tableA A) (tableB A) m) + 6 * m) := by
      rw [hproduct]
    _ = (Module.finrank ℝ (momentSubmodule A (m + 1) r) +
        Module.finrank ℝ (CubicProducts.productSpan (tableA A) (tableB A) m)) + 6 * m :=
      (Nat.add_assoc _ _ _).symm
    _ = 3 ^ (m + 1) + 6 * m := congrArg (fun n => n + 6 * m) hmoment

theorem finrank_moment {A : Table 2} (hA : PositiveTable A)
    (hN : ∀ t r, A t r 0 = 1) (m : ℕ) (r : State 2)
    (hL : ∀ t : Fin m, CubicRelations.LineConditions (tableA A t) (tableB A t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate
        (CubicIdeal.coefficientVectors (tableA A t) (tableB A t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (tableA A t) (tableB A t))) :
    Module.finrank ℝ (momentSubmodule A (m + 1) r) =
      3 ^ (m + 1) + 6 * m - (3 * m + 3).choose 2 := by
  have hdim := finrank_moment_add_choose hA hN m r hL hP hcross
  omega

end

end PanelMoments.StructuralMoments
