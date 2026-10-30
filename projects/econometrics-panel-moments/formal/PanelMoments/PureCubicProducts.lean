import PanelMoments.BlockExtension
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

/-!
# Pure cubic products in degree `3 * m`

Choose one actual cubic `X a * ∏ b ≠ a, L b` from each block, with no
additional coordinate factor. Surjective evaluation in degree `3 * m - 2`
lets `BlockExtension` correct the old coefficients in degree `3 * m`.
This proves an append step and a finite-horizon induction from an explicitly
assumed four-block span equality. Neither that finite base nor the lower-degree
interpolation hypothesis is certified in this module. The results concern all
pure path products, not the restricted econometric source combinations.
-/

namespace PanelMoments.PureCubicProducts

open scoped BigOperators
open MvPolynomial CubicRelations

noncomputable section

abbrev Point := Fin 3 → ℝ
abbrev Poly := MvPolynomial (Fin 3) ℝ
abbrev Coefficients := ℕ → Fin 3 → ℝ

/-- Exactly one cubic from each of the first `m` blocks. -/
def pureProduct (a b : Coefficients) (m : ℕ) (y : Fin m → Fin 3) : Poly :=
  ∏ t : Fin m, Geometry.blockFactor (lines (a t) (b t)) (y t)

def productSpan (a b : Coefficients) (m : ℕ) : Submodule ℝ Poly :=
  Submodule.span ℝ (Set.range (pureProduct a b m))

theorem pureProduct_mem (a b : Coefficients) (m : ℕ) (y : Fin m → Fin 3) :
    pureProduct a b m y ∈ productSpan a b m :=
  Submodule.subset_span ⟨y, rfl⟩

theorem pureProduct_snoc (a b : Coefficients) (m : ℕ)
    (y : Fin m → Fin 3) (r : Fin 3) :
    pureProduct a b (m + 1) (Fin.snoc y r) =
      pureProduct a b m y * Geometry.blockFactor (lines (a m) (b m)) r := by
  simp [pureProduct, Fin.prod_univ_castSucc]

theorem pureProduct_homogeneous (a b : Coefficients) (m : ℕ)
    (y : Fin m → Fin 3) : (pureProduct a b m y).IsHomogeneous (3 * m) := by
  simpa [pureProduct, Nat.mul_comm] using
    IsHomogeneous.prod Finset.univ
      (fun t : Fin m => Geometry.blockFactor (lines (a t) (b t)) (y t))
      (fun _ => 3) (fun t _ => blockFactor_isHomogeneous (a t) (b t) (y t))

theorem productSpan_le_homogeneous (a b : Coefficients) (m : ℕ) :
    productSpan a b m ≤ homogeneousSubmodule (Fin 3) ℝ (3 * m) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨y, rfl⟩
  exact pureProduct_homogeneous a b m y

instance productSpan_finiteDimensional (a b : Coefficients) (m : ℕ) :
    FiniteDimensional ℝ (productSpan a b m) :=
  Submodule.finiteDimensional_of_le (productSpan_le_homogeneous a b m)

/-- The same six explicit points per block as in the cubic ideal theorem. -/
def points (a b : Coefficients) (m : ℕ) (ti : Fin m × Fin 6) : Point :=
  GeneralGeometry.sixPoints (CubicIdeal.coefficientVectors (a ti.1) (b ti.1)) ti.2

def vanishingSpace (a b : Coefficients) (m : ℕ) : Submodule ℝ Poly :=
  homogeneousSubmodule (Fin 3) ℝ (3 * m) ⊓
    LinearMap.ker (LinearMap.pi fun ti : Fin m × Fin 6 =>
      (aeval (points a b m ti)).toLinearMap)

theorem mem_vanishingSpace (a b : Coefficients) (m : ℕ) (f : Poly) :
    f ∈ vanishingSpace a b m ↔
      f.IsHomogeneous (3 * m) ∧
        ∀ (t : Fin m) (i : Fin 6),
          eval (GeneralGeometry.sixPoints
            (CubicIdeal.coefficientVectors (a t) (b t)) i) f = 0 := by
  change (f.IsHomogeneous (3 * m) ∧
    (fun ti : Fin m × Fin 6 => eval (points a b m ti) f) = 0) ↔ _
  constructor
  · rintro ⟨hhom, hzero⟩
    exact ⟨hhom, fun t i => congrFun hzero (t, i)⟩
  · rintro ⟨hhom, hzero⟩
    refine ⟨hhom, ?_⟩
    funext ti
    exact hzero ti.1 ti.2

theorem pureProduct_vanishes (a b : Coefficients) (m : ℕ)
    (y : Fin m → Fin 3) (t : Fin m) (i : Fin 6) :
    eval (GeneralGeometry.sixPoints
      (CubicIdeal.coefficientVectors (a t) (b t)) i) (pureProduct a b m y) = 0 := by
  classical
  simp only [pureProduct, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ t)
    (CubicIdeal.blockFactor_zero (a t) (b t) i (y t))

theorem productSpan_le_vanishingSpace (a b : Coefficients) (m : ℕ) :
    productSpan a b m ≤ vanishingSpace a b m := by
  apply Submodule.span_le.mpr
  rintro _ ⟨y, rfl⟩
  exact (mem_vanishingSpace a b m _).mpr
    ⟨pureProduct_homogeneous a b m y, pureProduct_vanishes a b m y⟩

/-- Append one chosen cubic to every product in the old span. -/
theorem blockFactor_mul_mem_productSpan (a b : Coefficients) (m : ℕ) (r : Fin 3)
    {f : Poly} (hf : f ∈ productSpan a b m) :
    Geometry.blockFactor (lines (a m) (b m)) r * f ∈ productSpan a b (m + 1) := by
  have hle : productSpan a b m ≤
      (productSpan a b (m + 1)).comap
        (LinearMap.mulLeft ℝ (Geometry.blockFactor (lines (a m) (b m)) r)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change Geometry.blockFactor (lines (a m) (b m)) r *
      pureProduct a b m y ∈ productSpan a b (m + 1)
    have h := pureProduct_mem a b (m + 1) (Fin.snoc y r)
    rw [pureProduct_snoc] at h
    simpa only [mul_comm] using h
  exact hle hf

theorem cubicCombination_mem_productSpan (a b : Coefficients) (m : ℕ)
    (c : Fin 3 → Poly) (hc : ∀ i, c i ∈ productSpan a b m) :
    cubicCombination (a m) (b m) c ∈ productSpan a b (m + 1) := by
  unfold cubicCombination
  apply (productSpan a b (m + 1)).sum_mem
  intro i _
  simpa only [mul_comm] using blockFactor_mul_mem_productSpan a b m i (hc i)

/-- The degree-`3*m` append step. The interpolation degree is two less than
the old pure-product degree; the old span equality is an explicit hypothesis. -/
theorem productSpan_eq_vanishingSpace_succ (a b : Coefficients) (m : ℕ)
    (hm : 1 ≤ m)
    (hL : LineConditions (a m) (b m))
    (hP : GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a m) (b m)))
    (hOldP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t)))
    (hcross : ∀ (ti : Fin m × Fin 6) (i : Fin 3),
      eval (points a b m ti) (lines (a m) (b m) i) ≠ 0)
    (heval : Function.Surjective
      (HomogeneousInterpolation.evaluation (points a b m) (3 * m - 2)))
    (hspan : productSpan a b m = vanishingSpace a b m) :
    productSpan a b (m + 1) = vanishingSpace a b (m + 1) := by
  apply le_antisymm (productSpan_le_vanishingSpace a b (m + 1))
  intro f hf
  obtain ⟨hhom, hzero⟩ := (mem_vanishingSpace a b (m + 1) f).mp hf
  have hp (ti : Fin m × Fin 6) : points a b m ti ≠ 0 := by
    obtain ⟨r, hr⟩ := GeneralGeometry.sixPoints_coordinate_nonzero
      (CubicIdeal.coefficientVectors (a ti.1) (b ti.1)) (hOldP ti.1) ti.2
    intro h
    exact hr (congrFun h r)
  have hhom' : f.IsHomogeneous ((3 * m - 2) + 5) := by
    convert hhom using 1 <;> omega
  obtain ⟨c, hc_hom, hc_zero, hfc⟩ :=
    BlockExtension.exists_corrected_cubic_decomposition (points a b m) (3 * m - 2)
      hp heval (a m) (b m) hL hP hcross hhom'
      (fun ti => hzero ti.1.castSucc ti.2) (hzero (Fin.last m))
  rw [hfc]
  apply cubicCombination_mem_productSpan a b m c
  intro i
  rw [hspan]
  apply (mem_vanishingSpace a b m (c i)).mpr
  refine ⟨?_, fun t j => hc_zero i (t, j)⟩
  convert hc_hom i using 1 <;> omega

/-- Conditional pure-product induction from four blocks. Every premise is
restricted to the requested finite horizon; no infinite generic-open claim
or assertion about the restricted source combinations is made. -/
theorem productSpan_eq_vanishingSpace_of_four (a b : Coefficients) (m : ℕ)
    (hm : 4 ≤ m)
    (hL : ∀ t : Fin m, LineConditions (a t) (b t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (a t) (b t)))
    (heval : ∀ q, 4 ≤ q → q < m → Function.Surjective
      (HomogeneousInterpolation.evaluation (points a b q) (3 * q - 2)))
    (hbase : productSpan a b 4 = vanishingSpace a b 4) :
    productSpan a b m = vanishingSpace a b m := by
  have hspan : ∀ q, 4 ≤ q → q ≤ m → productSpan a b q = vanishingSpace a b q := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base =>
        intro _
        exact hbase
    | succ q hq ih =>
        intro hqm
        have hlt : q < m := by omega
        have hnewLine (ti : Fin q × Fin 6) (i : Fin 3) :
            eval (points a b q ti) (lines (a q) (b q) i) ≠ 0 := by
          let old : Fin m := ⟨ti.1, Nat.lt_trans ti.1.isLt hlt⟩
          let new : Fin m := ⟨q, hlt⟩
          have hne : old ≠ new := by
            intro h
            have hv := congrArg Fin.val h
            have ht := ti.1.isLt
            dsimp [old, new] at hv
            omega
          simpa only [points, old, new, CubicIdeal.linearForm_coefficientVectors] using
            hcross old new hne ti.2 i
        exact productSpan_eq_vanishingSpace_succ a b q (by omega)
          (hL ⟨q, hlt⟩) (hP ⟨q, hlt⟩)
          (fun t => hP ⟨t, Nat.lt_trans t.isLt hlt⟩)
          hnewLine (heval q hq hlt) (ih (by omega))
  exact hspan m hm le_rfl

end

end PanelMoments.PureCubicProducts
