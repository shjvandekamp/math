import PanelMoments.GlobalInterpolation

/-!
Polynomial formulas for the six points and their quadratic separators in an
arbitrary three-line block. The nonzero separator values are explicit algebraic
conditions; no dimension assertion occurs in their definition.
-/

namespace PanelMoments.GeneralGeometry

open MvPolynomial

noncomputable section

abbrev Point := Fin 3 → ℝ
abbrev Poly := MvPolynomial (Fin 3) ℝ

def linearForm (v : Point) : Poly := C (v 0) * X 0 + C (v 1) * X 1 + C (v 2) * X 2

def cross (v w : Point) : Point :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]

def coordinateVector (i : Fin 3) : Point := fun j => if j = i then 1 else 0

theorem linearForm_homogeneous (v : Point) : (linearForm v).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X (v 0) 0).add (isHomogeneous_C_mul_X (v 1) 1)).add
    (isHomogeneous_C_mul_X (v 2) 2)

theorem eval_linearForm_cross_left (v w : Point) :
    eval (cross v w) (linearForm v) = 0 := by
  simp [linearForm, cross]
  ring

theorem eval_linearForm_cross_right (v w : Point) :
    eval (cross v w) (linearForm w) = 0 := by
  simp [linearForm, cross]
  ring

theorem cross_coordinate (v : Point) (i : Fin 3) :
    cross v (coordinateVector i) i = 0 := by
  fin_cases i <;> simp [cross, coordinateVector]

@[simp] theorem eval_linearForm_zero (v : Point) : eval (0 : Point) (linearForm v) = 0 := by
  simp [linearForm]

theorem eval_linearForm_smul (v p : Point) (c : ℝ) :
    eval (c • p) (linearForm v) = c * eval p (linearForm v) := by
  simp [linearForm]
  ring

def coordinatePoint (l : Fin 3 → Point) (i : Fin 3) : Point :=
  cross (l i) (coordinateVector i)

def sixPoints (l : Fin 3 → Point) : Fin 6 → Point :=
  ![cross (l 0) (l 1), cross (l 0) (l 2), cross (l 1) (l 2),
    coordinatePoint l 0, coordinatePoint l 1, coordinatePoint l 2]

def separator (l : Fin 3 → Point) : Fin 6 → Poly :=
  ![linearForm (l 2) * linearForm (cross (coordinatePoint l 0) (coordinatePoint l 1)),
    linearForm (l 1) * linearForm (cross (coordinatePoint l 0) (coordinatePoint l 2)),
    linearForm (l 0) * linearForm (cross (coordinatePoint l 1) (coordinatePoint l 2)),
    linearForm (l 1) * linearForm (l 2),
    linearForm (l 0) * linearForm (l 2),
    linearForm (l 0) * linearForm (l 1)]

theorem separator_homogeneous (l : Fin 3 → Point) (i : Fin 6) :
    (separator l i).IsHomogeneous 2 := by
  fin_cases i <;> exact (linearForm_homogeneous _).mul (linearForm_homogeneous _)

theorem separator_offDiagonal (l : Fin 3 → Point) (i j : Fin 6) (hij : i ≠ j) :
    eval (sixPoints l i) (separator l j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [sixPoints, separator, coordinatePoint, linearForm, cross, coordinateVector] <;>
    ring_nf <;> simp

theorem eval_separator_smul (l : Fin 3 → Point) (i : Fin 6) (p : Point) (c : ℝ) :
    eval (c • p) (separator l i) = c ^ 2 * eval p (separator l i) := by
  fin_cases i <;> simp only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ',
    map_mul, eval_linearForm_smul] <;> ring

/-- The six nonzero values defining local interpolation are model primitives. -/
def LocalNondegenerate (l : Fin 3 → Point) : Prop :=
  ∀ i, eval (sixPoints l i) (separator l i) ≠ 0

def separatingFamily (l : Fin 3 → Point) (hl : LocalNondegenerate l) :
    HomogeneousInterpolation.SeparatingFamily (sixPoints l) 2 where
  polynomial := separator l
  homogeneous := separator_homogeneous l
  offDiagonal := separator_offDiagonal l
  diagonal := hl

theorem sixPoints_coordinate_nonzero (l : Fin 3 → Point) (hl : LocalNondegenerate l)
    (i : Fin 6) : ∃ j, sixPoints l i j ≠ 0 := by
  by_contra h
  push Not at h
  have hp : sixPoints l i = 0 := funext h
  apply hl i
  rw [hp]
  fin_cases i <;> simp [separator, linearForm]

def blockProduct (l : Fin 3 → Point) : Poly :=
  linearForm (l 0) * linearForm (l 1) * linearForm (l 2)

theorem blockProduct_homogeneous (l : Fin 3 → Point) :
    (blockProduct l).IsHomogeneous 3 :=
  ((linearForm_homogeneous _).mul (linearForm_homogeneous _)).mul (linearForm_homogeneous _)

theorem blockProduct_zero (l : Fin 3 → Point) (i : Fin 6) :
    eval (sixPoints l i) (blockProduct l) = 0 := by
  fin_cases i <;>
    simp [blockProduct, sixPoints, coordinatePoint, eval_linearForm_cross_left,
      eval_linearForm_cross_right]

theorem blockFactor_zero (l : Fin 3 → Point) (i : Fin 6) (r : Fin 3) :
    eval (sixPoints l i) (Geometry.blockFactor (fun j => linearForm (l j)) r) = 0 := by
  fin_cases i
  · apply Geometry.eval_blockFactor_pair _ _ 0 1 (by decide)
    · exact eval_linearForm_cross_left _ _
    · exact eval_linearForm_cross_right _ _
  · apply Geometry.eval_blockFactor_pair _ _ 0 2 (by decide)
    · exact eval_linearForm_cross_left _ _
    · exact eval_linearForm_cross_right _ _
  · apply Geometry.eval_blockFactor_pair _ _ 1 2 (by decide)
    · exact eval_linearForm_cross_left _ _
    · exact eval_linearForm_cross_right _ _
  · apply Geometry.eval_blockFactor_diagonal _ _ 0
    · exact cross_coordinate _ _
    · exact eval_linearForm_cross_left _ _
  · apply Geometry.eval_blockFactor_diagonal _ _ 1
    · exact cross_coordinate _ _
    · exact eval_linearForm_cross_left _ _
  · apply Geometry.eval_blockFactor_diagonal _ _ 2
    · exact cross_coordinate _ _
    · exact eval_linearForm_cross_left _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No point from one block lies on a line from another block. -/
def CrossNonincident (l : ι → Fin 3 → Point) : Prop :=
  ∀ b c, b ≠ c → ∀ i r, eval (sixPoints (l b) i) (linearForm (l c r)) ≠ 0

def globalSeparatingFamily (l : ι → Fin 3 → Point)
    (hl : ∀ b, LocalNondegenerate (l b)) (hc : CrossNonincident l) :
    HomogeneousInterpolation.SeparatingFamily
      (fun bi : ι × Fin 6 => sixPoints (l bi.1) bi.2)
      (2 + (Fintype.card ι - 1) * 3) := by
  apply GlobalInterpolation.assemble _ (fun b => separatingFamily (l b) (hl b))
    (fun b => blockProduct (l b)) (fun b => blockProduct_homogeneous (l b))
    (fun b i => blockProduct_zero (l b) i)
  intro b c hbc i
  simpa only [blockProduct, map_mul] using
    mul_ne_zero (mul_ne_zero (hc b c hbc i 0) (hc b c hbc i 1)) (hc b c hbc i 2)

theorem global_evaluation_surjective (l : ι → Fin 3 → Point)
    (hl : ∀ b, LocalNondegenerate (l b)) (hc : CrossNonincident l)
    {e : ℕ} (he : 2 + (Fintype.card ι - 1) * 3 ≤ e) :
    Function.Surjective (HomogeneousInterpolation.evaluation
      (fun bi : ι × Fin 6 => sixPoints (l bi.1) bi.2) e) := by
  classical
  let c (bi : ι × Fin 6) := Classical.choose (sixPoints_coordinate_nonzero (l bi.1) (hl bi.1) bi.2)
  have hn (bi : ι × Fin 6) : sixPoints (l bi.1) bi.2 (c bi) ≠ 0 :=
    Classical.choose_spec (sixPoints_coordinate_nonzero (l bi.1) (hl bi.1) bi.2)
  exact (globalSeparatingFamily l hl hc).evaluation_surjective_of_le c hn he

theorem global_finrank_vanishing (l : ι → Fin 3 → Point)
    (hl : ∀ b, LocalNondegenerate (l b)) (hc : CrossNonincident l)
    {e : ℕ} (he : 2 + (Fintype.card ι - 1) * 3 ≤ e) :
    Module.finrank ℝ (HomogeneousInterpolation.vanishingSubmodule
      (fun bi : ι × Fin 6 => sixPoints (l bi.1) bi.2) e) =
      (e + 2).choose 2 - 6 * Fintype.card ι := by
  classical
  let c (bi : ι × Fin 6) := Classical.choose (sixPoints_coordinate_nonzero (l bi.1) (hl bi.1) bi.2)
  have hn (bi : ι × Fin 6) : sixPoints (l bi.1) bi.2 (c bi) ≠ 0 :=
    Classical.choose_spec (sixPoints_coordinate_nonzero (l bi.1) (hl bi.1) bi.2)
  simpa [Fintype.card_prod, Nat.mul_comm] using
    (globalSeparatingFamily l hl hc).finrank_vanishing_of_le c hn he

end

end PanelMoments.GeneralGeometry
