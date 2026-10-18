import PanelMoments.Geometry
import PanelMoments.HomogeneousInterpolation

/-!
# Quadratic separators for one conic block

Each pair intersection is separated by the remaining conic line times the line
through the two corresponding coordinate-line intersections. Each coordinate
intersection is separated by the other two conic lines. These six quadratics
give the degree-two interpolation needed for the cubic-block induction.
-/

namespace PanelMoments.QuadraticSeparators

open MvPolynomial Geometry

noncomputable section

/-- The line through `diagonalPoint a 0` and `diagonalPoint b 1`. -/
def connector01 (a b : ℝ) : Poly :=
  C a * X 0 + C (b ^ 2) * X 1 + C (a * b ^ 2) * X 2

/-- The line through `diagonalPoint a 0` and `diagonalPoint c 2`. -/
def connector02 (a c : ℝ) : Poly :=
  X 0 + C c * X 1 + C (a * c) * X 2

/-- The line through `diagonalPoint b 1` and `diagonalPoint c 2`. -/
def connector12 (b c : ℝ) : Poly :=
  X 0 + C c * X 1 + C (b ^ 2) * X 2

theorem connector01_isHomogeneous (a b : ℝ) : (connector01 a b).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X (b ^ 2) 1)).add
    (isHomogeneous_C_mul_X (a * b ^ 2) 2)

theorem connector02_isHomogeneous (a c : ℝ) : (connector02 a c).IsHomogeneous 1 :=
  ((isHomogeneous_X ℝ 0).add (isHomogeneous_C_mul_X c 1)).add
    (isHomogeneous_C_mul_X (a * c) 2)

theorem connector12_isHomogeneous (b c : ℝ) : (connector12 b c).IsHomogeneous 1 :=
  ((isHomogeneous_X ℝ 0).add (isHomogeneous_C_mul_X c 1)).add
    (isHomogeneous_C_mul_X (b ^ 2) 2)

theorem eval_connector01_pair (a b : ℝ) :
    eval (pairPoint a b) (connector01 a b) = b * (a - b) * (a + b) := by
  simp [connector01, pairPoint]
  ring

theorem eval_connector02_pair (a c : ℝ) :
    eval (pairPoint a c) (connector02 a c) = c * (a - c) := by
  simp [connector02, pairPoint]
  ring

theorem eval_connector12_pair (b c : ℝ) :
    eval (pairPoint b c) (connector12 b c) = (b - c) * (b + c) := by
  simp [connector12, pairPoint]
  ring

/-- Pair-point separators followed by coordinate-point separators, using the
same ordering as `Geometry.localPoint`. -/
def separator (w : Fin 3 → ℝ) : Fin 6 → Poly :=
  ![conicLine (w 2) * connector01 (w 0) (w 1),
    conicLine (w 1) * connector02 (w 0) (w 2),
    conicLine (w 0) * connector12 (w 1) (w 2),
    conicLine (w 1) * conicLine (w 2),
    conicLine (w 0) * conicLine (w 2),
    conicLine (w 0) * conicLine (w 1)]

theorem separator_isHomogeneous (w : Fin 3 → ℝ) (i : Fin 6) :
    (separator w i).IsHomogeneous 2 := by
  fin_cases i <;> simp only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact (conicLine_isHomogeneous (w 2)).mul (connector01_isHomogeneous (w 0) (w 1))
  · exact (conicLine_isHomogeneous (w 1)).mul (connector02_isHomogeneous (w 0) (w 2))
  · exact (conicLine_isHomogeneous (w 0)).mul (connector12_isHomogeneous (w 1) (w 2))
  · exact (conicLine_isHomogeneous (w 1)).mul (conicLine_isHomogeneous (w 2))
  · exact (conicLine_isHomogeneous (w 0)).mul (conicLine_isHomogeneous (w 2))
  · exact (conicLine_isHomogeneous (w 0)).mul (conicLine_isHomogeneous (w 1))

theorem separator_offDiagonal (w : Fin 3 → ℝ)
    (i j : Fin 6) (hij : i ≠ j) :
    eval (localPoint w i) (separator w j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [localPoint, separator, conicLine, pairPoint, diagonalPoint,
      connector01, connector02, connector12] <;>
    ring_nf <;> simp

theorem separator_diagonal_ne_zero (w : Fin 3 → ℝ)
    (hw : ∀ r, 0 < w r) (hi : Function.Injective w) (i : Fin 6) :
    eval (localPoint w i) (separator w i) ≠ 0 := by
  have h01 : w 0 ≠ w 1 := hi.ne (by decide)
  have h02 : w 0 ≠ w 2 := hi.ne (by decide)
  have h12 : w 1 ≠ w 2 := hi.ne (by decide)
  have hn (r : Fin 3) : w r ≠ 0 := ne_of_gt (hw r)
  have hs (r s : Fin 3) : w r + w s ≠ 0 := ne_of_gt (add_pos (hw r) (hw s))
  fin_cases i <;>
    simp only [localPoint, separator, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    simp only [map_mul, eval_conicLine_pair, eval_conicLine_diagonal_zero,
      eval_conicLine_diagonal_one, eval_conicLine_diagonal_two,
      eval_connector01_pair, eval_connector02_pair, eval_connector12_pair] <;>
    simp [h01, h02, h12, h01.symm, h02.symm, h12.symm, hn, hs, sub_ne_zero]

/-- A concrete homogeneous separating family in degree two. -/
def separatingFamily (w : Fin 3 → ℝ)
    (hw : ∀ r, 0 < w r) (hi : Function.Injective w) :
    HomogeneousInterpolation.SeparatingFamily (localPoint w) 2 where
  polynomial := separator w
  homogeneous := separator_isHomogeneous w
  offDiagonal := separator_offDiagonal w
  diagonal := separator_diagonal_ne_zero w hw hi

/-- A coordinate equal to `1` or `-1` at each of the six representatives. -/
def nonzeroCoordinate : Fin 6 → Fin 3 := ![2, 2, 2, 2, 2, 1]

theorem localPoint_coordinate_ne_zero (w : Fin 3 → ℝ) (i : Fin 6) :
    localPoint w i (nonzeroCoordinate i) ≠ 0 := by
  fin_cases i <;> simp [localPoint, pairPoint, diagonalPoint, nonzeroCoordinate]

/-- The local six-point evaluations are surjective in every degree at least two. -/
theorem evaluation_surjective (w : Fin 3 → ℝ)
    (hw : ∀ r, 0 < w r) (hi : Function.Injective w)
    {d : ℕ} (hd : 2 ≤ d) :
    Function.Surjective (HomogeneousInterpolation.evaluation (localPoint w) d) :=
  (separatingFamily w hw hi).evaluation_surjective_of_le
    nonzeroCoordinate (localPoint_coordinate_ne_zero w) hd

/-- The degree-`d` homogeneous vanishing space has the expected codimension six. -/
theorem finrank_vanishing (w : Fin 3 → ℝ)
    (hw : ∀ r, 0 < w r) (hi : Function.Injective w)
    {d : ℕ} (hd : 2 ≤ d) :
    Module.finrank ℝ (HomogeneousInterpolation.vanishingSubmodule (localPoint w) d) =
      (d + 2).choose 2 - 6 := by
  simpa using (separatingFamily w hw hi).finrank_vanishing_of_le
    nonzeroCoordinate (localPoint_coordinate_ne_zero w) hd

end

end PanelMoments.QuadraticSeparators
