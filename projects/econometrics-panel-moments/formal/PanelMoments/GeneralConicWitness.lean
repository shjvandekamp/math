import PanelMoments.CubicIdeal
import PanelMoments.HomogeneousEvaluation

/-!
Positive distinct conic parameters satisfy the explicit general six-point
conditions. The cross-product representatives differ from the convenient
conic representatives only by the nonzero scalar factors displayed here.
-/

namespace PanelMoments.GeneralConicWitness

open MvPolynomial GeneralGeometry

noncomputable section

def coefficients (w : Fin 3 → ℝ) := CubicIdeal.coefficientVectors w (fun r => w r ^ 2)

theorem linearForm_coefficients (w : Fin 3 → ℝ) (r : Fin 3) :
    linearForm (coefficients w r) = Geometry.conicLine (w r) := by
  simp [linearForm, coefficients, CubicIdeal.coefficientVectors, Geometry.conicLine]

def pointScale (w : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![w 1 - w 0, w 2 - w 0, w 2 - w 1, -w 0, -1, -1]

def separatorScale (w : Fin 3 → ℝ) : Fin 6 → ℝ := ![w 0, -w 0, 1, 1, 1, 1]

theorem sixPoints_coefficients (w : Fin 3 → ℝ) (i : Fin 6) :
    sixPoints (coefficients w) i = pointScale w i • Geometry.localPoint w i := by
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [sixPoints, coefficients, CubicIdeal.coefficientVectors, cross,
      coordinatePoint, coordinateVector, pointScale, Geometry.localPoint,
      Geometry.pairPoint, Geometry.diagonalPoint] <;> ring

theorem separator_coefficients (w : Fin 3 → ℝ) (i : Fin 6) :
    separator (coefficients w) i = separatorScale w i • QuadraticSeparators.separator w i := by
  fin_cases i <;>
    simp [separator, coefficients, CubicIdeal.coefficientVectors, cross,
      coordinatePoint, coordinateVector, linearForm, separatorScale,
      QuadraticSeparators.separator, QuadraticSeparators.connector01,
      QuadraticSeparators.connector02, QuadraticSeparators.connector12,
      Geometry.conicLine, smul_eq_C_mul] <;> ring

theorem pointScale_ne_zero (w : Fin 3 → ℝ) (hw : ∀ r, 0 < w r)
    (hi : Function.Injective w) (i : Fin 6) : pointScale w i ≠ 0 := by
  have h10 : w 1 ≠ w 0 := hi.ne (by decide)
  have h20 : w 2 ≠ w 0 := hi.ne (by decide)
  have h21 : w 2 ≠ w 1 := hi.ne (by decide)
  fin_cases i <;> simp [pointScale, sub_ne_zero, h10, h20, h21, ne_of_gt (hw 0)]

theorem separatorScale_ne_zero (w : Fin 3 → ℝ) (hw : ∀ r, 0 < w r)
    (i : Fin 6) : separatorScale w i ≠ 0 := by
  fin_cases i <;> simp [separatorScale, ne_of_gt (hw 0)]

theorem localNondegenerate (w : Fin 3 → ℝ) (hw : ∀ r, 0 < w r)
    (hi : Function.Injective w) : LocalNondegenerate (coefficients w) := by
  intro i
  rw [separator_coefficients, sixPoints_coefficients, smul_eq_C_mul, map_mul, eval_C,
    HomogeneousEvaluation.eval_smul_of_isHomogeneous
      (QuadraticSeparators.separator_isHomogeneous w i)]
  exact mul_ne_zero (separatorScale_ne_zero w hw i)
    (mul_ne_zero (pow_ne_zero 2 (pointScale_ne_zero w hw hi i))
      (QuadraticSeparators.separator_diagonal_ne_zero w hw hi i))

theorem lineConditions (w : Fin 3 → ℝ) (hw : ∀ r, 0 < w r)
    (hi : Function.Injective w) : CubicRelations.LineConditions w (fun r => w r ^ 2) where
  nonCoordinate i := Or.inl (ne_of_gt (hw i))
  distinct i j hij := Or.inl (hi.ne hij)

theorem otherLine_nonzero (w : Fin 3 → ℝ) (hw : ∀ r, 0 < w r)
    (hi : Function.Injective w) {v : ℝ} (hv : 0 < v) (hvne : ∀ r, v ≠ w r)
    (i : Fin 6) : eval (sixPoints (coefficients w) i) (Geometry.conicLine v) ≠ 0 := by
  rw [sixPoints_coefficients,
    HomogeneousEvaluation.eval_smul_of_isHomogeneous (Geometry.conicLine_isHomogeneous v), pow_one]
  exact mul_ne_zero (pointScale_ne_zero w hw hi i)
    (GlobalInterpolation.otherLine_nonzero w hw hv hvne i)

variable {ι : Type*}

theorem crossNonincident (w : ι → Fin 3 → ℝ) (hw : ∀ b r, 0 < w b r)
    (hi : Function.Injective (fun br : ι × Fin 3 => w br.1 br.2)) :
    CrossNonincident (fun b => coefficients (w b)) := by
  intro b c hbc i r
  rw [linearForm_coefficients]
  apply otherLine_nonzero (w b) (hw b)
    (fun r s hrs => by
      have hpair : (b, r) = (b, s) := hi hrs
      exact congrArg Prod.snd hpair) (hw c r) _ i
  intro s h
  have hpair : (c, r) = (b, s) := hi h
  exact hbc (congrArg Prod.fst hpair).symm

end

end PanelMoments.GeneralConicWitness
