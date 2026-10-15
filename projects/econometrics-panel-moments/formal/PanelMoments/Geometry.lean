import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Projective vanishing conditions for three alternatives

This module works with the three homogeneous fixed-effect coordinates. It proves
the structural vanishing of the factors `η_r ∏_{s ≠ r} L_s` and constructs six
explicit separating polynomials for the conic line configuration `(1,w,w²)`.
These are geometric results; the model-to-geometry and generic-rank bridges are
separate obligations.
-/

namespace PanelMoments.Geometry

open scoped BigOperators
open MvPolynomial

noncomputable section

abbrev Point := Fin 3 → ℝ
abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- The factor associated with the lag state in one denominator block. -/
def blockFactor (L : Fin 3 → Poly) (r : Fin 3) : Poly :=
  X r * ∏ s ∈ Finset.univ.erase r, L s

theorem eval_blockFactor_pair (L : Fin 3 → Poly) (p : Point)
    (a b : Fin 3) (hab : a ≠ b) (ha : eval p (L a) = 0)
    (hb : eval p (L b) = 0) (r : Fin 3) :
    eval p (blockFactor L r) = 0 := by
  classical
  simp only [blockFactor, map_mul, eval_X, map_prod]
  apply mul_eq_zero_of_right
  by_cases hra : r = a
  · subst r
    exact Finset.prod_eq_zero (by simp [hab.symm]) hb
  · exact Finset.prod_eq_zero (by simp [Ne.symm hra]) ha

theorem eval_blockFactor_diagonal (L : Fin 3 → Poly) (p : Point)
    (a : Fin 3) (hη : p a = 0) (hL : eval p (L a) = 0) (r : Fin 3) :
    eval p (blockFactor L r) = 0 := by
  classical
  simp only [blockFactor, map_mul, eval_X, map_prod]
  by_cases hra : r = a
  · simp [hra, hη]
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (by simp [Ne.symm hra]) hL)

/-- The normalized positive table `(1,w,w²)` gives this homogeneous denominator. -/
def conicLine (w : ℝ) : Poly := X 0 + C w * X 1 + C (w ^ 2) * X 2

def pairPoint (u v : ℝ) : Point := ![u * v, -(u + v), 1]

def diagonalPoint (w : ℝ) : Fin 3 → Point :=
  ![![0, -w, 1], ![w ^ 2, 0, -1], ![-w, 1, 0]]

theorem eval_conicLine (w : ℝ) (p : Point) :
    eval p (conicLine w) = p 0 + w * p 1 + w ^ 2 * p 2 := by
  simp [conicLine]

theorem eval_conicLine_pair (w u v : ℝ) :
    eval (pairPoint u v) (conicLine w) = (w - u) * (w - v) := by
  simp [eval_conicLine, pairPoint]
  ring

theorem eval_conicLine_diagonal_zero (v w : ℝ) :
    eval (diagonalPoint w 0) (conicLine v) = v * (v - w) := by
  simp [eval_conicLine, diagonalPoint]
  ring

theorem eval_conicLine_diagonal_one (v w : ℝ) :
    eval (diagonalPoint w 1) (conicLine v) = (w - v) * (w + v) := by
  simp [eval_conicLine, diagonalPoint]
  ring

theorem eval_conicLine_diagonal_two (v w : ℝ) :
    eval (diagonalPoint w 2) (conicLine v) = v - w := by
  simp [eval_conicLine, diagonalPoint]
  ring

theorem eval_conicLine_pair_ne_zero {w u v : ℝ} (hwu : w ≠ u) (hwv : w ≠ v) :
    eval (pairPoint u v) (conicLine w) ≠ 0 := by
  rw [eval_conicLine_pair]
  exact mul_ne_zero (sub_ne_zero.mpr hwu) (sub_ne_zero.mpr hwv)

theorem eval_conicLine_diagonal_ne_zero {v w : ℝ} (hv : 0 < v) (hw : 0 < w)
    (hvw : v ≠ w) (a : Fin 3) :
    eval (diagonalPoint w a) (conicLine v) ≠ 0 := by
  fin_cases a
  · change eval (diagonalPoint w 0) (conicLine v) ≠ 0
    rw [eval_conicLine_diagonal_zero]
    exact mul_ne_zero (ne_of_gt hv) (sub_ne_zero.mpr hvw)
  · change eval (diagonalPoint w 1) (conicLine v) ≠ 0
    rw [eval_conicLine_diagonal_one]
    exact mul_ne_zero (sub_ne_zero.mpr hvw.symm) (ne_of_gt (add_pos hw hv))
  · change eval (diagonalPoint w 2) (conicLine v) ≠ 0
    rw [eval_conicLine_diagonal_two]
    exact sub_ne_zero.mpr hvw

/-- Three pair intersections followed by the three coordinate-line intersections. -/
def localPoint (w : Fin 3 → ℝ) : Fin 6 → Point :=
  ![pairPoint (w 0) (w 1), pairPoint (w 0) (w 2), pairPoint (w 1) (w 2),
    diagonalPoint (w 0) 0, diagonalPoint (w 1) 1, diagonalPoint (w 2) 2]

/-- Homogeneous degree-four separators, in the same order as `localPoint`. -/
def localSeparator (w : Fin 3 → ℝ) : Fin 6 → Poly :=
  ![conicLine (w 2) * X 0 ^ 2 * X 1,
    conicLine (w 1) * X 0 ^ 2 * X 2,
    conicLine (w 0) * X 1 ^ 2 * X 2,
    conicLine (w 1) * conicLine (w 2) * X 1 ^ 2,
    conicLine (w 0) * conicLine (w 2) * X 0 ^ 2,
    conicLine (w 0) * conicLine (w 1) * X 0 ^ 2]

theorem localSeparator_off_diagonal (w : Fin 3 → ℝ)
    (i j : Fin 6) (hij : i ≠ j) :
    eval (localPoint w i) (localSeparator w j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [localPoint, localSeparator, conicLine, pairPoint, diagonalPoint] <;>
    ring_nf <;> simp

theorem localSeparator_diagonal_ne_zero (w : Fin 3 → ℝ)
    (hw : ∀ r, 0 < w r) (hi : Function.Injective w) (i : Fin 6) :
    eval (localPoint w i) (localSeparator w i) ≠ 0 := by
  have h01 : w 0 ≠ w 1 := hi.ne (by decide)
  have h02 : w 0 ≠ w 2 := hi.ne (by decide)
  have h12 : w 1 ≠ w 2 := hi.ne (by decide)
  have hn (r : Fin 3) : w r ≠ 0 := ne_of_gt (hw r)
  have hs (r s : Fin 3) : w r + w s ≠ 0 := ne_of_gt (add_pos (hw r) (hw s))
  have hns (r s : Fin 3) : -w r + -w s ≠ 0 := by
    rw [← neg_add]
    exact neg_ne_zero.mpr (hs r s)
  fin_cases i <;> simp only [localPoint, localSeparator,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    simp only [map_mul, map_pow, eval_X,
      eval_conicLine_pair, eval_conicLine_diagonal_zero,
      eval_conicLine_diagonal_one, eval_conicLine_diagonal_two] <;>
    simp [pairPoint, diagonalPoint, h01, h02, h12, h01.symm, h02.symm, h12.symm,
      hn, hs, hns, sub_ne_zero]

theorem conicLine_isHomogeneous (w : ℝ) : (conicLine w).IsHomogeneous 1 :=
  ((isHomogeneous_X ℝ 0).add (isHomogeneous_C_mul_X w 1)).add
    (isHomogeneous_C_mul_X (w ^ 2) 2)

theorem localSeparator_isHomogeneous (w : Fin 3 → ℝ) (i : Fin 6) :
    (localSeparator w i).IsHomogeneous 4 := by
  fin_cases i <;> simp only [localSeparator, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact ((conicLine_isHomogeneous (w 2)).mul (isHomogeneous_X_pow (0 : Fin 3) 2)).mul
      (isHomogeneous_X ℝ 1)
  · exact ((conicLine_isHomogeneous (w 1)).mul (isHomogeneous_X_pow (0 : Fin 3) 2)).mul
      (isHomogeneous_X ℝ 2)
  · exact ((conicLine_isHomogeneous (w 0)).mul (isHomogeneous_X_pow (1 : Fin 3) 2)).mul
      (isHomogeneous_X ℝ 2)
  · exact ((conicLine_isHomogeneous (w 1)).mul (conicLine_isHomogeneous (w 2))).mul
      (isHomogeneous_X_pow (1 : Fin 3) 2)
  · exact ((conicLine_isHomogeneous (w 0)).mul (conicLine_isHomogeneous (w 2))).mul
      (isHomogeneous_X_pow (0 : Fin 3) 2)
  · exact ((conicLine_isHomogeneous (w 0)).mul (conicLine_isHomogeneous (w 1))).mul
      (isHomogeneous_X_pow (0 : Fin 3) 2)

theorem localPoint_blockFactor_zero (w : Fin 3 → ℝ) (i : Fin 6) (r : Fin 3) :
    eval (localPoint w i) (blockFactor (fun a => conicLine (w a)) r) = 0 := by
  fin_cases i
  · apply eval_blockFactor_pair _ _ 0 1 (by decide)
    all_goals simp [localPoint, eval_conicLine_pair]
  · apply eval_blockFactor_pair _ _ 0 2 (by decide)
    all_goals simp [localPoint, eval_conicLine_pair]
  · apply eval_blockFactor_pair _ _ 1 2 (by decide)
    all_goals simp [localPoint, eval_conicLine_pair]
  · apply eval_blockFactor_diagonal _ _ 0
    all_goals simp [localPoint, eval_conicLine, diagonalPoint] <;> ring
  · apply eval_blockFactor_diagonal _ _ 1
    all_goals simp [localPoint, eval_conicLine, diagonalPoint]
  · apply eval_blockFactor_diagonal _ _ 2
    all_goals simp [localPoint, eval_conicLine, diagonalPoint]

/-- Homogeneous polynomials of degree four in the three fixed-effect coordinates. -/
abbrev Quartic := homogeneousSubmodule (Fin 3) ℝ 4

/-- Evaluation at one of the six explicit points, restricted to homogeneous quartics. -/
def localEvaluation (w : Fin 3 → ℝ) (i : Fin 6) : Quartic →ₗ[ℝ] ℝ :=
  (aeval (localPoint w i)).toLinearMap.comp (homogeneousSubmodule (Fin 3) ℝ 4).subtype

@[simp] theorem localEvaluation_apply (w : Fin 3 → ℝ) (i : Fin 6) (p : Quartic) :
    localEvaluation w i p = eval (localPoint w i) p.1 := rfl

/-- Six independent linear conditions on homogeneous quartics. The proof uses
the constructed separators and assumes only positive, distinct conic parameters. -/
theorem localEvaluation_linearIndependent (w : Fin 3 → ℝ)
    (hw : ∀ r, 0 < w r) (hi : Function.Injective w) :
    LinearIndependent ℝ (localEvaluation w) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi_mem
  let p : Quartic := ⟨localSeparator w i, localSeparator_isHomogeneous w i⟩
  have he := congrArg (fun f : Quartic →ₗ[ℝ] ℝ => f p) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, localEvaluation_apply] at he
  change (∑ j ∈ s, c j * eval (localPoint w j) (localSeparator w i)) = 0 at he
  rw [Finset.sum_eq_single i] at he
  · exact (mul_eq_zero.mp he).resolve_right (localSeparator_diagonal_ne_zero w hw hi i)
  · intro j _ hji
    rw [localSeparator_off_diagonal w j i hji, mul_zero]
  · intro h
    exact (h hi_mem).elim

end

end PanelMoments.Geometry
