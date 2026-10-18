import PanelMoments.Model
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# Exact polynomial restrictions

This module clears a common, strictly positive denominator and characterizes all
fixed-effect-free moments by coefficients of an explicitly constructed polynomial.
The construction works for every finite number of alternatives and periods. It does not
compute the rank of these restrictions or identify a basis of the moment space.
-/

namespace PanelMoments

open scoped BigOperators
open MvPolynomial

noncomputable section

def effectPoly (Q : ℕ) : State Q → MvPolynomial (Fin Q) ℝ := Fin.cons 1 X

@[simp] theorem eval_effectPoly {Q : ℕ} (η : Fin Q → ℝ) (q : State Q) :
    eval η (effectPoly Q q) = effect η q := by
  refine Fin.cases ?_ (fun i => ?_) q <;> simp [effectPoly, effect]

def denominatorPoly {Q : ℕ} (A : Table Q) (t : ℕ) (r : State Q) :
    MvPolynomial (Fin Q) ℝ := ∑ q, C (A t r q) * effectPoly Q q

@[simp] theorem eval_denominatorPoly {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (t : ℕ) (r : State Q) :
    eval η (denominatorPoly A t r) = denominator A η t r := by
  simp [denominatorPoly, denominator]

/-- A common denominator, including every lag state at every period. -/
def allDenominatorPoly {Q : ℕ} (A : Table Q) : ℕ → MvPolynomial (Fin Q) ℝ
  | 0 => 1
  | T + 1 => (∏ r, denominatorPoly A 0 r) * allDenominatorPoly (shift A) T

theorem eval_allDenominatorPoly_pos {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ) :
    0 < eval η (allDenominatorPoly A T) := by
  induction T generalizing A with
  | zero => simp [allDenominatorPoly]
  | succ T ih =>
    simp only [allDenominatorPoly, map_mul, map_prod, eval_denominatorPoly]
    exact mul_pos (Finset.prod_pos (fun r _ => denominator_pos hA hη 0 r))
      (ih (shift_pos hA))

/-- The path numerator after multiplying by the common denominator. -/
def fullyClearedPathPoly {Q : ℕ} (A : Table Q) :
    (T : ℕ) → State Q → Path Q T → MvPolynomial (Fin Q) ℝ
  | 0, _, _ => 1
  | T + 1, r, y =>
      (C (A 0 r (y 0)) * effectPoly Q (y 0)) *
      (∏ s ∈ Finset.univ.erase r, denominatorPoly A 0 s) *
      fullyClearedPathPoly (shift A) T (y 0) (Fin.tail y)

/-- Exact clearing of the model likelihood; positivity justifies every cancellation. -/
theorem allDenominator_mul_likelihood {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ)
    (r : State Q) (y : Path Q T) :
    eval η (allDenominatorPoly A T) * likelihood A η T r y =
      eval η (fullyClearedPathPoly A T r y) := by
  induction T generalizing A r with
  | zero => simp [allDenominatorPoly, likelihood, fullyClearedPathPoly]
  | succ T ih =>
    simp only [allDenominatorPoly, likelihood, fullyClearedPathPoly, map_mul,
      map_prod, eval_C, eval_effectPoly, eval_denominatorPoly, transition]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    have hd := ne_of_gt (denominator_pos hA hη 0 r)
    have hi := ih (shift_pos hA) (y 0) (Fin.tail y)
    calc
      _ = (A 0 r (y 0) * effect η (y 0)) *
          (∏ s ∈ Finset.univ.erase r, denominator A η 0 s) *
          (eval η (allDenominatorPoly (shift A) T) *
            likelihood (shift A) η T (y 0) (Fin.tail y)) := by
        field_simp
      _ = _ := by rw [hi]

/-- The minimal common denominator: only the actual initial lag state occurs at time zero. -/
def commonDenominatorPoly {Q : ℕ} (A : Table Q) :
    (T : ℕ) → State Q → MvPolynomial (Fin Q) ℝ
  | 0, _ => 1
  | T + 1, r => denominatorPoly A 0 r * allDenominatorPoly (shift A) T

theorem eval_commonDenominatorPoly_pos {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ) (r : State Q) :
    0 < eval η (commonDenominatorPoly A T r) := by
  cases T with
  | zero => simp [commonDenominatorPoly]
  | succ T =>
    simp only [commonDenominatorPoly, map_mul, eval_denominatorPoly]
    exact mul_pos (denominator_pos hA hη 0 r)
      (eval_allDenominatorPoly_pos (shift_pos hA) hη T)

/-- Numerator after clearing the minimal common denominator. -/
def clearedPathPoly {Q : ℕ} (A : Table Q) :
    (T : ℕ) → State Q → Path Q T → MvPolynomial (Fin Q) ℝ
  | 0, _, _ => 1
  | T + 1, r, y => (C (A 0 r (y 0)) * effectPoly Q (y 0)) *
      fullyClearedPathPoly (shift A) T (y 0) (Fin.tail y)

/-- Exact denominator clearing with the minimal first-period factor. -/
theorem commonDenominator_mul_likelihood {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ)
    (r : State Q) (y : Path Q T) :
    eval η (commonDenominatorPoly A T r) * likelihood A η T r y =
      eval η (clearedPathPoly A T r y) := by
  cases T with
  | zero => simp [commonDenominatorPoly, likelihood, clearedPathPoly]
  | succ T =>
    simp only [commonDenominatorPoly, likelihood, clearedPathPoly, map_mul,
      eval_denominatorPoly, eval_C, eval_effectPoly, transition]
    rw [← allDenominator_mul_likelihood (shift_pos hA) hη T (y 0) (Fin.tail y)]
    have hd := ne_of_gt (denominator_pos hA hη 0 r)
    field_simp

def momentPoly {Q : ℕ} (A : Table Q) (T : ℕ) (r : State Q)
    (m : Path Q T → ℝ) : MvPolynomial (Fin Q) ℝ :=
  ∑ y, C (m y) * clearedPathPoly A T r y

theorem eval_momentPoly {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ)
    (r : State Q) (m : Path Q T → ℝ) :
    eval η (momentPoly A T r m) =
      eval η (commonDenominatorPoly A T r) * (∑ y, m y * likelihood A η T r y) := by
  simp only [momentPoly, map_sum, map_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← commonDenominator_mul_likelihood hA hη T r y]
  ring

/-- Vanishing on strictly positive fixed effects is enough to determine a polynomial. -/
theorem polynomial_eq_zero_iff_positive_evaluations {Q : ℕ}
    (p : MvPolynomial (Fin Q) ℝ) :
    p = 0 ↔ ∀ η : Fin Q → ℝ, PositiveEffects η → eval η p = 0 := by
  constructor
  · rintro rfl η _
    exact map_zero _
  · intro h
    apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ))
      (fun _ => Set.Ioi_infinite 0)
    intro η hη
    simpa only [map_zero] using h η (fun q => hη q (Set.mem_univ q))

/-- Both directions of the model-to-polynomial equivalence, on the true positive domain. -/
theorem isMoment_iff_momentPoly_eq_zero {Q : ℕ} {A : Table Q}
    (hA : PositiveTable A) (T : ℕ) (r : State Q) (m : Path Q T → ℝ) :
    IsMoment A T r m ↔ momentPoly A T r m = 0 := by
  rw [polynomial_eq_zero_iff_positive_evaluations]
  constructor
  · intro hm η hη
    rw [eval_momentPoly hA hη, hm η hη, mul_zero]
  · intro hp η hη
    have h := hp η hη
    rw [eval_momentPoly hA hη] at h
    exact (mul_eq_zero.mp h).resolve_left
      (ne_of_gt (eval_commonDenominatorPoly_pos hA hη T r))

theorem coeff_momentPoly {Q : ℕ} (A : Table Q) (T : ℕ) (r : State Q)
    (m : Path Q T → ℝ) (d : Fin Q →₀ ℕ) :
    (momentPoly A T r m).coeff d = ∑ y, m y * (clearedPathPoly A T r y).coeff d := by
  simp [momentPoly, coeff_C_mul]

/-- The exact coefficient-kernel restriction, without any assumption about its rank. -/
theorem isMoment_iff_coefficient_kernel {Q : ℕ} {A : Table Q}
    (hA : PositiveTable A) (T : ℕ) (r : State Q) (m : Path Q T → ℝ) :
    IsMoment A T r m ↔
      ∀ d : Fin Q →₀ ℕ, ∑ y, m y * (clearedPathPoly A T r y).coeff d = 0 := by
  rw [isMoment_iff_momentPoly_eq_zero hA]
  constructor
  · intro h d
    rw [← coeff_momentPoly, h]
    simp
  · intro h
    ext d
    simpa only [coeff_momentPoly, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] using h d

end

end PanelMoments
