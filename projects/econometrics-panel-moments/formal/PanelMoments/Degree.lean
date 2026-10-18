import PanelMoments.Polynomial
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false

/-!
# Finite restriction degree

For `Q + 1` alternatives and `T + 1` periods, the minimal cleared path numerator has
total degree at most `1 + (Q + 1) * T`. Thus three alternatives and four periods need
only monomials of total degree at most ten in the two normalized fixed effects.
-/

namespace PanelMoments

open scoped BigOperators
open MvPolynomial

noncomputable section

theorem totalDegree_effectPoly_le (Q : ℕ) (q : State Q) :
    (effectPoly Q q).totalDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) q <;> simp [effectPoly]

theorem totalDegree_numeratorPoly_le {Q : ℕ} (A : Table Q)
    (t : ℕ) (r q : State Q) :
    (C (A t r q) * effectPoly Q q).totalDegree ≤ 1 := by
  exact (totalDegree_mul _ _).trans (by simpa using totalDegree_effectPoly_le Q q)

theorem totalDegree_denominatorPoly_le {Q : ℕ} (A : Table Q) (t : ℕ) (r : State Q) :
    (denominatorPoly A t r).totalDegree ≤ 1 := by
  apply (totalDegree_finsetSum _ _).trans
  exact Finset.sup_le (fun q _ => totalDegree_numeratorPoly_le A t r q)

theorem totalDegree_otherDenominators_le {Q : ℕ} (A : Table Q)
    (t : ℕ) (r : State Q) :
    (∏ s ∈ Finset.univ.erase r, denominatorPoly A t s).totalDegree ≤ Q := by
  calc
    _ ≤ ∑ s ∈ Finset.univ.erase r, (denominatorPoly A t s).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _s ∈ Finset.univ.erase r, 1 :=
      Finset.sum_le_sum (fun s _ => totalDegree_denominatorPoly_le A t s)
    _ = Q := by simp [State]

theorem totalDegree_fullyClearedPathPoly_le {Q : ℕ} (A : Table Q)
    (T : ℕ) (r : State Q) (y : Path Q T) :
    (fullyClearedPathPoly A T r y).totalDegree ≤ (Q + 1) * T := by
  induction T generalizing A r with
  | zero => simp [fullyClearedPathPoly]
  | succ T ih =>
    simp only [fullyClearedPathPoly]
    calc
      _ ≤ ((C (A 0 r (y 0)) * effectPoly Q (y 0)) *
          (∏ s ∈ Finset.univ.erase r, denominatorPoly A 0 s)).totalDegree +
          (fullyClearedPathPoly (shift A) T (y 0) (Fin.tail y)).totalDegree :=
        totalDegree_mul _ _
      _ ≤ ((C (A 0 r (y 0)) * effectPoly Q (y 0)).totalDegree +
          (∏ s ∈ Finset.univ.erase r, denominatorPoly A 0 s).totalDegree) +
          (fullyClearedPathPoly (shift A) T (y 0) (Fin.tail y)).totalDegree :=
        Nat.add_le_add_right (totalDegree_mul _ _) _
      _ ≤ (1 + Q) + (Q + 1) * T :=
        Nat.add_le_add
          (Nat.add_le_add (totalDegree_numeratorPoly_le A 0 r (y 0))
            (totalDegree_otherDenominators_le A 0 r))
          (ih (shift A) (y 0) (Fin.tail y))
      _ = (Q + 1) * (T + 1) := by ring

def restrictionDegree (Q : ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => 1 + (Q + 1) * T

theorem totalDegree_clearedPathPoly_le {Q : ℕ} (A : Table Q)
    (T : ℕ) (r : State Q) (y : Path Q T) :
    (clearedPathPoly A T r y).totalDegree ≤ restrictionDegree Q T := by
  cases T with
  | zero => simp [clearedPathPoly, restrictionDegree]
  | succ T =>
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (totalDegree_numeratorPoly_le A 0 r (y 0))
      (totalDegree_fullyClearedPathPoly_le (shift A) T (y 0) (Fin.tail y)))

theorem clearedPathPoly_coeff_eq_zero_above_degree {Q : ℕ} (A : Table Q)
    (T : ℕ) (r : State Q) (y : Path Q T) (d : Fin Q →₀ ℕ)
    (hd : restrictionDegree Q T < d.sum (fun _ n => n)) :
    (clearedPathPoly A T r y).coeff d = 0 := by
  exact coeff_eq_zero_of_totalDegree_lt
    (lt_of_le_of_lt (totalDegree_clearedPathPoly_le A T r y) hd)

/-- It suffices to check the finitely many degrees below the explicit bound. -/
theorem isMoment_iff_bounded_coefficient_kernel {Q : ℕ} {A : Table Q}
    (hA : PositiveTable A) (T : ℕ) (r : State Q) (m : Path Q T → ℝ) :
    IsMoment A T r m ↔
      ∀ d : Fin Q →₀ ℕ, d.sum (fun _ n => n) ≤ restrictionDegree Q T →
        ∑ y, m y * (clearedPathPoly A T r y).coeff d = 0 := by
  rw [isMoment_iff_coefficient_kernel hA]
  constructor
  · intro h d _
    exact h d
  · intro h d
    by_cases hd : d.sum (fun _ n => n) ≤ restrictionDegree Q T
    · exact h d hd
    · simp only [clearedPathPoly_coeff_eq_zero_above_degree A T r _ d (Nat.lt_of_not_ge hd),
        mul_zero, Finset.sum_const_zero]

theorem three_choice_four_period_restriction_degree : restrictionDegree 2 4 = 10 := rfl

end

end PanelMoments
