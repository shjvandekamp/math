import PanelMoments.Polynomial
import PanelMoments.Geometry
import PanelMoments.HomogeneousEvaluation

set_option autoImplicit false

/-!
# Homogeneous cleared likelihoods for three alternatives

For `m + 1` observed transitions, the reduced homogeneous path polynomial
has degree `3 * m + 1`. Its first cubic block uses time one and the first
observed state as its lag; time zero contributes only to the positive path
weight. Dehomogenizing and restoring this weight gives exactly the model's
minimally cleared likelihood numerator.
-/

namespace PanelMoments.HomogeneousLikelihood

open scoped BigOperators
open MvPolynomial HomogeneousEvaluation

noncomputable section

abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- The homogeneous denominator for one time and lag state. -/
def homogeneousDenominator (A : Table 2) (t : ℕ) (r : State 2) : Poly :=
  ∑ q, C (A t r q) * X q

/-- The product of primitive table entries along the path, without effects. -/
def pathWeight (A : Table 2) : (T : ℕ) → State 2 → Path 2 T → ℝ
  | 0, _, _ => 1
  | T + 1, r, y => A 0 r (y 0) * pathWeight (shift A) T (y 0) (Fin.tail y)

/-- The path polynomial after removing its positive scalar path weight.
The `m` cubic factors correspond to times one through `m`. -/
def reducedPath (A : Table 2) : (m : ℕ) → Path 2 (m + 1) → Poly
  | 0, y => X (y 0)
  | m + 1, y =>
      Geometry.blockFactor (homogeneousDenominator A 1) (y 0) *
        reducedPath (shift A) m (Fin.tail y)

theorem pathWeight_pos {A : Table 2} (hA : PositiveTable A) (T : ℕ)
    (r : State 2) (y : Path 2 T) : 0 < pathWeight A T r y := by
  induction T generalizing A r with
  | zero => exact zero_lt_one
  | succ T ih =>
    exact mul_pos (hA 0 r (y 0)) (ih (shift_pos hA) (y 0) (Fin.tail y))

theorem homogeneousDenominator_isHomogeneous (A : Table 2) (t : ℕ) (r : State 2) :
    (homogeneousDenominator A t r).IsHomogeneous 1 := by
  apply IsHomogeneous.sum Finset.univ _ 1
  intro q _
  exact isHomogeneous_C_mul_X (A t r q) q

theorem homogeneousBlock_isHomogeneous (A : Table 2) (t : ℕ) (r : State 2) :
    (Geometry.blockFactor (homogeneousDenominator A t) r).IsHomogeneous 3 := by
  have hprod :
      (∏ s ∈ Finset.univ.erase r, homogeneousDenominator A t s).IsHomogeneous 2 := by
    have h := IsHomogeneous.prod (Finset.univ.erase r)
      (homogeneousDenominator A t) (fun _ => 1)
      (fun s _ => homogeneousDenominator_isHomogeneous A t s)
    simpa [Finset.card_erase_of_mem, State] using h
  exact (isHomogeneous_X ℝ r).mul hprod

theorem reducedPath_isHomogeneous (A : Table 2) (m : ℕ) (y : Path 2 (m + 1)) :
    (reducedPath A m y).IsHomogeneous (3 * m + 1) := by
  induction m generalizing A with
  | zero => simpa only [reducedPath, Nat.mul_zero, Nat.zero_add] using
      isHomogeneous_X ℝ (y 0)
  | succ m ih =>
    change (Geometry.blockFactor (homogeneousDenominator A 1) (y 0) *
      reducedPath (shift A) m (Fin.tail y)).IsHomogeneous (3 * (m + 1) + 1)
    convert (homogeneousBlock_isHomogeneous A 1 (y 0)).mul
      (ih (shift A) (Fin.tail y)) using 1 <;> ring

@[simp]
theorem dehomogenize_C (a : ℝ) : dehomogenize (C a) = C a := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_homogeneousDenominator (A : Table 2) (t : ℕ) (r : State 2) :
    dehomogenize (homogeneousDenominator A t r) = denominatorPoly A t r := by
  simp only [homogeneousDenominator, denominatorPoly, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul]
  exact congrArg₂ (fun a b : HomogeneousEvaluation.EffectPoly => a * b)
    (dehomogenize_C (A t r q)) (dehomogenize_X q)

theorem dehomogenize_blockFactor (A : Table 2) (t : ℕ) (r : State 2) :
    dehomogenize (Geometry.blockFactor (homogeneousDenominator A t) r) =
      effectPoly 2 r * ∏ s ∈ Finset.univ.erase r, denominatorPoly A t s := by
  simp only [Geometry.blockFactor, map_mul, map_prod, dehomogenize_X,
    dehomogenize_homogeneousDenominator]

theorem denominatorPoly_shift_zero (A : Table 2) (r : State 2) :
    denominatorPoly (shift A) 0 r = denominatorPoly A 1 r := rfl

/-- Exposing the first cubic block separates the initial transition weight
from the minimally cleared numerator of the shifted tail. -/
theorem clearedPathPoly_succ_succ (A : Table 2) (m : ℕ) (r : State 2)
    (y : Path 2 (m + 2)) :
    clearedPathPoly A (m + 2) r y =
      C (A 0 r (y 0)) *
        (effectPoly 2 (y 0) *
          ∏ s ∈ Finset.univ.erase (y 0), denominatorPoly A 1 s) *
        clearedPathPoly (shift A) (m + 1) (y 0) (Fin.tail y) := by
  simp only [clearedPathPoly, fullyClearedPathPoly, denominatorPoly_shift_zero]
  ring

/-- The homogeneous construction is exactly the true cleared likelihood
numerator after dehomogenization and restoration of its path weight. -/
theorem pathWeight_mul_dehomogenize_reducedPath (A : Table 2) (m : ℕ)
    (r : State 2) (y : Path 2 (m + 1)) :
    C (pathWeight A (m + 1) r y) * dehomogenize (reducedPath A m y) =
      clearedPathPoly A (m + 1) r y := by
  induction m generalizing A r with
  | zero =>
    simp [pathWeight, reducedPath, clearedPathPoly, fullyClearedPathPoly,
      dehomogenize_X]
  | succ m ih =>
    calc
      _ = C (A 0 r (y 0)) *
          (effectPoly 2 (y 0) *
            ∏ s ∈ Finset.univ.erase (y 0), denominatorPoly A 1 s) *
          (C (pathWeight (shift A) (m + 1) (y 0) (Fin.tail y)) *
            dehomogenize (reducedPath (shift A) m (Fin.tail y))) := by
        simp only [pathWeight, reducedPath, map_mul, dehomogenize_blockFactor]
        ring
      _ = clearedPathPoly A (m + 2) r y := by
        rw [ih (shift A) (y 0) (Fin.tail y)]
        exact (clearedPathPoly_succ_succ A m r y).symm

/-- The homogeneous polynomial whose vanishing expresses a model moment. -/
def homogeneousMoment (A : Table 2) (m : ℕ) (r : State 2)
    (μ : Path 2 (m + 1) → ℝ) : Poly :=
  ∑ y, C (μ y * pathWeight A (m + 1) r y) * reducedPath A m y

theorem homogeneousMoment_isHomogeneous (A : Table 2) (m : ℕ) (r : State 2)
    (μ : Path 2 (m + 1) → ℝ) :
    (homogeneousMoment A m r μ).IsHomogeneous (3 * m + 1) := by
  apply IsHomogeneous.sum Finset.univ _ (3 * m + 1)
  intro y _
  exact (reducedPath_isHomogeneous A m y).C_mul _

@[simp]
theorem dehomogenize_homogeneousMoment (A : Table 2) (m : ℕ) (r : State 2)
    (μ : Path 2 (m + 1) → ℝ) :
    dehomogenize (homogeneousMoment A m r μ) = momentPoly A (m + 1) r μ := by
  simp only [homogeneousMoment, momentPoly, map_sum, map_mul, dehomogenize_C,
    mul_assoc, pathWeight_mul_dehomogenize_reducedPath]

/-- On the positive economic domain, a moment is equivalent to a vanishing
homogeneous polynomial of the fixed degree `3 * m + 1`. -/
theorem isMoment_iff_homogeneousMoment_eq_zero {A : Table 2} (hA : PositiveTable A)
    (m : ℕ) (r : State 2) (μ : Path 2 (m + 1) → ℝ) :
    IsMoment A (m + 1) r μ ↔ homogeneousMoment A m r μ = 0 := by
  calc
    IsMoment A (m + 1) r μ ↔ momentPoly A (m + 1) r μ = 0 :=
      isMoment_iff_momentPoly_eq_zero hA (m + 1) r μ
    _ ↔ dehomogenize (homogeneousMoment A m r μ) = 0 := by
      rw [dehomogenize_homogeneousMoment]
    _ ↔ homogeneousMoment A m r μ = 0 :=
      dehomogenize_eq_zero_iff (homogeneousMoment_isHomogeneous A m r μ)

end

end PanelMoments.HomogeneousLikelihood
