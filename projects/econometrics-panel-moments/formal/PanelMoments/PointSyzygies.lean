import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Coordinate relations at a projective point

At any nonzero real point, the three coordinate Koszul relations span the
kernel of the coordinate functional. When three line values are nonzero,
multiplication by those values transfers this spanning statement to the
evaluated cubic block generators.
-/

namespace PanelMoments.PointSyzygies

open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- The three coordinate relations span the kernel at every nonzero point. -/
theorem coordinate_syzygy (x b : Point) (hx : x ≠ 0)
    (h : ∑ i, x i * b i = 0) :
    ∃ c₀₁ c₀₂ c₁₂ : ℝ,
      b 0 = -x 1 * c₀₁ - x 2 * c₀₂ ∧
      b 1 = x 0 * c₀₁ - x 2 * c₁₂ ∧
      b 2 = x 0 * c₀₂ + x 1 * c₁₂ := by
  have hthree : x 0 * b 0 + x 1 * b 1 + x 2 * b 2 = 0 := by
    simpa only [Fin.sum_univ_three] using h
  by_cases hx₀ : x 0 ≠ 0
  · refine ⟨b 1 / x 0, b 2 / x 0, 0, ?_, ?_, ?_⟩
    · field_simp [hx₀]
      linear_combination hthree
    · field_simp [hx₀] <;> ring
    · field_simp [hx₀] <;> ring
  have hx₀ : x 0 = 0 := not_ne_iff.mp hx₀
  by_cases hx₁ : x 1 ≠ 0
  · refine ⟨-b 0 / x 1, 0, b 2 / x 1, ?_, ?_, ?_⟩
    · field_simp [hx₁] <;> ring
    · have hpair : x 1 * b 1 + x 2 * b 2 = 0 := by
        simpa only [hx₀, zero_mul, zero_add] using hthree
      simp only [hx₀, zero_mul, zero_sub]
      field_simp [hx₁]
      linear_combination hpair
    · field_simp [hx₀, hx₁] <;> ring
  have hx₁ : x 1 = 0 := not_ne_iff.mp hx₁
  have hx₂ : x 2 ≠ 0 := by
    intro hx₂
    apply hx
    funext i
    fin_cases i <;> simp [hx₀, hx₁, hx₂]
  have hb₂ : b 2 = 0 := by
    have hlast : x 2 * b 2 = 0 := by
      simpa only [hx₀, hx₁, zero_mul, zero_add] using hthree
    exact (mul_eq_zero.mp hlast).resolve_left hx₂
  refine ⟨0, -b 0 / x 2, -b 1 / x 2, ?_, ?_, ?_⟩
  · field_simp [hx₂] <;> ring
  · field_simp [hx₂] <;> ring
  · simp [hx₀, hx₁, hb₂]

/-- The value of `X i * ∏ j ≠ i, L j` at a point with coordinate values `x`
and line values `l`. -/
def blockValue (x l : Point) (i : Fin 3) : ℝ :=
  x i * ∏ j ∈ Finset.univ.erase i, l j

/-- Dividing coefficients by their own line values converts the cubic
functional into the coordinate functional, up to a nonzero common factor. -/
theorem block_combination_eq (x l a : Point) (hl : ∀ i, l i ≠ 0) :
    (∑ i, a i * blockValue x l i) =
      (∏ i, l i) * ∑ i, x i * (a i / l i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [blockValue, ← Finset.mul_prod_erase Finset.univ l (Finset.mem_univ i)]
  calc
    a i * (x i * ∏ j ∈ Finset.univ.erase i, l j) =
        (l i * (a i / l i)) * (x i * ∏ j ∈ Finset.univ.erase i, l j) := by
      rw [mul_div_cancel₀ _ (hl i)]
    _ = (l i * ∏ j ∈ Finset.univ.erase i, l j) * (x i * (a i / l i)) := by
      ring

/-- At a point where all line values are nonzero, the three evaluated
polynomial syzygies span the kernel of the cubic block functional. -/
theorem scaled_coordinate_syzygy (x l a : Point) (hx : x ≠ 0)
    (hl : ∀ i, l i ≠ 0) (h : ∑ i, a i * blockValue x l i = 0) :
    ∃ c₀₁ c₀₂ c₁₂ : ℝ,
      a 0 = l 0 * (-x 1 * c₀₁ - x 2 * c₀₂) ∧
      a 1 = l 1 * (x 0 * c₀₁ - x 2 * c₁₂) ∧
      a 2 = l 2 * (x 0 * c₀₂ + x 1 * c₁₂) := by
  have hprod : (∏ i, l i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hl i
  have hcoord : ∑ i, x i * (a i / l i) = 0 := by
    have hmul : (∏ i, l i) * (∑ i, x i * (a i / l i)) = 0 := by
      rw [← block_combination_eq x l a hl]
      exact h
    exact (mul_eq_zero.mp hmul).resolve_left hprod
  obtain ⟨c₀₁, c₀₂, c₁₂, h₀, h₁, h₂⟩ :=
    coordinate_syzygy x (fun i => a i / l i) hx hcoord
  refine ⟨c₀₁, c₀₂, c₁₂, ?_, ?_, ?_⟩
  · calc
      a 0 = l 0 * (a 0 / l 0) := (mul_div_cancel₀ _ (hl 0)).symm
      _ = l 0 * (-x 1 * c₀₁ - x 2 * c₀₂) := by rw [h₀]
  · calc
      a 1 = l 1 * (a 1 / l 1) := (mul_div_cancel₀ _ (hl 1)).symm
      _ = l 1 * (x 0 * c₀₁ - x 2 * c₁₂) := by rw [h₁]
  · calc
      a 2 = l 2 * (a 2 / l 2) := (mul_div_cancel₀ _ (hl 2)).symm
      _ = l 2 * (x 0 * c₀₂ + x 1 * c₁₂) := by rw [h₂]

end PanelMoments.PointSyzygies
