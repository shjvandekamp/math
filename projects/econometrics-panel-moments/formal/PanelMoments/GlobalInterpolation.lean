import PanelMoments.QuadraticSeparators

/-!
Separators for several disjoint point blocks. A polynomial vanishing on one
whole block and nonzero on the other blocks lets us isolate a local separator.
For conic blocks this gives degree `3m - 1` interpolation at all `6m` points.
This is an interpolation result, not yet the equality with the likelihood span.
-/

namespace PanelMoments.GlobalInterpolation

open scoped BigOperators
open MvPolynomial HomogeneousInterpolation

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiply each local separator by the vanishing polynomial of every other
block. Only explicit polynomial evaluations are assumed. -/
def assemble (p : ι → κ → Point) {d e : ℕ}
    (s : ∀ b, SeparatingFamily (p b) d)
    (g : ι → Poly) (hg : ∀ b, (g b).IsHomogeneous e)
    (hz : ∀ b i, eval (p b i) (g b) = 0)
    (hn : ∀ b c, b ≠ c → ∀ i, eval (p b i) (g c) ≠ 0) :
    SeparatingFamily (fun bi : ι × κ => p bi.1 bi.2)
      (d + (Fintype.card ι - 1) * e) where
  polynomial bi := (s bi.1).polynomial bi.2 * ∏ c ∈ Finset.univ.erase bi.1, g c
  homogeneous bi := by
    have hp := IsHomogeneous.prod (Finset.univ.erase bi.1) g (fun _ => e)
      (fun c _ => hg c)
    have hc : (∑ _c ∈ Finset.univ.erase bi.1, e) =
        (Fintype.card ι - 1) * e := by simp
    rw [hc] at hp
    exact ((s bi.1).homogeneous bi.2).mul hp
  offDiagonal bi cj hij := by
    classical
    simp only [map_mul, map_prod]
    by_cases hbc : bi.1 = cj.1
    · have hic : bi.2 ≠ cj.2 := by
        intro h
        exact hij (Prod.ext hbc h)
      have hs := (s bi.1).offDiagonal bi.2 cj.2 hic
      rw [hbc] at hs
      rw [hbc, hs, zero_mul]
    · have hm : bi.1 ∈ Finset.univ.erase cj.1 := by simp [hbc]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero hm (hz bi.1 bi.2))
  diagonal bi := by
    simp only [map_mul, map_prod]
    apply mul_ne_zero ((s bi.1).diagonal bi.2)
    apply Finset.prod_ne_zero_iff.mpr
    intro c hc
    exact hn bi.1 c (Ne.symm (Finset.mem_erase.mp hc).1) bi.2

open Geometry

/-- The product of the three lines vanishes at all six points of one block. -/
def blockProduct (w : Fin 3 → ℝ) : Geometry.Poly :=
  conicLine (w 0) * conicLine (w 1) * conicLine (w 2)

theorem blockProduct_homogeneous (w : Fin 3 → ℝ) :
    (blockProduct w).IsHomogeneous 3 :=
  ((conicLine_isHomogeneous (w 0)).mul
    (conicLine_isHomogeneous (w 1))).mul (conicLine_isHomogeneous (w 2))

theorem blockProduct_zero (w : Fin 3 → ℝ) (i : Fin 6) :
    eval (localPoint w i) (blockProduct w) = 0 := by
  fin_cases i <;>
    simp [blockProduct, localPoint, eval_conicLine_pair,
      eval_conicLine_diagonal_zero, eval_conicLine_diagonal_one,
      eval_conicLine_diagonal_two]

theorem otherLine_nonzero (w : Fin 3 → ℝ) (hw : ∀ r, 0 < w r)
    {v : ℝ} (hv : 0 < v) (hne : ∀ r, v ≠ w r) (i : Fin 6) :
    eval (localPoint w i) (conicLine v) ≠ 0 := by
  fin_cases i
  · exact eval_conicLine_pair_ne_zero (hne 0) (hne 1)
  · exact eval_conicLine_pair_ne_zero (hne 0) (hne 2)
  · exact eval_conicLine_pair_ne_zero (hne 1) (hne 2)
  · exact eval_conicLine_diagonal_ne_zero hv (hw 0) (hne 0) 0
  · exact eval_conicLine_diagonal_ne_zero hv (hw 1) (hne 1) 1
  · exact eval_conicLine_diagonal_ne_zero hv (hw 2) (hne 2) 2

/-- All positive conic parameters are distinct, including across blocks. -/
def conicSeparators (w : ι → Fin 3 → ℝ) (hw : ∀ b r, 0 < w b r)
    (hi : Function.Injective (fun br : ι × Fin 3 => w br.1 br.2)) :
    SeparatingFamily (fun bi : ι × Fin 6 => localPoint (w bi.1) bi.2)
      (2 + (Fintype.card ι - 1) * 3) := by
  apply assemble _ (fun b => QuadraticSeparators.separatingFamily (w b) (hw b)
    (fun r s hrs => by
      have hpair : (b, r) = (b, s) := hi hrs
      exact congrArg Prod.snd hpair))
    (fun b => blockProduct (w b))
    (fun b => blockProduct_homogeneous (w b))
    (fun b i => blockProduct_zero (w b) i)
  intro b c hbc i
  have hn (r : Fin 3) :
      eval (localPoint (w b) i) (conicLine (w c r)) ≠ 0 := by
    apply otherLine_nonzero (w b) (hw b) (hw c r) _ i
    intro s h
    have hpair : (c, r) = (b, s) := hi h
    exact hbc (congrArg Prod.fst hpair).symm
  simpa only [blockProduct, map_mul] using mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)

/-- Explicit interpolation gives the codimension of all point constraints in
every degree at least `3m - 1` (written without a nonempty-type assumption). -/
theorem conic_finrank_vanishing (w : ι → Fin 3 → ℝ)
    (hw : ∀ b r, 0 < w b r)
    (hi : Function.Injective (fun br : ι × Fin 3 => w br.1 br.2))
    {e : ℕ} (he : 2 + (Fintype.card ι - 1) * 3 ≤ e) :
    Module.finrank ℝ (vanishingSubmodule
      (fun bi : ι × Fin 6 => localPoint (w bi.1) bi.2) e) =
      (e + 2).choose 2 - 6 * Fintype.card ι := by
  simpa [Fintype.card_prod, Nat.mul_comm] using
    (conicSeparators w hw hi).finrank_vanishing_of_le
      (fun bi => QuadraticSeparators.nonzeroCoordinate bi.2)
      (fun bi => QuadraticSeparators.localPoint_coordinate_ne_zero (w bi.1) bi.2) he

end

end PanelMoments.GlobalInterpolation
