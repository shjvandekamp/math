import PanelMoments.SourceEndpointCoalescenceKernel

set_option autoImplicit false

/-!
# An actual-kernel rational extension witness for endpoint coupling

At `z* = (3/2,1,1)`, the ideal coupling is defined from the actual exceptional
rows and the existing endpoint coefficients. The calculation uses canceled
active-coordinate ratios at the three concrete edge representatives.

The resulting determinant is positive for every `m ≥ 1`. This is a rational
extension witness only: one last node lies on a coordinate edge and two last
nodes coincide, so the original generic cancellation pivots are not valid at
this specialization. Perturbation to generic positive times and convergence
from distinct earlier times are not proved here. The cancellation ratio is
the explicitly defined ratio in `SourceEndpointCoalescenceKernel`.
-/

namespace PanelMoments.SourceEndpointCoalescenceWitness

open scoped BigOperators
open SourceHomogeneous SourceBoundaryEndpointAlgebra SourceEndpointCoalescenceKernel

noncomputable section

def witnessZ : State 2 → ℝ := ![3 / 2, 1, 1]

def edgePoint (b : State 2) : State 2 → ℝ :=
  ![![0, 1, -1], ![1, 0, -2], ![1, -2, 0]] b

/-- The ideal endpoint coupling, using actual exceptional rows; the diagonal is zero. -/
def idealCoupling (m : ℕ) : Matrix (State 2) (State 2) ℝ :=
  fun b c => if b = c then 0 else
    ∑ i : State 2, if i = b then 0 else
      (endpointCoefficient (fun _ => 1) g b i -
        endpointCoefficient (fun _ => 1) (lastTime witnessZ) b i) *
        (exceptionalRow m witnessZ (edgePoint b) c i / edgePoint b i)

def upperEntry (m : ℕ) : ℝ := 2 * (3 : ℝ) ^ m / ((4 : ℝ) ^ m - 1)

def lowerEntry (m : ℕ) : ℝ :=
  -(((4 : ℝ) ^ m + 5) * (3 : ℝ) ^ m + 3 * (4 : ℝ) ^ m) /
    (30 * ((4 : ℝ) ^ m - 1))

def sideEntry (m : ℕ) : ℝ :=
  ((4 : ℝ) ^ m - ((4 : ℝ) ^ m + 6) * (3 : ℝ) ^ m) /
    (9 * ((4 : ℝ) ^ m - 1))

private theorem edge_plane (b : State 2) :
    (∑ i, scaledPoint (edgePoint b) i) = 0 := by
  fin_cases b <;> norm_num [edgePoint, scaledPoint, g, Fin.sum_univ_succ]

private theorem edge_zero (b : State 2) : edgePoint b b = 0 := by
  fin_cases b <;> norm_num [edgePoint]

private theorem edge_active (b i : State 2) (hib : i ≠ b) : edgePoint b i ≠ 0 := by
  fin_cases b <;> fin_cases i <;> norm_num [edgePoint] at *

private theorem edge_last_rowForm (b c : State 2) (hbc : b ≠ c) :
    rowForm (lastTable witnessZ) (edgePoint b) 0 c ≠ 0 := by
  rw [lastTable, weightedTime_rowForm]
  fin_cases b <;> fin_cases c <;>
    norm_num [lastTime, witnessZ, g, edgePoint, Fin.sum_univ_succ] at *

/-- Cancel the actual active output coordinate before evaluating at an edge. -/
theorem exceptionalRow_div_edge (m : ℕ) (b c i : State 2)
    (hbc : b ≠ c) (hib : i ≠ b) :
    exceptionalRow m witnessZ (edgePoint b) c i / edgePoint b i =
      g i * (headFactor witnessZ (edgePoint b) c *
        ((3 : ℝ) ^ m - cancellationFactor m witnessZ c *
          (witnessZ i * (1 + if i = c then 1 else 0) +
            activeCoefficient m * ((∑ j, witnessZ j) + witnessZ c - witnessZ b)))) := by
  have hgi : g i ≠ 0 := by fin_cases i <;> norm_num [g]
  have hXi := edge_active b i hib
  calc
    exceptionalRow m witnessZ (edgePoint b) c i / edgePoint b i =
      g i * (exceptionalRow m witnessZ (edgePoint b) c i /
        scaledPoint (edgePoint b) i) := by
          unfold scaledPoint
          field_simp [hgi, hXi]
    _ = _ := by
      rw [exceptionalRow_active_ratio m witnessZ (edgePoint b) b c i
        (edge_plane b) (edge_zero b) (edge_active b) (Ne.symm hbc) hib
        (edge_last_rowForm b c hbc)]

private theorem idealCoupling_expanded (m : ℕ) (b c : State 2) (hbc : b ≠ c) :
    idealCoupling m b c =
      ∑ i : State 2, if i = b then 0 else
        (endpointCoefficient (fun _ => 1) g b i -
          endpointCoefficient (fun _ => 1) (lastTime witnessZ) b i) *
          (g i * (headFactor witnessZ (edgePoint b) c *
            ((3 : ℝ) ^ m - cancellationFactor m witnessZ c *
              (witnessZ i * (1 + if i = c then 1 else 0) + activeCoefficient m *
                ((∑ j, witnessZ j) + witnessZ c - witnessZ b))))) := by
  simp only [idealCoupling, hbc, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hib : i = b
  · simp only [hib, ↓reduceIte]
  · simp only [hib, ↓reduceIte]
    rw [exceptionalRow_div_edge m b c i hbc hib]

private theorem pow_four_gt_one (m : ℕ) (hm : 1 ≤ m) : 1 < (4 : ℝ) ^ m :=
  one_lt_pow₀ (by norm_num) (Nat.one_le_iff_ne_zero.mp hm)

/-- All six entries are evaluated from the actual weighted-kernel exceptional rows. -/
theorem idealCoupling_eq (m : ℕ) (hm : 1 ≤ m) :
    idealCoupling m =
      ![![0, upperEntry m, upperEntry m],
        ![lowerEntry m, 0, sideEntry m],
        ![lowerEntry m, sideEntry m, 0]] := by
  have hden : (4 : ℝ) ^ m - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (pow_four_gt_one m hm))
  ext b c
  by_cases hbc : b = c
  · subst c
    fin_cases b <;> simp [idealCoupling]
  · rw [idealCoupling_expanded m b c hbc]
    fin_cases b <;> fin_cases c <;> try contradiction
    all_goals norm_num [endpointCoefficient, SourceWeightedPrependAlgebra.weight,
      SourceWeightedPrependAlgebra.preservingScale, witnessZ, g, lastTime, headFactor,
      scaledPoint, rowForm, lastTable, weightedTimeTable, SourceTimeScaling.scaledTable,
      SourceWeightedPrependAlgebra.weightedTable, activeCoefficient, cancellationFactor,
      interiorCoefficient, edgePoint, Fin.sum_univ_succ, upperEntry, lowerEntry, sideEntry]
    all_goals field_simp [hden]
    all_goals ring

theorem idealCoupling_det (m : ℕ) (hm : 1 ≤ m) :
    (idealCoupling m).det =
      2 * (3 : ℝ) ^ m * (((4 : ℝ) ^ m + 5) * (3 : ℝ) ^ m + 3 * (4 : ℝ) ^ m) *
        (((4 : ℝ) ^ m + 6) * (3 : ℝ) ^ m - (4 : ℝ) ^ m) /
          (135 * ((4 : ℝ) ^ m - 1) ^ 3) := by
  have hden : (4 : ℝ) ^ m - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (pow_four_gt_one m hm))
  rw [Matrix.det_fin_three (idealCoupling m)]
  simp only [idealCoupling_eq m hm]
  simp [upperEntry, lowerEntry, sideEntry]
  field_simp [hden]
  ring

/-- Positivity of the ideal rational extension witness, not of an original source fixture. -/
theorem idealCoupling_det_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (idealCoupling m).det := by
  rw [idealCoupling_det m hm]
  have hA := pow_four_gt_one m hm
  have hA0 : 0 < (4 : ℝ) ^ m := lt_trans zero_lt_one hA
  have hB : (3 : ℝ) ≤ 3 ^ m := le_self_pow₀ (by norm_num) (Nat.one_le_iff_ne_zero.mp hm)
  have hB0 : (0 : ℝ) < 3 ^ m := by linarith
  have hfirst : 0 < ((4 : ℝ) ^ m + 5) * 3 ^ m + 3 * (4 : ℝ) ^ m :=
    add_pos (mul_pos (by linarith) hB0) (mul_pos (by norm_num) hA0)
  have hsecond : 0 < ((4 : ℝ) ^ m + 6) * 3 ^ m - (4 : ℝ) ^ m := by
    have hproduct := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ (4 : ℝ) ^ m + 6)
    nlinarith
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hB0) hfirst) hsecond)
    (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hA) 3))

end

end PanelMoments.SourceEndpointCoalescenceWitness
