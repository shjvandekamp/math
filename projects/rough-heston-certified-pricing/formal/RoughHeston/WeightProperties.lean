module

public import RoughHeston.Weights
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Positivity and exact row sums of the fractional Adams weights

The results hold for every `alpha > 0`, and therefore in particular for the
rough regime `0 < alpha < 1`. The corrector row includes its endpoint.
The original definitions in `Weights` are used without modification.
-/

@[expose] public section

noncomputable section
open Finset

namespace RoughHeston

theorem correctorWeight_endpoint (alpha dt : ℝ) (n : ℕ) :
    correctorWeight alpha dt n n = dt ^ alpha / Real.Gamma (alpha + 2) := by
  simp [correctorWeight]

theorem predictorWeight_nonneg {alpha dt : ℝ} (ha : 0 < alpha) (ht : 0 < dt)
    (j n : ℕ) : 0 ≤ predictorWeight alpha dt j n := by
  apply mul_nonneg
  · exact div_nonneg (Real.rpow_nonneg ht.le _)
      (Real.Gamma_pos_of_pos (by linarith)).le
  · exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.sub_le (n - j) 1) ha.le)

private theorem initial_corrector_nonneg {alpha x : ℝ} (ha : 0 ≤ alpha) (hx : 1 ≤ x) :
    0 ≤ (x - 1) ^ (alpha + 1) - (x - 1 - alpha) * x ^ alpha := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs : -1 ≤ -1 / x := (le_div_iff₀ hxpos).mpr (by linarith)
  have hb := one_add_mul_self_le_rpow_one_add hs (show 1 ≤ alpha + 1 by linarith)
  have hbase : 0 ≤ 1 + -1 / x := by linarith
  have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hxpos.le (alpha + 1))
  have hleft : x ^ (alpha + 1) * (1 + (alpha + 1) * (-1 / x)) =
      (x - 1 - alpha) * x ^ alpha := by
    rw [Real.rpow_add_one hxpos.ne']
    field_simp
    ring
  have hright : x ^ (alpha + 1) * (1 + -1 / x) ^ (alpha + 1) =
      (x - 1) ^ (alpha + 1) := by
    rw [← Real.mul_rpow hxpos.le hbase]
    congr 1
    field_simp
    ring
  rw [hleft, hright] at h
  linarith

private theorem second_difference_nonneg {alpha x : ℝ} (ha : 0 ≤ alpha) (hx : 1 ≤ x) :
    0 ≤ (x + 1) ^ (alpha + 1) + (x - 1) ^ (alpha + 1) -
      2 * x ^ (alpha + 1) := by
  have h := (convexOn_rpow (show 1 ≤ alpha + 1 by linarith)).2
    (show x - 1 ∈ Set.Ici (0 : ℝ) by simpa using sub_nonneg.mpr hx)
    (show x + 1 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have hmid : (1 / 2 : ℝ) * (x - 1) + (1 / 2 : ℝ) * (x + 1) = x := by ring
  rw [hmid] at h
  linarith

theorem correctorWeight_nonneg {alpha dt : ℝ} (ha : 0 < alpha) (ht : 0 < dt)
    {j n : ℕ} (hj : j ≤ n) : 0 ≤ correctorWeight alpha dt j n := by
  unfold correctorWeight
  apply mul_nonneg
  · exact div_nonneg (Real.rpow_nonneg ht.le _)
      (Real.Gamma_pos_of_pos (by linarith)).le
  · by_cases hdiag : j = n
    · simp [hdiag]
    · by_cases hzero : j = 0
      · subst j
        have hn : 1 ≤ n := by omega
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn, Nat.cast_one]
        simp only [hdiag, ite_false, ite_true, hcast]
        exact initial_corrector_nonneg ha.le (by exact_mod_cast hn)
      · have hgap : 1 ≤ n - j := by omega
        have hcast : ((n - j - 1 : ℕ) : ℝ) = ((n - j : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub hgap, Nat.cast_one]
        simp only [hdiag, hzero, ite_false, Nat.cast_add, Nat.cast_one, hcast]
        exact second_difference_nonneg ha.le (by exact_mod_cast hgap)

private theorem sum_reverse_difference (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, (f (n - j) - f (n - j - 1)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero,
      Nat.add_sub_cancel_right]
    rw [ih]
    ring

private theorem sum_reverse_second_difference (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, (f (n - j + 1) + f (n - j - 1) - 2 * f (n - j)) =
      f (n + 1) - f n - f 1 + f 0 := by
  calc
    _ = ∑ j ∈ range n,
        ((f (n - j + 1) - f (n - j - 1 + 1)) - (f (n - j) - f (n - j - 1))) := by
      apply sum_congr rfl
      intro j hj
      have heq : n - j - 1 + 1 = n - j := by have := mem_range.mp hj; omega
      rw [heq]
      ring
    _ = (f (n + 1) - f 1) - (f n - f 0) := by
      rw [sum_sub_distrib, sum_reverse_difference (fun k => f (k + 1)), sum_reverse_difference]
    _ = _ := by ring

/-- The predictor uses exactly the mass of the fractional kernel on the
whole time interval. This formula also covers the empty row `n = 0`. -/
theorem predictorWeight_row_sum {alpha : ℝ} (ha : 0 < alpha) (dt : ℝ) (n : ℕ) :
    ∑ j ∈ range n, predictorWeight alpha dt j n =
      dt ^ alpha * (n : ℝ) ^ alpha / Real.Gamma (alpha + 1) := by
  simp only [predictorWeight, ← mul_sum]
  rw [sum_reverse_difference (fun k => (k : ℝ) ^ alpha)]
  simp only [Nat.cast_zero, Real.zero_rpow ha.ne', sub_zero]
  ring

private def correctorNumerator (alpha : ℝ) (j n : ℕ) : ℝ :=
  if j = n then 1
  else if j = 0 then
    ((n - 1 : ℕ) : ℝ) ^ (alpha + 1) -
      (((n - 1 : ℕ) : ℝ) - alpha) * (n : ℝ) ^ alpha
  else
    ((n - j + 1 : ℕ) : ℝ) ^ (alpha + 1) +
    ((n - j - 1 : ℕ) : ℝ) ^ (alpha + 1) -
    2 * ((n - j : ℕ) : ℝ) ^ (alpha + 1)

private theorem correctorNumerator_row_sum {alpha : ℝ} (ha : 0 < alpha)
    {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ range (n + 1), correctorNumerator alpha j n =
      (alpha + 1) * (n : ℝ) ^ alpha := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn1 : 1 ≤ n := hn
  have hpred : n - 1 + 1 = n := by omega
  have hsplit := sum_range_succ' (fun j => correctorNumerator alpha j n) (n - 1)
  rw [hpred] at hsplit
  have hinterior :
      ∑ j ∈ range (n - 1), correctorNumerator alpha (j + 1) n =
        (n : ℝ) ^ (alpha + 1) - ((n - 1 : ℕ) : ℝ) ^ (alpha + 1) - 1 := by
    calc
      _ = ∑ j ∈ range (n - 1),
          (((n - 1 - j + 1 : ℕ) : ℝ) ^ (alpha + 1) +
            ((n - 1 - j - 1 : ℕ) : ℝ) ^ (alpha + 1) -
            2 * ((n - 1 - j : ℕ) : ℝ) ^ (alpha + 1)) := by
        apply sum_congr rfl
        intro j hj
        have hjn : j + 1 ≠ n := by have := mem_range.mp hj; omega
        have hsub : n - (j + 1) = n - 1 - j := by omega
        simp only [correctorNumerator, hjn, Nat.add_one_ne_zero, ite_false, hsub]
      _ = _ := by
        rw [sum_reverse_second_difference (fun k => (k : ℝ) ^ (alpha + 1))]
        simp only [hpred, Nat.cast_one, Real.one_rpow, Nat.cast_zero,
          Real.zero_rpow (show alpha + 1 ≠ 0 by linarith), add_zero]
  rw [sum_range_succ, hsplit, hinterior]
  simp only [correctorNumerator, hn0.symm, ↓reduceIte]
  rw [Real.rpow_add_one (show (n : ℝ) ≠ 0 by exact_mod_cast hn0),
    Nat.cast_sub hn1, Nat.cast_one]
  ring

/-- The complete corrector row, including its implicit endpoint, has the
same exact fractional-kernel mass as the predictor row. -/
theorem correctorWeight_row_sum {alpha : ℝ} (ha : 0 < alpha) (dt : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ range (n + 1), correctorWeight alpha dt j n =
      dt ^ alpha * (n : ℝ) ^ alpha / Real.Gamma (alpha + 1) := by
  have hweight : ∀ j, correctorWeight alpha dt j n =
      dt ^ alpha / Real.Gamma (alpha + 2) * correctorNumerator alpha j n := by
    intro j
    rfl
  simp only [hweight, ← mul_sum]
  rw [correctorNumerator_row_sum ha hn]
  have hGamma : Real.Gamma (alpha + 2) = (alpha + 1) * Real.Gamma (alpha + 1) := by
    rw [show alpha + 2 = (alpha + 1) + 1 by ring]
    exact Real.Gamma_add_one (by linarith)
  rw [hGamma]
  have ha1 : alpha + 1 ≠ 0 := by linarith
  field_simp

theorem predictorWeight_sum_fin {alpha : ℝ} (ha : 0 < alpha) (dt : ℝ) (n : ℕ) :
    ∑ j : Fin n, predictorWeight alpha dt j.val n =
      dt ^ alpha * (n : ℝ) ^ alpha / Real.Gamma (alpha + 1) := by
  exact (Fin.sum_univ_eq_sum_range (fun j => predictorWeight alpha dt j n) n).trans
    (predictorWeight_row_sum ha dt n)

theorem correctorWeight_sum_fin {alpha : ℝ} (ha : 0 < alpha) (dt : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ∑ j : Fin (n + 1), correctorWeight alpha dt j.val n =
      dt ^ alpha * (n : ℝ) ^ alpha / Real.Gamma (alpha + 1) := by
  exact (Fin.sum_univ_eq_sum_range (fun j => correctorWeight alpha dt j n) (n + 1)).trans
    (correctorWeight_row_sum ha dt hn)

/-- Separating the endpoint leaves the corrector history mass. -/
theorem correctorWeight_history_sum_fin {alpha : ℝ} (ha : 0 < alpha) (dt : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ∑ j : Fin n, correctorWeight alpha dt j.val n =
      dt ^ alpha * (n : ℝ) ^ alpha / Real.Gamma (alpha + 1) -
        dt ^ alpha / Real.Gamma (alpha + 2) := by
  have h := correctorWeight_sum_fin ha dt hn
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last, correctorWeight_endpoint] at h
  linarith

end RoughHeston
