module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit, nonvacuous mesh conditions for fixed-horizon continuation

The damping rate and maximum step size are given by explicit positive real
expressions. A sufficiently fine integer seed makes every dyadic refinement
satisfy the exponential-step, corrector-endpoint, and error-margin conditions.
These are mathematical real-valued formulas; no floating-point evaluator is
used in their proofs.
-/

@[expose] public section

noncomputable section

namespace RoughHeston

/-- A concrete damping rate that makes the weighted Lipschitz mass at most
`1/8`. The maximum also handles a zero Lipschitz constant. -/
def continuationRate (α L : ℝ) : ℝ :=
  (8 * max 1 L) ^ (1 / α)

/-- Explicit admissible upper bound on the time step. The three entries
control exponential growth, the predicted endpoint, and the error margin. -/
def continuationMeshThreshold (α T rate L D eta : ℝ) : ℝ :=
  min (Real.log 2 / rate)
    (min ((Real.Gamma (α + 2) / max 1 L) ^ (1 / α))
      ((eta / (4 * max 1 D * Real.exp (rate * T))) ^ (1 / α)))

theorem continuationRate_pos (α L : ℝ) : 0 < continuationRate α L := by
  apply Real.rpow_pos_of_pos
  have hmax : (0 : ℝ) < max 1 L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem continuationRate_contraction {α L : ℝ} (hα : 0 < α) :
    L * (continuationRate α L) ^ (-α) ≤ 1 / 8 := by
  have hmax : (0 : ℝ) < max 1 L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbase : (0 : ℝ) < 8 * max 1 L := by positivity
  have hpow : (continuationRate α L) ^ α = 8 * max 1 L := by
    unfold continuationRate
    rw [one_div, Real.rpow_inv_rpow hbase.le hα.ne']
  rw [Real.rpow_neg (continuationRate_pos α L).le, hpow, ← div_eq_mul_inv]
  apply (div_le_iff₀ hbase).mpr
  have hL : L ≤ max 1 L := le_max_right _ _
  nlinarith

theorem continuationMeshThreshold_pos {α T rate L D eta : ℝ}
    (hα : 0 < α) (hrate : 0 < rate) (heta : 0 < eta) :
    0 < continuationMeshThreshold α T rate L D eta := by
  have hmaxL : (0 : ℝ) < max 1 L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmaxD : (0 : ℝ) < max 1 D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hGamma : 0 < Real.Gamma (α + 2) := Real.Gamma_pos_of_pos (by linarith)
  unfold continuationMeshThreshold
  apply lt_min
  · exact div_pos (Real.log_pos (by norm_num)) hrate
  · apply lt_min
    · exact Real.rpow_pos_of_pos (div_pos hGamma hmaxL) _
    · exact Real.rpow_pos_of_pos (div_pos heta (by positivity)) _

/-- Every positive step below the explicit threshold satisfies all three
accuracy restrictions used in the fixed-horizon continuation theorem. -/
theorem continuationMeshThreshold_conditions {α T rate L D eta dt : ℝ}
    (hα : 0 < α) (hrate : 0 < rate) (heta : 0 < eta)
    (hdt : 0 < dt) (hbound : dt ≤ continuationMeshThreshold α T rate L D eta) :
    Real.exp (rate * dt) ≤ 2 ∧
      dt ^ α / Real.Gamma (α + 2) * L ≤ 1 ∧
      4 * D * dt ^ α * Real.exp (rate * T) ≤ eta := by
  have hmaxL : (0 : ℝ) < max 1 L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmaxD : (0 : ℝ) < max 1 D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hGamma : 0 < Real.Gamma (α + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hden : 0 < 4 * max 1 D * Real.exp (rate * T) := by positivity
  have hstep : dt ≤ Real.log 2 / rate :=
    hbound.trans (min_le_left _ _)
  have hrest : dt ≤ min ((Real.Gamma (α + 2) / max 1 L) ^ (1 / α))
      ((eta / (4 * max 1 D * Real.exp (rate * T))) ^ (1 / α)) :=
    hbound.trans (min_le_right _ _)
  have hpowL : dt ^ α ≤ Real.Gamma (α + 2) / max 1 L := by
    apply (Real.le_rpow_inv_iff_of_pos hdt.le (div_pos hGamma hmaxL).le hα).mp
    simpa only [one_div] using hrest.trans (min_le_left _ _)
  have hpowD : dt ^ α ≤ eta / (4 * max 1 D * Real.exp (rate * T)) := by
    apply (Real.le_rpow_inv_iff_of_pos hdt.le (div_pos heta hden).le hα).mp
    simpa only [one_div] using hrest.trans (min_le_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mp
    have := (le_div_iff₀ hrate).mp hstep
    nlinarith
  · have hprod : dt ^ α * L ≤ Real.Gamma (α + 2) :=
      (mul_le_mul_of_nonneg_left (le_max_right 1 L) (Real.rpow_nonneg hdt.le _)).trans
        ((le_div_iff₀ hmaxL).mp hpowL)
    calc
      dt ^ α / Real.Gamma (α + 2) * L = (dt ^ α * L) / Real.Gamma (α + 2) := by ring
      _ ≤ 1 := (div_le_iff₀ hGamma).mpr (by simpa only [one_mul] using hprod)
  · calc
      4 * D * dt ^ α * Real.exp (rate * T) =
          D * (4 * dt ^ α * Real.exp (rate * T)) := by ring
      _ ≤ max 1 D * (4 * dt ^ α * Real.exp (rate * T)) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 D) (by positivity)
      _ = dt ^ α * (4 * max 1 D * Real.exp (rate * T)) := by ring
      _ ≤ eta := (le_div_iff₀ hden).mp hpowD

/-- Every positive threshold admits an integer seed such that all dyadic
refinements have positive step size and lie below that threshold. -/
theorem exists_dyadic_mesh_le {T delta : ℝ} (hT : 0 < T) (hdelta : 0 < delta) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      0 < T / ((2 ^ ell * M0 : ℕ) : ℝ) ∧
        T / ((2 ^ ell * M0 : ℕ) : ℝ) ≤ delta := by
  obtain ⟨M0, hM0⟩ := exists_nat_gt (T / delta)
  have hMpos : (0 : ℝ) < M0 := (div_pos hT hdelta).trans hM0
  have hMnat : 0 < M0 := by exact_mod_cast hMpos
  have hseed : T / (M0 : ℝ) ≤ delta := by
    apply (div_le_iff₀ hMpos).mpr
    have := (div_lt_iff₀ hdelta).mp hM0
    nlinarith
  refine ⟨M0, hMnat, fun ell => ?_⟩
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ ell := one_le_pow₀ (by norm_num)
  have hden : (M0 : ℝ) ≤ (2 : ℝ) ^ ell * (M0 : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo hMpos.le
  have hdenpos : (0 : ℝ) < (2 : ℝ) ^ ell * (M0 : ℝ) := hMpos.trans_le hden
  push_cast
  exact ⟨div_pos hT hdenpos, (div_le_div_of_nonneg_left hT.le hMpos hden).trans hseed⟩

/-- For any positive damping rate, a single integer seed makes the entire
dyadic family pass the three explicit continuation conditions. -/
theorem exists_dyadic_continuation_mesh {α T rate L D eta : ℝ}
    (hα : 0 < α) (hT : 0 < T) (hrate : 0 < rate) (heta : 0 < eta) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      let dt := T / ((2 ^ ell * M0 : ℕ) : ℝ)
      0 < dt ∧ Real.exp (rate * dt) ≤ 2 ∧
        dt ^ α / Real.Gamma (α + 2) * L ≤ 1 ∧
        4 * D * dt ^ α * Real.exp (rate * T) ≤ eta := by
  obtain ⟨M0, hM0, hmesh⟩ := exists_dyadic_mesh_le hT
    (continuationMeshThreshold_pos (T := T) (L := L) (D := D) hα hrate heta)
  refine ⟨M0, hM0, fun ell => ?_⟩
  exact ⟨(hmesh ell).1,
    continuationMeshThreshold_conditions hα hrate heta (hmesh ell).1 (hmesh ell).2⟩

/-- The damping rate can also be chosen explicitly, so the weighted-row
contraction and every mesh condition are simultaneously satisfiable. -/
theorem explicit_continuation_mesh_exists {α T L D eta : ℝ}
    (hα : 0 < α) (hT : 0 < T) (heta : 0 < eta) :
    0 < continuationRate α L ∧
      L * (continuationRate α L) ^ (-α) ≤ 1 / 8 ∧
      ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
        let dt := T / ((2 ^ ell * M0 : ℕ) : ℝ)
        0 < dt ∧ Real.exp (continuationRate α L * dt) ≤ 2 ∧
          dt ^ α / Real.Gamma (α + 2) * L ≤ 1 ∧
          4 * D * dt ^ α * Real.exp (continuationRate α L * T) ≤ eta := by
  exact ⟨continuationRate_pos α L, continuationRate_contraction hα,
    exists_dyadic_continuation_mesh hα hT (continuationRate_pos α L) heta⟩

end RoughHeston

#print axioms RoughHeston.continuationMeshThreshold_conditions
#print axioms RoughHeston.explicit_continuation_mesh_exists
