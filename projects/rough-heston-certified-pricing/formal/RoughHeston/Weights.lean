module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform-mesh fractional Adams weights

These are the predictor and corrector weights of the standard product-
integration method, indexed at target node `n`, with history `0 ≤ j < n`.
The zero row is immaterial. The corrector endpoint is `a n n`.
-/

@[expose] public section

noncomputable section
namespace RoughHeston

def predictorWeight (alpha dt : ℝ) (j n : ℕ) : ℝ :=
  dt ^ alpha / Real.Gamma (alpha + 1) *
    (((n - j : ℕ) : ℝ) ^ alpha - ((n - j - 1 : ℕ) : ℝ) ^ alpha)

def correctorWeight (alpha dt : ℝ) (j n : ℕ) : ℝ :=
  dt ^ alpha / Real.Gamma (alpha + 2) *
    if j = n then 1
    else if j = 0 then
      ((n - 1 : ℕ) : ℝ) ^ (alpha + 1) -
        (((n - 1 : ℕ) : ℝ) - alpha) * (n : ℝ) ^ alpha
    else
      ((n - j + 1 : ℕ) : ℝ) ^ (alpha + 1) +
      ((n - j - 1 : ℕ) : ℝ) ^ (alpha + 1) -
      2 * ((n - j : ℕ) : ℝ) ^ (alpha + 1)

theorem predictorWeight_last_pos {alpha dt : ℝ} (ha : 0 < alpha) (ht : 0 < dt)
    (n : ℕ) : 0 < predictorWeight alpha dt n (n + 1) := by
  have hG : 0 < Real.Gamma (alpha + 1) := Real.Gamma_pos_of_pos (by linarith)
  simp [predictorWeight, Real.zero_rpow (ne_of_gt ha)]
  exact div_pos (Real.rpow_pos_of_pos ht _) hG

theorem correctorWeight_diagonal_pos {alpha dt : ℝ} (ha : 0 < alpha) (ht : 0 < dt)
    (n : ℕ) : 0 < correctorWeight alpha dt n n := by
  have hG : 0 < Real.Gamma (alpha + 2) := Real.Gamma_pos_of_pos (by linarith)
  simp [correctorWeight]
  exact div_pos (Real.rpow_pos_of_pos ht _) hG

end RoughHeston
