module

public import RoughHeston.Continuation
public import RoughHeston.WeightProperties
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stability statements for the concrete rough-Heston Adams recurrence

The exact Gamma weights, predictor, and single-correction recurrence are
used throughout. The short-horizon theorem proves invariance of a ball from
the full row mass. The continuation theorem discharges recurrence and weight
positivity, but retains its explicit residual and weighted-row certificate;
it does not assert that a particular mesh passes that certificate.
-/

@[expose] public section
noncomputable section
open Polynomial Finset

namespace RoughHeston

/-- The actual explicit predictor at target node `n`, with full history. -/
def roughPredictor (alpha dt R gamma rho nu u : ℝ) (n : ℕ) : ℂ :=
  weightedHistory (fun j : Fin n => predictorWeight alpha dt j.val n)
    (riccati R gamma rho nu u) (fun j : Fin n => roughState alpha dt R gamma rho nu u j.val)

theorem roughPredictor_zero (alpha dt R gamma rho nu u : ℝ) :
    roughPredictor alpha dt R gamma rho nu u 0 = 0 := by
  simp [roughPredictor, weightedHistory]

/-- The polynomial-evaluated states satisfy the concrete two-stage map
used by the deterministic stability estimates. -/
theorem roughState_eq_singleCorrection (alpha dt R gamma rho nu u : ℝ) (n : ℕ) :
    roughState alpha dt R gamma rho nu u (n + 1) =
      singleCorrection (fun j : Fin (n + 1) => correctorWeight alpha dt j.val (n + 1))
        (fun j : Fin (n + 1) => predictorWeight alpha dt j.val (n + 1))
        (correctorWeight alpha dt (n + 1) (n + 1)) (riccati R gamma rho nu u)
        (fun j : Fin (n + 1) => roughState alpha dt R gamma rho nu u j.val) := by
  simpa only [singleCorrection, weightedHistory] using roughState_succ alpha dt R gamma rho nu u n

/-- Exact total mass of either complete Adams row. -/
def adamsRowMass (alpha dt : ℝ) (n : ℕ) : ℝ :=
  dt ^ alpha * (n : ℝ) ^ alpha / Real.Gamma (alpha + 1)

theorem adamsRowMass_mono {alpha dt : ℝ} (ha : 0 < alpha) (ht : 0 < dt)
    {n N : ℕ} (hn : n ≤ N) : adamsRowMass alpha dt n ≤ adamsRowMass alpha dt N := by
  apply (div_le_div_iff_of_pos_right (Real.Gamma_pos_of_pos (show 0 < alpha + 1 by linarith))).mpr
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) ha.le)
    (Real.rpow_nonneg ht.le _)

/-- If the largest full-row mass times the force bound fits in the ball,
all corrected nodes and all predictors on the horizon remain in that ball.
No bound on the numerical trajectory is assumed. -/
theorem roughState_invariant_ball (alpha dt R gamma rho nu u : ℝ) (N : ℕ)
    {Q M : ℝ} (ha : 0 < alpha) (ht : 0 < dt) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hsmall : adamsRowMass alpha dt N * M ≤ Q)
    (hF : ∀ z : ℂ, ‖z‖ ≤ Q → ‖riccati R gamma rho nu u z‖ ≤ M) :
    ∀ n ≤ N, ‖roughState alpha dt R gamma rho nu u n‖ ≤ Q ∧
      ‖roughPredictor alpha dt R gamma rho nu u n‖ ≤ Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa only [roughState_zero, roughPredictor_zero, norm_zero, and_self] using hQ
    | succ n =>
      have hrowA :
          (∑ j : Fin (n + 1), correctorWeight alpha dt j.val (n + 1)) +
            correctorWeight alpha dt (n + 1) (n + 1) ≤ adamsRowMass alpha dt N := by
        rw [correctorWeight_history_sum_fin ha dt (Nat.succ_pos n), correctorWeight_endpoint]
        simpa only [sub_add_cancel, adamsRowMass] using adamsRowMass_mono ha ht hn
      have hrowB : (∑ j : Fin (n + 1), predictorWeight alpha dt j.val (n + 1)) ≤
          adamsRowMass alpha dt N := by
        rw [predictorWeight_sum_fin ha dt (n + 1)]
        exact adamsRowMass_mono ha ht hn
      have hstep := singleCorrection_ball
        (fun j : Fin (n + 1) => correctorWeight alpha dt j.val (n + 1))
        (fun j : Fin (n + 1) => predictorWeight alpha dt j.val (n + 1))
        (correctorWeight alpha dt (n + 1) (n + 1))
        (riccati R gamma rho nu u)
        (fun j : Fin (n + 1) => roughState alpha dt R gamma rho nu u j.val)
        (fun j => correctorWeight_nonneg ha ht j.isLt.le)
        (fun j => predictorWeight_nonneg ha ht j.val (n + 1))
        (correctorWeight_nonneg ha ht le_rfl) hM hrowA hrowB hsmall
        (fun j => (ih j.val j.isLt (j.isLt.le.trans hn)).1) hF
      refine ⟨?_, hstep.1⟩
      rw [roughState_eq_singleCorrection]
      exact hstep.2

/-- A finite weighted-row continuation certificate for the actual
rough-Heston Adams states. The two residuals are displayed product-
integration formulas evaluated on the comparison data `y`.

The assumptions on those residuals and weighted rows remain obligations;
this theorem does not silently replace them by a solver or accuracy axiom. -/
theorem roughState_validated_continuation (alpha dt R gamma rho nu u : ℝ)
    (y : ℕ → ℂ) (W : ℕ → ℝ) (N : ℕ) {Wmax Q0 eta L ε : ℝ}
    (ha : 0 < alpha) (ht : 0 < dt) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hW : ∀ n ≤ N, 1 ≤ W n ∧ W n ≤ Wmax)
    (hmargin : 4 * ε * Wmax ≤ eta)
    (hy : ∀ n ≤ N, ‖y n‖ ≤ Q0) (hyzero : y 0 = 0)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q0 + eta → ‖w‖ ≤ Q0 + eta →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (hpred : ∀ n, 0 < n → n ≤ N →
      ‖(∑ j : Fin n, (predictorWeight alpha dt j.val n : ℂ) *
        riccati R gamma rho nu u (y j.val)) - y n‖ ≤ ε)
    (hcorr : ∀ n, 0 < n → n ≤ N →
      ‖(∑ j : Fin n, (correctorWeight alpha dt j.val n : ℂ) *
        riccati R gamma rho nu u (y j.val)) +
        (correctorWeight alpha dt n n : ℂ) * riccati R gamma rho nu u (y n) - y n‖ ≤ ε)
    (hrows : ∀ n, 0 < n → n ≤ N →
      L * weightedRow (predictorWeight alpha dt) W n ≤ W n / 8 ∧
      L * weightedRow (correctorWeight alpha dt) W n +
        correctorWeight alpha dt n n * L ^ 2 * weightedRow (predictorWeight alpha dt) W n ≤
          3 * W n / 8 ∧
      correctorWeight alpha dt n n * L ≤ 1) :
    ∀ n ≤ N, ‖roughState alpha dt R gamma rho nu u n - y n‖ ≤ 4 * ε * W n := by
  apply validated_continuation (correctorWeight alpha dt) (predictorWeight alpha dt)
    (riccati R gamma rho nu u) (roughState alpha dt R gamma rho nu u) y W N
    (fun _ _ _ hj => correctorWeight_nonneg ha ht hj)
    (fun n _ j _ => predictorWeight_nonneg ha ht j n) hL hε hW hmargin hy
  · rw [roughState_zero, hyzero]
  · intro n _
    exact roughState_eq_singleCorrection alpha dt R gamma rho nu u n
  · exact hlip
  · exact hpred
  · exact hcorr
  · exact hrows

end RoughHeston
