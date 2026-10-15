module

public import RoughHeston.AdamsStability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform nodal error on a contraction horizon

The two exact-data defects remain displayed in this algebraic layer. They
are supplied by product-integration consistency in the analytic layer.
-/

@[expose] public section
noncomputable section
open Finset

namespace RoughHeston

theorem roughState_local_error (alpha dt R gamma rho nu u : ℝ)
    (y : ℕ → ℂ) (N : ℕ) {Q M L ε : ℝ}
    (ha : 0 < alpha) (ht : 0 < dt) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hsmall : adamsRowMass alpha dt N * M ≤ Q)
    (hcontract : adamsRowMass alpha dt N * L < 1)
    (hFbound : ∀ z : ℂ, ‖z‖ ≤ Q → ‖riccati R gamma rho nu u z‖ ≤ M)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (hy : ∀ n ≤ N, ‖y n‖ ≤ Q) (hyzero : y 0 = 0)
    (hpred : ∀ n, 0 < n → n ≤ N →
      ‖(∑ j : Fin n, (predictorWeight alpha dt j.val n : ℂ) *
        riccati R gamma rho nu u (y j.val)) - y n‖ ≤ ε)
    (hcorr : ∀ n, 0 < n → n ≤ N →
      ‖(∑ j : Fin n, (correctorWeight alpha dt j.val n : ℂ) *
        riccati R gamma rho nu u (y j.val)) +
        (correctorWeight alpha dt n n : ℂ) * riccati R gamma rho nu u (y n) - y n‖ ≤ ε) :
    ∀ n ≤ N, ‖roughState alpha dt R gamma rho nu u n - y n‖ ≤
      ε * (1 + adamsRowMass alpha dt N * L) / (1 - adamsRowMass alpha dt N * L) := by
  let κ := adamsRowMass alpha dt N
  let E := ε * (1 + κ * L) / (1 - κ * L)
  have hk : 0 ≤ κ := by
    dsimp [κ, adamsRowMass]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.Gamma_pos_of_pos (by linarith)).le
  have hd : 0 < 1 - κ * L := by dsimp [κ]; linarith
  have hE : 0 ≤ E := div_nonneg (mul_nonneg hε (by positivity)) hd.le
  have hfix : ε * (1 + κ * L) + κ * L * E = E := by
    dsimp [E]
    field_simp
    ring
  have hball := roughState_invariant_ball alpha dt R gamma rho nu u N ha ht hQ hM hsmall hFbound
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    change ‖roughState alpha dt R gamma rho nu u n - y n‖ ≤ E
    cases n with
    | zero => simpa only [roughState_zero, hyzero, sub_self, norm_zero] using hE
    | succ n =>
      have hrowA :
          (∑ j : Fin (n + 1), correctorWeight alpha dt j.val (n + 1)) +
            correctorWeight alpha dt (n + 1) (n + 1) ≤ κ := by
        rw [correctorWeight_history_sum_fin ha dt (Nat.succ_pos n), correctorWeight_endpoint]
        simpa only [sub_add_cancel, adamsRowMass, κ] using adamsRowMass_mono ha ht hn
      have hrowB : (∑ j : Fin (n + 1), predictorWeight alpha dt j.val (n + 1)) ≤ κ := by
        rw [predictorWeight_sum_fin ha dt (n + 1)]
        exact adamsRowMass_mono ha ht hn
      have hstep := singleCorrection_error_uniform
        (fun j : Fin (n + 1) => correctorWeight alpha dt j.val (n + 1))
        (fun j : Fin (n + 1) => predictorWeight alpha dt j.val (n + 1))
        (correctorWeight alpha dt (n + 1) (n + 1))
        (riccati R gamma rho nu u)
        (fun j : Fin (n + 1) => roughState alpha dt R gamma rho nu u j.val)
        (fun j : Fin (n + 1) => y j.val) (y (n + 1))
        (fun j => correctorWeight_nonneg ha ht j.isLt.le)
        (fun j => predictorWeight_nonneg ha ht j.val (n + 1))
        (correctorWeight_nonneg ha ht le_rfl) hL hE hε hrowA hrowB hcontract.le
        (fun j => (hlip _ _ (hball _ (j.isLt.le.trans hn)).1
          (hy _ (j.isLt.le.trans hn))).trans
            (mul_le_mul_of_nonneg_left (ih j.val j.isLt (j.isLt.le.trans hn)) hL))
        (hpred _ (Nat.succ_pos n) hn) (hcorr _ (Nat.succ_pos n) hn)
        (hlip _ _ (hball _ hn).2 (hy _ hn))
      rw [roughState_eq_singleCorrection]
      exact hstep.trans_eq hfix

end RoughHeston
