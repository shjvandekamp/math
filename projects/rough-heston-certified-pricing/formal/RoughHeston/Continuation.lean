module

public import RoughHeston.FiniteBand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite certificate for continuation of the explicit Adams recurrence

All rows below retain the full history. The certificate uses positive
comparison weights `W`; exponential or geometric choices may be used. Its
premises are concrete finite-sum inequalities, two displayed consistency
residuals, and local bounds for the comparison solution and force. In
particular the numerical solution is not assumed to remain in the ball.
-/

@[expose] public section
noncomputable section
open Finset

namespace RoughHeston

def weightedRow (a : ℕ → ℕ → ℝ) (W : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin n, a j.val n * W j.val

theorem history_error_weighted {n : ℕ} (a : Fin n → ℝ) (F : ℂ → ℂ)
    (x y : Fin n → ℂ) (W : Fin n → ℝ) {L E : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hF : ∀ j, ‖F (x j) - F (y j)‖ ≤ L * (E * W j)) :
    ‖weightedHistory a F x - weightedHistory a F y‖ ≤
      E * L * (∑ j, a j * W j) := by
  calc
    ‖weightedHistory a F x - weightedHistory a F y‖ ≤
        ∑ j, a j * (L * (E * W j)) := weightedHistory_sub_le a F x y _ ha hF
    _ = E * L * (∑ j, a j * W j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

/-- A single validated continuation step. The predicted endpoint is first
shown to lie in the local Lipschitz ball, before its force is compared. -/
theorem singleCorrection_validated {n : ℕ} (a b : Fin n → ℝ) (ae : ℝ)
    (F : ℂ → ℂ) (x y : Fin n → ℂ) (yn : ℂ) (W : Fin n → ℝ)
    {wn Wmax Q0 eta L ε : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (he : 0 ≤ ae)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hwn : 1 ≤ wn) (hwnmax : wn ≤ Wmax)
    (hWmax : ∀ j, W j ≤ Wmax)
    (hmargin : 4 * ε * Wmax ≤ eta)
    (hy : ∀ j, ‖y j‖ ≤ Q0) (hyn : ‖yn‖ ≤ Q0)
    (herror : ∀ j, ‖x j - y j‖ ≤ 4 * ε * W j)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q0 + eta → ‖w‖ ≤ Q0 + eta →
      ‖F z - F w‖ ≤ L * ‖z - w‖)
    (hpred : ‖weightedHistory b F y - yn‖ ≤ ε)
    (hcorr : ‖weightedHistory a F y + (ae : ℂ) * F yn - yn‖ ≤ ε)
    (hrowB : L * (∑ j, b j * W j) ≤ wn / 8)
    (hrowAB : L * (∑ j, a j * W j) + ae * L ^ 2 * (∑ j, b j * W j) ≤ 3 * wn / 8)
    (haL : ae * L ≤ 1) :
    ‖weightedHistory b F x - yn‖ ≤ 3 / 2 * ε * wn ∧
    ‖weightedHistory b F x‖ ≤ Q0 + eta ∧
    ‖singleCorrection a b ae F x - yn‖ ≤ 4 * ε * wn := by
  have he4 : 0 ≤ 4 * ε := by positivity
  have heta : 0 ≤ eta := by
    have : 0 ≤ 4 * ε * Wmax := mul_nonneg he4 (by linarith)
    linarith
  have hxball (j : Fin n) : ‖x j‖ ≤ Q0 + eta := by
    calc
      ‖x j‖ ≤ ‖x j - y j‖ + ‖y j‖ := norm_le_norm_sub_add _ _
      _ ≤ 4 * ε * W j + Q0 := add_le_add (herror j) (hy j)
      _ ≤ Q0 + eta := by
        have := mul_le_mul_of_nonneg_left (hWmax j) he4
        linarith
  have hF (j : Fin n) : ‖F (x j) - F (y j)‖ ≤ L * (4 * ε * W j) :=
    (hlip _ _ (hxball j) (by have := hy j; linarith)).trans
      (mul_le_mul_of_nonneg_left (herror j) hL)
  have hp : ‖weightedHistory b F x - yn‖ ≤ 3 / 2 * ε * wn := by
    calc
      ‖weightedHistory b F x - yn‖ ≤
          ‖weightedHistory b F x - weightedHistory b F y‖ +
            ‖weightedHistory b F y - yn‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (4 * ε) * L * (∑ j, b j * W j) + ε :=
        add_le_add (history_error_weighted b F x y W hb hF) hpred
      _ ≤ 3 / 2 * ε * wn := by
        have hm := mul_le_mul_of_nonneg_left hrowB he4
        have hw := mul_le_mul_of_nonneg_left hwn hε
        nlinarith
  have hpball : ‖weightedHistory b F x‖ ≤ Q0 + eta := by
    calc
      ‖weightedHistory b F x‖ ≤ ‖weightedHistory b F x - yn‖ + ‖yn‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ 3 / 2 * ε * wn + Q0 := add_le_add hp hyn
      _ ≤ Q0 + eta := by
        have hm := mul_le_mul_of_nonneg_left hwnmax he4
        have hw : 0 ≤ ε * wn := mul_nonneg hε (by linarith)
        nlinarith
  refine ⟨hp, hpball, ?_⟩
  have hstep := singleCorrection_error a b ae F x y yn
    (fun j => 4 * ε * W j) ha hb he hL hF hpred hcorr
    (hlip _ _ hpball (by linarith))
  have hs (v : Fin n → ℝ) :
      (∑ j, v j * (L * (4 * ε * W j))) = 4 * ε * L * (∑ j, v j * W j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [hs a, hs b] at hstep
  have hm := mul_le_mul_of_nonneg_left hrowAB he4
  have heL := mul_le_mul_of_nonneg_left haL hε
  have hw := mul_le_mul_of_nonneg_left hwn hε
  nlinarith

/-- Finite-horizon validation for an actual PECE recurrence. The weighted
row and residual conditions are explicit, checkable mathematical premises;
this declaration alone does not assert that a mesh passes the certificate. -/
theorem validated_continuation (a b : ℕ → ℕ → ℝ) (F : ℂ → ℂ)
    (x y : ℕ → ℂ) (W : ℕ → ℝ) (N : ℕ) {Wmax Q0 eta L ε : ℝ}
    (ha : ∀ n ≤ N, ∀ j ≤ n, 0 ≤ a j n)
    (hb : ∀ n ≤ N, ∀ j < n, 0 ≤ b j n)
    (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hW : ∀ n ≤ N, 1 ≤ W n ∧ W n ≤ Wmax)
    (hmargin : 4 * ε * Wmax ≤ eta)
    (hy : ∀ n ≤ N, ‖y n‖ ≤ Q0) (hzero : x 0 = y 0)
    (hrec : ∀ n, n + 1 ≤ N → x (n + 1) =
      singleCorrection (fun j : Fin (n + 1) => a j.val (n + 1))
        (fun j : Fin (n + 1) => b j.val (n + 1)) (a (n + 1) (n + 1)) F
        (fun j : Fin (n + 1) => x j.val))
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q0 + eta → ‖w‖ ≤ Q0 + eta →
      ‖F z - F w‖ ≤ L * ‖z - w‖)
    (hpred : ∀ n, 0 < n → n ≤ N →
      ‖weightedHistory (fun j : Fin n => b j.val n) F (fun j : Fin n => y j.val) - y n‖ ≤ ε)
    (hcorr : ∀ n, 0 < n → n ≤ N →
      ‖weightedHistory (fun j : Fin n => a j.val n) F (fun j : Fin n => y j.val) +
        (a n n : ℂ) * F (y n) - y n‖ ≤ ε)
    (hrows : ∀ n, 0 < n → n ≤ N →
      L * weightedRow b W n ≤ W n / 8 ∧
      L * weightedRow a W n + a n n * L ^ 2 * weightedRow b W n ≤ 3 * W n / 8 ∧
      a n n * L ≤ 1) :
    ∀ n ≤ N, ‖x n - y n‖ ≤ 4 * ε * W n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero =>
      rw [hzero, sub_self, norm_zero]
      exact mul_nonneg (by positivity) (by have := (hW 0 hn).1; linarith)
    | succ n =>
      have hi (j : Fin (n + 1)) : ‖x j.val - y j.val‖ ≤ 4 * ε * W j.val :=
        ih j.val j.isLt (j.isLt.le.trans hn)
      have hs := singleCorrection_validated
        (fun j : Fin (n + 1) => a j.val (n + 1))
        (fun j : Fin (n + 1) => b j.val (n + 1))
        (a (n + 1) (n + 1)) F
        (fun j : Fin (n + 1) => x j.val) (fun j : Fin (n + 1) => y j.val)
        (y (n + 1)) (fun j : Fin (n + 1) => W j.val)
        (fun j => ha _ hn _ j.isLt.le) (fun j => hb _ hn _ j.isLt)
        (ha _ hn _ le_rfl) hL hε (hW _ hn).1 (hW _ hn).2
        (fun j => (hW _ (j.isLt.le.trans hn)).2) hmargin
        (fun j => hy _ (j.isLt.le.trans hn)) (hy _ hn) hi hlip
        (hpred _ (Nat.succ_pos n) hn) (hcorr _ (Nat.succ_pos n) hn)
        (hrows _ (Nat.succ_pos n) hn).1 (hrows _ (Nat.succ_pos n) hn).2.1
        (hrows _ (Nat.succ_pos n) hn).2.2
      rw [hrec n hn]
      exact hs.2.2

end RoughHeston
