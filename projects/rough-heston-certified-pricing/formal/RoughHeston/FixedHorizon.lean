module

public import RoughHeston.Convergence
public import RoughHeston.WeightedRows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Validated Adams convergence on an arbitrary fixed horizon

The exponential row bounds are derived for the concrete Gamma weights and
the defects are derived from the actual Volterra equation. The restrictions
are explicit mesh conditions. No smallness of the whole maturity is needed.
An exact bounded solution is still an explicit mathematical hypothesis.
-/

@[expose] public section
noncomputable section
open Set Finset

namespace RoughHeston

theorem exponential_adams_row_certificate {alpha dt rate L : ℝ}
    (ha : 0 < alpha) (ht : 0 < dt) (hr : 0 < rate) (hL : 0 ≤ L)
    (hrL : L * rate ^ (-alpha) ≤ 1 / 8)
    (hstep : Real.exp (rate * dt) ≤ 2)
    (haL : dt ^ alpha / Real.Gamma (alpha + 2) * L ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    L * weightedRow (predictorWeight alpha dt) (fun j => Real.exp (rate * ((j : ℝ) * dt))) n ≤
        Real.exp (rate * ((n : ℝ) * dt)) / 8 ∧
    L * weightedRow (correctorWeight alpha dt) (fun j => Real.exp (rate * ((j : ℝ) * dt))) n +
        correctorWeight alpha dt n n * L ^ 2 *
          weightedRow (predictorWeight alpha dt) (fun j => Real.exp (rate * ((j : ℝ) * dt))) n ≤
        3 * Real.exp (rate * ((n : ℝ) * dt)) / 8 ∧
    correctorWeight alpha dt n n * L ≤ 1 := by
  let W := Real.exp (rate * ((n : ℝ) * dt))
  have hW : 0 ≤ W := (Real.exp_pos _).le
  have hae : 0 ≤ correctorWeight alpha dt n n := correctorWeight_nonneg ha ht le_rfl
  have haeL : correctorWeight alpha dt n n * L ≤ 1 := by
    simpa only [correctorWeight_endpoint] using haL
  have hp : L * weightedRow (predictorWeight alpha dt)
      (fun j => Real.exp (rate * ((j : ℝ) * dt))) n ≤ W / 8 := by
    calc
      _ ≤ L * (W * rate ^ (-alpha)) :=
        mul_le_mul_of_nonneg_left (predictorWeight_exp_growth_row_le ha ht hr n) hL
      _ = W * (L * rate ^ (-alpha)) := by ring
      _ ≤ W * (1 / 8) := mul_le_mul_of_nonneg_left hrL hW
      _ = W / 8 := by ring
  have hA : L * weightedRow (correctorWeight alpha dt)
      (fun j => Real.exp (rate * ((j : ℝ) * dt))) n ≤ W / 4 := by
    calc
      _ ≤ L * (W * (Real.exp (rate * dt) * rate ^ (-alpha))) :=
        mul_le_mul_of_nonneg_left (correctorWeight_exp_growth_history_row_le ha ht hr hn) hL
      _ = W * (Real.exp (rate * dt) * (L * rate ^ (-alpha))) := by ring
      _ ≤ W * (Real.exp (rate * dt) * (1 / 8)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrL (Real.exp_pos _).le) hW
      _ ≤ W * (2 * (1 / 8)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hstep (by norm_num)) hW
      _ = W / 4 := by ring
  have hcross : correctorWeight alpha dt n n * L ^ 2 *
      weightedRow (predictorWeight alpha dt) (fun j => Real.exp (rate * ((j : ℝ) * dt))) n ≤ W / 8 := by
    calc
      _ = (correctorWeight alpha dt n n * L) *
          (L * weightedRow (predictorWeight alpha dt) (fun j => Real.exp (rate * ((j : ℝ) * dt))) n) := by ring
      _ ≤ (correctorWeight alpha dt n n * L) * (W / 8) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hae hL)
      _ ≤ 1 * (W / 8) := mul_le_mul_of_nonneg_right haeL (by positivity)
      _ = W / 8 := one_mul _
  exact ⟨hp, by dsimp [W] at hA hcross; linarith, haeL⟩

/-- Fixed-maturity nodal convergence of the unchanged explicit Adams scheme.
The only accuracy restrictions are the displayed exponential-step, endpoint,
and error-margin inequalities. All history and consistency estimates have
been discharged for the concrete weights and integral equation. -/
theorem riccati_fixed_horizon_nodal_error (alpha dt R gamma rho nu u rate : ℝ)
    (N : ℕ) (h : ℝ → ℂ) {Q0 eta M L : ℝ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < dt) (hr : 0 < rate)
    (heta : 0 ≤ eta) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hrL : L * rate ^ (-alpha) ≤ 1 / 8)
    (hstep : Real.exp (rate * dt) ≤ 2)
    (haL : dt ^ alpha / Real.Gamma (alpha + 2) * L ≤ 1)
    (hmargin : 4 * riccatiDefectBound alpha dt M L N *
      Real.exp (rate * ((N : ℝ) * dt)) ≤ eta)
    (hFbound : ∀ z : ℂ, ‖z‖ ≤ Q0 + eta → ‖riccati R gamma rho nu u z‖ ≤ M)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q0 + eta → ‖w‖ ≤ Q0 + eta →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (hhbound : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q0) :
    ∀ n ≤ N,
      ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ ≤
        4 * riccatiDefectBound alpha dt M L N * Real.exp (rate * ((N : ℝ) * dt)) ∧
      ‖roughState alpha dt R gamma rho nu u n‖ ≤ Q0 + eta := by
  let W : ℕ → ℝ := fun n => Real.exp (rate * ((n : ℝ) * dt))
  have hW (n : ℕ) (hn : n ≤ N) : 1 ≤ W n ∧ W n ≤ W N := by
    constructor
    · apply Real.one_le_exp_iff.mpr
      positivity
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht.le) hr.le
  have hε : 0 ≤ riccatiDefectBound alpha dt M L N := riccatiDefectBound_nonneg N ha ht hM hL
  have hpath (t : ℝ) (ht' : t ∈ Icc 0 ((N : ℝ) * dt)) : ‖h t‖ ≤ Q0 + eta :=
    (hhbound t ht').trans (le_add_of_nonneg_right heta)
  have hcons (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) := hh.adams_consistency ha ha1 ht hM hL
    (fun t ht' => hFbound _ (hpath t ht')) hpath hlip hn hnN
  have herr := roughState_validated_continuation alpha dt R gamma rho nu u
    (fun n => h ((n : ℝ) * dt)) W N ha ht hL hε hW hmargin
    (fun n hn => hhbound _ ⟨mul_nonneg (Nat.cast_nonneg _) ht.le,
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht.le⟩)
    (by simpa only [Nat.cast_zero, zero_mul] using hh.zero (mul_nonneg (Nat.cast_nonneg _) ht.le))
    hlip (fun n hn hnN => (hcons n hn hnN).1) (fun n hn hnN => (hcons n hn hnN).2)
    (fun n hn _ => exponential_adams_row_certificate ha ht hr hL hrL hstep haL hn)
  intro n hn
  have hnerr : ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ ≤
      4 * riccatiDefectBound alpha dt M L N * W N :=
    (herr n hn).trans (mul_le_mul_of_nonneg_left (hW n hn).2 (by positivity))
  refine ⟨hnerr, ?_⟩
  calc
    ‖roughState alpha dt R gamma rho nu u n‖ ≤
        ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ + ‖h ((n : ℝ) * dt)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 4 * riccatiDefectBound alpha dt M L N * W N + Q0 :=
      add_le_add hnerr (hhbound _ ⟨mul_nonneg (Nat.cast_nonneg _) ht.le,
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht.le⟩)
    _ ≤ Q0 + eta := by linarith

end RoughHeston
