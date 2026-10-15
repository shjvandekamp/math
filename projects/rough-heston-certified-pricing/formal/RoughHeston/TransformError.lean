module

public import RoughHeston.ExponentError
public import RoughHeston.Volterra
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Error in the actual Riccati exponent and its exponential

The polynomial exponent evaluates to the specified trapezoidal rule. Its
error is derived from nodal error and the Hölder regularity of an actual
Volterra solution. Exponentiation is controlled by an explicit norm bound;
no identity with a financial characteristic function is assumed here.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Polynomial

namespace RoughHeston

def riccatiExponentIntegrand (R gamma rho nu theta V0 u : ℝ) (z : ℂ) : ℂ :=
  ((theta * gamma : ℝ) : ℂ) * z + (V0 : ℂ) * riccati R gamma rho nu u z

def exactRiccatiExponent (R gamma rho nu theta V0 u T : ℝ) (h : ℝ → ℂ) : ℂ :=
  ∫ t in 0..T, riccatiExponentIntegrand R gamma rho nu theta V0 u (h t)

def riccatiExponentLipschitz (theta gamma V0 L : ℝ) : ℝ :=
  |theta * gamma| + |V0| * L

theorem riccatiExponentLipschitz_nonneg (theta gamma V0 : ℝ) {L : ℝ}
    (hL : 0 ≤ L) : 0 ≤ riccatiExponentLipschitz theta gamma V0 L :=
  add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hL)

theorem continuous_riccatiExponentIntegrand (R gamma rho nu theta V0 u : ℝ) :
    Continuous (riccatiExponentIntegrand R gamma rho nu theta V0 u) := by
  unfold riccatiExponentIntegrand
  exact (continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_riccati R gamma rho nu u))

/-- This identifies the actual polynomial exponent with the actual nodal rule. -/
theorem roughExponent_eval_eq_trapezoid
    (alpha dt R gamma rho nu theta V0 u : ℝ) (N : ℕ) :
    (roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) =
      ∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
        riccatiExponentIntegrand R gamma rho nu theta V0 u
          (roughState alpha dt R gamma rho nu u j.val) := by
  simp only [roughExponent, exponentPoly, eval_finsetSum, eval_mul, eval_C,
    integrandPoly, eval_add, forcePoly_eval, riccatiExponentIntegrand, roughState]

theorem riccatiExponentIntegrand_norm_le
    (R gamma rho nu theta V0 u : ℝ) {Q M : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ Q) (hF : ‖riccati R gamma rho nu u z‖ ≤ M) :
    ‖riccatiExponentIntegrand R gamma rho nu theta V0 u z‖ ≤
      |theta * gamma| * Q + |V0| * M := by
  calc
    _ ≤ ‖((theta * gamma : ℝ) : ℂ) * z‖ +
        ‖(V0 : ℂ) * riccati R gamma rho nu u z‖ := norm_add_le _ _
    _ = |theta * gamma| * ‖z‖ + |V0| * ‖riccati R gamma rho nu u z‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hF (abs_nonneg _))

theorem riccatiExponentIntegrand_lipschitz
    (R gamma rho nu theta V0 u : ℝ) {L Q : ℝ}
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    {z w : ℂ} (hz : ‖z‖ ≤ Q) (hw : ‖w‖ ≤ Q) :
    ‖riccatiExponentIntegrand R gamma rho nu theta V0 u z -
      riccatiExponentIntegrand R gamma rho nu theta V0 u w‖ ≤
      riccatiExponentLipschitz theta gamma V0 L * ‖z - w‖ := by
  have heq : riccatiExponentIntegrand R gamma rho nu theta V0 u z -
      riccatiExponentIntegrand R gamma rho nu theta V0 u w =
      ((theta * gamma : ℝ) : ℂ) * (z - w) +
        (V0 : ℂ) * (riccati R gamma rho nu u z - riccati R gamma rho nu u w) := by
    unfold riccatiExponentIntegrand
    ring
  rw [heq]
  calc
    _ ≤ ‖((theta * gamma : ℝ) : ℂ) * (z - w)‖ +
        ‖(V0 : ℂ) * (riccati R gamma rho nu u z - riccati R gamma rho nu u w)‖ :=
      norm_add_le _ _
    _ = |theta * gamma| * ‖z - w‖ +
        |V0| * ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |theta * gamma| * ‖z - w‖ + |V0| * (L * ‖z - w‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hlip z w hz hw) (abs_nonneg _))
    _ = _ := by unfold riccatiExponentLipschitz; ring

theorem IsRiccatiSolution.exponentIntegrand_continuous
    {alpha R gamma rho nu u T : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u T h) (theta V0 : ℝ) :
    ContinuousOn (fun t => riccatiExponentIntegrand R gamma rho nu theta V0 u (h t))
      (Icc 0 T) :=
  (continuous_riccatiExponentIntegrand R gamma rho nu theta V0 u).comp_continuousOn hh.1

theorem IsRiccatiSolution.exponentIntegrand_holder
    {alpha R gamma rho nu theta V0 u T M L Q : ℝ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u T h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hL : 0 ≤ L)
    (hforce : ∀ t ∈ Icc 0 T, ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    (hpath : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖riccatiExponentIntegrand R gamma rho nu theta V0 u (h t) -
      riccatiExponentIntegrand R gamma rho nu theta V0 u (h s)‖ ≤
      (riccatiExponentLipschitz theta gamma V0 L * (2 * M / Real.Gamma (alpha + 1))) *
        (t - s) ^ alpha := by
  have h := (riccatiExponentIntegrand_lipschitz R gamma rho nu theta V0 u hlip
    (hpath t ⟨hs.trans hst, htT⟩) (hpath s ⟨hs, hst.trans htT⟩)).trans
    (mul_le_mul_of_nonneg_left (hh.holder ha ha1 hforce hs hst htT)
      (riccatiExponentLipschitz_nonneg theta gamma V0 hL))
  simpa only [mul_assoc] using h

/-- Nodal error and derived Volterra regularity control the actual exponent. -/
theorem IsRiccatiSolution.roughExponent_error
    {alpha dt R gamma rho nu theta V0 u M L Q E : ℝ} {N : ℕ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < dt) (hN : 0 < N) (hL : 0 ≤ L)
    (hforce : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    (hpath : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q)
    (hnumeric : ∀ j ≤ N, ‖roughState alpha dt R gamma rho nu u j‖ ≤ Q)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (herror : ∀ j ≤ N,
      ‖roughState alpha dt R gamma rho nu u j - h ((j : ℝ) * dt)‖ ≤ E) :
    ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
      exactRiccatiExponent R gamma rho nu theta V0 u ((N : ℝ) * dt) h‖ ≤
      ((N : ℝ) * dt) * riccatiExponentLipschitz theta gamma V0 L *
        (E + (2 * M / Real.Gamma (alpha + 1)) * dt ^ alpha) := by
  have hT : 0 ≤ (N : ℝ) * dt := mul_nonneg (Nat.cast_nonneg _) ht.le
  have hM : 0 ≤ M := (norm_nonneg _).trans (hforce 0 ⟨le_rfl, hT⟩)
  have hLJ := riccatiExponentLipschitz_nonneg theta gamma V0 hL
  have hH : 0 ≤ riccatiExponentLipschitz theta gamma V0 L *
      (2 * M / Real.Gamma (alpha + 1)) :=
    mul_nonneg hLJ (div_nonneg (mul_nonneg (by norm_num) hM)
      (Real.Gamma_pos_of_pos (by linarith : 0 < alpha + 1)).le)
  let J := riccatiExponentIntegrand R gamma rho nu theta V0 u
  have hquad := trapezoid_consistency ha ht hH hN (fun t => J (h t))
    (hh.exponentIntegrand_continuous theta V0)
    (fun s t hs hst htT => hh.exponentIntegrand_holder ha ha1 hL hforce hpath hlip hs hst htT)
  have hnodal := trapezoid_nodal_perturbation ht.le hN
    (fun j => J (roughState alpha dt R gamma rho nu u j))
    (fun j => J (h ((j : ℝ) * dt))) (fun j hj => by
      have hjT : (j : ℝ) * dt ∈ Icc 0 ((N : ℝ) * dt) :=
        ⟨mul_nonneg (Nat.cast_nonneg _) ht.le,
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ht.le⟩
      exact (riccatiExponentIntegrand_lipschitz R gamma rho nu theta V0 u hlip
        (hnumeric j hj) (hpath _ hjT)).trans
          (mul_le_mul_of_nonneg_left (herror j hj) hLJ))
  rw [roughExponent_eval_eq_trapezoid]
  unfold exactRiccatiExponent
  calc
    _ ≤ ‖(∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
          J (roughState alpha dt R gamma rho nu u j.val)) -
        ∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
          J (h ((j.val : ℝ) * dt))‖ +
        ‖(∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
          J (h ((j.val : ℝ) * dt))) - ∫ t in 0..(N : ℝ) * dt, J (h t)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((N : ℝ) * dt) * (riccatiExponentLipschitz theta gamma V0 L * E) +
        ((N : ℝ) * dt) *
          (riccatiExponentLipschitz theta gamma V0 L * (2 * M / Real.Gamma (alpha + 1))) *
            dt ^ alpha :=
      add_le_add hnodal (by simpa only [norm_sub_rev] using hquad)
    _ = _ := by ring

theorem exactRiccatiExponent_norm_le
    {R gamma rho nu theta V0 u T Q M : ℝ} {h : ℝ → ℂ} (hT : 0 ≤ T)
    (hpath : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q)
    (hforce : ∀ t ∈ Icc 0 T, ‖riccati R gamma rho nu u (h t)‖ ≤ M) :
    ‖exactRiccatiExponent R gamma rho nu theta V0 u T h‖ ≤
      T * (|theta * gamma| * Q + |V0| * M) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T)
    (f := fun t => riccatiExponentIntegrand R gamma rho nu theta V0 u (h t))
    (C := |theta * gamma| * Q + |V0| * M) (fun t ht => by
      rw [uIoc_of_le hT] at ht
      exact riccatiExponentIntegrand_norm_le R gamma rho nu theta V0 u
        (hpath t ⟨ht.1.le, ht.2⟩) (hforce t ⟨ht.1.le, ht.2⟩))
  simpa only [exactRiccatiExponent, sub_zero, abs_of_nonneg hT, mul_comm] using hb

/-- A global exponential perturbation estimate; no small-error condition is needed. -/
theorem norm_exp_sub_exp_le {z w : ℂ} {B D : ℝ}
    (hw : ‖w‖ ≤ B) (hd : ‖z - w‖ ≤ D) :
    ‖Complex.exp z - Complex.exp w‖ ≤ Real.exp (B + D) * D := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hd
  have hsmall : ‖Complex.exp (z - w) - 1‖ ≤ ‖z - w‖ * Real.exp ‖z - w‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (z - w) 1
  have hdelta : ‖Complex.exp (z - w) - 1‖ ≤ D * Real.exp D :=
    hsmall.trans (mul_le_mul hd (Real.exp_le_exp.mpr hd) (Real.exp_pos _).le hD)
  have heq : Complex.exp z - Complex.exp w =
      Complex.exp w * (Complex.exp (z - w) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, Complex.norm_mul]
  calc
    _ ≤ Real.exp B * (D * Real.exp D) :=
      mul_le_mul ((Complex.norm_exp_le_exp_norm w).trans (Real.exp_le_exp.mpr hw))
        hdelta (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

/-- The exponential of the computed exponent is controlled by its actual
exponent error and explicit exact-path bounds. -/
theorem roughTransform_error_of_exponent_error
    {alpha dt R gamma rho nu theta V0 u Q M D : ℝ} {N : ℕ} {h : ℝ → ℂ}
    (ht : 0 ≤ dt)
    (hpath : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q)
    (hforce : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    (herror : ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
      exactRiccatiExponent R gamma rho nu theta V0 u ((N : ℝ) * dt) h‖ ≤ D) :
    ‖Complex.exp ((roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ)) -
      Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u ((N : ℝ) * dt) h)‖ ≤
      Real.exp (((N : ℝ) * dt) * (|theta * gamma| * Q + |V0| * M) + D) * D :=
  norm_exp_sub_exp_le
    (exactRiccatiExponent_norm_le (mul_nonneg (Nat.cast_nonneg _) ht) hpath hforce) herror

/-- The exact exponent with the same affine spot/rate phase as the discrete rule. -/
def exactRiccatiExponentWithDrift (R gamma rho nu theta V0 u m T : ℝ) (h : ℝ → ℂ) : ℂ :=
  (driftPoly R m).eval (u : ℂ) + exactRiccatiExponent R gamma rho nu theta V0 u T h

theorem driftPoly_eval_eq_phase (R m u : ℝ) :
    (driftPoly R m).eval (u : ℂ) =
      Complex.I * ((u : ℂ) + Complex.I * (R : ℂ)) * (m : ℂ) := by
  simp only [driftPoly, eval_add, eval_mul, eval_C, eval_X]
  linear_combination -(R : ℂ) * (m : ℂ) * Complex.I_sq

theorem driftPoly_eval_re (R m u : ℝ) :
    ((driftPoly R m).eval (u : ℂ)).re = -R * m := by
  simp [driftPoly, Complex.mul_re, Complex.mul_im]

/-- A common complex phase contributes only its real exponential to the error norm. -/
theorem norm_exp_add_sub_exp_add (v z w : ℂ) :
    ‖Complex.exp (v + z) - Complex.exp (v + w)‖ =
      Real.exp v.re * ‖Complex.exp z - Complex.exp w‖ := by
  rw [Complex.exp_add, Complex.exp_add, ← mul_sub, Complex.norm_mul, Complex.norm_exp]

theorem roughExponentWithDrift_error_eq
    (alpha dt R gamma rho nu theta V0 u m T : ℝ) (N : ℕ) (h : ℝ → ℂ) :
    ‖(roughExponentWithDrift alpha dt R gamma rho nu theta V0 m N).eval (u : ℂ) -
      exactRiccatiExponentWithDrift R gamma rho nu theta V0 u m T h‖ =
      ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
        exactRiccatiExponent R gamma rho nu theta V0 u T h‖ := by
  simp [roughExponentWithDrift, exactRiccatiExponentWithDrift]

theorem roughTransformWithDrift_error_eq
    (alpha dt R gamma rho nu theta V0 u m T : ℝ) (N : ℕ) (h : ℝ → ℂ) :
    ‖Complex.exp ((roughExponentWithDrift alpha dt R gamma rho nu theta V0 m N).eval
        (u : ℂ)) -
      Complex.exp (exactRiccatiExponentWithDrift R gamma rho nu theta V0 u m T h)‖ =
      Real.exp (-R * m) *
        ‖Complex.exp ((roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ)) -
          Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T h)‖ := by
  rw [roughExponentWithDrift, eval_add, exactRiccatiExponentWithDrift,
    norm_exp_add_sub_exp_add, driftPoly_eval_re]

end RoughHeston
