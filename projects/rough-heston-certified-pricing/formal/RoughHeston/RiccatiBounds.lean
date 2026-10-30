module

public import RoughHeston.FiniteBand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Explicit finite-frequency Riccati constants

The last identities provide inward-pointing boundary calculations for the
nondegenerate parameter example. They are algebraic statements, not a
fractional comparison principle or an existence theorem.
-/

@[expose] public section
noncomputable section

namespace RoughHeston

def riccatiConstant (R u : ℝ) : ℂ :=
  let xi : ℂ := (u : ℂ) + Complex.I * (R : ℂ);
  -(xi ^ 2 + Complex.I * xi) / 2

def riccatiLinear (R gamma rho nu u : ℝ) : ℂ :=
  let xi : ℂ := (u : ℂ) + Complex.I * (R : ℂ);
  (gamma : ℂ) * (Complex.I * xi * (rho : ℂ) * (nu : ℂ) - 1)

theorem riccati_eq_quadraticForce (R gamma rho nu u : ℝ) (z : ℂ) :
    riccati R gamma rho nu u z =
      quadraticForce (riccatiConstant R u) (riccatiLinear R gamma rho nu u)
        ((gamma * nu) ^ 2 / 2) z := rfl

theorem riccati_norm_le (R gamma rho nu u : ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    {z : ℂ} (hz : ‖z‖ ≤ Q) :
    ‖riccati R gamma rho nu u z‖ ≤ ‖riccatiConstant R u‖ +
      ‖riccatiLinear R gamma rho nu u‖ * Q + (gamma * nu) ^ 2 / 2 * Q ^ 2 := by
  rw [riccati_eq_quadraticForce]
  exact quadraticForce_norm_le _ _ (by positivity) hQ hz

theorem riccati_lipschitz (R gamma rho nu u : ℝ) {Q : ℝ}
    {z w : ℂ} (hz : ‖z‖ ≤ Q) (hw : ‖w‖ ≤ Q) :
    ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤
      (‖riccatiLinear R gamma rho nu u‖ + (gamma * nu) ^ 2 * Q) * ‖z - w‖ := by
  rw [riccati_eq_quadraticForce, riccati_eq_quadraticForce]
  calc
    _ ≤ (‖riccatiLinear R gamma rho nu u‖ + 2 * ((gamma * nu) ^ 2 / 2) * Q) *
        ‖z - w‖ := quadraticForce_lipschitz _ _ (by positivity) hz hw
    _ = _ := by ring

def bandConstantBound (R U : ℝ) : ℝ := ((U + |R|) ^ 2 + (U + |R|)) / 2

def bandLinearBound (R gamma rho nu U : ℝ) : ℝ :=
  |gamma| * ((U + |R|) * |rho| * |nu| + 1)

theorem frequency_norm_le {R U u : ℝ} (hu : |u| ≤ U) :
    ‖(u : ℂ) + Complex.I * (R : ℂ)‖ ≤ U + |R| := by
  calc
    ‖(u : ℂ) + Complex.I * (R : ℂ)‖ ≤ ‖(u : ℂ)‖ + ‖Complex.I * (R : ℂ)‖ :=
      norm_add_le _ _
    _ = |u| + |R| := by simp
    _ ≤ U + |R| := add_le_add hu le_rfl

theorem riccatiConstant_norm_le {R U u : ℝ} (hu : |u| ≤ U) :
    ‖riccatiConstant R u‖ ≤ bandConstantBound R U := by
  let xi : ℂ := (u : ℂ) + Complex.I * (R : ℂ)
  have hxi : ‖xi‖ ≤ U + |R| := frequency_norm_le hu
  change ‖-(xi ^ 2 + Complex.I * xi) / (2 : ℂ)‖ ≤ _
  calc
    ‖-(xi ^ 2 + Complex.I * xi) / (2 : ℂ)‖ = ‖xi ^ 2 + Complex.I * xi‖ / 2 := by
      rw [norm_div, norm_neg]
      norm_num
    _ ≤ (‖xi‖ ^ 2 + ‖xi‖) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        ‖xi ^ 2 + Complex.I * xi‖ ≤ ‖xi ^ 2‖ + ‖Complex.I * xi‖ := norm_add_le _ _
        _ = ‖xi‖ ^ 2 + ‖xi‖ := by
          rw [Complex.norm_pow, Complex.norm_mul, Complex.norm_I, one_mul]
    _ ≤ bandConstantBound R U := by
      unfold bandConstantBound
      gcongr

theorem riccatiLinear_norm_le {R gamma rho nu U u : ℝ} (hu : |u| ≤ U) :
    ‖riccatiLinear R gamma rho nu u‖ ≤ bandLinearBound R gamma rho nu U := by
  let xi : ℂ := (u : ℂ) + Complex.I * (R : ℂ)
  have hxi : ‖xi‖ ≤ U + |R| := frequency_norm_le hu
  change ‖(gamma : ℂ) * (Complex.I * xi * (rho : ℂ) * (nu : ℂ) - 1)‖ ≤ _
  rw [norm_mul]
  calc
    ‖(gamma : ℂ)‖ * ‖Complex.I * xi * (rho : ℂ) * (nu : ℂ) - 1‖ ≤
        ‖(gamma : ℂ)‖ * (‖Complex.I * xi * (rho : ℂ) * (nu : ℂ)‖ + ‖(1 : ℂ)‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = |gamma| * (‖xi‖ * |rho| * |nu| + 1) := by simp
    _ ≤ bandLinearBound R gamma rho nu U := by
      unfold bandLinearBound
      gcongr

theorem riccati_band_lipschitz {R gamma rho nu U u Q : ℝ} (hu : |u| ≤ U)
    {z w : ℂ} (hz : ‖z‖ ≤ Q) (hw : ‖w‖ ≤ Q) :
    ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤
      (bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * Q) * ‖z - w‖ :=
  (riccati_lipschitz _ _ _ _ _ hz hw).trans
    (mul_le_mul_of_nonneg_right (add_le_add (riccatiLinear_norm_le hu) le_rfl) (norm_nonneg _))

theorem riccati_band_norm_le {R gamma rho nu U u Q : ℝ} (hu : |u| ≤ U)
    (hQ : 0 ≤ Q) {z : ℂ} (hz : ‖z‖ ≤ Q) :
    ‖riccati R gamma rho nu u z‖ ≤ bandConstantBound R U +
      bandLinearBound R gamma rho nu U * Q + (gamma * nu) ^ 2 / 2 * Q ^ 2 :=
  (riccati_norm_le _ _ _ _ _ hQ hz).trans
    (add_le_add (add_le_add (riccatiConstant_norm_le hu)
      (mul_le_mul_of_nonneg_right (riccatiLinear_norm_le hu) hQ)) le_rfl)

/-- The concrete finite-band example has an inward half-plane boundary. -/
theorem concrete_riccati_halfplane (u y : ℝ) :
    (riccati (-2) 1 (-1 / 2) 1 u (1 + Complex.I * (y : ℂ))).re =
      -1 / 2 - 3 / 8 * u ^ 2 - 1 / 2 * (y - u / 2) ^ 2 := by
  simp [riccati, Complex.add_re, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem concrete_riccati_halfplane_neg (u y : ℝ) :
    (riccati (-2) 1 (-1 / 2) 1 u (1 + Complex.I * (y : ℂ))).re ≤ -1 / 2 := by
  rw [concrete_riccati_halfplane]
  nlinarith [sq_nonneg u, sq_nonneg (y - u / 2)]

/-- The quadratic term has a favorable radial sign while Re z ≤ 1. -/
theorem concrete_riccati_radial_identity (u : ℝ) (z : ℂ) :
    (star z * riccati (-2) 1 (-1 / 2) 1 u z).re =
      (star z * riccatiConstant (-2) u).re + (-2 + z.re / 2) * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp [riccati, riccatiConstant, Complex.normSq_apply, pow_two]
  ring

theorem concrete_riccati_radial_bound (u : ℝ) (z : ℂ) (hx : z.re ≤ 1) :
    (star z * riccati (-2) 1 (-1 / 2) 1 u z).re ≤
      ‖riccatiConstant (-2) u‖ * ‖z‖ - 3 / 2 * ‖z‖ ^ 2 := by
  rw [concrete_riccati_radial_identity]
  have hq : (star z * riccatiConstant (-2) u).re ≤ ‖riccatiConstant (-2) u‖ * ‖z‖ := by
    calc
      _ ≤ ‖star z * riccatiConstant (-2) u‖ := Complex.re_le_norm _
      _ = _ := by simp [mul_comm]
  have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg ‖z‖)
  nlinarith

end RoughHeston
