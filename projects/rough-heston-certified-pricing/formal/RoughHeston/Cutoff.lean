module

public import RoughHeston.Volterra
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A globally Lipschitz cutoff for the Riccati force

Clamping each real component to `[-Q,Q]` fixes the complex ball of radius
`Q`. Its image has norm at most `2*Q`, and the clamp is globally
`2`-Lipschitz. Composing the actual Riccati polynomial with this map gives
an explicit globally Lipschitz force, uniformly on a finite frequency band.
No existence or invariant-region conclusion is included here.
-/

@[expose] public section
noncomputable section

namespace RoughHeston

/-- Componentwise clamping to the square `[-Q,Q] × [-Q,Q]`. -/
def squareClamp (Q : ℝ) (z : ℂ) : ℂ :=
  ⟨max (-Q) (min Q z.re), max (-Q) (min Q z.im)⟩

private theorem scalarClamp_abs_le {Q : ℝ} (hQ : 0 ≤ Q) (x : ℝ) :
    |max (-Q) (min Q x)| ≤ Q := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem scalarClamp_eq_self {Q x : ℝ} (hx : |x| ≤ Q) :
    max (-Q) (min Q x) = x := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  rw [min_eq_right hu, max_eq_right hl]

private theorem scalarClamp_lipschitz (Q : ℝ) :
    LipschitzWith 1 (fun x : ℝ => max (-Q) (min Q x)) :=
  (LipschitzWith.id.const_min Q).const_max (-Q)

theorem squareClamp_norm_le {Q : ℝ} (hQ : 0 ≤ Q) (z : ℂ) :
    ‖squareClamp Q z‖ ≤ 2 * Q := by
  calc
    ‖squareClamp Q z‖ ≤ |(squareClamp Q z).re| + |(squareClamp Q z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Q + Q := add_le_add (scalarClamp_abs_le hQ z.re) (scalarClamp_abs_le hQ z.im)
    _ = 2 * Q := by ring

/-- The cutoff fixes every point in the closed complex ball of radius `Q`. -/
theorem squareClamp_eq_self_of_norm_le {Q : ℝ} (_hQ : 0 ≤ Q)
    {z : ℂ} (hz : ‖z‖ ≤ Q) : squareClamp Q z = z := by
  apply Complex.ext
  · exact scalarClamp_eq_self ((Complex.abs_re_le_norm z).trans hz)
  · exact scalarClamp_eq_self ((Complex.abs_im_le_norm z).trans hz)

@[simp] theorem squareClamp_zero {Q : ℝ} (hQ : 0 ≤ Q) : squareClamp Q 0 = 0 :=
  squareClamp_eq_self_of_norm_le hQ (by simpa using hQ)

theorem squareClamp_norm_sub_le (Q : ℝ) (z w : ℂ) :
    ‖squareClamp Q z - squareClamp Q w‖ ≤ 2 * ‖z - w‖ := by
  have hre : |max (-Q) (min Q z.re) - max (-Q) (min Q w.re)| ≤ |z.re - w.re| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (scalarClamp_lipschitz Q).dist_le_mul z.re w.re
  have him : |max (-Q) (min Q z.im) - max (-Q) (min Q w.im)| ≤ |z.im - w.im| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (scalarClamp_lipschitz Q).dist_le_mul z.im w.im
  calc
    ‖squareClamp Q z - squareClamp Q w‖ ≤
        |(squareClamp Q z - squareClamp Q w).re| +
          |(squareClamp Q z - squareClamp Q w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |z.re - w.re| + |z.im - w.im| := add_le_add hre him
    _ ≤ ‖z - w‖ + ‖z - w‖ :=
      add_le_add (Complex.abs_re_le_norm (z - w)) (Complex.abs_im_le_norm (z - w))
    _ = 2 * ‖z - w‖ := by ring

theorem squareClamp_lipschitz (Q : ℝ) : LipschitzWith 2 (squareClamp Q) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using squareClamp_norm_sub_le Q z w

theorem continuous_squareClamp (Q : ℝ) : Continuous (squareClamp Q) :=
  (squareClamp_lipschitz Q).continuous

/-- The actual Riccati polynomial composed with the componentwise cutoff. -/
def cutoffRiccati (Q R gamma rho nu u : ℝ) (z : ℂ) : ℂ :=
  riccati R gamma rho nu u (squareClamp Q z)

theorem cutoffRiccati_eq_of_norm_le {Q R gamma rho nu u : ℝ}
    (hQ : 0 ≤ Q) {z : ℂ} (hz : ‖z‖ ≤ Q) :
    cutoffRiccati Q R gamma rho nu u z = riccati R gamma rho nu u z := by
  rw [cutoffRiccati, squareClamp_eq_self_of_norm_le hQ hz]

theorem continuous_cutoffRiccati (Q R gamma rho nu u : ℝ) :
    Continuous (cutoffRiccati Q R gamma rho nu u) :=
  (continuous_riccati R gamma rho nu u).comp (continuous_squareClamp Q)

/-- A global Lipschitz constant for the cutoff force, uniform on `|u| ≤ U`. -/
def cutoffRiccatiLipschitz (Q R gamma rho nu U : ℝ) : ℝ :=
  2 * (bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * (2 * Q))

theorem cutoffRiccatiLipschitz_nonneg {Q R gamma rho nu U : ℝ}
    (hQ : 0 ≤ Q) (hU : 0 ≤ U) :
    0 ≤ cutoffRiccatiLipschitz Q R gamma rho nu U := by
  unfold cutoffRiccatiLipschitz bandLinearBound
  positivity

theorem cutoffRiccati_norm_sub_le {Q R gamma rho nu U u : ℝ}
    (hQ : 0 ≤ Q) (hu : |u| ≤ U) (z w : ℂ) :
    ‖cutoffRiccati Q R gamma rho nu u z - cutoffRiccati Q R gamma rho nu u w‖ ≤
      cutoffRiccatiLipschitz Q R gamma rho nu U * ‖z - w‖ := by
  have hU : 0 ≤ U := (abs_nonneg u).trans hu
  have hC : 0 ≤ bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * (2 * Q) := by
    unfold bandLinearBound
    positivity
  calc
    _ ≤ (bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * (2 * Q)) *
        ‖squareClamp Q z - squareClamp Q w‖ :=
      riccati_band_lipschitz hu (squareClamp_norm_le hQ z) (squareClamp_norm_le hQ w)
    _ ≤ (bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * (2 * Q)) *
        (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left (squareClamp_norm_sub_le Q z w) hC
    _ = _ := by unfold cutoffRiccatiLipschitz; ring

theorem cutoffRiccati_lipschitz {Q R gamma rho nu U u : ℝ}
    (hQ : 0 ≤ Q) (hu : |u| ≤ U) :
    LipschitzWith (Real.toNNReal (cutoffRiccatiLipschitz Q R gamma rho nu U))
      (cutoffRiccati Q R gamma rho nu u) := by
  apply LipschitzWith.of_dist_le'
  intro z w
  simpa only [dist_eq_norm] using cutoffRiccati_norm_sub_le hQ hu z w

/-- The cutoff force is globally bounded by the actual finite-band
coefficient bound evaluated at the image radius `2*Q`. -/
theorem cutoffRiccati_norm_le {Q R gamma rho nu U u : ℝ}
    (hQ : 0 ≤ Q) (hu : |u| ≤ U) (z : ℂ) :
    ‖cutoffRiccati Q R gamma rho nu u z‖ ≤
      bandConstantBound R U + bandLinearBound R gamma rho nu U * (2 * Q) +
        (gamma * nu) ^ 2 / 2 * (2 * Q) ^ 2 :=
  riccati_band_norm_le hu (by positivity) (squareClamp_norm_le hQ z)

end RoughHeston

#print axioms RoughHeston.squareClamp_norm_sub_le
#print axioms RoughHeston.cutoffRiccati_norm_sub_le
#print axioms RoughHeston.cutoffRiccati_eq_of_norm_le
