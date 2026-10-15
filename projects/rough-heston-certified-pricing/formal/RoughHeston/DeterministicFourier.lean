module

public import RoughHeston.GlobalRiccati
public import RoughHeston.TransformBound
public import RoughHeston.FourierBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The concrete deterministic Fourier integral

The actual Riccati equation supplies its own finite-band norm bounds and
global real-part barrier. Certified uniform approximation then supplies
frequency continuity. Together these prove absolute integrability of the
genuine call-weighted transform and an explicit numerical cutoff error.
No stochastic transform identity or financial inversion formula is used.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Topology

namespace RoughHeston

/-- The exact deterministic transform for the concrete parameters. -/
def concreteRiccatiTransform (T : ℝ) (h : ℝ → ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp (exactRiccatiExponent (-2) 1 (-1 / 2) 1 1 1 u T (h u))

/-- The global frequency-independent transform bound derived from `Re h < 1`. -/
def concreteTransformBound (alpha T : ℝ) : ℝ :=
  Real.exp (T + T ^ (1 - alpha) / Real.Gamma (2 - alpha))

theorem concreteTransformBound_pos (alpha T : ℝ) : 0 < concreteTransformBound alpha T :=
  Real.exp_pos _

theorem norm_concreteRiccatiTransform_le (alpha T : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 ≤ T)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u))
    (u : ℝ) : ‖concreteRiccatiTransform T h u‖ ≤ concreteTransformBound alpha T := by
  have hb := (hsol u).norm_exp_exponent_le_of_re_le
    (theta := 1) (V0 := 1) (B := 1) ha ha1 hT (by norm_num) (by norm_num)
    (fun r hr => ((hsol u).concrete_re_lt_one ha ha1 hT r hr).le)
  simpa only [concreteRiccatiTransform, concreteTransformBound, one_mul, mul_one] using hb

private theorem concrete_band_radius_nonneg {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ bandConstantBound (-2) U + 1 := by
  unfold bandConstantBound
  positivity

/-- A common state bound on every finite band follows from the equation. -/
theorem concrete_riccati_band_bound (alpha T U : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 ≤ T)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ bandConstantBound (-2) U + 1 := by
  intro u hu t ht
  exact ((hsol u).concrete_norm_lt_band ha ha1 hT
    (by simpa only [abs_of_nonneg hu.1] using hu.2) t ht).le

/-- Band continuity is a consequence of the equation and its invariant
region, with no regularity hypothesis in the frequency variable. -/
theorem continuousOn_concreteRiccatiTransform_band (alpha T U : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 ≤ U)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    ContinuousOn (concreteRiccatiTransform T h) (Icc 0 U) :=
  continuousOn_exactRiccatiTransform_band alpha T (-2) 1 (-1 / 2) 1 1 1 U
    (bandConstantBound (-2) U + 1) h ha ha1 hT hU (concrete_band_radius_nonneg hU)
    (fun u _ => hsol u) (concrete_riccati_band_bound alpha T U h ha ha1 hT.le hsol)

theorem continuousOn_concreteRiccatiTransform_Ioi (alpha T : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    ContinuousOn (concreteRiccatiTransform T h) (Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro u hu
  change 0 < u at hu
  exact (continuousOn_concreteRiccatiTransform_band alpha T (u + 1) h
    ha ha1 hT (by linarith) hsol).continuousAt (Icc_mem_nhds hu (by linarith))

theorem aestronglyMeasurable_concreteRiccatiTransform_Ioi
    (alpha T U : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 ≤ U)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    AEStronglyMeasurable (concreteRiccatiTransform T h) (volume.restrict (Ioi U)) :=
  ((continuousOn_concreteRiccatiTransform_Ioi alpha T h ha ha1 hT hsol).mono
    (fun _ hu => lt_of_le_of_lt hU hu)).aestronglyMeasurable measurableSet_Ioi

theorem concrete_call_fourier_intervalIntegrable
    (alpha T U : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 ≤ U)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    IntervalIntegrable (fun u => callPayoffTransform u * concreteRiccatiTransform T h u)
      volume 0 U := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le hU, Pi.mul_def] using
    continuous_callPayoffTransform.continuousOn.mul
      (continuousOn_concreteRiccatiTransform_band alpha T U h ha ha1 hT hU hsol)

/-- The tail is absolutely integrable and has the explicit `B/U` bound. -/
theorem concrete_call_fourier_tail_bound (alpha T U : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 < U)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    IntegrableOn (fun u => callPayoffTransform u * concreteRiccatiTransform T h u) (Ioi U) ∧
      ‖∫ u in Ioi U, callPayoffTransform u * concreteRiccatiTransform T h u‖ ≤
        concreteTransformBound alpha T / U :=
  call_fourier_tail_bound hU (concreteRiccatiTransform T h)
    (aestronglyMeasurable_concreteRiccatiTransform_Ioi alpha T U h ha ha1 hT hU.le hsol)
    (fun u _ => norm_concreteRiccatiTransform_le alpha T h ha ha1 hT.le hsol u)

/-- Absolute integrability on the full positive half-line follows without
an integrability, measurability, or state-bound premise. -/
theorem concrete_call_fourier_integrable (alpha T : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    IntegrableOn (fun u => callPayoffTransform u * concreteRiccatiTransform T h u) (Ioi 0) := by
  have hband := concrete_call_fourier_intervalIntegrable alpha T 1 h ha ha1 hT (by norm_num) hsol
  have htail := (concrete_call_fourier_tail_bound alpha T 1 h ha ha1 hT (by norm_num) hsol).1
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).1
    hband).union htail

/-- The actual half-line Fourier integral is approximated by the actual
Adams transform on a finite band, with separate time-discretization and
frequency-tail terms. The certified state radius is `A_U + 1`, and the
numerical continuation margin is one. -/
theorem concrete_call_cutoff_error (alpha T U : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hU : 0 < U)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ‖(∫ u in Ioi 0, callPayoffTransform u * concreteRiccatiTransform T h u) -
        ∫ u in 0..U, callPayoffTransform u *
          Complex.exp ((roughExponent alpha dt (-2) 1 (-1 / 2) 1 1 1 N).eval (u : ℂ))‖ ≤
        U / 2 * finiteBandTransformConstant alpha T (-2) 1 (-1 / 2) 1 1 1 U
          (bandConstantBound (-2) U + 2) * dt ^ alpha + concreteTransformBound alpha T / U := by
  obtain ⟨M0, hM0, herr⟩ := riccati_dyadic_band_transform_error
    alpha T (-2) 1 (-1 / 2) 1 1 1 U (bandConstantBound (-2) U + 1) 1 h
    ha ha1 hT hU.le (concrete_band_radius_nonneg hU.le) (by norm_num)
    (fun u _ => hsol u) (concrete_riccati_band_bound alpha T U h ha ha1 hT.le hsol)
  have hQ : bandConstantBound (-2) U + 1 + 1 = bandConstantBound (-2) U + 2 := by ring
  simp only [hQ] at herr
  have hie := concrete_call_fourier_intervalIntegrable alpha T U h ha ha1 hT hU.le hsol
  have hm := aestronglyMeasurable_concreteRiccatiTransform_Ioi alpha T U h ha ha1 hT hU.le hsol
  refine ⟨M0, hM0, fun ell => ?_⟩
  dsimp only
  have hin : IntervalIntegrable (fun u => callPayoffTransform u *
      Complex.exp ((roughExponent alpha (T / (2 ^ ell * M0 : ℕ))
        (-2) 1 (-1 / 2) 1 1 1 (2 ^ ell * M0)).eval (u : ℂ))) volume 0 U :=
    (continuous_callPayoffTransform.mul
      (continuous_roughTransform_eval _ _ _ _ _ _ _ _ _)).intervalIntegrable _ _
  have hcut := call_cutoff_error hU (concreteRiccatiTransform T h)
    (fun u => Complex.exp ((roughExponent alpha (T / (2 ^ ell * M0 : ℕ))
      (-2) 1 (-1 / 2) 1 1 1 (2 ^ ell * M0)).eval (u : ℂ))) hie hin hm
    (fun u _ => norm_concreteRiccatiTransform_le alpha T h ha ha1 hT.le hsol u)
    (fun u hu => by
      simpa only [concreteRiccatiTransform, norm_sub_rev] using (herr ell u hu).2)
  simpa only [mul_assoc] using hcut.2

end RoughHeston

#print axioms RoughHeston.norm_concreteRiccatiTransform_le
#print axioms RoughHeston.continuousOn_concreteRiccatiTransform_Ioi
#print axioms RoughHeston.concrete_call_fourier_integrable
#print axioms RoughHeston.concrete_call_cutoff_error
