module

public import RoughHeston.FixedHorizon
public import RoughHeston.MeshConditions
public import RoughHeston.TransformError
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A uniform finite-band family of validated Adams meshes

This is a deterministic convergence theorem for bounded exact solutions of
the specified fractional Riccati equation. It constructs one base mesh for
the whole band and all dyadic refinements. Stochastic identification is not
part of the statement.
-/

@[expose] public section
noncomputable section
open Set

namespace RoughHeston

def finiteBandForceBound (R gamma rho nu U Q : ℝ) : ℝ :=
  bandConstantBound R U + bandLinearBound R gamma rho nu U * Q + (gamma * nu) ^ 2 / 2 * Q ^ 2

def finiteBandLipschitz (R gamma rho nu U Q : ℝ) : ℝ :=
  bandLinearBound R gamma rho nu U + (gamma * nu) ^ 2 * Q

def finiteBandDefectConstant (alpha T R gamma rho nu U Q : ℝ) : ℝ :=
  finiteBandLipschitz R gamma rho nu U Q *
    (2 * finiteBandForceBound R gamma rho nu U Q / Real.Gamma (alpha + 1)) *
    (T ^ alpha / Real.Gamma (alpha + 1))

def finiteBandNodalConstant (alpha T R gamma rho nu U Q : ℝ) : ℝ :=
  4 * finiteBandDefectConstant alpha T R gamma rho nu U Q *
    Real.exp (continuationRate alpha (finiteBandLipschitz R gamma rho nu U Q) * T)

def finiteBandExponentConstant (alpha T R gamma rho nu theta V0 U Q : ℝ) : ℝ :=
  T * riccatiExponentLipschitz theta gamma V0 (finiteBandLipschitz R gamma rho nu U Q) *
    (finiteBandNodalConstant alpha T R gamma rho nu U Q +
      2 * finiteBandForceBound R gamma rho nu U Q / Real.Gamma (alpha + 1))

def finiteBandTransformConstant (alpha T R gamma rho nu theta V0 U Q : ℝ) : ℝ :=
  Real.exp (T * (|theta * gamma| * Q + |V0| * finiteBandForceBound R gamma rho nu U Q) +
    finiteBandExponentConstant alpha T R gamma rho nu theta V0 U Q * T ^ alpha) *
      finiteBandExponentConstant alpha T R gamma rho nu theta V0 U Q

theorem finiteBandForceBound_nonneg (R gamma rho nu : ℝ) {U Q : ℝ}
    (hU : 0 ≤ U) (hQ : 0 ≤ Q) : 0 ≤ finiteBandForceBound R gamma rho nu U Q := by
  unfold finiteBandForceBound bandConstantBound bandLinearBound
  positivity

theorem finiteBandLipschitz_nonneg (R gamma rho nu : ℝ) {U Q : ℝ}
    (hU : 0 ≤ U) (hQ : 0 ≤ Q) : 0 ≤ finiteBandLipschitz R gamma rho nu U Q := by
  unfold finiteBandLipschitz bandLinearBound
  positivity

/-- A single base mesh works uniformly over the finite frequency band and
every refinement. The constant is explicit and independent of frequency,
level and node. The hypothesis is an actual bounded solution family, not a
numerical solver accuracy assumption. -/
theorem riccati_dyadic_band_error (alpha T R gamma rho nu U Q0 eta : ℝ)
    (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0) (heta : 0 < eta)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha R gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ∀ u ∈ Icc 0 U, ∀ n ≤ N,
        ‖roughState alpha dt R gamma rho nu u n - h u ((n : ℝ) * dt)‖ ≤
          finiteBandNodalConstant alpha T R gamma rho nu U (Q0 + eta) * dt ^ alpha ∧
        ‖roughState alpha dt R gamma rho nu u n‖ ≤ Q0 + eta := by
  let Q := Q0 + eta
  let M := finiteBandForceBound R gamma rho nu U Q
  let L := finiteBandLipschitz R gamma rho nu U Q
  let D := finiteBandDefectConstant alpha T R gamma rho nu U Q
  have hQ : 0 ≤ Q := add_nonneg hQ0 heta.le
  have hM : 0 ≤ M := finiteBandForceBound_nonneg R gamma rho nu hU hQ
  have hL : 0 ≤ L := finiteBandLipschitz_nonneg R gamma rho nu hU hQ
  obtain ⟨hr, hrL, M0, hM0, hmesh⟩ :=
    explicit_continuation_mesh_exists (L := L) (D := D) ha hT heta
  refine ⟨M0, hM0, ?_⟩
  intro ell
  let N := 2 ^ ell * M0
  let dt := T / (N : ℝ)
  have hN : 0 < N := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hdt : 0 < dt := (hmesh ell).1
  have hNd : (N : ℝ) * dt = T := by dsimp [dt]; field_simp
  have hdef : riccatiDefectBound alpha dt M L N = D * dt ^ alpha :=
    riccatiDefectBound_eq_maturity hdt.le hNd
  dsimp only
  intro u hu n hn
  have huabs : |u| ≤ U := by simpa only [abs_of_nonneg hu.1] using hu.2
  have hsol' : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) (h u) := by
    rw [hNd]
    exact hsol u hu
  have hmargin : 4 * riccatiDefectBound alpha dt M L N *
      Real.exp (continuationRate alpha L * ((N : ℝ) * dt)) ≤ eta := by
    rw [hdef, hNd]
    nlinarith [(hmesh ell).2.2.2]
  have hbnd : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h u t‖ ≤ Q0 := by
    rw [hNd]
    exact hbound u hu
  have herr := riccati_fixed_horizon_nodal_error alpha dt R gamma rho nu u
    (continuationRate alpha L) N (h u) hsol' ha ha1 hdt hr heta.le hM hL hrL
    (hmesh ell).2.1 (hmesh ell).2.2.1 hmargin
    (fun z hz => riccati_band_norm_le huabs hQ hz)
    (fun z w hz hw => riccati_band_lipschitz huabs hz hw) hbnd n hn
  refine ⟨?_, herr.2⟩
  calc
    _ ≤ 4 * riccatiDefectBound alpha dt M L N *
        Real.exp (continuationRate alpha L * ((N : ℝ) * dt)) := herr.1
    _ = finiteBandNodalConstant alpha T R gamma rho nu U (Q0 + eta) * dt ^ alpha := by
      rw [hdef, hNd]
      unfold finiteBandNodalConstant
      dsimp [D, L, Q]
      ring

/-- The source's complete trapezoidal exponent and its exponential converge
uniformly on the band at derived order `alpha`, on one validated dyadic
family. These are deterministic exponentials, without a stochastic affine
transform or option-pricing identification. -/
theorem riccati_dyadic_band_transform_error (alpha T R gamma rho nu theta V0 U Q0 eta : ℝ)
    (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hU : 0 ≤ U) (hQ0 : 0 ≤ Q0) (heta : 0 < eta)
    (hsol : ∀ u ∈ Icc 0 U, IsRiccatiSolution alpha R gamma rho nu u T (h u))
    (hbound : ∀ u ∈ Icc 0 U, ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q0) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ∀ u ∈ Icc 0 U,
        ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
            exactRiccatiExponent R gamma rho nu theta V0 u T (h u)‖ ≤
          finiteBandExponentConstant alpha T R gamma rho nu theta V0 U (Q0 + eta) * dt ^ alpha ∧
        ‖Complex.exp ((roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ)) -
            Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T (h u))‖ ≤
          finiteBandTransformConstant alpha T R gamma rho nu theta V0 U (Q0 + eta) * dt ^ alpha := by
  let Q := Q0 + eta
  let M := finiteBandForceBound R gamma rho nu U Q
  let L := finiteBandLipschitz R gamma rho nu U Q
  let Ch := finiteBandNodalConstant alpha T R gamma rho nu U Q
  let Cg := finiteBandExponentConstant alpha T R gamma rho nu theta V0 U Q
  have hQ : 0 ≤ Q := add_nonneg hQ0 heta.le
  have hM : 0 ≤ M := finiteBandForceBound_nonneg R gamma rho nu hU hQ
  have hL : 0 ≤ L := finiteBandLipschitz_nonneg R gamma rho nu hU hQ
  have hGamma : 0 < Real.Gamma (alpha + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hCh : 0 ≤ Ch := by
    change 0 ≤ 4 * (L * (2 * M / Real.Gamma (alpha + 1)) *
      (T ^ alpha / Real.Gamma (alpha + 1))) * Real.exp (continuationRate alpha L * T)
    positivity
  have hCg : 0 ≤ Cg := by
    change 0 ≤ T * riccatiExponentLipschitz theta gamma V0 L *
      (Ch + 2 * M / Real.Gamma (alpha + 1))
    exact mul_nonneg (mul_nonneg hT.le (riccatiExponentLipschitz_nonneg theta gamma V0 hL))
      (add_nonneg hCh (by positivity))
  obtain ⟨M0, hM0, hnodes⟩ := riccati_dyadic_band_error alpha T R gamma rho nu U Q0 eta h
    ha ha1 hT hU hQ0 heta hsol hbound
  refine ⟨M0, hM0, ?_⟩
  intro ell
  let N := 2 ^ ell * M0
  let dt := T / (N : ℝ)
  have hN : 0 < N := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hdt : 0 < dt := div_pos hT hNreal
  have hdtT : dt ≤ T := div_le_self hT.le (by exact_mod_cast hN)
  have hNd : (N : ℝ) * dt = T := by dsimp [dt]; field_simp
  dsimp only
  intro u hu
  have huabs : |u| ≤ U := by simpa only [abs_of_nonneg hu.1] using hu.2
  have hsol' : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) (h u) := by
    rw [hNd]
    exact hsol u hu
  have hpath : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h u t‖ ≤ Q := by
    rw [hNd]
    exact fun t ht => (hbound u hu t ht).trans (le_add_of_nonneg_right heta.le)
  have hforce : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖riccati R gamma rho nu u (h u t)‖ ≤ M :=
    fun t ht => riccati_band_norm_le huabs hQ (hpath t ht)
  have hg0 := hsol'.roughExponent_error (theta := theta) (V0 := V0)
    ha ha1 hdt hN hL hforce hpath
    (fun n hn => (hnodes ell u hu n hn).2)
    (fun z w hz hw => riccati_band_lipschitz huabs hz hw)
    (fun n hn => (hnodes ell u hu n hn).1)
  have hg : ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
      exactRiccatiExponent R gamma rho nu theta V0 u ((N : ℝ) * dt) (h u)‖ ≤ Cg * dt ^ alpha := by
    apply hg0.trans_eq
    rw [hNd]
    change T * riccatiExponentLipschitz theta gamma V0 L *
      (Ch * dt ^ alpha + (2 * M / Real.Gamma (alpha + 1)) * dt ^ alpha) = _
    dsimp [Cg, finiteBandExponentConstant, Ch, M, L]
    ring
  refine ⟨by simpa only [hNd] using hg, ?_⟩
  have htransform := roughTransform_error_of_exponent_error hdt.le hpath hforce hg
  have hpow : dt ^ alpha ≤ T ^ alpha := Real.rpow_le_rpow hdt.le hdtT ha.le
  have hD : 0 ≤ Cg * dt ^ alpha := mul_nonneg hCg (Real.rpow_nonneg hdt.le _)
  calc
    _ ≤ Real.exp (T * (|theta * gamma| * Q + |V0| * M) + Cg * dt ^ alpha) *
        (Cg * dt ^ alpha) := by simpa only [hNd] using htransform
    _ ≤ Real.exp (T * (|theta * gamma| * Q + |V0| * M) + Cg * T ^ alpha) *
        (Cg * dt ^ alpha) := by
      apply mul_le_mul_of_nonneg_right _ hD
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hCg)
    _ = finiteBandTransformConstant alpha T R gamma rho nu theta V0 U (Q0 + eta) * dt ^ alpha := by
      dsimp [finiteBandTransformConstant, Cg, M, Q]
      ring

end RoughHeston
