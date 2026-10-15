module

public import RoughHeston.DeterministicFourier
public import RoughHeston.CoarseLevels
public import RoughHeston.ExactQuadrature
public import RoughHeston.Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Global deterministic obstruction with derived convergence rates

The comparison exponential comes from a constructed global solution of
the actual concrete Riccati equation. Both source rates are derived for
every original dyadic level, and the domination exponent is `alpha`.
This does not identify the exponential with a stochastic model transform.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RoughHeston

/-- The source's pointwise rate conclusion for the specified actual
recurrence. This is a conclusion proved below, not a solver assumption. -/
def ConcreteSourceRates (alpha T : ℝ) (h : ℝ → ℝ → ℂ) (M0 : ℕ) (u : ℝ) : Prop :=
  ∃ Cn Ct Cg Cf : ℝ, 0 < Cn ∧ 0 < Ct ∧ 0 ≤ Cg ∧ 0 ≤ Cf ∧ ∀ ell : ℕ,
    let N := 2 ^ ell * M0
    let dt := T / (N : ℝ)
    (∀ n, 0 < n → n ≤ N →
      ‖roughState alpha dt (-2) 1 (-1 / 2) 1 u n - h u ((n : ℝ) * dt)‖ ≤
        Cn * ((n : ℝ) * dt) ^ (alpha - 1) * dt ^ alpha) ∧
    ‖exactRiccatiExponent (-2) 1 (-1 / 2) 1 1 1 u T (h u) -
      ∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
        riccatiExponentIntegrand (-2) 1 (-1 / 2) 1 1 1 u (h u ((j.val : ℝ) * dt))‖ ≤
      Ct * dt ^ alpha ∧
    ‖(roughExponent alpha dt (-2) 1 (-1 / 2) 1 1 1 N).eval (u : ℂ) -
      exactRiccatiExponent (-2) 1 (-1 / 2) 1 1 1 u T (h u)‖ ≤ Cg * dt ^ alpha ∧
    ‖Complex.exp ((roughExponent alpha dt (-2) 1 (-1 / 2) 1 1 1 N).eval (u : ℂ)) -
      concreteRiccatiTransform T h u‖ ≤ Cf * dt ^ alpha

theorem concrete_source_rates {alpha T : ℝ} (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hsol : ∀ u, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u))
    (M0 : ℕ) (hM0 : 0 < M0) (u : ℝ) : ConcreteSourceRates alpha T h M0 u := by
  let Q := bandConstantBound (-2) |u| + 1
  have hQ : 0 ≤ Q := by
    have hb := riccatiConstant_norm_le (R := -2) (le_refl |u|)
    have hA := (norm_nonneg _).trans hb
    dsimp [Q]
    linarith
  have hb : ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q := fun t ht =>
    ((hsol u).concrete_norm_lt_band ha ha1 hT.le (le_refl |u|) t ht).le
  obtain ⟨Cn, hCn, hn⟩ := riccati_original_dyadic_time_weighted_error
    alpha T (-2) 1 (-1 / 2) 1 u Q (h u) M0 ha ha1 hT hQ hM0 (hsol u) hb
  obtain ⟨Cg, Cf, hCg, hCf, hg⟩ := riccati_original_dyadic_transform_error
    alpha T (-2) 1 (-1 / 2) 1 1 1 u Q (h u) M0 ha ha1 hT hQ hM0 (hsol u) hb
  obtain ⟨Ct, hCt, ht⟩ := concrete_original_dyadic_exact_quadrature_error
    alpha T h ha ha1 hT hsol M0 hM0 u
  refine ⟨Cn + 1, Ct, Cg, Cf, by linarith, hCt, hCg, hCf, fun ell => ?_⟩
  dsimp only
  refine ⟨?_, ht ell, hg ell⟩
  intro n hn0 hnN
  have hdt : 0 ≤ T / ((2 ^ ell * M0 : ℕ) : ℝ) :=
    div_nonneg hT.le (Nat.cast_nonneg _)
  have hw : 0 ≤ (((n : ℝ) * (T / ((2 ^ ell * M0 : ℕ) : ℝ))) ^ (alpha - 1)) *
      (T / ((2 ^ ell * M0 : ℕ) : ℝ)) ^ alpha :=
    mul_nonneg (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hdt) _)
      (Real.rpow_nonneg hdt _)
  calc
    _ ≤ Cn * (((n : ℝ) * (T / ((2 ^ ell * M0 : ℕ) : ℝ))) ^ (alpha - 1)) *
        (T / ((2 ^ ell * M0 : ℕ) : ℝ)) ^ alpha := hn ell n hn0 hnN
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (show Cn ≤ Cn + 1 by linarith) hw

/-- A constructed global exact Riccati family has both derived source
rates, yet its actual Adams all-level domination function at `pG=alpha`
has infinite integral for every positive original base mesh. -/
theorem exists_concrete_deterministic_obstruction {alpha T : ℝ}
    (ha : (1 / 2 : ℝ) < alpha) (ha1 : alpha < 1) (hT : 0 < T) :
    ∃ h : ℝ → ℝ → ℂ,
      (∀ u, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) ∧
      (∀ M0 : ℕ, 0 < M0 → ∀ u, ConcreteSourceRates alpha T h M0 u) ∧
      (∀ u, ‖concreteRiccatiTransform T h u‖ ≤ concreteTransformBound alpha T) ∧
      (∀ M0 : ℕ, 0 < M0 →
        (∫⁻ u in Ioi (0 : ℝ), domination alpha T 1 (-1 / 2) 1 1 1 alpha M0
          (concreteRiccatiTransform T h) u) = ∞) := by
  have ha0 : 0 < alpha := by linarith
  obtain ⟨h, hsol, _, _⟩ := exists_concrete_global_riccati_family ha0 ha1 hT.le
  have hb : ∀ u, ‖concreteRiccatiTransform T h u‖ ≤ concreteTransformBound alpha T := by
    intro u
    have he := (hsol u).norm_exp_exponent_le_of_re_le
      (theta := 1) (V0 := 1) (B := 1) ha0 ha1 hT.le
      (by norm_num) (by norm_num)
      (fun t ht => ((hsol u).concrete_re_lt_one ha0 ha1 hT.le t ht).le)
    simpa only [concreteRiccatiTransform, concreteTransformBound, one_mul] using he
  refine ⟨h, hsol, fun M0 hM0 u => concrete_source_rates h ha0 ha1 hT hsol M0 hM0 u, hb, ?_⟩
  intro M0 hM0
  exact domination_lintegral_eq_top alpha T 1 (-1 / 2) 1 1 1 alpha M0
    (concreteRiccatiTransform T h) (concreteTransformBound alpha T)
    ha0 hT (by norm_num) (by norm_num) (by norm_num) hM0 hb

/-- The same construction supplies a genuine, absolutely integrable
deterministic call Fourier integral and a cutoff-and-time-error repair at
every fixed positive maturity and cutoff. Quadrature and stochastic
identification are not conclusions of this theorem. -/
theorem exists_concrete_deterministic_cutoff {alpha T : ℝ}
    (ha : (1 / 2 : ℝ) < alpha) (ha1 : alpha < 1) (hT : 0 < T) :
    ∃ h : ℝ → ℝ → ℂ,
      (∀ u, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u)) ∧
      IntegrableOn (fun u => callPayoffTransform u * concreteRiccatiTransform T h u) (Ioi 0) ∧
      ∀ U : ℝ, 0 < U → ∃ M0 : ℕ, 0 < M0 ∧ ∀ ell : ℕ,
        let N := 2 ^ ell * M0
        let dt := T / (N : ℝ)
        ‖(∫ u in Ioi 0, callPayoffTransform u * concreteRiccatiTransform T h u) -
          ∫ u in 0..U, callPayoffTransform u *
            Complex.exp ((roughExponent alpha dt (-2) 1 (-1 / 2) 1 1 1 N).eval (u : ℂ))‖ ≤
          U / 2 * finiteBandTransformConstant alpha T (-2) 1 (-1 / 2) 1 1 1 U
            (bandConstantBound (-2) U + 2) * dt ^ alpha + concreteTransformBound alpha T / U := by
  have ha0 : 0 < alpha := by linarith
  obtain ⟨h, hsol, _, _⟩ := exists_concrete_global_riccati_family ha0 ha1 hT.le
  exact ⟨h, hsol, concrete_call_fourier_integrable alpha T h ha0 ha1 hT hsol,
    fun U hU => concrete_call_cutoff_error alpha T U h ha0 ha1 hT hU hsol⟩

end RoughHeston

#print axioms RoughHeston.concrete_source_rates
#print axioms RoughHeston.exists_concrete_deterministic_obstruction
#print axioms RoughHeston.exists_concrete_deterministic_cutoff
