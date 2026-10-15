module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A deterministic obstruction to global Fourier error domination

The call payoff factor is the rational formula for strike `K = 1` on the
damping line `R = -2`. This file does not identify a comparison function with a
rough-Heston transform, prove moment admissibility, or prove Fourier inversion.
Its conclusion is a deterministic nonintegrability theorem for every bounded
comparison function.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Polynomial
open scoped Topology

namespace RoughHeston

/-- The denominator `z² + iz` on the line `z = u - 2i`. -/
def callDenominator (u : ℝ) : ℂ :=
  ((u : ℂ) - 2 * Complex.I) ^ 2 + Complex.I * ((u : ℂ) - 2 * Complex.I)

/-- Vanilla-call payoff transform formula at strike one and damping `R = -2`.
The identification with the payoff's defining Fourier integral is a separate
financial-bridge obligation. -/
def callPayoffTransform (u : ℝ) : ℂ := -1 / callDenominator u

/-- Absolute call-weighted error of an exponential approximation. -/
def callWeightedError (G Φ : ℝ → ℂ) (u : ℝ) : ℝ :=
  ‖callPayoffTransform u‖ * ‖Φ u - Complex.exp (G u)‖

theorem callWeightedError_nonneg (G Φ : ℝ → ℂ) (u : ℝ) :
    0 ≤ callWeightedError G Φ u := mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem callDenominator_ne_zero (u : ℝ) : callDenominator u ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [callDenominator, pow_two, Complex.mul_re, Complex.mul_im] at hre him
  nlinarith

/-- An explicit quadratic upper bound, sufficient for tail comparison. -/
theorem norm_callDenominator_le (u : ℝ) (hu : 1 ≤ u) :
    ‖callDenominator u‖ ≤ 12 * u ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have hz : ‖(u : ℂ) - 2 * Complex.I‖ ≤ u + 2 := by
    calc
      ‖(u : ℂ) - 2 * Complex.I‖ ≤ ‖(u : ℂ)‖ + ‖(2 : ℂ) * Complex.I‖ :=
        norm_sub_le _ _
      _ = u + 2 := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  calc
    ‖callDenominator u‖ ≤ ‖(u : ℂ) - 2 * Complex.I‖ ^ 2 +
        ‖(u : ℂ) - 2 * Complex.I‖ := by
      simpa only [callDenominator, pow_two, norm_mul, Complex.norm_I, one_mul]
        using norm_add_le (((u : ℂ) - 2 * Complex.I) ^ (2 : ℕ))
          (Complex.I * ((u : ℂ) - 2 * Complex.I))
    _ ≤ (u + 2) ^ 2 + (u + 2) := by
      exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (by linarith)).2 hz) hz
    _ ≤ 12 * u ^ 2 := by nlinarith [sq_nonneg (u - 1)]

/-- A function bounded below by one on a tail cannot be integrable on the
positive half-line. No measurability assumption on the function is needed. -/
theorem not_integrableOn_of_eventually_one_le (f : ℝ → ℝ)
    (hf : ∀ᶠ u in atTop, 1 ≤ f u) : ¬ IntegrableOn f (Ioi 0) := by
  intro hint
  obtain ⟨a, ha⟩ := eventually_atTop.1 hf
  have htail : IntegrableOn f (Ioi (max a 0)) :=
    hint.mono_set (fun u hu => lt_of_le_of_lt (le_max_right a 0) hu)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (max a 0)) := by
    apply htail.mono' aestronglyMeasurable_const
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    simpa using ha u (le_trans (le_max_left a 0) (le_of_lt hu))
  simp [integrableOn_const_iff, Real.volume_Ioi] at hone

/-- A positive-leading polynomial of degree above two eventually dominates
any fixed multiple of `u²` plus any fixed constant. -/
theorem polynomial_eventually_ge_quadratic (p : ℝ[X])
    (hdegree : 2 < p.natDegree) (hlead : 0 < p.leadingCoeff) (A B : ℝ) :
    ∀ᶠ u in atTop, A * u ^ 2 + B ≤ p.eval u := by
  let q : ℝ[X] := C A * X ^ 2 + C B
  have hq : q.degree ≤ 2 := by
    apply degree_add_le_of_degree_le
    · exact degree_C_mul_X_pow_le 2 A
    · exact (degree_C_le).trans (by norm_num)
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hlead)
  have hpdegree : (2 : WithBot ℕ) < p.degree := by
    rw [degree_eq_natDegree hp0]
    exact_mod_cast hdegree
  have hpq : q.degree < p.degree := lt_of_le_of_lt hq hpdegree
  have hpos : 0 < (p - q).degree := by
    rw [degree_sub_eq_left_of_degree_lt hpq]
    exact lt_trans (by norm_num : (0 : WithBot ℕ) < 2) hpdegree
  have hlead' : 0 ≤ (p - q).leadingCoeff := by
    rw [leadingCoeff_sub_of_degree_lt hpq]
    exact hlead.le
  have h := (p - q).tendsto_atTop_of_leadingCoeff_nonneg hpos hlead'
  filter_upwards [h.eventually (eventually_ge_atTop 0)] with u hu
  simp only [eval_sub, q, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hu
  linarith

/-- Under an eventual quadratic lower bound on the real exponent, the weighted
error exceeds one eventually, uniformly against any bounded comparison. -/
theorem eventually_one_le_callWeightedError (G Φ : ℝ → ℂ) (B : ℝ)
    (hbounded : ∀ u, ‖Φ u‖ ≤ B)
    (hgrowth : ∀ᶠ u in atTop, 12 * u ^ 2 + B ≤ (G u).re) :
    ∀ᶠ u in atTop, 1 ≤ callWeightedError G Φ u := by
  filter_upwards [hgrowth, eventually_ge_atTop (1 : ℝ)] with u hg hu
  have hd : 0 < ‖callDenominator u‖ := norm_pos_iff.mpr (callDenominator_ne_zero u)
  have herror : ‖callDenominator u‖ ≤ ‖Φ u - Complex.exp (G u)‖ := by
    have he := Real.add_one_le_exp (G u).re
    have hr := norm_sub_norm_le (Complex.exp (G u)) (Φ u)
    rw [Complex.norm_exp, norm_sub_rev] at hr
    have hb := hbounded u
    have hden := norm_callDenominator_le u hu
    linarith
  unfold callWeightedError callPayoffTransform
  rw [norm_div, norm_neg, norm_one]
  calc
    1 ≤ ‖Φ u - Complex.exp (G u)‖ / ‖callDenominator u‖ :=
      (le_div_iff₀ hd).2 (by simpa using herror)
    _ = 1 / ‖callDenominator u‖ * ‖Φ u - Complex.exp (G u)‖ := by ring

/-- The real-part polynomial version of the deterministic tail theorem. -/
theorem not_integrableOn_callWeightedError_of_real_polynomial
    (p : ℝ[X]) (G Φ : ℝ → ℂ) (B : ℝ)
    (hreal : ∀ u, (G u).re = p.eval u)
    (hdegree : 2 < p.natDegree) (hlead : 0 < p.leadingCoeff)
    (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    ¬ IntegrableOn (callWeightedError G Φ) (Ioi 0) := by
  apply not_integrableOn_of_eventually_one_le
  apply eventually_one_le_callWeightedError G Φ B hbounded
  simpa only [hreal] using polynomial_eventually_ge_quadratic p hdegree hlead 12 B

/-- Coefficientwise real part; unlike a polynomial ring homomorphism, this
operation is only additive. -/
def realPartPolynomial (p : ℂ[X]) : ℝ[X] :=
  .ofFinsupp (.ofCoeff (p.coeff.mapRange Complex.re (by simp)))

@[simp] theorem realPartPolynomial_coeff (p : ℂ[X]) (n : ℕ) :
    (realPartPolynomial p).coeff n = (p.coeff n).re := rfl

theorem realPartPolynomial_natDegree_le (p : ℂ[X]) :
    (realPartPolynomial p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn]

theorem realPartPolynomial_eval (p : ℂ[X]) (u : ℝ) :
    (realPartPolynomial p).eval u = (p.eval (u : ℂ)).re := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le (realPartPolynomial_natDegree_le p)),
    eval_eq_sum_range]
  simp [Complex.re_sum, Complex.mul_re, ← Complex.ofReal_pow]

theorem realPartPolynomial_natDegree (p : ℂ[X]) (hlead : 0 < p.leadingCoeff.re) :
    (realPartPolynomial p).natDegree = p.natDegree := by
  apply le_antisymm (realPartPolynomial_natDegree_le p)
  apply le_natDegree_of_ne_zero
  simpa only [realPartPolynomial_coeff, coeff_natDegree] using ne_of_gt hlead

theorem realPartPolynomial_leadingCoeff (p : ℂ[X]) (hlead : 0 < p.leadingCoeff.re) :
    (realPartPolynomial p).leadingCoeff = p.leadingCoeff.re := by
  rw [← coeff_natDegree, realPartPolynomial_natDegree p hlead,
    realPartPolynomial_coeff, coeff_natDegree]

/-- Deterministic complex-polynomial tail obstruction. A positive real leading
coefficient of degree greater than two forces nonintegrability against every
bounded comparison function, with the genuine rational vanilla-call factor at
`K = 1`, `R = -2`. This is not an option-pricing theorem. -/
theorem not_integrableOn_callWeightedError_of_polynomial
    (p : ℂ[X]) (Φ : ℝ → ℂ) (B : ℝ)
    (hdegree : 2 < p.natDegree) (hlead : 0 < p.leadingCoeff.re)
    (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    ¬ IntegrableOn (callWeightedError (fun u => p.eval (u : ℂ)) Φ) (Ioi 0) := by
  apply not_integrableOn_callWeightedError_of_real_polynomial
    (realPartPolynomial p) (fun u => p.eval (u : ℂ)) Φ B
  · intro u
    exact (realPartPolynomial_eval p u).symm
  · simpa only [realPartPolynomial_natDegree p hlead] using hdegree
  · simpa only [realPartPolynomial_leadingCoeff p hlead] using hlead
  · exact hbounded

end RoughHeston
