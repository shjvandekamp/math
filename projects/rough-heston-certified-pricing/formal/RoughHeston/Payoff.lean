module

public import RoughHeston.Tail
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The genuine vanilla-call payoff transform

For strike one, the payoff as a function of log-price is
`max (Real.exp x - 1) 0`. On the line `z = u - 2i`, its Fourier integral with
kernel `exp (-izx)` is absolutely integrable and equals the rational factor
used in `Tail.lean`.

This identifies the deterministic payoff factor. It does not establish a
rough-Heston model identity, its moment domain, or pricing inversion.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace RoughHeston

/-- Strike-one vanilla call as a function of log-price. -/
def vanillaCallLogPayoff (x : ℝ) : ℝ := max (Real.exp x - 1) 0

/-- The Fourier kernel's exponential coefficient on the damping line `R = -2`. -/
def callDecay (u : ℝ) : ℂ := -Complex.I * ((u : ℂ) - 2 * Complex.I)

/-- The Fourier integrand of the genuine call payoff at `K = 1`, `R = -2`. -/
def callFourierIntegrand (u x : ℝ) : ℂ :=
  Complex.exp (callDecay u * (x : ℂ)) * (vanillaCallLogPayoff x : ℂ)

theorem callDecay_re (u : ℝ) : (callDecay u).re = -2 := by
  simp [callDecay, Complex.mul_re, Complex.mul_im]

theorem callDecay_ne_zero (u : ℝ) : callDecay u ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [callDecay_re] at this

theorem callDecay_add_one_ne_zero (u : ℝ) : callDecay u + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [callDecay_re] at this

theorem callDecay_product (u : ℝ) :
    callDecay u * (callDecay u + 1) = -callDenominator u := by
  apply Complex.ext <;>
    simp [callDecay, callDenominator, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The call integrand vanishes on the nonpositive half-line; on the positive
half-line it is the difference of two decaying complex exponentials. -/
theorem callFourierIntegrand_eq_indicator (u : ℝ) :
    callFourierIntegrand u = (Ioi (0 : ℝ)).indicator
      (fun x : ℝ => Complex.exp ((callDecay u + 1) * (x : ℂ)) -
        Complex.exp (callDecay u * (x : ℂ))) := by
  funext x
  by_cases hx : 0 < x
  · have hpay : 0 ≤ Real.exp x - 1 :=
      sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx.le)
    rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    simp only [callFourierIntegrand, vanillaCallLogPayoff, max_eq_left hpay,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp, mul_sub, mul_one,
      ← Complex.exp_add]
    rw [show (callDecay u + 1) * (x : ℂ) = callDecay u * (x : ℂ) + x by ring]
  · have hpay : Real.exp x - 1 ≤ 0 :=
      sub_nonpos.mpr (Real.exp_le_one_iff.mpr (le_of_not_gt hx))
    rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    simp [callFourierIntegrand, vanillaCallLogPayoff, max_eq_right hpay]

/-- Absolute integrability of the actual damped vanilla-call integrand. -/
theorem integrable_callFourierIntegrand (u : ℝ) : Integrable (callFourierIntegrand u) := by
  rw [callFourierIntegrand_eq_indicator]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
  apply Integrable.sub
  · apply integrableOn_exp_mul_complex_Ioi
    simp [callDecay_re]
  · apply integrableOn_exp_mul_complex_Ioi
    simp [callDecay_re]

/-- The call factor used in the tail theorem is the actual Fourier integral,
not merely a rational surrogate. The integral is a complex Bochner integral. -/
theorem integral_callFourierIntegrand (u : ℝ) :
    (∫ x : ℝ, callFourierIntegrand u x) = callPayoffTransform u := by
  have hfirst : (callDecay u + 1).re < 0 := by simp [callDecay_re]
  have hsecond : (callDecay u).re < 0 := by simp [callDecay_re]
  rw [callFourierIntegrand_eq_indicator, integral_indicator measurableSet_Ioi,
    integral_sub (integrableOn_exp_mul_complex_Ioi hfirst 0)
      (integrableOn_exp_mul_complex_Ioi hsecond 0),
    integral_exp_mul_complex_Ioi hfirst 0, integral_exp_mul_complex_Ioi hsecond 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_sub_div (-1) (-1) (callDecay_add_one_ne_zero u) (callDecay_ne_zero u)]
  calc
    (-1 * callDecay u - (callDecay u + 1) * -1) /
        ((callDecay u + 1) * callDecay u) = 1 / (callDecay u * (callDecay u + 1)) := by
      congr 1 <;> ring
    _ = callPayoffTransform u := by
      rw [callDecay_product]
      simp [callPayoffTransform, div_eq_mul_inv]

/-- The explicit full-real-line Fourier identity in the source convention,
for `K = 1`, `R = -2`. -/
theorem vanillaCall_fourier_transform (u : ℝ) :
    (∫ x : ℝ, Complex.exp (-Complex.I * ((u : ℂ) - 2 * Complex.I) * (x : ℂ)) *
      ((max (Real.exp x - 1) 0 : ℝ) : ℂ)) = callPayoffTransform u :=
  integral_callFourierIntegrand u

end RoughHeston

#print axioms RoughHeston.integrable_callFourierIntegrand
#print axioms RoughHeston.vanillaCall_fourier_transform
