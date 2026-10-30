module

public import RoughHeston.Adams
public import RoughHeston.Weights
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The trapezoidal transform exponent

The quadrature is applied to `theta * gamma * h + V0 * F(h)`, including
both half-weight endpoints. This is the deterministic numerical exponent;
no stochastic transform identity is assumed here.
-/

@[expose] public section

noncomputable section
open Polynomial Finset

namespace RoughHeston

/-- Complex numerical states obtained by evaluating the exact frequency
polynomials. The following theorem exposes their Adams recurrence. -/
def roughState (alpha dt R gamma rho nu u : ℝ) (n : ℕ) : ℂ :=
  (adamsPolynomial (constantPoly R) (linearPoly R gamma rho nu) ((gamma * nu) ^ 2 / 2)
    (correctorWeight alpha dt) (predictorWeight alpha dt) n).eval (u : ℂ)

theorem roughState_zero (alpha dt R gamma rho nu u : ℝ) :
    roughState alpha dt R gamma rho nu u 0 = 0 := by
  simp [roughState, adamsPolynomial]

theorem roughState_succ (alpha dt R gamma rho nu u : ℝ) (n : ℕ) :
    roughState alpha dt R gamma rho nu u (n + 1) =
      (∑ j : Fin (n + 1), (correctorWeight alpha dt j.val (n + 1) : ℂ) *
        riccati R gamma rho nu u (roughState alpha dt R gamma rho nu u j.val)) +
      (correctorWeight alpha dt (n + 1) (n + 1) : ℂ) *
        riccati R gamma rho nu u
          (∑ j : Fin (n + 1), (predictorWeight alpha dt j.val (n + 1) : ℂ) *
            riccati R gamma rho nu u (roughState alpha dt R gamma rho nu u j.val)) := by
  simp only [roughState, adamsPolynomial, eval_add, eval_mul, eval_C,
    eval_finsetSum, forcePoly_eval]

def trapezoidWeight (dt : ℝ) (M j : ℕ) : ℝ :=
  if j = 0 ∨ j = M then dt / 2 else dt

def integrandPoly (q l : ℂ[X]) (c thetaGamma V0 : ℝ) (h : ℂ[X]) : ℂ[X] :=
  C (thetaGamma : ℂ) * h + C (V0 : ℂ) * forcePoly q l c h

def exponentPoly (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ)
    (thetaGamma V0 dt : ℝ) (M : ℕ) : ℂ[X] :=
  ∑ j : Fin (M + 1), C (trapezoidWeight dt M j.val : ℂ) *
    integrandPoly q l c thetaGamma V0 (adamsPolynomial q l c a b j.val)

theorem adams_degree_lt_force (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ)
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1) (n : ℕ) :
    (adamsPolynomial q l c a b n).natDegree < 2 * 4 ^ n := by
  cases n with
  | zero => simp [adamsPolynomial]
  | succ n =>
    have hp := (adams_hasTop q l c a b hq hl n).1
    have hpos : 0 < 4 ^ (n + 1) := by positivity
    omega

theorem integrand_node_hasTop (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ)
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1)
    (thetaGamma V0 : ℝ) (n : ℕ) :
    HasTop (integrandPoly q l c thetaGamma V0 (adamsPolynomial q l c a b n))
      (2 * 4 ^ n) ((V0 * forceTop c a b n : ℝ) : ℂ) := by
  have h := ((force_hasTop q l c a b hq hl n).const_mul (V0 : ℂ)).add_lower
    ((natDegree_C_mul_le (thetaGamma : ℂ) _).trans_lt (adams_degree_lt_force q l c a b hq hl n))
  simpa [integrandPoly] using h

theorem exponent_hasTop (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ)
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1)
    (thetaGamma V0 dt : ℝ) (M : ℕ) :
    HasTop (exponentPoly q l c a b thetaGamma V0 dt M) (2 * 4 ^ M)
      ((dt / 2 * V0 * forceTop c a b M : ℝ) : ℂ) := by
  have h := weighted_history_hasTop
    (fun j => integrandPoly q l c thetaGamma V0 (adamsPolynomial q l c a b j))
    (fun j => 2 * 4 ^ j) (fun j => ((V0 * forceTop c a b j : ℝ) : ℂ))
    (trapezoidWeight dt M) M
    (fun j _ => integrand_node_hasTop q l c a b hq hl thetaGamma V0 j)
    (fun _ hj => force_degree_strict hj)
  simpa [exponentPoly, trapezoidWeight, mul_assoc] using h

theorem forceTop_succ_pos {c : ℝ} {a b : ℕ → ℕ → ℝ}
    (hc : 0 < c) (ha : ∀ n, 0 < a (n + 1) (n + 1))
    (hb : ∀ n, 0 < b n (n + 1)) (n : ℕ) : 0 < forceTop c a b (n + 1) := by
  change 0 < c * (stateTop c a b n) ^ 2
  exact mul_pos hc (sq_pos_of_ne_zero (stateTop_pos hc ha hb n).ne')

/-- Every nonempty mesh has a positive real leading exponent coefficient
and degree `2 * 4^M`, independently of the remaining history weights. -/
theorem exponent_degree_and_leading (q l : ℂ[X]) {c : ℝ} {a b : ℕ → ℕ → ℝ}
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1)
    (hc : 0 < c) (ha : ∀ n, 0 < a (n + 1) (n + 1))
    (hb : ∀ n, 0 < b n (n + 1))
    (thetaGamma V0 dt : ℝ) (hV : 0 < V0) (hdt : 0 < dt) (n : ℕ) :
    (exponentPoly q l c a b thetaGamma V0 dt (n + 1)).natDegree = 2 * 4 ^ (n + 1) ∧
    0 < (exponentPoly q l c a b thetaGamma V0 dt (n + 1)).leadingCoeff.re := by
  have hp : 0 < dt / 2 * V0 * forceTop c a b (n + 1) :=
    mul_pos (mul_pos (div_pos hdt (by norm_num)) hV) (forceTop_succ_pos hc ha hb n)
  have he := (exponent_hasTop q l c a b hq hl thetaGamma V0 dt (n + 1)).exact
    (by exact_mod_cast hp.ne')
  exact ⟨he.1, by rw [he.2]; exact hp⟩

/-- The fully specified standard single-correction rough-Heston exponent. -/
def roughExponent (alpha dt R gamma rho nu theta V0 : ℝ) (M : ℕ) : ℂ[X] :=
  exponentPoly (constantPoly R) (linearPoly R gamma rho nu) ((gamma * nu) ^ 2 / 2)
    (correctorWeight alpha dt) (predictorWeight alpha dt) (theta * gamma) V0 dt M

/-- Concrete Adams weights, concrete complex Riccati coefficients and
concrete trapezoidal quadrature satisfy the high-frequency degree claim. -/
theorem roughExponent_degree_and_leading
    (alpha dt R gamma rho nu theta V0 : ℝ)
    (ha : 0 < alpha) (hdt : 0 < dt) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (n : ℕ) :
    (roughExponent alpha dt R gamma rho nu theta V0 (n + 1)).natDegree = 2 * 4 ^ (n + 1) ∧
    0 < (roughExponent alpha dt R gamma rho nu theta V0 (n + 1)).leadingCoeff.re := by
  exact exponent_degree_and_leading (constantPoly R) (linearPoly R gamma rho nu)
    (constantPoly_hasTop R) (linearPoly_degree R gamma rho nu) (by positivity)
    (fun n => correctorWeight_diagonal_pos ha hdt (n + 1))
    (fun n => predictorWeight_last_pos ha hdt n)
    (theta * gamma) V0 dt hV hdt n

/-- The affine Fourier phase `i (u+iR) m`, where for pricing
`m = log S0 + r T`. -/
def driftPoly (R m : ℝ) : ℂ[X] :=
  C (Complex.I * (m : ℂ)) * X + C (-(R : ℂ) * (m : ℂ))

def roughExponentWithDrift (alpha dt R gamma rho nu theta V0 m : ℝ) (M : ℕ) : ℂ[X] :=
  driftPoly R m + roughExponent alpha dt R gamma rho nu theta V0 M

theorem driftPoly_degree (R m : ℝ) : (driftPoly R m).natDegree ≤ 1 := by
  unfold driftPoly
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp only [natDegree_C]; omega

/-- Adding the affine spot/rate phase does not change the obstruction. -/
theorem roughExponentWithDrift_degree_and_leading
    (alpha dt R gamma rho nu theta V0 m : ℝ)
    (ha : 0 < alpha) (hdt : 0 < dt) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (n : ℕ) :
    (roughExponentWithDrift alpha dt R gamma rho nu theta V0 m (n + 1)).natDegree =
      2 * 4 ^ (n + 1) ∧
    0 < (roughExponentWithDrift alpha dt R gamma rho nu theta V0 m (n + 1)).leadingCoeff.re := by
  have he := roughExponent_degree_and_leading alpha dt R gamma rho nu theta V0 ha hdt hg hn hV n
  have ht : HasTop (roughExponent alpha dt R gamma rho nu theta V0 (n + 1))
      (2 * 4 ^ (n + 1))
      (roughExponent alpha dt R gamma rho nu theta V0 (n + 1)).leadingCoeff :=
    ⟨he.1.le, by rw [← he.1]; rfl⟩
  have hd : 1 < 2 * 4 ^ (n + 1) := by have := Nat.one_le_pow (n + 1) 4 (by norm_num); omega
  have h := (ht.add_lower ((driftPoly_degree R m).trans_lt hd)).exact
    (by intro hz; exact he.2.ne' (by simp [hz]))
  exact ⟨h.1, by rw [roughExponentWithDrift, h.2]; exact he.2⟩

end RoughHeston
