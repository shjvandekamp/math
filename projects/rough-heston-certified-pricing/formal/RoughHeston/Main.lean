module

public import RoughHeston.Exponent
public import RoughHeston.Payoff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The concrete fixed-mesh obstruction

This is a deterministic theorem for the specified reference PECE recurrence,
strike one and damping minus two. The drift is zero (`S₀ = 1`, `r = 0`). A
bounded comparison function is not asserted to be a financial model transform.
The stochastic model, moment identity and pricing bridge remain separate.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory Polynomial
open scoped Topology ENNReal

namespace RoughHeston

/-- Time-step count at dyadic level `ell`, including the base level. -/
def meshSteps (M0 ell : ℕ) : ℕ := 2 ^ ell * M0

/-- Exact positive time width, when maturity and base step count are positive. -/
def meshWidth (T : ℝ) (M0 ell : ℕ) : ℝ := T / (meshSteps M0 ell : ℝ)

theorem meshSteps_pos {M0 : ℕ} (hM : 0 < M0) (ell : ℕ) :
    0 < meshSteps M0 ell := Nat.mul_pos (by positivity) hM

theorem meshWidth_pos {T : ℝ} {M0 : ℕ} (hT : 0 < T) (hM : 0 < M0) (ell : ℕ) :
    0 < meshWidth T M0 ell := by
  exact div_pos hT (by exact_mod_cast meshSteps_pos hM ell)

/-- Every finite positive mesh, with the concrete fractional weights and
published trapezoidal exponent, has nonintegrable call-weighted modulus error
against any bounded comparison function. -/
theorem reference_fixed_mesh_not_integrable
    (alpha T gamma rho nu theta V0 : ℝ) (M : ℕ) (Φ : ℝ → ℂ) (B : ℝ)
    (ha : 0 < alpha) (hT : 0 < T) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (hM : 0 < M) (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    ¬ IntegrableOn
      (callWeightedError
        (fun u => (roughExponent alpha (T / (M : ℝ)) (-2) gamma rho nu theta V0 M).eval
          (u : ℂ)) Φ) (Ioi 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  have hdt : 0 < T / ((n + 1 : ℕ) : ℝ) := div_pos hT (by positivity)
  have hex := roughExponent_degree_and_leading alpha (T / ((n + 1 : ℕ) : ℝ))
    (-2) gamma rho nu theta V0 ha hdt hg hn hV n
  apply not_integrableOn_callWeightedError_of_polynomial _ Φ B _ hex.2 hbounded
  rw [hex.1]
  have hp : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by norm_num)
  rw [pow_succ]
  omega

/-- The same fixed-mesh theorem with the actual defining Fourier integral
of the vanilla call in the conclusion. -/
theorem reference_genuine_call_not_integrable
    (alpha T gamma rho nu theta V0 : ℝ) (M : ℕ) (Φ : ℝ → ℂ) (B : ℝ)
    (ha : 0 < alpha) (hT : 0 < T) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (hM : 0 < M) (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    ¬ IntegrableOn
      (fun u : ℝ => ‖∫ x : ℝ, callFourierIntegrand u x‖ *
        ‖Φ u - Complex.exp
          ((roughExponent alpha (T / (M : ℝ)) (-2) gamma rho nu theta V0 M).eval
            (u : ℂ))‖) (Ioi 0) := by
  have h := reference_fixed_mesh_not_integrable alpha T gamma rho nu theta V0 M Φ B
    ha hT hg hn hV hM hbounded
  unfold callWeightedError at h
  simpa only [integral_callFourierIntegrand] using h

/-- The positive call-weighted error at a refinement level. The exponent `p`
is arbitrary: no empirical convergence order is used in this obstruction. -/
def levelError (alpha T gamma rho nu theta V0 p : ℝ) (M0 ell : ℕ)
    (Φ : ℝ → ℂ) (u : ℝ) : ℝ :=
  (meshWidth T M0 ell) ^ (-p) *
    callWeightedError
      (fun v => (roughExponent alpha (meshWidth T M0 ell) (-2)
        gamma rho nu theta V0 (meshSteps M0 ell)).eval (v : ℂ)) Φ u

/-- The actual supremum is defined in the extended nonnegative reals so that
an unbounded supremum is never silently replaced by a real default. -/
def domination (alpha T gamma rho nu theta V0 p : ℝ) (M0 : ℕ)
    (Φ : ℝ → ℂ) (u : ℝ) : ENNReal :=
  ⨆ ell : ℕ, ENNReal.ofReal (levelError alpha T gamma rho nu theta V0 p M0 ell Φ u)

/-- At each fixed level the weighted error eventually exceeds its positive
mesh normalization. This provides an analytic lower bound on an entire tail. -/
theorem levelError_eventually_ge_scale
    (alpha T gamma rho nu theta V0 p : ℝ) (M0 L : ℕ)
    (Φ : ℝ → ℂ) (B : ℝ)
    (ha : 0 < alpha) (hT : 0 < T) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (hM : 0 < M0) (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    ∀ᶠ u in atTop, (meshWidth T M0 L) ^ (-p) ≤
      levelError alpha T gamma rho nu theta V0 p M0 L Φ u := by
  have hsteps := meshSteps_pos hM L
  obtain ⟨n, hnsteps⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsteps)
  have hdt := meshWidth_pos hT hM L
  let P := roughExponent alpha (meshWidth T M0 L) (-2) gamma rho nu theta V0
    (meshSteps M0 L)
  have hex : P.natDegree = 2 * 4 ^ (n + 1) ∧ 0 < P.leadingCoeff.re := by
    dsimp [P]
    rw [hnsteps]
    exact roughExponent_degree_and_leading alpha (meshWidth T M0 L) (-2)
      gamma rho nu theta V0 ha hdt hg hn hV n
  have hdeg : 2 < P.natDegree := by
    rw [hex.1, pow_succ]
    have hp : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by norm_num)
    omega
  have hrealdeg : 2 < (realPartPolynomial P).natDegree := by
    simpa only [realPartPolynomial_natDegree P hex.2] using hdeg
  have hrealpos : 0 < (realPartPolynomial P).leadingCoeff := by
    simpa only [realPartPolynomial_leadingCoeff P hex.2] using hex.2
  have hgrowth :=
    polynomial_eventually_ge_quadratic (realPartPolynomial P) hrealdeg hrealpos 12 B
  have hevent := eventually_one_le_callWeightedError
    (fun (u : ℝ) => P.eval (Complex.ofReal u)) Φ B hbounded
    (by simpa only [realPartPolynomial_eval] using hgrowth)
  filter_upwards [hevent] with u hu
  simpa [levelError, P] using
    (mul_le_mul_of_nonneg_left hu (Real.rpow_pos_of_pos hdt (-p)).le)

/-- No integrable real function can dominate all the level errors, even if
any fixed number `L` of initial levels is discarded. -/
theorem no_integrable_majorant_after_fixed_level
    (alpha T gamma rho nu theta V0 p : ℝ) (M0 L : ℕ)
    (Φ : ℝ → ℂ) (B : ℝ) (D : ℝ → ℝ)
    (ha : 0 < alpha) (hT : 0 < T) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (hM : 0 < M0) (hbounded : ∀ u, ‖Φ u‖ ≤ B)
    (hdom : ∀ ell, L ≤ ell → ∀ u, 0 < u →
      levelError alpha T gamma rho nu theta V0 p M0 ell Φ u ≤ D u) :
    ¬ IntegrableOn D (Ioi 0) := by
  have hevent := levelError_eventually_ge_scale alpha T gamma rho nu theta V0 p M0 L
    Φ B ha hT hg hn hV hM hbounded
  let scale : ℝ := (meshWidth T M0 L) ^ (-p)
  have hscale : 0 < scale := Real.rpow_pos_of_pos (meshWidth_pos hT hM L) _
  have hD : ∀ᶠ u in atTop, 1 ≤ D u / scale := by
    filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with u he hu
    apply (le_div_iff₀ hscale).2
    simpa only [one_mul] using he.trans (hdom L le_rfl u hu)
  intro hint
  exact not_integrableOn_of_eventually_one_le (fun u => D u / scale) hD
    (hint.div_const scale)

/-- The all-level domination function itself has infinite Lebesgue integral.
This is an extended-real statement, without any hidden bounded-supremum
assumption or chosen convergence rate. -/
theorem domination_lintegral_eq_top
    (alpha T gamma rho nu theta V0 p : ℝ) (M0 : ℕ)
    (Φ : ℝ → ℂ) (B : ℝ)
    (ha : 0 < alpha) (hT : 0 < T) (hg : 0 < gamma) (hn : 0 < nu)
    (hV : 0 < V0) (hM : 0 < M0) (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    (∫⁻ u in Ioi (0 : ℝ), domination alpha T gamma rho nu theta V0 p M0 Φ u) = ∞ := by
  have hevent := levelError_eventually_ge_scale alpha T gamma rho nu theta V0 p M0 0
    Φ B ha hT hg hn hV hM hbounded
  obtain ⟨a, haevent⟩ := eventually_atTop.1 hevent
  let scale : ℝ := (meshWidth T M0 0) ^ (-p)
  have hscale : 0 < scale := Real.rpow_pos_of_pos (meshWidth_pos hT hM 0) _
  have hconst :
      (∫⁻ _ in Ioi (max a 0), ENNReal.ofReal scale) = (∞ : ENNReal) := by
    rw [setLIntegral_const, Real.volume_Ioi]
    exact ENNReal.mul_top (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
  apply top_unique
  calc
    ∞ = ∫⁻ _ in Ioi (max a 0), ENNReal.ofReal scale := hconst.symm
    _ ≤ ∫⁻ u in Ioi (max a 0), domination alpha T gamma rho nu theta V0 p M0 Φ u := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro u hu
      exact (ENNReal.ofReal_le_ofReal (haevent u
        ((le_max_left a 0).trans (le_of_lt hu)))).trans
        (le_iSup (fun ell : ℕ => ENNReal.ofReal
          (levelError alpha T gamma rho nu theta V0 p M0 ell Φ u)) 0)
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), domination alpha T gamma rho nu theta V0 p M0 Φ u :=
      lintegral_mono_set (fun u hu => (le_max_right a 0).trans_lt hu)

/-- A fully explicit nondegenerate algebraic instance. This does not assert
that the arbitrary bounded comparison is a rough-Heston transform. -/
theorem concrete_example_not_integrable (M : ℕ) (hM : 0 < M)
    (Φ : ℝ → ℂ) (B : ℝ) (hbounded : ∀ u, ‖Φ u‖ ≤ B) :
    ¬ IntegrableOn
      (callWeightedError
        (fun u => (roughExponent (3 / 4) (1 / (M : ℝ)) (-2)
          1 (-(1 / 2)) 1 1 1 M).eval (u : ℂ)) Φ) (Ioi 0) := by
  exact reference_fixed_mesh_not_integrable (3 / 4) 1 1 (-(1 / 2)) 1 1 1 M Φ B
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM hbounded

/-- Explicit nonvacuity of the deterministic hypotheses. The comparison one
is merely a bounded test function, not asserted to be a rough-Heston model. -/
theorem concrete_example_against_one (M : ℕ) (hM : 0 < M) :
    ¬ IntegrableOn
      (callWeightedError
        (fun u => (roughExponent (3 / 4) (1 / (M : ℝ)) (-2)
          1 (-(1 / 2)) 1 1 1 M).eval (u : ℂ)) (fun _ => 1)) (Ioi 0) := by
  exact concrete_example_not_integrable M hM (fun _ => 1) 1 (by intro u; simp)

end RoughHeston
