module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The single-correction fractional Adams scheme as complex polynomials

The frequency variable is the polynomial indeterminate. All quantities here
are exact; this file does not model floating-point evaluation or a different
number of corrector iterations.
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RoughHeston

/-- The complex Riccati right-hand side, with its quadratic and linear
frequency polynomials separated from its quadratic state coefficient. -/
def forcePoly (q l : ℂ[X]) (c : ℝ) (h : ℂ[X]) : ℂ[X] :=
  q + l * h + C (c : ℂ) * h ^ 2

/-- Exact polynomial recurrence: one explicit predictor followed by one
corrector evaluation at that predictor. `a j n` and `b j n` are real weights.
The terminal corrector coefficient is `a n n`. -/
def adamsPolynomial (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ) : ℕ → ℂ[X]
  | 0 => 0
  | n + 1 =>
      (∑ j : Fin (n + 1), C (a j.val (n + 1) : ℂ) *
        forcePoly q l c (adamsPolynomial q l c a b j.val)) +
      C (a (n + 1) (n + 1) : ℂ) *
        forcePoly q l c (∑ j : Fin (n + 1), C (b j.val (n + 1) : ℂ) *
          forcePoly q l c (adamsPolynomial q l c a b j.val))
termination_by n => n
decreasing_by all_goals exact Fin.isLt _

/-- A degree bound together with the coefficient at that bound.
Nonzero `v` then gives the exact degree and leading coefficient. -/
def HasTop (p : ℂ[X]) (d : ℕ) (v : ℂ) : Prop :=
  p.natDegree ≤ d ∧ p.coeff d = v

theorem HasTop.exact {p : ℂ[X]} {d : ℕ} {v : ℂ}
    (h : HasTop p d v) (hv : v ≠ 0) :
    p.natDegree = d ∧ p.leadingCoeff = v := by
  have hd := natDegree_eq_of_le_of_coeff_ne_zero h.1 (h.2 ▸ hv)
  exact ⟨hd, by simpa only [Polynomial.leadingCoeff, hd] using h.2⟩

theorem natDegree_sum_le_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ[X])
    (d : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d) :
    (∑ i ∈ s, f i).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [finsetSum_coeff]
  exact Finset.sum_eq_zero fun i hi => coeff_eq_zero_of_natDegree_lt ((h i hi).trans_lt hk)

theorem HasTop.const_mul {p : ℂ[X]} {d : ℕ} {v : ℂ}
    (h : HasTop p d v) (w : ℂ) : HasTop (C w * p) d (w * v) := by
  exact ⟨(natDegree_C_mul_le _ _).trans h.1, by simp [coeff_C_mul, h.2]⟩

theorem HasTop.add_lower {p r : ℂ[X]} {d : ℕ} {v : ℂ}
    (h : HasTop p d v) (hr : r.natDegree < d) : HasTop (r + p) d v := by
  exact ⟨natDegree_add_le_of_degree_le hr.le h.1,
    by rw [coeff_add, coeff_eq_zero_of_natDegree_lt hr, zero_add, h.2]⟩

/-- At degree at least two, the state-square term uniquely dominates the
linear-state and quadratic-frequency terms. -/
theorem forcePoly_hasTop {q l p : ℂ[X]} {c : ℝ} {d : ℕ} {v : ℂ}
    (hq : q.natDegree ≤ 2) (hl : l.natDegree ≤ 1) (hd : 2 ≤ d)
    (hp : HasTop p d v) :
    HasTop (forcePoly q l c p) (2 * d) ((c : ℂ) * v ^ 2) := by
  have hlow : (q + l * p).natDegree < 2 * d := by
    have hmul : (l * p).natDegree ≤ 1 + d :=
      natDegree_mul_le.trans (Nat.add_le_add hl hp.1)
    exact (natDegree_add_le _ _).trans_lt (by omega)
  have hpow : HasTop (p ^ 2) (2 * d) (v ^ 2) :=
    ⟨natDegree_pow_le_of_le 2 hp.1, by rw [coeff_pow_of_natDegree_le hp.1, hp.2]⟩
  exact (hpow.const_mul _).add_lower hlow

/-- A weighted history has the degree and coefficient of its last term if
the history degrees strictly increase. Earlier weights may have any sign. -/
theorem weighted_history_hasTop (p : ℕ → ℂ[X]) (d : ℕ → ℕ) (v : ℕ → ℂ)
    (w : ℕ → ℝ) (n : ℕ)
    (hp : ∀ j ≤ n, HasTop (p j) (d j) (v j))
    (hd : ∀ j < n, d j < d n) :
    HasTop (∑ j : Fin (n + 1), C (w j.val : ℂ) * p j.val)
      (d n) ((w n : ℂ) * v n) := by
  constructor
  · apply natDegree_sum_le_bound
    intro j _
    have hj : j.val ≤ n := by omega
    have hdj : d j.val ≤ d n := by
      by_cases h : j.val < n
      · exact (hd _ h).le
      · have heq : j.val = n := by omega
        simp only [heq, le_refl]
    exact (natDegree_C_mul_le _ _).trans ((hp j.val hj).1.trans hdj)
  · rw [finsetSum_coeff, Fin.sum_univ_castSucc]
    have hzero : (∑ j : Fin n,
        (C (w j.castSucc.val : ℂ) * p j.castSucc.val).coeff (d n)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact coeff_eq_zero_of_natDegree_lt
        ((natDegree_C_mul_le _ _).trans_lt
          ((hp j.val (Nat.le_of_lt j.isLt)).1.trans_lt (hd _ j.isLt)))
    rw [hzero, zero_add]
    simpa only [Fin.val_last, coeff_C_mul] using congrArg (fun z => (w n : ℂ) * z) (hp n le_rfl).2

/-- The real highest coefficient of the force evaluated at each node. -/
def forceTop (c : ℝ) (a b : ℕ → ℕ → ℝ) : ℕ → ℝ
  | 0 => -1 / 2
  | n + 1 => c * (a (n + 1) (n + 1) * c * (b n (n + 1) * forceTop c a b n) ^ 2) ^ 2

/-- The real highest coefficient of corrected node `n+1`. -/
def stateTop (c : ℝ) (a b : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  a (n + 1) (n + 1) * c * (b n (n + 1) * forceTop c a b n) ^ 2

theorem stateTop_zero (c : ℝ) (a b : ℕ → ℕ → ℝ) :
    stateTop c a b 0 = a 1 1 * c * (b 0 1) ^ 2 / 4 := by
  simp only [stateTop, forceTop]
  ring

theorem stateTop_succ (c : ℝ) (a b : ℕ → ℕ → ℝ) (n : ℕ) :
    stateTop c a b (n + 1) =
      a (n + 2) (n + 2) * c ^ 3 * (b (n + 1) (n + 2)) ^ 2 * (stateTop c a b n) ^ 4 := by
  simp only [stateTop, forceTop]
  ring

theorem force_degree_strict {j n : ℕ} (h : j < n) : 2 * 4 ^ j < 2 * 4 ^ n := by
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) h) (by norm_num)

/-- One complete update, conditional only on already-established force
coefficients at the preceding nodes. -/
theorem adams_step_hasTop (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ) (n : ℕ)
    (hq : q.natDegree ≤ 2) (hl : l.natDegree ≤ 1)
    (ih : ∀ j ≤ n, HasTop (forcePoly q l c (adamsPolynomial q l c a b j))
      (2 * 4 ^ j) (forceTop c a b j : ℂ)) :
    HasTop (adamsPolynomial q l c a b (n + 1)) (4 ^ (n + 1))
      (stateTop c a b n : ℂ) := by
  have hp := weighted_history_hasTop
    (fun j => forcePoly q l c (adamsPolynomial q l c a b j))
    (fun j => 2 * 4 ^ j) (fun j => (forceTop c a b j : ℂ))
    (fun j => b j (n + 1)) n ih (fun _ hj => force_degree_strict hj)
  have hh := weighted_history_hasTop
    (fun j => forcePoly q l c (adamsPolynomial q l c a b j))
    (fun j => 2 * 4 ^ j) (fun j => (forceTop c a b j : ℂ))
    (fun j => a j (n + 1)) n ih (fun _ hj => force_degree_strict hj)
  have hd : 2 ≤ 2 * 4 ^ n := by have := Nat.one_le_pow n 4 (by norm_num); omega
  have hfp := (forcePoly_hasTop (c := c) hq hl hd hp).const_mul (a (n + 1) (n + 1) : ℂ)
  have hlow : (∑ j : Fin (n + 1), C (a j.val (n + 1) : ℂ) *
      forcePoly q l c (adamsPolynomial q l c a b j.val)).natDegree < 2 * (2 * 4 ^ n) := by
    exact hh.1.trans_lt (by omega)
  have h := hfp.add_lower hlow
  rw [adamsPolynomial]
  convert h using 1 <;> simp [pow_succ, stateTop, mul_assoc] <;> omega

theorem force_hasTop (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ)
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1) (n : ℕ) :
    HasTop (forcePoly q l c (adamsPolynomial q l c a b n))
      (2 * 4 ^ n) (forceTop c a b n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [adamsPolynomial, forcePoly, forceTop] using hq
    | succ n =>
      have hs := adams_step_hasTop q l c a b n hq.1 hl
        (fun j hj => ih j (by omega))
      have hd : 2 ≤ 4 ^ (n + 1) := by
        have hpos := Nat.one_le_pow n 4 (by norm_num)
        rw [pow_succ]
        omega
      have h := forcePoly_hasTop (c := c) hq.1 hl hd hs
      simpa [forceTop, stateTop, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem adams_hasTop (q l : ℂ[X]) (c : ℝ) (a b : ℕ → ℕ → ℝ)
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1) (n : ℕ) :
    HasTop (adamsPolynomial q l c a b (n + 1)) (4 ^ (n + 1))
      (stateTop c a b n : ℂ) :=
  adams_step_hasTop q l c a b n hq.1 hl (fun j _ => force_hasTop q l c a b hq hl j)

theorem forceTop_ne_zero {c : ℝ} {a b : ℕ → ℕ → ℝ}
    (hc : 0 < c) (ha : ∀ n, 0 < a (n + 1) (n + 1))
    (hb : ∀ n, 0 < b n (n + 1)) (n : ℕ) : forceTop c a b n ≠ 0 := by
  induction n with
  | zero => norm_num [forceTop]
  | succ n ih =>
    simp only [forceTop]
    exact mul_ne_zero hc.ne' (pow_ne_zero _
      (mul_ne_zero (mul_ne_zero (ha n).ne' hc.ne')
        (pow_ne_zero _ (mul_ne_zero (hb n).ne' ih))))

theorem stateTop_pos {c : ℝ} {a b : ℕ → ℕ → ℝ}
    (hc : 0 < c) (ha : ∀ n, 0 < a (n + 1) (n + 1))
    (hb : ∀ n, 0 < b n (n + 1)) (n : ℕ) : 0 < stateTop c a b n := by
  exact mul_pos (mul_pos (ha n) hc) (sq_pos_of_ne_zero
    (mul_ne_zero (hb n).ne' (forceTop_ne_zero hc ha hb n)))

/-- Every positive node of every finite mesh has exact degree `4^n` and
a strictly positive real leading coefficient. -/
theorem adams_degree_and_leading (q l : ℂ[X]) {c : ℝ} {a b : ℕ → ℕ → ℝ}
    (hq : HasTop q 2 (-1 / 2)) (hl : l.natDegree ≤ 1)
    (hc : 0 < c) (ha : ∀ n, 0 < a (n + 1) (n + 1))
    (hb : ∀ n, 0 < b n (n + 1)) (n : ℕ) :
    (adamsPolynomial q l c a b (n + 1)).natDegree = 4 ^ (n + 1) ∧
    (adamsPolynomial q l c a b (n + 1)).leadingCoeff = (stateTop c a b n : ℂ) ∧
    0 < stateTop c a b n := by
  have hp := stateTop_pos hc ha hb n
  have he := (adams_hasTop q l c a b hq hl n).exact (by exact_mod_cast hp.ne')
  exact ⟨he.1, he.2, hp⟩

/-- Frequency polynomial `u + iR`. -/
def frequencyPoly (R : ℝ) : ℂ[X] := X + C (Complex.I * (R : ℂ))

/-- `-(xi²+i xi)/2`, expanded so its frequency degree is transparent. -/
def constantPoly (R : ℝ) : ℂ[X] :=
  C (-1 / 2 : ℂ) * X ^ 2 +
  C (-(Complex.I * (2 * (R : ℂ) + 1)) / 2) * X +
  C (((R : ℂ) ^ 2 + (R : ℂ)) / 2)

/-- `gamma (i xi rho nu - 1)`, expanded in the frequency variable. -/
def linearPoly (R gamma rho nu : ℝ) : ℂ[X] :=
  C ((gamma : ℂ) * Complex.I * (rho : ℂ) * (nu : ℂ)) * X +
  C ((gamma : ℂ) * (-(R : ℂ) * (rho : ℂ) * (nu : ℂ) - 1))

theorem constantPoly_hasTop (R : ℝ) :
    HasTop (constantPoly R) 2 (-1 / 2) := by
  constructor
  · unfold constantPoly
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_C_mul_X_pow_le _ _
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  · simp [constantPoly, coeff_add, coeff_C_mul, coeff_X_pow]

theorem linearPoly_degree (R gamma rho nu : ℝ) :
    (linearPoly R gamma rho nu).natDegree ≤ 1 := by
  unfold linearPoly
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp only [natDegree_C]; omega

/-- The expanded constant polynomial is exactly the complex Riccati
frequency term on the displaced Fourier line. -/
theorem constantPoly_eval (R u : ℝ) :
    (constantPoly R).eval (u : ℂ) =
      -(((u : ℂ) + Complex.I * (R : ℂ)) ^ 2 +
        Complex.I * ((u : ℂ) + Complex.I * (R : ℂ))) / 2 := by
  simp only [constantPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem linearPoly_eval (R gamma rho nu u : ℝ) :
    (linearPoly R gamma rho nu).eval (u : ℂ) =
      (gamma : ℂ) *
        (Complex.I * ((u : ℂ) + Complex.I * (R : ℂ)) * (rho : ℂ) * (nu : ℂ) - 1) := by
  simp only [linearPoly, eval_add, eval_mul, eval_C, eval_X]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Actual complex Riccati right-hand side evaluated at `xi=u+iR`. -/
def riccati (R gamma rho nu u : ℝ) (h : ℂ) : ℂ :=
  let xi : ℂ := (u : ℂ) + Complex.I * (R : ℂ);
  -(xi ^ 2 + Complex.I * xi) / 2 +
    (gamma : ℂ) * (Complex.I * xi * (rho : ℂ) * (nu : ℂ) - 1) * h +
    (((gamma * nu) ^ 2 / 2 : ℝ) : ℂ) * h ^ 2

theorem forcePoly_eval (R gamma rho nu u : ℝ) (p : ℂ[X]) :
    (forcePoly (constantPoly R) (linearPoly R gamma rho nu)
      ((gamma * nu) ^ 2 / 2) p).eval (u : ℂ) =
    riccati R gamma rho nu u (p.eval (u : ℂ)) := by
  simp only [forcePoly, eval_add, eval_mul, eval_C, eval_pow,
    constantPoly_eval, linearPoly_eval, riccati]

end RoughHeston
