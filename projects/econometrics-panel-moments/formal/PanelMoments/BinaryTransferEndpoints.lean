import PanelMoments.BinaryTransferSpan
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

/-!
# Polynomial endpoints of the actual binary transfer defects

Multiplying a defect with a prefix of length `k` by `z^k` gives the
polynomial constructed below. Its degree is at most `2*k`. For a nonempty
prefix, the constant and degree-`2*k` coefficients are both nonzero when
`ρ ≠ 0,1`, every coefficient is nonzero, and the final prefix coefficient
differs from the appended coefficient.

The representation uses the actual rational functions from
`BinaryTransferAlgebra`, evaluated on nonzero reals. The endpoint-separation
lemma isolates a polynomial and its `X` multiple from any remainder having
zero extreme coefficients. No family independence or rank is asserted here.
-/

noncomputable section

namespace PanelMoments.BinaryTransferEndpoints

open Polynomial

def quadratic (a b c : ℝ) : ℝ[X] := C a + C b * X + C c * X ^ 2

@[simp] theorem quadratic_coeff_zero (a b c : ℝ) : (quadratic a b c).coeff 0 = a := by
  simp [quadratic]

@[simp] theorem quadratic_coeff_two (a b c : ℝ) : (quadratic a b c).coeff 2 = c := by
  simp [quadratic]

theorem quadratic_natDegree_le (a b c : ℝ) : (quadratic a b c).natDegree ≤ 2 := by
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_mul_le_of_le (show (C b).natDegree ≤ 0 by simp)
        (show (X : ℝ[X]).natDegree ≤ 1 by simp)).trans (by omega)
  · exact (natDegree_mul_le_of_le (show (C c).natDegree ≤ 0 by simp)
      (show (X ^ 2 : ℝ[X]).natDegree ≤ 2 by simp)).trans (by omega)

/-- Clearing the single negative power in a transfer factor. -/
def factorPolynomial (ρ c : ℝ) : ℝ[X] :=
  quadratic (1 / ((ρ - 1) * c)) ((ρ + 1) / (ρ - 1)) (ρ * c / (ρ - 1))

def pairScale (ρ e c : ℝ) : ℝ := (e - c) / (e * c * (ρ - 1) ^ 2)

/-- Clearing the single negative power in the two-coefficient defect. -/
def pairPolynomial (ρ e c : ℝ) : ℝ[X] :=
  quadratic (pairScale ρ e c) (pairScale ρ e c * ρ * (e + c))
    (pairScale ρ e c * ρ * e * c)

theorem factorPolynomial_natDegree_le (ρ c : ℝ) :
    (factorPolynomial ρ c).natDegree ≤ 2 :=
  quadratic_natDegree_le _ _ _

theorem pairPolynomial_natDegree_le (ρ e c : ℝ) :
    (pairPolynomial ρ e c).natDegree ≤ 2 :=
  quadratic_natDegree_le _ _ _

def prefixProduct (ρ : ℝ) : List ℝ → ℝ[X]
  | [] => 1
  | c :: cs => factorPolynomial ρ c * prefixProduct ρ cs

/-- The polynomial obtained by clearing exactly `cs.length` negative powers
from the actual defect with prefix `cs` and appended coefficient `c`. -/
def defectPolynomial (ρ : ℝ) (cs : List ℝ) (c : ℝ) : ℝ[X] :=
  cs.reverseRecOn 0 (fun ds e p => X * p + prefixProduct ρ ds * pairPolynomial ρ e c)

@[simp] theorem defectPolynomial_nil (ρ c : ℝ) : defectPolynomial ρ [] c = 0 := by
  simp [defectPolynomial]

@[simp] theorem defectPolynomial_append (ρ e c : ℝ) (cs : List ℝ) :
    defectPolynomial ρ (cs ++ [e]) c =
      X * defectPolynomial ρ cs c + prefixProduct ρ cs * pairPolynomial ρ e c := by
  simp [defectPolynomial]

theorem factorPolynomial_eval (ρ c z : ℝ) (hρ : ρ ≠ 1) (hc : c ≠ 0) (hz : z ≠ 0) :
    (factorPolynomial ρ c).eval z = z * BinaryTransferAlgebra.H ρ c z := by
  simp only [factorPolynomial, quadratic, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  unfold BinaryTransferAlgebra.H
  field_simp [sub_ne_zero.mpr hρ, hc, hz]
  ring

theorem pairPolynomial_eval (ρ e c z : ℝ) (hρ : ρ ≠ 1)
    (he : e ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) :
    (pairPolynomial ρ e c).eval z = z * BinaryTransferAlgebra.moveFirst ρ [e] c z := by
  simp only [pairPolynomial, quadratic, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  simp only [BinaryTransferAlgebra.moveFirst, BinaryTransferAlgebra.prefixQ_singleton,
    BinaryTransferAlgebra.prefixR_singleton]
  unfold pairScale BinaryTransferAlgebra.moveDefect BinaryTransferAlgebra.Q BinaryTransferAlgebra.R
  field_simp [sub_ne_zero.mpr hρ, he, hc, hz]
  ring

theorem prefixProduct_eval (ρ z : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hz : z ≠ 0) (hcs : ∀ c ∈ cs, c ≠ 0) :
    (prefixProduct ρ cs).eval z = z ^ cs.length * BinaryTransferAlgebra.prefixH ρ cs z := by
  induction cs with
  | nil => simp [prefixProduct]
  | cons c cs ih =>
    have hc : c ≠ 0 := hcs c (by simp)
    have hcs' : ∀ e ∈ cs, e ≠ 0 := fun e he => hcs e (by simp [he])
    simp only [prefixProduct, eval_mul, factorPolynomial_eval ρ c z hρ hc hz,
      ih hcs', List.length_cons, BinaryTransferAlgebra.prefixH, pow_succ]
    ring

theorem moveFirst_append (ρ c z : ℝ) (cs ds : List ℝ) :
    BinaryTransferAlgebra.moveFirst ρ (cs ++ ds) c z =
      BinaryTransferAlgebra.moveFirst ρ cs c z +
        BinaryTransferAlgebra.prefixH ρ cs z * BinaryTransferAlgebra.moveFirst ρ ds c z := by
  simp only [BinaryTransferAlgebra.moveFirst, BinaryTransferAlgebra.prefixQ_append,
    BinaryTransferAlgebra.prefixR_append, BinaryTransferAlgebra.moveDefect]
  ring

/-- Exact evaluation bridge from the constructed polynomial to the actual defect. -/
theorem defectPolynomial_eval (ρ c z : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hc : c ≠ 0) (hz : z ≠ 0) (hcs : ∀ e ∈ cs, e ≠ 0) :
    (defectPolynomial ρ cs c).eval z =
      z ^ cs.length * BinaryTransferAlgebra.moveFirst ρ cs c z := by
  induction cs using List.reverseRecOn with
  | nil => simp
  | append_singleton cs e ih =>
    have he : e ≠ 0 := hcs e (by simp)
    have hcs' : ∀ d ∈ cs, d ≠ 0 := fun d hd => hcs d (by simp [hd])
    rw [defectPolynomial_append]
    simp only [eval_add, eval_mul, eval_X, ih hcs',
      prefixProduct_eval ρ z cs hρ hz hcs', pairPolynomial_eval ρ e c z hρ he hc hz,
      List.length_append, List.length_singleton, pow_succ, moveFirst_append]
    ring

theorem prefixProduct_natDegree_le (ρ : ℝ) (cs : List ℝ) :
    (prefixProduct ρ cs).natDegree ≤ 2 * cs.length := by
  induction cs with
  | nil => simp [prefixProduct]
  | cons c cs ih =>
    have h := natDegree_mul_le_of_le (factorPolynomial_natDegree_le ρ c) ih
    simpa only [prefixProduct, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.add_comm] using h

theorem defectPolynomial_natDegree_le (ρ c : ℝ) (cs : List ℝ) :
    (defectPolynomial ρ cs c).natDegree ≤ 2 * cs.length := by
  induction cs using List.reverseRecOn with
  | nil => simp
  | append_singleton cs e ih =>
    rw [defectPolynomial_append]
    apply natDegree_add_le_of_degree_le
    · have h := natDegree_mul_le_of_le (show (X : ℝ[X]).natDegree ≤ 1 by simp) ih
      simp only [List.length_append, List.length_singleton]
      omega
    · have h := natDegree_mul_le_of_le (prefixProduct_natDegree_le ρ cs)
        (pairPolynomial_natDegree_le ρ e c)
      simp only [List.length_append, List.length_singleton]
      omega

theorem prefixProduct_coeff_zero (ρ : ℝ) (cs : List ℝ) :
    (prefixProduct ρ cs).coeff 0 = (cs.map (fun c => 1 / ((ρ - 1) * c))).prod := by
  induction cs with
  | nil => simp [prefixProduct]
  | cons c cs ih => simp [prefixProduct, mul_coeff_zero, factorPolynomial, ih]

theorem prefixProduct_coeff_top (ρ : ℝ) (cs : List ℝ) :
    (prefixProduct ρ cs).coeff (2 * cs.length) =
      (cs.map (fun c => ρ * c / (ρ - 1))).prod := by
  induction cs with
  | nil => simp [prefixProduct]
  | cons c cs ih =>
    rw [prefixProduct, show 2 * (c :: cs).length = 2 + 2 * cs.length by simp; omega,
      coeff_mul_add_eq_of_natDegree_le (factorPolynomial_natDegree_le ρ c)
        (prefixProduct_natDegree_le ρ cs)]
    simp [factorPolynomial, ih]

theorem defectPolynomial_coeff_zero (ρ e c : ℝ) (cs : List ℝ) :
    (defectPolynomial ρ (cs ++ [e]) c).coeff 0 =
      (cs.map (fun d => 1 / ((ρ - 1) * d))).prod * pairScale ρ e c := by
  simp [defectPolynomial_append, mul_coeff_zero, prefixProduct_coeff_zero, pairPolynomial]

theorem defectPolynomial_coeff_top (ρ e c : ℝ) (cs : List ℝ) :
    (defectPolynomial ρ (cs ++ [e]) c).coeff (2 * (cs.length + 1)) =
      (cs.map (fun d => ρ * d / (ρ - 1))).prod * (pairScale ρ e c * ρ * e * c) := by
  rw [defectPolynomial_append, coeff_add]
  have hshort : (X * defectPolynomial ρ cs c).natDegree < 2 * (cs.length + 1) := by
    have h := natDegree_mul_le_of_le (show (X : ℝ[X]).natDegree ≤ 1 by simp)
      (defectPolynomial_natDegree_le ρ c cs)
    omega
  rw [coeff_eq_zero_of_natDegree_lt hshort, zero_add,
    show 2 * (cs.length + 1) = 2 * cs.length + 2 by omega,
    coeff_mul_add_eq_of_natDegree_le (prefixProduct_natDegree_le ρ cs)
      (pairPolynomial_natDegree_le ρ e c), prefixProduct_coeff_top]
  simp [pairPolynomial]

theorem pairScale_ne_zero (ρ e c : ℝ) (hρ : ρ ≠ 1) (he : e ≠ 0)
    (hc : c ≠ 0) (hec : e ≠ c) : pairScale ρ e c ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hec)
    (mul_ne_zero (mul_ne_zero he hc) (pow_ne_zero 2 (sub_ne_zero.mpr hρ)))

theorem defectPolynomial_coeff_zero_ne_zero (ρ e c : ℝ) (cs : List ℝ)
    (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0) (he : e ≠ 0) (hc : c ≠ 0) (hec : e ≠ c) :
    (defectPolynomial ρ (cs ++ [e]) c).coeff 0 ≠ 0 := by
  rw [defectPolynomial_coeff_zero]
  apply mul_ne_zero _ (pairScale_ne_zero ρ e c hρ he hc hec)
  apply List.prod_ne_zero
  intro hx
  obtain ⟨d, hd, hzero⟩ := List.mem_map.mp hx
  exact div_ne_zero one_ne_zero (mul_ne_zero (sub_ne_zero.mpr hρ) (hcs d hd)) hzero

theorem defectPolynomial_coeff_top_ne_zero (ρ e c : ℝ) (cs : List ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0)
    (he : e ≠ 0) (hc : c ≠ 0) (hec : e ≠ c) :
    (defectPolynomial ρ (cs ++ [e]) c).coeff (2 * (cs.length + 1)) ≠ 0 := by
  rw [defectPolynomial_coeff_top]
  apply mul_ne_zero _ (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (pairScale_ne_zero ρ e c hρ he hc hec) hρ0) he) hc)
  apply List.prod_ne_zero
  intro hx
  obtain ⟨d, hd, hzero⟩ := List.mem_map.mp hx
  exact div_ne_zero (mul_ne_zero hρ0 (hcs d hd)) (sub_ne_zero.mpr hρ) hzero

theorem defectPolynomial_natDegree (ρ e c : ℝ) (cs : List ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0)
    (he : e ≠ 0) (hc : c ≠ 0) (hec : e ≠ c) :
    (defectPolynomial ρ (cs ++ [e]) c).natDegree = 2 * (cs.length + 1) := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simpa only [List.length_append, List.length_singleton] using
      defectPolynomial_natDegree_le ρ c (cs ++ [e])
  · exact defectPolynomial_coeff_top_ne_zero ρ e c cs hρ0 hρ hcs he hc hec

/-- A polynomial with nonzero extreme coefficients and its `X` multiple
cannot cancel a remainder whose corresponding extreme coefficients vanish. -/
theorem separate_endpoints {n : ℕ} (p q : ℝ[X]) (a b : ℝ)
    (hp0 : p.coeff 0 ≠ 0) (hpn : p.coeff n ≠ 0)
    (hq0 : q.coeff 0 = 0) (hqtop : q.coeff (n + 1) = 0)
    (h : C a * p + C b * (X * p) + q = 0) : a = 0 ∧ b = 0 ∧ q = 0 := by
  have h0 := congrArg (fun r : ℝ[X] => r.coeff 0) h
  simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, hq0, coeff_zero,
    mul_zero, add_zero] at h0
  have ha : a = 0 := (mul_eq_zero.mp h0).resolve_right hp0
  have htop := congrArg (fun r : ℝ[X] => r.coeff (n + 1)) h
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, hqtop, coeff_zero, ha,
    zero_mul, zero_add, add_zero] at htop
  have hb : b = 0 := (mul_eq_zero.mp htop).resolve_right hpn
  exact ⟨ha, hb, by simpa [ha, hb] using h⟩

/-- Restricting polynomial evaluation to nonzero real arguments remains injective. -/
theorem evaluation_injective : Function.Injective
    (fun p : ℝ[X] => (fun z : BinaryTransferSpan.NonzeroReal => p.eval z.val)) := by
  let : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  intro p q h
  apply Polynomial.eq_of_infinite_eval_eq
  have hs := (Set.finite_singleton (0 : ℝ)).infinite_compl
  exact hs.mono (fun z hz => congr_fun h ⟨z, by simpa using hz⟩)

/-- The exact bridge in the same function space used by `BinaryTransferSpan`. -/
theorem defectPolynomial_as_function (ρ c : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hc : c ≠ 0) (hcs : ∀ e ∈ cs, e ≠ 0) :
    (fun z : BinaryTransferSpan.NonzeroReal => (defectPolynomial ρ cs c).eval z.val) =
      fun z => z.val ^ cs.length * BinaryTransferSpan.defect ρ cs c z := by
  funext z
  exact defectPolynomial_eval ρ c z.val cs hρ hc z.property hcs

/-- The actual final defect and its `z` multiple cannot cancel a function
whose shorter clearing has degree at most `2*cs.length+1`. This is the
endpoint step needed to remove successive pairs from a finite relation. -/
theorem separate_actual_pair (ρ e c : ℝ) (cs : List ℝ) (p : ℝ[X]) (a b : ℝ)
    (f : BinaryTransferSpan.FunctionSpace) (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1)
    (hcs : ∀ d ∈ cs, d ≠ 0) (he : e ≠ 0) (hc : c ≠ 0) (hec : e ≠ c)
    (hp : p.natDegree ≤ 2 * cs.length + 1)
    (hrep : ∀ z : BinaryTransferSpan.NonzeroReal, p.eval z.val = z.val ^ cs.length * f z)
    (hrel : a • BinaryTransferSpan.defect ρ (cs ++ [e]) c +
      b • BinaryTransferSpan.mulZ (BinaryTransferSpan.defect ρ (cs ++ [e]) c) + f = 0) :
    a = 0 ∧ b = 0 ∧ f = 0 := by
  have hcs' : ∀ d ∈ cs ++ [e], d ≠ 0 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hcs d hd
    · rcases List.mem_singleton.mp hd with rfl
      exact he
  have hpoly : C a * defectPolynomial ρ (cs ++ [e]) c +
      C b * (X * defectPolynomial ρ (cs ++ [e]) c) + X * p = 0 := by
    apply evaluation_injective
    funext z
    have hzrel := congr_fun hrel z
    change a * BinaryTransferAlgebra.moveFirst ρ (cs ++ [e]) c z.val +
      b * (z.val * BinaryTransferAlgebra.moveFirst ρ (cs ++ [e]) c z.val) + f z = 0 at hzrel
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero,
      defectPolynomial_eval ρ c z.val (cs ++ [e]) hρ hc z.property hcs', hrep z,
      List.length_append, List.length_singleton, pow_succ]
    calc
      _ = (z.val ^ cs.length * z.val) *
        (a * BinaryTransferAlgebra.moveFirst ρ (cs ++ [e]) c z.val +
          b * (z.val * BinaryTransferAlgebra.moveFirst ρ (cs ++ [e]) c z.val) + f z) := by ring
      _ = 0 := by rw [hzrel, mul_zero]
  have hqtop : (X * p).coeff (2 * (cs.length + 1) + 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hd := natDegree_mul_le_of_le (show (X : ℝ[X]).natDegree ≤ 1 by simp) hp
    omega
  obtain ⟨ha, hb, _⟩ := separate_endpoints
    (defectPolynomial ρ (cs ++ [e]) c) (X * p) a b
    (defectPolynomial_coeff_zero_ne_zero ρ e c cs hρ hcs he hc hec)
    (defectPolynomial_coeff_top_ne_zero ρ e c cs hρ0 hρ hcs he hc hec)
    (by simp) hqtop hpoly
  exact ⟨ha, hb, by simpa [ha, hb] using hrel⟩

end PanelMoments.BinaryTransferEndpoints
