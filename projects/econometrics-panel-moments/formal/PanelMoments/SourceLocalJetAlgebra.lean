import PanelMoments.SourceRelativeTimeJet

set_option autoImplicit false

/-!
# Exact local cancellation for the actual special kernel jet

For a fixed tail matrix `Q`, the special combination is
`dotp * e_b (I - K Q) + p * e_b dotK Q`, where `p = X_a K(a,b)`.
Both `K` and `dotK` are the existing actual homogeneous kernel and its
proved relative-time derivative. The plus sign is part of this combination;
this is not asserted to be the derivative of an individual source column.
An exact difference of the two perturbed kernel branches has this derivative.

The expansion and diagonal cancellation hold for arbitrary state count
and arbitrary fixed tail matrix wherever the indicated row forms are
nonzero. The diagonal formula clears with two row denominators. No residue
operator, pole-order theorem, or independence conclusion is asserted.
-/

namespace PanelMoments.SourceLocalJetAlgebra

open scoped BigOperators
open SourceHomogeneous SourceRelativeTimeJet

noncomputable section

def prefixNumerator {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (a b : State n) : ℝ :=
  A t a b * X a * X b

def rowTail {n : ℕ} (A : Table n) (X : State n → ℝ) (t : ℕ)
    (Q : Matrix (State n) (State n) ℝ) (b j : State n) : ℝ :=
  ∑ k : State n, A t b k * X k * Q k j

def rowDirectionTail {n : ℕ} (A : Table n) (X : State n → ℝ) (t : ℕ)
    (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ) (b j : State n) : ℝ :=
  ∑ k : State n, A t b k * X k * (d k - d b) * Q k j

/-- The actual prefix and kernel jets, with a fixed arbitrary tail matrix. -/
def specialJet {n : ℕ} (A : Table n) (X : State n → ℝ) (t : ℕ)
    (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ) (a b : State n) :
    State n → ℝ :=
  fun j => X a * kernelJet A X t d a b *
      ((if b = j then 1 else 0) - (kernel A X t * Q) b j) +
    X a * kernel A X t a b * (kernelJet A X t d * Q) b j

theorem prefix_hasDerivAt {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (a b : State n)
    (hL : rowForm A X t a ≠ 0) :
    HasDerivAt (fun ε : ℝ => X a * kernel (perturbTable A t d ε) X t a b)
      (X a * kernelJet A X t d a b) 0 :=
  (kernel_hasDerivAt A X t d a b hL).const_mul (X a)

/-- The special jet is the derivative of the exact two-branch kernel difference.
The tail is fixed in both branches; no identification with a full source word is needed. -/
theorem specialDifference_hasDerivAt {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a b j : State n) (hL : ∀ i, rowForm A X t i ≠ 0) :
    HasDerivAt
      (fun ε : ℝ =>
        X a * kernel (perturbTable A t d ε) X t a b *
          ((if b = j then 1 else 0) - (kernel A X t * Q) b j) -
        X a * kernel A X t a b *
          ((if b = j then 1 else 0) -
            (kernel (perturbTable A t d ε) X t * Q) b j))
      (specialJet A X t d Q a b j) 0 := by
  have htail : HasDerivAt
      (fun ε : ℝ => (kernel (perturbTable A t d ε) X t * Q) b j)
      ((kernelJet A X t d * Q) b j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum (fun k _ =>
      (kernel_hasDerivAt A X t d b k (hL b)).mul_const (Q k j))
  have hfirst := (prefix_hasDerivAt A X t d a b (hL a)).mul_const
    ((if b = j then 1 else 0) - (kernel A X t * Q) b j)
  have hsecond := (htail.const_sub (if b = j then 1 else 0)).const_mul
    (X a * kernel A X t a b)
  apply (hfirst.fun_sub hsecond).congr_deriv
  simp [specialJet, sub_eq_add_neg]

theorem prefix_formula {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (a b : State n) :
    X a * kernel A X t a b = prefixNumerator A X t a b / rowForm A X t a := by
  simp only [kernel, Matrix.of_apply, prefixNumerator]
  ring

theorem prefixJet_formula {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (a b : State n)
    (hL : rowForm A X t a ≠ 0) :
    X a * kernelJet A X t d a b = prefixNumerator A X t a b *
      (d b / rowForm A X t a - rowFormJet A X t d a / rowForm A X t a ^ 2) := by
  simp only [kernelJet, kernel, Matrix.of_apply, prefixNumerator]
  field_simp [hL]

theorem kernel_mul_tail {n : ℕ} (A : Table n) (X : State n → ℝ) (t : ℕ)
    (Q : Matrix (State n) (State n) ℝ) (b j : State n) :
    (kernel A X t * Q) b j = rowTail A X t Q b j / rowForm A X t b := by
  simp only [Matrix.mul_apply, kernel, Matrix.of_apply, rowTail,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem direction_sum {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ) (b j : State n) :
    (∑ k : State n, A t b k * X k * d k * Q k j) =
      rowDirectionTail A X t d Q b j + d b * rowTail A X t Q b j := by
  rw [rowDirectionTail, rowTail, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem kernelJet_mul_tail {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (b j : State n) (hL : rowForm A X t b ≠ 0) :
    (kernelJet A X t d * Q) b j =
      (rowDirectionTail A X t d Q b j + d b * rowTail A X t Q b j) /
        rowForm A X t b -
      rowFormJet A X t d b * rowTail A X t Q b j / rowForm A X t b ^ 2 := by
  rw [← direction_sum A X t d Q b j]
  simp only [Matrix.mul_apply, kernelJet, kernel, Matrix.of_apply, rowTail,
    div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [hL]

/-- The five-term local identity, derived from the actual kernel jet. -/
theorem specialJet_expansion {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a b j : State n) (hLa : rowForm A X t a ≠ 0) (hLb : rowForm A X t b ≠ 0) :
    specialJet A X t d Q a b j = prefixNumerator A X t a b *
      (d b * (if b = j then 1 else 0) / rowForm A X t a -
       rowFormJet A X t d a * (if b = j then 1 else 0) / rowForm A X t a ^ 2 +
       rowDirectionTail A X t d Q b j / (rowForm A X t a * rowForm A X t b) +
       rowFormJet A X t d a * rowTail A X t Q b j /
         (rowForm A X t a ^ 2 * rowForm A X t b) -
       rowFormJet A X t d b * rowTail A X t Q b j /
         (rowForm A X t a * rowForm A X t b ^ 2)) := by
  rw [specialJet, prefixJet_formula A X t d a b hLa, prefix_formula,
    kernel_mul_tail, kernelJet_mul_tail A X t d Q b j hLb]
  field_simp [hLa, hLb]
  ring

/-- For a diagonal prefix, the two terms with three row denominators cancel. -/
theorem specialJet_diagonal {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a j : State n) (hL : rowForm A X t a ≠ 0) :
    specialJet A X t d Q a a j = prefixNumerator A X t a a *
      (d a * (if a = j then 1 else 0) / rowForm A X t a +
       (rowDirectionTail A X t d Q a j -
         rowFormJet A X t d a * (if a = j then 1 else 0)) / rowForm A X t a ^ 2) := by
  rw [specialJet_expansion A X t d Q a a j hL hL]
  field_simp [hL]
  ring

/-- The diagonal identity after clearing only the square of its own row form. -/
theorem specialJet_diagonal_cleared {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a j : State n) (hL : rowForm A X t a ≠ 0) :
    rowForm A X t a ^ 2 * specialJet A X t d Q a a j =
      prefixNumerator A X t a a *
        (d a * (if a = j then 1 else 0) * rowForm A X t a +
          rowDirectionTail A X t d Q a j -
          rowFormJet A X t d a * (if a = j then 1 else 0)) := by
  rw [specialJet_diagonal A X t d Q a j hL]
  field_simp [hL]
  ring

end

end PanelMoments.SourceLocalJetAlgebra
