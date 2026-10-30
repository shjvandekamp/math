import PanelMoments.SourcePolynomialKernels

set_option autoImplicit false

/-!
# Repeated rank-one values of the actual cleared source kernels

At a zero of one row form, the existing polynomial-cleared kernel has only
that row remaining. Its scalar factor is the product of the other row forms;
its row is the actual numerator `A t c j * X j`. This statement evaluates
polynomials, rather than a rational expression with a zero denominator.

The surviving matrix is `e_c` times that row. Its arbitrary positive-length
powers, with an initial row and an arbitrary final matrix, have an explicit
scalar factor. The same identity applies to actual cleared word products
whose time blocks agree. Nonvanishing follows from the stated nonzero scalar
and final-row hypotheses. No residue extraction, generic existence, or source
independence theorem is asserted here.
-/

namespace PanelMoments.SourceRepeatedPoleAlgebra

open scoped BigOperators
open SourceHomogeneous SourcePolynomialKernels

noncomputable section

def rowNumerator (A : Table 2) (X : State 2 → ℝ) (t : ℕ) (c : State 2) :
    State 2 → ℝ := fun j => A t c j * X j

def rowPoleScale (A : Table 2) (X : State 2 → ℝ) (t : ℕ) (c : State 2) : ℝ :=
  ∏ b ∈ Finset.univ.erase c, rowForm A X t b

/-- The rank-one matrix `e_c` times `w`, in the existing matrix interface. -/
def rowMatrix (c : State 2) (w : State 2 → ℝ) : Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun i j => if i = c then w j else 0)

theorem vecMul_rowMatrix (u w : State 2 → ℝ) (c : State 2) :
    Matrix.vecMul u (rowMatrix c w) = u c • w := by
  ext j
  simp [Matrix.vecMul, dotProduct, rowMatrix, mul_ite]

theorem rowMatrix_mul (w z : State 2 → ℝ) (c : State 2) :
    rowMatrix c w * rowMatrix c z = w c • rowMatrix c z := by
  ext i j
  by_cases hi : i = c
  · subst i
    simp [Matrix.mul_apply, rowMatrix, mul_ite]
  · simp [Matrix.mul_apply, rowMatrix, hi]

theorem rowMatrix_pow_succ (w : State 2 → ℝ) (c : State 2) (n : ℕ) :
    rowMatrix c w ^ (n + 1) = w c ^ n • rowMatrix c w := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, smul_mul_assoc, rowMatrix_mul, smul_smul, pow_succ]

theorem vecMul_rowMatrix_pow_succ (u w : State 2 → ℝ) (c : State 2) (n : ℕ) :
    Matrix.vecMul u (rowMatrix c w ^ (n + 1)) = (u c * w c ^ n) • w := by
  rw [rowMatrix_pow_succ, Matrix.vecMul_smul, vecMul_rowMatrix, smul_smul]
  congr 1
  ring

theorem vecMul_rowMatrix_pow (u w : State 2 → ℝ) (c : State 2)
    (n : ℕ) (hn : 1 ≤ n) :
    Matrix.vecMul u (rowMatrix c w ^ n) = (u c * w c ^ (n - 1)) • w := by
  cases n with
  | zero => omega
  | succ n => simpa using vecMul_rowMatrix_pow_succ u w c n

theorem vecMul_rowMatrix_pow_right (u w : State 2 → ℝ) (c : State 2)
    (V : Matrix (State 2) (State 2) ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Matrix.vecMul (Matrix.vecMul u (rowMatrix c w ^ n)) V =
      (u c * w c ^ (n - 1)) • Matrix.vecMul w V := by
  rw [vecMul_rowMatrix_pow u w c n hn, Matrix.smul_vecMul]

theorem vecMul_rowMatrix_pow_right_ne_zero (u w : State 2 → ℝ) (c : State 2)
    (V : Matrix (State 2) (State 2) ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hu : u c ≠ 0) (hw : w c ≠ 0) (hV : Matrix.vecMul w V ≠ 0) :
    Matrix.vecMul (Matrix.vecMul u (rowMatrix c w ^ n)) V ≠ 0 := by
  rw [vecMul_rowMatrix_pow_right u w c V n hn]
  exact smul_ne_zero (mul_ne_zero hu (pow_ne_zero _ hw)) hV

theorem vecMul_scaled_rowMatrix_pow_right (u w : State 2 → ℝ) (c : State 2)
    (s : ℝ) (V : Matrix (State 2) (State 2) ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Matrix.vecMul (Matrix.vecMul u ((s • rowMatrix c w) ^ n)) V =
      (s ^ n * u c * w c ^ (n - 1)) • Matrix.vecMul w V := by
  rw [smul_pow, Matrix.vecMul_smul, Matrix.smul_vecMul,
    vecMul_rowMatrix_pow_right u w c V n hn, smul_smul]
  congr 1
  ring

/-- Only the numerator row `c` survives polynomial evaluation at its row pole. -/
theorem clearedKernel_eval_at_rowPole (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (c : State 2) (hc : rowForm A X t c = 0) :
    evalMatrix X (clearedKernel A t) =
      rowPoleScale A X t c • rowMatrix c (rowNumerator A X t c) := by
  ext i j
  simp only [evalMatrix_apply, clearedKernel, Matrix.of_apply, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, rowPolynomial_eval,
    Matrix.smul_apply, smul_eq_mul, rowMatrix, Matrix.of_apply]
  by_cases hi : i = c
  · subst i
    simp only [↓reduceIte, rowPoleScale, rowNumerator]
    ring
  · have hz : (∏ b ∈ Finset.univ.erase i, rowForm A X t b) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ c⟩) hc
    simp only [hi, ↓reduceIte, hz, mul_zero]

theorem rowPoleScale_ne_zero (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (c : State 2) (hL : ∀ b, b ≠ c → rowForm A X t b ≠ 0) :
    rowPoleScale A X t c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  exact hL b (Finset.mem_erase.mp hb).1

/-- Dividing out the other row forms gives the actual rank-one numerator. -/
theorem normalized_clearedKernel_at_rowPole (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (c : State 2) (hc : rowForm A X t c = 0)
    (hL : ∀ b, b ≠ c → rowForm A X t b ≠ 0) :
    (rowPoleScale A X t c)⁻¹ • evalMatrix X (clearedKernel A t) =
      rowMatrix c (rowNumerator A X t c) := by
  rw [clearedKernel_eval_at_rowPole A X t c hc, smul_smul,
    inv_mul_cancel₀ (rowPoleScale_ne_zero A X t c hL), one_smul]

theorem clearedKernel_pow_at_rowPole (A : Table 2) (X u : State 2 → ℝ)
    (t : ℕ) (c : State 2) (V : Matrix (State 2) (State 2) ℝ)
    (n : ℕ) (hn : 1 ≤ n) (hc : rowForm A X t c = 0) :
    Matrix.vecMul (Matrix.vecMul u (evalMatrix X (clearedKernel A t) ^ n)) V =
      (rowPoleScale A X t c ^ n * u c * rowNumerator A X t c c ^ (n - 1)) •
        Matrix.vecMul (rowNumerator A X t c) V := by
  rw [clearedKernel_eval_at_rowPole A X t c hc]
  exact vecMul_scaled_rowMatrix_pow_right u (rowNumerator A X t c) c
    (rowPoleScale A X t c) V n hn

theorem clearedKernel_pow_at_rowPole_ne_zero (A : Table 2) (X u : State 2 → ℝ)
    (t : ℕ) (c : State 2) (V : Matrix (State 2) (State 2) ℝ)
    (n : ℕ) (hn : 1 ≤ n) (hc : rowForm A X t c = 0)
    (hL : ∀ b, b ≠ c → rowForm A X t b ≠ 0)
    (hu : u c ≠ 0) (hw : rowNumerator A X t c c ≠ 0)
    (hV : Matrix.vecMul (rowNumerator A X t c) V ≠ 0) :
    Matrix.vecMul (Matrix.vecMul u (evalMatrix X (clearedKernel A t) ^ n)) V ≠ 0 := by
  rw [clearedKernel_pow_at_rowPole A X u t c V n hn hc]
  exact smul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (rowPoleScale_ne_zero A X t c hL)) hu)
      (pow_ne_zero _ hw)) hV

/-- Equal actual time blocks give the corresponding repeated cleared product. -/
theorem clearedWordProduct_eval_repeated {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (w : List (Fin N)) (t : ℕ) (hA : ∀ k ∈ w, A (k.val + 2) = A t) :
    evalMatrix X (clearedWordProduct A w) =
      evalMatrix X (clearedKernel A t) ^ w.length := by
  induction w with
  | nil => simp [clearedWordProduct]
  | cons k w ih =>
      have hk : clearedKernel A (k.val + 2) = clearedKernel A t := by
        ext i j
        simp only [clearedKernel, Matrix.of_apply, rowPolynomial, hA k (by simp)]
      have hw := ih (fun j hj => hA j (by simp [hj]))
      change evalMatrix X (clearedKernel A (k.val + 2) * clearedWordProduct A w) = _
      rw [map_mul, hk, hw, List.length_cons, pow_succ']

theorem clearedWordProduct_at_rowPole {N : ℕ} (A : Table 2) (X u : State 2 → ℝ)
    (w : List (Fin N)) (t : ℕ) (c : State 2) (V : Matrix (State 2) (State 2) ℝ)
    (hw : 1 ≤ w.length) (hA : ∀ k ∈ w, A (k.val + 2) = A t)
    (hc : rowForm A X t c = 0) :
    Matrix.vecMul (Matrix.vecMul u (evalMatrix X (clearedWordProduct A w))) V =
      (rowPoleScale A X t c ^ w.length * u c *
        rowNumerator A X t c c ^ (w.length - 1)) •
        Matrix.vecMul (rowNumerator A X t c) V := by
  rw [clearedWordProduct_eval_repeated A X w t hA]
  exact clearedKernel_pow_at_rowPole A X u t c V w.length hw hc

theorem clearedWordProduct_at_rowPole_ne_zero {N : ℕ} (A : Table 2)
    (X u : State 2 → ℝ) (w : List (Fin N)) (t : ℕ) (c : State 2)
    (V : Matrix (State 2) (State 2) ℝ) (hw : 1 ≤ w.length)
    (hA : ∀ k ∈ w, A (k.val + 2) = A t) (hc : rowForm A X t c = 0)
    (hL : ∀ b, b ≠ c → rowForm A X t b ≠ 0)
    (hu : u c ≠ 0) (hnum : rowNumerator A X t c c ≠ 0)
    (hV : Matrix.vecMul (rowNumerator A X t c) V ≠ 0) :
    Matrix.vecMul (Matrix.vecMul u (evalMatrix X (clearedWordProduct A w))) V ≠ 0 := by
  rw [clearedWordProduct_eval_repeated A X w t hA]
  exact clearedKernel_pow_at_rowPole_ne_zero A X u t c V w.length hw hc hL hu hnum hV

end

end PanelMoments.SourceRepeatedPoleAlgebra
