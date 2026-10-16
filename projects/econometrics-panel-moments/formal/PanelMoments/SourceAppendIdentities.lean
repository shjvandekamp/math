import PanelMoments.SourceCoordinateFactors

set_option autoImplicit false

/-!
# Exact append identities for the actual fixed-transition block

The table below is `G* diag(1, ε, v)` with rows `(1, ε, v)`,
`(1, 2ε, v)`, and `(1, 3ε, 2v)`. All matrix operations use the
existing homogeneous model kernel and its polynomial clearing.

At `ε = 0`, a zero-sum row appends to a scalar multiple of
`e₂ - e₀`; an old scalar-kernel row therefore appends to zero.
The cleared first splitting identity is exact for every `ε`.

The last lemmas factor the actual cleared matrix on a row-form zero
and prove the output-divided cancellation underlying the new-pole
invariants. They do not define a residue operator or formalize an
asymptotic rank argument.
-/

namespace PanelMoments.SourceAppendIdentities

open scoped BigOperators
open SourceHomogeneous SourcePolynomialKernels

noncomputable section

def gamma : State 2 → ℝ := ![1, 2, 3]

def delta : State 2 → ℝ := ![1, 1, 2]

/-- The actual three-state block used in the boundary extension. -/
def blockTable (ε v : ℝ) : Table 2 :=
  fun _ a => ![1, gamma a * ε, delta a * v]

theorem block_rowForm (ε v : ℝ) (X : State 2 → ℝ) (t : ℕ) (a : State 2) :
    rowForm (blockTable ε v) X t a =
      X 0 + gamma a * ε * X 1 + delta a * v * X 2 := by
  simp [rowForm, blockTable, Fin.sum_univ_succ]
  ring

theorem kernel_eq_block_of_entries (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (ε v : ℝ)
    (hA : ∀ a i, A t a i = blockTable ε v 0 a i) :
    kernel A X t = kernel (blockTable ε v) X 0 := by
  ext a i
  simp only [kernel, Matrix.of_apply, rowForm]
  simp_rw [hA]

def appendRow (ε v : ℝ) (X R : State 2 → ℝ) : State 2 → ℝ :=
  Matrix.vecMul R (kernel (blockTable ε v) X 0)

theorem homogeneousWordProduct_append {N : ℕ} (A : Table 2)
    (X : State 2 → ℝ) (w : List (Fin N)) (u : Fin N) :
    homogeneousWordProduct A X (w ++ [u]) =
      homogeneousWordProduct A X w * kernel A X (u.val + 2) := by
  simp [homogeneousWordProduct, List.map_append, List.prod_append]

/-- The append operation is the final factor of the actual ordered model word. -/
theorem actual_word_append_block {N : ℕ} (A : Table 2)
    (X R : State 2 → ℝ) (w : List (Fin N)) (u : Fin N) (ε v : ℝ)
    (hA : ∀ a i, A (u.val + 2) a i = blockTable ε v 0 a i) :
    Matrix.vecMul R (homogeneousWordProduct A X (w ++ [u])) =
      appendRow ε v X (Matrix.vecMul R (homogeneousWordProduct A X w)) := by
  rw [homogeneousWordProduct_append, kernel_eq_block_of_entries A X _ ε v hA]
  exact (Matrix.vecMul_vecMul _ _ _).symm

def boundaryMultiplier (v : ℝ) (X : State 2 → ℝ) : ℝ :=
  v * X 0 * X 2 / ((X 0 + v * X 2) * (X 0 + 2 * v * X 2))

theorem boundary_append_formula (v : ℝ) (X R : State 2 → ℝ)
    (hR : ∑ a : State 2, R a = 0)
    (hL₀ : X 0 + v * X 2 ≠ 0) (hL₂ : X 0 + 2 * v * X 2 ≠ 0) :
    appendRow 0 v X R =
      ![-(boundaryMultiplier v X * R 2), 0, boundaryMultiplier v X * R 2] := by
  have hsum : R 0 + R 1 + R 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hR
  have hzero : R 0 = -R 1 - R 2 := by linarith
  have hL₀' : v * X 2 + X 0 ≠ 0 := by simpa [add_comm] using hL₀
  have hL₂' : X 0 + v * X 2 * 2 ≠ 0 := by
    convert hL₂ using 1 <;> ring
  have hL₂'' : v * X 2 * 2 + X 0 ≠ 0 := by simpa [add_comm] using hL₂'
  funext i
  fin_cases i <;>
    simp [appendRow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, kernel,
      blockTable, block_rowForm, gamma, delta, boundaryMultiplier, hzero] <;>
    field_simp [hL₀, hL₀', hL₂, hL₂', hL₂''] <;> ring

/-- The boundary annihilates the whole old scalar-kernel row. -/
theorem boundary_append_zero (v : ℝ) (X R : State 2 → ℝ)
    (hR : ∑ a : State 2, R a = 0) (hR₂ : R 2 = 0) :
    appendRow 0 v X R = 0 := by
  have hsum : R 0 + R 1 + R 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hR
  have hzero : R 0 = -R 1 := by linarith
  funext i
  fin_cases i <;>
    simp [appendRow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, kernel,
      blockTable, block_rowForm, gamma, delta, hzero, hR₂]

def rowCofactor (A : Table 2) (X : State 2 → ℝ) (t : ℕ) (a : State 2) : ℝ :=
  ∏ b ∈ Finset.univ.erase a, rowForm A X t b

theorem rowCofactor_zero (A : Table 2) (X : State 2 → ℝ) (t : ℕ) :
    rowCofactor A X t 0 = rowForm A X t 1 * rowForm A X t 2 := by
  have h : (Finset.univ : Finset (State 2)).erase 0 = {1, 2} := by decide
  simp [rowCofactor, h]

theorem rowCofactor_one (A : Table 2) (X : State 2 → ℝ) (t : ℕ) :
    rowCofactor A X t 1 = rowForm A X t 0 * rowForm A X t 2 := by
  have h : (Finset.univ : Finset (State 2)).erase 1 = {0, 2} := by decide
  simp [rowCofactor, h]

/-- The output coordinate has been removed from the actual cleared entry. -/
def dividedClearedKernel (A : Table 2) (X : State 2 → ℝ) (t : ℕ) :
    Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun a i => A t a i * rowCofactor A X t a)

theorem clearedKernel_eval_coordinate_factor (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (a i : State 2) :
    evalMatrix X (clearedKernel A t) a i = X i * dividedClearedKernel A X t a i := by
  simp only [evalMatrix_apply, clearedKernel, dividedClearedKernel, Matrix.of_apply,
    map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X,
    rowPolynomial_eval, rowCofactor]
  ring

theorem cleared_vecMul_coordinate_factor (A : Table 2) (X R : State 2 → ℝ)
    (t : ℕ) (i : State 2) :
    Matrix.vecMul R (evalMatrix X (clearedKernel A t)) i =
      X i * Matrix.vecMul R (dividedClearedKernel A X t) i := by
  simp only [Matrix.vecMul_apply_eq_sum, clearedKernel_eval_coordinate_factor,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

def clearedAppendRow (ε v : ℝ) (X R : State 2 → ℝ) : State 2 → ℝ :=
  Matrix.vecMul R (evalMatrix X (clearedKernel (blockTable ε v) 0))

/-- This is the cleared actual kernel product, including at the merged boundary. -/
theorem cleared_append_scalar_split (ε v : ℝ) (X R : State 2 → ℝ)
    (hR : ∑ a : State 2, R a = 0) (hR₂ : R 2 = 0) :
    clearedAppendRow ε v X R 2 =
      -ε * v * X 1 * X 2 * rowForm (blockTable ε v) X 0 2 * R 1 := by
  have hsum : R 0 + R 1 + R 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hR
  have hzero : R 0 = -R 1 := by linarith
  rw [clearedAppendRow, cleared_vecMul_coordinate_factor]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, dividedClearedKernel,
    hzero, hR₂, rowCofactor_zero, rowCofactor_one, blockTable, block_rowForm,
    gamma, delta]
  ring

/-- The same identity for the rational actual kernel wherever its row forms are units. -/
theorem denominator_mul_append_scalar_split (ε v : ℝ) (X R : State 2 → ℝ)
    (hR : ∑ a : State 2, R a = 0) (hR₂ : R 2 = 0)
    (hL : ∀ a, rowForm (blockTable ε v) X 0 a ≠ 0) :
    MvPolynomial.eval X (blockDenominator (blockTable ε v) 0) * appendRow ε v X R 2 =
      -ε * v * X 1 * X 2 * rowForm (blockTable ε v) X 0 2 * R 1 := by
  have h := cleared_append_scalar_split ε v X R hR hR₂
  rw [clearedAppendRow, clearedKernel_eval_of_nonzero _ _ _ hL,
    Matrix.vecMul_smul] at h
  exact h

theorem rowCofactor_eq_zero_of_other_row_zero (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (a c : State 2) (hac : a ≠ c) (hc : rowForm A X t c = 0) :
    rowCofactor A X t a = 0 := by
  exact Finset.prod_eq_zero (by simp [Ne.symm hac]) hc

/-- On a row-form zero, only its own summand remains in the cleared actual product. -/
theorem divided_cleared_pole_factorization (A : Table 2) (X R : State 2 → ℝ)
    (t : ℕ) (c i : State 2) (hc : rowForm A X t c = 0) :
    Matrix.vecMul R (dividedClearedKernel A X t) i =
      R c * A t c i * rowCofactor A X t c := by
  rw [Matrix.vecMul_apply_eq_sum]
  calc
    (∑ a : State 2, R a * dividedClearedKernel A X t a i) =
        R c * dividedClearedKernel A X t c i := by
      apply Finset.sum_eq_single c
      · intro a _ hac
        simp [dividedClearedKernel, rowCofactor_eq_zero_of_other_row_zero A X t a c hac hc]
      · intro h
        exact (h (Finset.mem_univ c)).elim
    _ = _ := by simp [dividedClearedKernel]; ring

/-- Output division is explicit and performed before the pole evaluation.
This is the algebraic invariant cancellation for every actual row ending in the block. -/
theorem endBlock_outputDivided_pole_cancellation (ε v : ℝ) (X R : State 2 → ℝ)
    (c : State 2) (hc : rowForm (blockTable ε v) X 0 c = 0) :
    delta c * v * Matrix.vecMul R (dividedClearedKernel (blockTable ε v) X 0) 1 -
      gamma c * ε * Matrix.vecMul R (dividedClearedKernel (blockTable ε v) X 0) 2 = 0 := by
  rw [divided_cleared_pole_factorization _ _ _ _ _ _ hc,
    divided_cleared_pole_factorization _ _ _ _ _ _ hc]
  simp [blockTable]
  ring

end

end PanelMoments.SourceAppendIdentities
