import PanelMoments.SourceRelativeTimeJet
import PanelMoments.SourceTimeScaling
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

/-!
# Missing-output derivative at a binary terminal block

The actual terminal time factors are `(1, ε, τ)`, so its output-1 column
vanishes at `ε = 0`. For a fixed completed row `C` and fixed head `h`,
the output-1 derivative of `h diag(X) - C K(ε)` is computed directly
from `SourceHomogeneous.kernel`.

When `C = (s₀, f, s₂) G⁻¹ diag(L(0))`, the derivative is exactly
`-X₁ f`. Only the fixed matrix `G` is inverted; the binary terminal
kernel is never inverted. All baseline denominator conditions are
explicit. This module proves no source-rank, residue, or convergence
statement.
-/

namespace PanelMoments.SourceBinaryTerminalAlgebra

open scoped BigOperators
open SourceHomogeneous

noncomputable section

def terminalTime (τ ε : ℝ) : State 2 → ℝ := ![1, ε, τ]

/-- A common table with the actual terminal time factors. -/
def terminalTable (G : Matrix (State 2) (State 2) ℝ) (τ ε : ℝ) : Table 2 :=
  SourceTimeScaling.scaledTable (fun _ c i => G c i) (terminalTime τ ε)

def baselineForms (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) : State 2 → ℝ :=
  rowForm (terminalTable G τ 0) X 0

def terminalRow (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (head C : State 2 → ℝ) (ε : ℝ) : State 2 → ℝ :=
  Matrix.vecMul head (Matrix.diagonal X) -
    Matrix.vecMul C (kernel (terminalTable G τ ε) X 0)

def canonicalCompleted (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (data : State 2 → ℝ) : State 2 → ℝ :=
  Matrix.vecMul (Matrix.vecMul data G⁻¹) (Matrix.diagonal (baselineForms G X τ))

theorem terminal_rowForm (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ ε : ℝ) (c : State 2) :
    rowForm (terminalTable G τ ε) X 0 c =
      baselineForms G X τ c + ε * (G c 1 * X 1) := by
  simp [baselineForms, rowForm, terminalTable, SourceTimeScaling.scaledTable,
    terminalTime, Fin.sum_univ_succ]
  ring

theorem terminal_missing_formula (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ ε : ℝ) (c : State 2) :
    kernel (terminalTable G τ ε) X 0 c 1 =
      ε * (G c 1 * X 1) /
        (baselineForms G X τ c + ε * (G c 1 * X 1)) := by
  simp only [kernel, Matrix.of_apply, terminal_rowForm]
  simp only [terminalTable, SourceTimeScaling.scaledTable, terminalTime,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  congr 1
  ring

theorem terminal_missing_zero (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (c : State 2) :
    kernel (terminalTable G τ 0) X 0 c 1 = 0 := by
  simp [terminal_missing_formula]

/-- The missing column's actual derivative needs only its baseline row unit. -/
theorem terminal_missing_hasDerivAt (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (c : State 2)
    (hL : baselineForms G X τ c ≠ 0) :
    HasDerivAt (fun ε : ℝ => kernel (terminalTable G τ ε) X 0 c 1)
      (G c 1 * X 1 / baselineForms G X τ c) 0 := by
  have hn : HasDerivAt (fun ε : ℝ => ε * (G c 1 * X 1)) (G c 1 * X 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (G c 1 * X 1)
  have hd : HasDerivAt
      (fun ε : ℝ => baselineForms G X τ c + ε * (G c 1 * X 1))
      (G c 1 * X 1) 0 := hn.const_add (baselineForms G X τ c)
  have hq : HasDerivAt
      (fun ε : ℝ => ε * (G c 1 * X 1) /
        (baselineForms G X τ c + ε * (G c 1 * X 1)))
      (G c 1 * X 1 * baselineForms G X τ c / baselineForms G X τ c ^ 2) 0 := by
    simpa using hn.fun_div hd (by simpa using hL)
  have hc : G c 1 * X 1 * baselineForms G X τ c / baselineForms G X τ c ^ 2 =
      G c 1 * X 1 / baselineForms G X τ c := by
    field_simp [hL]
  apply (hq.congr_deriv hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε => terminal_missing_formula G X τ ε c)

theorem terminalRow_missing_zero (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (head C : State 2 → ℝ) :
    terminalRow G X τ head C 0 1 = head 1 * X 1 := by
  simp only [terminalRow, Pi.sub_apply, Matrix.vecMul_diagonal]
  simp [Matrix.vecMul, dotProduct, terminal_missing_zero]

/-- The completed row and head are fixed while the terminal factor varies. -/
theorem terminalRow_missing_hasDerivAt (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (head C : State 2 → ℝ)
    (hL : ∀ c, baselineForms G X τ c ≠ 0) :
    HasDerivAt (fun ε : ℝ => terminalRow G X τ head C ε 1)
      (-X 1 * ∑ c : State 2, C c * G c 1 / baselineForms G X τ c) 0 := by
  have hs : HasDerivAt
      (fun ε : ℝ => Matrix.vecMul C (kernel (terminalTable G τ ε) X 0) 1)
      (∑ c : State 2, C c * (G c 1 * X 1 / baselineForms G X τ c)) 0 := by
    simp only [Matrix.vecMul, dotProduct]
    exact HasDerivAt.fun_sum (fun c _ =>
      (terminal_missing_hasDerivAt G X τ c (hL c)).const_mul (C c))
  have hf : (∑ c : State 2, C c * (G c 1 * X 1 / baselineForms G X τ c)) =
      X 1 * ∑ c : State 2, C c * G c 1 / baselineForms G X τ c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simpa only [terminalRow, Pi.sub_apply, Matrix.vecMul_diagonal, neg_mul] using
    (hs.congr_deriv hf).const_sub (head 1 * X 1)

/-- The canonical completed row contracts to its data's middle coordinate. -/
theorem canonicalCompleted_contraction (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (data : State 2 → ℝ)
    (hG : G.det ≠ 0) (hL : ∀ c, baselineForms G X τ c ≠ 0) :
    (∑ c : State 2,
      canonicalCompleted G X τ data c * G c 1 / baselineForms G X τ c) = data 1 := by
  calc
    _ = Matrix.vecMul (Matrix.vecMul data G⁻¹) G 1 := by
      simp only [canonicalCompleted, Matrix.vecMul_diagonal]
      simp only [Matrix.vecMul, dotProduct]
      apply Finset.sum_congr rfl
      intro c _
      field_simp [hL c]
    _ = data 1 := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG),
        Matrix.vecMul_one]

/-- For canonical data `(s₀, f, s₂)`, the actual missing-output derivative is `-X₁ f`. -/
theorem canonical_terminalRow_missing_hasDerivAt (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (τ : ℝ) (head : State 2 → ℝ) (s₀ f s₂ : ℝ)
    (hG : G.det ≠ 0) (hL : ∀ c, baselineForms G X τ c ≠ 0) :
    HasDerivAt
      (fun ε : ℝ => terminalRow G X τ head (canonicalCompleted G X τ ![s₀, f, s₂]) ε 1)
      (-X 1 * f) 0 := by
  simpa only [canonicalCompleted_contraction G X τ ![s₀, f, s₂] hG hL,
    Matrix.cons_val_one, Matrix.cons_val_zero] using
    terminalRow_missing_hasDerivAt G X τ head (canonicalCompleted G X τ ![s₀, f, s₂]) hL

end

end PanelMoments.SourceBinaryTerminalAlgebra
