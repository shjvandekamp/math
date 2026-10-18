import PanelMoments.SourceHomogeneous
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

/-!
# Relative-time derivatives of the actual homogeneous kernel

Perturb one actual time block by multiplying its outcome column `b` by
`1 + ε * d b`. For three states, `d = (0, τ, ν)` is the relative-time
curve `(u, v) ↦ (u (1 + τ ε), v (1 + ν ε))` used in the last-time
coalescence check. Other time blocks remain unchanged.

The derivative is proved for the existing `SourceHomogeneous.kernel`,
at every effect point where its baseline row denominator is nonzero.
The final append corollary keeps the fixed prefix correction. No claim
about collision-family independence or its determinant is made here.
-/

namespace PanelMoments.SourceRelativeTimeJet

open scoped BigOperators
open SourceHomogeneous

noncomputable section

/-- Change exactly one time block, keeping the actual table interface. -/
def perturbTable {Q : ℕ} (A : Table Q) (t : ℕ) (d : State Q → ℝ)
    (ε : ℝ) : Table Q :=
  fun s a b => if s = t then A s a b * (1 + ε * d b) else A s a b

theorem perturbTable_zero {Q : ℕ} (A : Table Q) (t : ℕ) (d : State Q → ℝ) :
    perturbTable A t d 0 = A := by
  funext s a b
  simp [perturbTable]

theorem perturbTable_other {Q : ℕ} (A : Table Q) (t s : ℕ)
    (d : State Q → ℝ) (ε : ℝ) (hst : s ≠ t) :
    perturbTable A t d ε s = A s := by
  funext a b
  simp [perturbTable, hst]

def rowFormJet {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (a : State Q) : ℝ :=
  ∑ b : State Q, A t a b * X b * d b

theorem rowForm_perturbTable {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (ε : ℝ) (a : State Q) :
    rowForm (perturbTable A t d ε) X t a =
      rowForm A X t a + ε * rowFormJet A X t d a := by
  unfold rowForm rowFormJet
  simp only [perturbTable, ↓reduceIte]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

def kernelJet {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) : Matrix (State Q) (State Q) ℝ :=
  Matrix.of (fun a b =>
    (A t a b * X b * d b - kernel A X t a b * rowFormJet A X t d a) /
      rowForm A X t a)

/-- An exact finite-parameter formula, prior to differentiating. -/
theorem kernel_perturbTable {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (ε : ℝ) (a b : State Q) :
    kernel (perturbTable A t d ε) X t a b =
      (A t a b * X b + ε * (A t a b * X b * d b)) /
        (rowForm A X t a + ε * rowFormJet A X t d a) := by
  simp only [kernel, Matrix.of_apply, rowForm_perturbTable, perturbTable, ↓reduceIte]
  congr 1
  ring

/-- The actual relative-time derivative, not a formal replacement kernel. -/
theorem kernel_hasDerivAt {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (a b : State Q)
    (hL : rowForm A X t a ≠ 0) :
    HasDerivAt (fun ε : ℝ => kernel (perturbTable A t d ε) X t a b)
      (kernelJet A X t d a b) 0 := by
  have hn : HasDerivAt
      (fun ε : ℝ => A t a b * X b + ε * (A t a b * X b * d b))
      (A t a b * X b * d b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (A t a b * X b * d b)).const_add (A t a b * X b)
  have hd : HasDerivAt
      (fun ε : ℝ => rowForm A X t a + ε * rowFormJet A X t d a)
      (rowFormJet A X t d a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (rowFormJet A X t d a)).const_add (rowForm A X t a)
  have hq : HasDerivAt
      (fun ε : ℝ => (A t a b * X b + ε * (A t a b * X b * d b)) /
        (rowForm A X t a + ε * rowFormJet A X t d a))
      ((A t a b * X b * d b * rowForm A X t a -
        A t a b * X b * rowFormJet A X t d a) / rowForm A X t a ^ 2) 0 := by
    simpa using hn.fun_div hd (by simpa using hL)
  have hc : (A t a b * X b * d b * rowForm A X t a -
      A t a b * X b * rowFormJet A X t d a) / rowForm A X t a ^ 2 =
        kernelJet A X t d a b := by
    simp only [kernelJet, kernel, Matrix.of_apply]
    field_simp [hL]
  apply (hq.congr_deriv hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε => kernel_perturbTable A X t d ε a b)

/-- Clearing the two baseline row denominators gives a polynomial identity. -/
theorem kernelJet_cleared {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (a b : State Q)
    (hL : rowForm A X t a ≠ 0) :
    rowForm A X t a ^ 2 * kernelJet A X t d a b =
      A t a b * X b *
        (d b * rowForm A X t a - rowFormJet A X t d a) := by
  simp only [kernelJet, kernel, Matrix.of_apply]
  field_simp [hL]

theorem kernelJet_row_sum {Q : ℕ} (A : Table Q) (X : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (a : State Q)
    (hL : rowForm A X t a ≠ 0) :
    ∑ b : State Q, kernelJet A X t d a b = 0 := by
  have hs : ∑ b : State Q, kernel A X t a b = 1 := by
    simp only [kernel, Matrix.of_apply, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hL
  simp only [kernelJet, Matrix.of_apply, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_sub_distrib]
  rw [hs]
  change (rowFormJet A X t d a - 1 * rowFormJet A X t d a) *
    (rowForm A X t a)⁻¹ = 0
  simp

theorem vecMul_kernel_hasDerivAt {Q : ℕ} (A : Table Q) (X R : State Q → ℝ)
    (t : ℕ) (d : State Q → ℝ) (b : State Q)
    (hL : ∀ a, rowForm A X t a ≠ 0) :
    HasDerivAt
      (fun ε : ℝ => Matrix.vecMul R (kernel (perturbTable A t d ε) X t) b)
      (Matrix.vecMul R (kernelJet A X t d) b) 0 := by
  simp only [Matrix.vecMul, dotProduct]
  exact HasDerivAt.fun_sum (fun a _ => (kernel_hasDerivAt A X t d a b (hL a)).const_mul (R a))

/-- For fixed old rows, the actual append derivative retains `R - I`.
This is the kernel operation appearing in the copied-source prefix identity. -/
theorem prefix_corrected_append_hasDerivAt {Q : ℕ} (A : Table Q)
    (X R I : State Q → ℝ) (t : ℕ) (d : State Q → ℝ) (b : State Q)
    (hL : ∀ a, rowForm A X t a ≠ 0) :
    HasDerivAt
      (fun ε : ℝ => I b + Matrix.vecMul (R - I)
        (kernel (perturbTable A t d ε) X t) b)
      (Matrix.vecMul (R - I) (kernelJet A X t d) b) 0 :=
  (vecMul_kernel_hasDerivAt A X (R - I) t d b hL).const_add (I b)

def relativeDirection (τ ν : ℝ) : State 2 → ℝ := ![0, τ, ν]

theorem rowFormJet_relativeDirection (A : Table 2) (X : State 2 → ℝ)
    (t : ℕ) (τ ν : ℝ) (a : State 2) :
    rowFormJet A X t (relativeDirection τ ν) a =
      τ * A t a 1 * X 1 + ν * A t a 2 * X 2 := by
  simp [rowFormJet, relativeDirection, Fin.sum_univ_succ]
  ring

end

end PanelMoments.SourceRelativeTimeJet
