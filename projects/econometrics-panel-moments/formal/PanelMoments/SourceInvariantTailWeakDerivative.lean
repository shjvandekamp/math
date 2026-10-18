import PanelMoments.SourceRelativeTimeJet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# IT13 from derivatives of the actual perturbed homogeneous kernels

The table is `Gᵢⱼ timeⱼ`, where `G = I + 11ᵀ` and the actual time
factors are `(1,A,b δ)`. With `X = (1,-r,r-z)`, `K` is defined directly
through `SourceHomogeneous.kernel`. Its binary row forms are
`(2-Ar,1-2Ar,1-Ar)`.

The missing-column derivative is `b (r-z) u`, where
`u = (1/l₀,1/l₁,2/l₂)`. The product rule for the completed H/J rows
then gives IT13: the earlier factor's derivative is multiplied by the
last kernel's zero column. No differentiability or rank premise is
assumed; the only analytic hypotheses are the displayed binary row-form
units. All parameters below are arbitrary real numbers.

The H/J derivatives first concern completed rows. The actual displayed
source rows are their fixed retained heads minus the completed rows,
so their missing-output derivatives have the opposite sign. The final
normalization statements require `r ≠ z` and keep this sign explicit.
No identification with a complete source-family coefficient indexing,
finite coefficient matrix, or all-length rank theorem is asserted.
-/

namespace PanelMoments.SourceInvariantTailWeakDerivative

open scoped BigOperators
open SourceHomogeneous

noncomputable section

def G : Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun i j => 1 + if i = j then 1 else 0)

def X (z r : ℝ) : State 2 → ℝ := ![1, -r, r - z]
def v (z r : ℝ) : State 2 → ℝ := ![z, -r, r - z]
def timeFactors (A b δ : ℝ) : State 2 → ℝ := ![1, A, b * δ]

def actualTable (A b δ : ℝ) : Table 2 :=
  fun _ i j => G i j * timeFactors A b δ j

def actualRowForm (A b z r δ : ℝ) (i : State 2) : ℝ :=
  SourceHomogeneous.rowForm (actualTable A b δ) (X z r) 0 i

/-- This is the existing homogeneous kernel applied to the actual time table. -/
def K (A b z r δ : ℝ) : Matrix (State 2) (State 2) ℝ :=
  SourceHomogeneous.kernel (actualTable A b δ) (X z r) 0

def rowForms (A r : ℝ) : State 2 → ℝ :=
  ![2 - A * r, 1 - 2 * A * r, 1 - A * r]

def binaryScale (A r : ℝ) : State 2 → ℝ := ![1, -A * r, 0]
def scaleJet (b z r : ℝ) : State 2 → ℝ := ![0, 0, b * (r - z)]
def formJet (b z r : ℝ) (i : State 2) : ℝ := b * (r - z) * G i 2

def binaryK (A r : ℝ) : Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun i j => G i j * binaryScale A r j / rowForms A r i)

def u (A r : ℝ) : State 2 → ℝ :=
  ![1 / rowForms A r 0, 1 / rowForms A r 1, 2 / rowForms A r 2]

def kernelJet (A b z r : ℝ) (i j : State 2) : ℝ :=
  ((G i j * scaleJet b z r j) * rowForms A r i -
    (G i j * binaryScale A r j) * formJet b z r i) / rowForms A r i ^ 2

def prefixNumerator (z r : ℝ) : State 2 → ℝ := ![2, -r, r - z]

def mu (A b z r δ : ℝ) (c : State 2) : ℝ :=
  prefixNumerator z r c / actualRowForm A b z r δ c

def binaryMu (A z r : ℝ) (c : State 2) : ℝ :=
  prefixNumerator z r c / rowForms A r c

def completedH (A B bA bB z r δ : ℝ) (c j : State 2) : ℝ :=
  X z r c * ∑ i : State 2, K A bA z r δ c i * K B bB z r δ i j

def completedJ (A B bA bB z r δ : ℝ) (c j : State 2) : ℝ :=
  mu A bA z r δ c * ∑ i : State 2, v z r i * K B bB z r δ i j

def weakH (A B bB z r : ℝ) (c : State 2) : ℝ :=
  bB * X z r c * ∑ i : State 2, binaryK A r c i * u B r i

def weakJ (A B bB z r : ℝ) (c : State 2) : ℝ :=
  bB * binaryMu A z r c * ∑ i : State 2, v z r i * u B r i

def retainedH (z r : ℝ) (c j : State 2) : ℝ := if c = j then X z r c else 0

def sourceH (A B bA bB z r δ : ℝ) (c j : State 2) : ℝ :=
  retainedH z r c j - completedH A B bA bB z r δ c j

def sourceJ (A B bA bB z r δ : ℝ) (c j : State 2) : ℝ :=
  0 - completedJ A B bA bB z r δ c j

theorem kernel_eq_homogeneous (A b z r δ : ℝ) :
    K A b z r δ = SourceHomogeneous.kernel (actualTable A b δ) (X z r) 0 := rfl

theorem completedH_eq_matrix_product (A B bA bB z r δ : ℝ) (c j : State 2) :
    completedH A B bA bB z r δ c j =
      X z r c * (K A bA z r δ * K B bB z r δ) c j := rfl

theorem completedJ_eq_vecMul (A B bA bB z r δ : ℝ) (c j : State 2) :
    completedJ A B bA bB z r δ c j =
      mu A bA z r δ c * Matrix.vecMul (v z r) (K B bB z r δ) j := rfl

theorem actualRowForm_eq (A b z r δ : ℝ) (i : State 2) :
    actualRowForm A b z r δ i = rowForms A r i + δ * formJet b z r i := by
  fin_cases i <;>
    simp [actualRowForm, SourceHomogeneous.rowForm, actualTable,
      G, timeFactors, X, rowForms, formJet, Fin.sum_univ_succ] <;> ring

theorem kernel_affine_formula (A b z r δ : ℝ) (i j : State 2) :
    K A b z r δ i j =
      (G i j * binaryScale A r j + δ * (G i j * scaleJet b z r j)) /
        (rowForms A r i + δ * formJet b z r i) := by
  change G i j * timeFactors A b δ j * X z r j / actualRowForm A b z r δ i = _
  rw [actualRowForm_eq]
  congr 1
  fin_cases j <;> simp [timeFactors, X, binaryScale, scaleJet] <;> ring

theorem kernel_zero (A b z r : ℝ) : K A b z r 0 = binaryK A r := by
  ext i j
  simp [kernel_affine_formula, binaryK]

theorem kernel_missing_formula (A b z r δ : ℝ) (i : State 2) :
    K A b z r δ i 2 =
      δ * formJet b z r i / (rowForms A r i + δ * formJet b z r i) := by
  rw [kernel_affine_formula]
  simp [binaryScale, scaleJet, formJet]
  congr 1
  ring

theorem kernel_missing_zero (A b z r : ℝ) (i : State 2) :
    K A b z r 0 i 2 = 0 := by
  simp [kernel_missing_formula]

theorem u_eq_last_column (A r : ℝ) (i : State 2) :
    u A r i = G i 2 / rowForms A r i := by
  fin_cases i <;> norm_num [u, G]

private theorem affine_quotient_hasDerivAt (n₀ n₁ d₀ d₁ : ℝ) (hd : d₀ ≠ 0) :
    HasDerivAt (fun δ : ℝ => (n₀ + δ * n₁) / (d₀ + δ * d₁))
      ((n₁ * d₀ - n₀ * d₁) / d₀ ^ 2) 0 := by
  have hn : HasDerivAt (fun δ : ℝ => n₀ + δ * n₁) n₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const n₁).const_add n₀
  have hd' : HasDerivAt (fun δ : ℝ => d₀ + δ * d₁) d₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d₁).const_add d₀
  simpa using hn.fun_div hd' (by simpa using hd)

/-- Every entry is differentiable using only its binary row-form unit. -/
theorem kernel_hasDerivAt (A b z r : ℝ) (i j : State 2)
    (hL : rowForms A r i ≠ 0) :
    HasDerivAt (fun δ : ℝ => K A b z r δ i j) (kernelJet A b z r i j) 0 := by
  apply (affine_quotient_hasDerivAt (G i j * binaryScale A r j)
    (G i j * scaleJet b z r j) (rowForms A r i) (formJet b z r i) hL).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun δ => kernel_affine_formula A b z r δ i j)

theorem kernelJet_missing_eq (A b z r : ℝ) (i : State 2)
    (hL : rowForms A r i ≠ 0) :
    kernelJet A b z r i 2 = b * (r - z) * u A r i := by
  rw [u_eq_last_column]
  simp [kernelJet, binaryScale, scaleJet]
  field_simp [hL]

theorem kernel_missing_hasDerivAt (A b z r : ℝ) (i : State 2)
    (hL : rowForms A r i ≠ 0) :
    HasDerivAt (fun δ : ℝ => K A b z r δ i 2) (b * (r - z) * u A r i) 0 :=
  (kernel_hasDerivAt A b z r i 2 hL).congr_deriv (kernelJet_missing_eq A b z r i hL)

theorem mu_zero (A b z r : ℝ) (c : State 2) :
    mu A b z r 0 c = binaryMu A z r c := by
  simp [mu, binaryMu, actualRowForm_eq]

theorem mu_hasDerivAt (A b z r : ℝ) (c : State 2)
    (hL : rowForms A r c ≠ 0) :
    HasDerivAt (fun δ : ℝ => mu A b z r δ c)
      (-(prefixNumerator z r c * formJet b z r c) / rowForms A r c ^ 2) 0 := by
  have h := affine_quotient_hasDerivAt (prefixNumerator z r c) 0
    (rowForms A r c) (formJet b z r c) hL
  simp only [mul_zero, add_zero, zero_mul, zero_sub] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun δ => by simp [mu, actualRowForm_eq])

/-- The derivative of the earlier factor vanishes against the last zero column. -/
theorem completedH_missing_hasDerivAt (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) :
    HasDerivAt (fun δ : ℝ => completedH A B bA bB z r δ c 2)
      ((r - z) * weakH A B bB z r c) 0 := by
  have hs : HasDerivAt
      (fun δ : ℝ => ∑ i : State 2, K A bA z r δ c i * K B bB z r δ i 2)
      (∑ i : State 2, K A bA z r 0 c i * (bB * (r - z) * u B r i)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [kernel_missing_zero, mul_zero, zero_add] using
      (kernel_hasDerivAt A bA z r c i hA).fun_mul
        (kernel_missing_hasDerivAt B bB z r i (hB i))
  have hc : X z r c *
      (∑ i : State 2, K A bA z r 0 c i * (bB * (r - z) * u B r i)) =
      (r - z) * weakH A B bB z r c := by
    simp only [weakH, kernel_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (hs.const_mul (X z r c)).congr_deriv hc

/-- The derivative of μ also vanishes against the last zero column. -/
theorem completedJ_missing_hasDerivAt (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) :
    HasDerivAt (fun δ : ℝ => completedJ A B bA bB z r δ c 2)
      ((r - z) * weakJ A B bB z r c) 0 := by
  have hs : HasDerivAt
      (fun δ : ℝ => ∑ i : State 2, v z r i * K B bB z r δ i 2)
      (∑ i : State 2, v z r i * (bB * (r - z) * u B r i)) 0 := by
    exact HasDerivAt.fun_sum (fun i _ =>
      (kernel_missing_hasDerivAt B bB z r i (hB i)).const_mul (v z r i))
  have hp : HasDerivAt (fun δ : ℝ => completedJ A B bA bB z r δ c 2)
      (binaryMu A z r c * ∑ i : State 2, v z r i * (bB * (r - z) * u B r i)) 0 := by
    simpa only [completedJ, kernel_missing_zero, mul_zero, Finset.sum_const_zero,
      zero_mul, zero_add, mu_zero] using (mu_hasDerivAt A bA z r c hA).fun_mul hs
  have hc : binaryMu A z r c *
      (∑ i : State 2, v z r i * (bB * (r - z) * u B r i)) =
      (r - z) * weakJ A B bB z r c := by
    simp only [weakJ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact hp.congr_deriv hc

/-- Actual source = retained head minus completed row; the sign is negative. -/
theorem sourceH_missing_hasDerivAt (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) :
    HasDerivAt (fun δ : ℝ => sourceH A B bA bB z r δ c 2)
      (-((r - z) * weakH A B bB z r c)) 0 :=
  (completedH_missing_hasDerivAt A B bA bB z r c hA hB).const_sub (retainedH z r c 2)

/-- The J head is zero, so the actual J source has the same negative sign. -/
theorem sourceJ_missing_hasDerivAt (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) :
    HasDerivAt (fun δ : ℝ => sourceJ A B bA bB z r δ c 2)
      (-((r - z) * weakJ A B bB z r c)) 0 :=
  (completedJ_missing_hasDerivAt A B bA bB z r c hA hB).const_sub 0

theorem completedH_normalized_deriv (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) (hrz : r ≠ z) :
    deriv (fun δ : ℝ => completedH A B bA bB z r δ c 2) 0 / (r - z) =
      weakH A B bB z r c := by
  rw [(completedH_missing_hasDerivAt A B bA bB z r c hA hB).deriv]
  field_simp [sub_ne_zero.mpr hrz]

theorem completedJ_normalized_deriv (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) (hrz : r ≠ z) :
    deriv (fun δ : ℝ => completedJ A B bA bB z r δ c 2) 0 / (r - z) =
      weakJ A B bB z r c := by
  rw [(completedJ_missing_hasDerivAt A B bA bB z r c hA hB).deriv]
  field_simp [sub_ne_zero.mpr hrz]

theorem sourceH_normalized_deriv (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) (hrz : r ≠ z) :
    deriv (fun δ : ℝ => sourceH A B bA bB z r δ c 2) 0 / (r - z) =
      -weakH A B bB z r c := by
  rw [(sourceH_missing_hasDerivAt A B bA bB z r c hA hB).deriv]
  field_simp [sub_ne_zero.mpr hrz]

theorem sourceJ_normalized_deriv (A B bA bB z r : ℝ) (c : State 2)
    (hA : rowForms A r c ≠ 0) (hB : ∀ i, rowForms B r i ≠ 0) (hrz : r ≠ z) :
    deriv (fun δ : ℝ => sourceJ A B bA bB z r δ c 2) 0 / (r - z) =
      -weakJ A B bB z r c := by
  rw [(sourceJ_missing_hasDerivAt A B bA bB z r c hA hB).deriv]
  field_simp [sub_ne_zero.mpr hrz]

end

end PanelMoments.SourceInvariantTailWeakDerivative
