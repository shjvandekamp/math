import PanelMoments.SourceBoundaryEndpointAlgebra

set_option autoImplicit false

/-!
# Actual active-edge kernels in the endpoint coalescence calculation

The old weighted table is `(I + 11ᵀ) diag(g)`, with `g = (2,1,1)`, and
the last table has time factors `g · z`. On `∑ i, g i * X i = 0` and
`X b = 0`, the actual old kernel has a zero inactive row. Its closed
active block gives the factor `3^m`, not the interior factor `4^m`.

The exceptional-row formula below uses the actual homogeneous kernels and
their matrix powers. The proposed cancellation ratio is explicitly defined;
its derivation from a generic coalescent limit is not asserted. There is no
residue extraction, convergence, or source-independence theorem here.
-/

namespace PanelMoments.SourceEndpointCoalescenceKernel

open scoped BigOperators
open SourceHomogeneous SourceBoundaryEndpointAlgebra

noncomputable section

def g : State 2 → ℝ := ![2, 1, 1]

def scaledPoint (X : State 2 → ℝ) : State 2 → ℝ := fun i => g i * X i

def oldTable : Table 2 := weightedTimeTable (fun _ => 1) g

def lastTime (z : State 2 → ℝ) : State 2 → ℝ := fun i => g i * z i

def lastTable (z : State 2 → ℝ) : Table 2 :=
  weightedTimeTable (fun _ => 1) (lastTime z)

def activeCoefficient (m : ℕ) : ℝ := ((3 : ℝ) ^ m - 1) / 2

def interiorCoefficient (m : ℕ) : ℝ := ((4 : ℝ) ^ m - 1) / 3

def cancellationFactor (m : ℕ) (z : State 2 → ℝ) (c : State 2) : ℝ :=
  (4 : ℝ) ^ m / (interiorCoefficient m * ((∑ i, z i) + z c))

def cancellationRatio (m : ℕ) (z : State 2 → ℝ) (c : State 2) : ℝ :=
  lastTable z 0 c 0 * cancellationFactor m z c

def mu (z X : State 2 → ℝ) (c : State 2) : ℝ :=
  lastTable z 0 c 0 * X c / rowForm (lastTable z) X 0 c

def headFactor (z X : State 2 → ℝ) (c : State 2) : ℝ :=
  lastTime z 0 * scaledPoint X c / rowForm (lastTable z) X 0 c

def exceptionalInput (m : ℕ) (z X : State 2 → ℝ) (c : State 2) : State 2 → ℝ :=
  fun i => mu z X c * scaledPoint X i -
    cancellationRatio m z c * X c * kernel (lastTable z) X 0 c i

def exceptionalRow (m : ℕ) (z X : State 2 → ℝ) (c : State 2) : State 2 → ℝ :=
  Matrix.vecMul (exceptionalInput m z X c) ((kernel oldTable X 0) ^ m)

private theorem g_ne_zero (i : State 2) : g i ≠ 0 := by
  fin_cases i <;> norm_num [g]

private theorem scaledPoint_ne_zero (X : State 2 → ℝ) (i : State 2) (hX : X i ≠ 0) :
    scaledPoint X i ≠ 0 := mul_ne_zero (g_ne_zero i) hX

theorem old_rowForm (X : State 2 → ℝ)
    (hplane : ∑ i, scaledPoint X i = 0) (a : State 2) :
    rowForm oldTable X 0 a = scaledPoint X a := by
  rw [oldTable, weightedTime_rowForm]
  simp only [one_mul]
  change (∑ i, scaledPoint X i) + scaledPoint X a = scaledPoint X a
  rw [hplane, zero_add]

/-- The inactive row really has a zero denominator in the actual kernel. -/
theorem old_kernel_inactive_row (X : State 2 → ℝ) (b : State 2)
    (hplane : ∑ i, scaledPoint X i = 0) (hXb : X b = 0) (i : State 2) :
    kernel oldTable X 0 b i = 0 := by
  simp [kernel, old_rowForm X hplane, scaledPoint, hXb]

theorem old_kernel_inactive_column (X : State 2 → ℝ) (b : State 2)
    (hXb : X b = 0) (a : State 2) : kernel oldTable X 0 a b = 0 := by
  simp [kernel, hXb]

private theorem old_kernel_active_entry (X : State 2 → ℝ)
    (hplane : ∑ i, scaledPoint X i = 0) (a i : State 2) (ha : X a ≠ 0) :
    kernel oldTable X 0 a i = (if a = i then 1 else 0) +
      scaledPoint X i / scaledPoint X a := by
  have hYa := scaledPoint_ne_zero X a ha
  change oldTable 0 a i * X i / rowForm oldTable X 0 a = _
  rw [old_rowForm X hplane a]
  simp only [oldTable,
    weightedTimeTable, SourceTimeScaling.scaledTable, SourceWeightedPrependAlgebra.weightedTable]
  by_cases hai : a = i
  · subst i
    simp only [↓reduceIte]
    rw [show ((1 + 1) * g a) * X a = 2 * scaledPoint X a by simp [scaledPoint]; ring]
    field_simp [hYa]
    norm_num
  · simp only [hai, ↓reduceIte, zero_add]
    simp [scaledPoint]

/-- One step on a row supported on the two active states. -/
theorem old_kernel_action (X : State 2 → ℝ) (b : State 2)
    (hplane : ∑ i, scaledPoint X i = 0) (hX : ∀ i, i ≠ b → X i ≠ 0)
    (R : State 2 → ℝ) (hRb : R b = 0) (i : State 2) :
    Matrix.vecMul R (kernel oldTable X 0) i =
      R i + (∑ a, R a / scaledPoint X a) * scaledPoint X i := by
  have hterm (a : State 2) : R a * kernel oldTable X 0 a i =
      (if a = i then R a else 0) + (R a / scaledPoint X a) * scaledPoint X i := by
    by_cases hab : a = b
    · subst a
      simp [hRb]
    · rw [old_kernel_active_entry X hplane a i (hX a hab)]
      by_cases hai : a = i
      · subst i
        simp only [↓reduceIte]
        ring
      · simp only [hai, ↓reduceIte, zero_add]
        ring
  change (∑ a, R a * kernel oldTable X 0 a i) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp

private theorem sum_scaledPoint_div (X : State 2 → ℝ) (b : State 2)
    (hXb : X b = 0) (hX : ∀ i, i ≠ b → X i ≠ 0) :
    (∑ i, scaledPoint X i / scaledPoint X i) = (2 : ℝ) := by
  have hterm (i : State 2) : scaledPoint X i / scaledPoint X i =
      if i = b then 0 else 1 := by
    by_cases hib : i = b
    · subst i
      simp [scaledPoint, hXb]
    · simp [hib, scaledPoint_ne_zero X i (hX i hib)]
  simp_rw [hterm]
  fin_cases b <;> norm_num [Fin.sum_univ_succ]

/-- The actual active block has `3^m`, while its inactive row is totalized to zero. -/
theorem old_kernel_power_action (X : State 2 → ℝ) (b : State 2)
    (hplane : ∑ i, scaledPoint X i = 0) (hXb : X b = 0)
    (hX : ∀ i, i ≠ b → X i ≠ 0) (R : State 2 → ℝ) (hRb : R b = 0) (m : ℕ) :
    ∀ i, Matrix.vecMul R ((kernel oldTable X 0) ^ m) i =
      R i + activeCoefficient m * (∑ a, R a / scaledPoint X a) * scaledPoint X i := by
  induction m with
  | zero =>
      intro i
      simp [activeCoefficient]
  | succ m ih =>
      intro i
      have hzero : Matrix.vecMul R ((kernel oldTable X 0) ^ m) b = 0 := by
        rw [ih b]
        simp [hRb, scaledPoint, hXb]
      have hsum : (∑ a, Matrix.vecMul R ((kernel oldTable X 0) ^ m) a / scaledPoint X a) =
          (∑ a, R a / scaledPoint X a) +
            activeCoefficient m * (∑ a, R a / scaledPoint X a) * 2 := by
        simp_rw [ih, add_div, mul_div_assoc]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_scaledPoint_div X b hXb hX]
      rw [pow_succ, ← Matrix.vecMul_vecMul, old_kernel_action X b hplane hX _ hzero i, ih i, hsum]
      simp only [activeCoefficient, pow_succ]
      ring

private theorem last_kernel_entry (z X : State 2 → ℝ) (c i : State 2) :
    kernel (lastTable z) X 0 c i =
      z i * (1 + if i = c then 1 else 0) * scaledPoint X i /
        rowForm (lastTable z) X 0 c := by
  simp only [kernel, Matrix.of_apply, lastTable, weightedTimeTable,
    SourceTimeScaling.scaledTable, SourceWeightedPrependAlgebra.weightedTable, lastTime, scaledPoint]
  by_cases hic : i = c
  · subst i
    simp only [↓reduceIte]
    ring
  · simp only [hic, Ne.symm hic, ↓reduceIte, zero_add, add_zero]
    ring

private theorem first_prefactor (z X : State 2 → ℝ) (c : State 2) :
    lastTable z 0 c 0 * X c = lastTime z 0 * scaledPoint X c := by
  fin_cases c <;>
    simp [lastTable, weightedTimeTable, SourceTimeScaling.scaledTable,
      SourceWeightedPrependAlgebra.weightedTable, lastTime, scaledPoint, g]
  all_goals ring

private theorem mu_eq_headFactor (z X : State 2 → ℝ) (c : State 2) :
    mu z X c = headFactor z X c := by
  unfold mu headFactor
  rw [first_prefactor]

private theorem ratio_times_coordinate (m : ℕ) (z X : State 2 → ℝ) (c : State 2) :
    cancellationRatio m z c * X c =
      lastTime z 0 * scaledPoint X c * cancellationFactor m z c := by
  unfold cancellationRatio
  calc
    lastTable z 0 c 0 * cancellationFactor m z c * X c =
        (lastTable z 0 c 0 * X c) * cancellationFactor m z c := by ring
    _ = _ := by rw [first_prefactor]

theorem exceptionalInput_inactive (m : ℕ) (z X : State 2 → ℝ) (b c : State 2)
    (hXb : X b = 0) : exceptionalInput m z X c b = 0 := by
  simp [exceptionalInput, scaledPoint, hXb, kernel]

theorem exceptionalInput_div (m : ℕ) (z X : State 2 → ℝ) (c i : State 2)
    (hXi : X i ≠ 0) (hL : rowForm (lastTable z) X 0 c ≠ 0) :
    exceptionalInput m z X c i / scaledPoint X i =
      headFactor z X c *
        (1 - cancellationFactor m z c * z i * (1 + if i = c then 1 else 0)) := by
  have hYi := scaledPoint_ne_zero X i hXi
  unfold exceptionalInput
  rw [mu_eq_headFactor, ratio_times_coordinate, last_kernel_entry]
  unfold headFactor
  field_simp [hYi, hL]

private theorem sum_active_expression (z : State 2 → ℝ) (b c : State 2)
    (hcb : c ≠ b) (f F : ℝ) :
    (∑ i : State 2, if i = b then 0 else f * (1 - F * z i * (1 + if i = c then 1 else 0))) =
      f * (2 - F * ((∑ i, z i) + z c - z b)) := by
  fin_cases b <;> fin_cases c <;> simp_all [Fin.sum_univ_succ] <;> ring

theorem exceptionalInput_sum_div (m : ℕ) (z X : State 2 → ℝ) (b c : State 2)
    (hcb : c ≠ b) (hXb : X b = 0) (hX : ∀ i, i ≠ b → X i ≠ 0)
    (hL : rowForm (lastTable z) X 0 c ≠ 0) :
    (∑ i, exceptionalInput m z X c i / scaledPoint X i) =
      headFactor z X c * (2 - cancellationFactor m z c * ((∑ i, z i) + z c - z b)) := by
  have hterm (i : State 2) : exceptionalInput m z X c i / scaledPoint X i =
      if i = b then 0 else headFactor z X c *
        (1 - cancellationFactor m z c * z i * (1 + if i = c then 1 else 0)) := by
    by_cases hib : i = b
    · subst i
      simp [scaledPoint, hXb]
    · simp only [hib, ↓reduceIte]
      exact exceptionalInput_div m z X c i (hX i hib) hL
  simp_rw [hterm]
  exact sum_active_expression z b c hcb _ _

/-- The active exceptional-row formula below LC120, through the actual old and last kernels. -/
theorem exceptionalRow_active_ratio (m : ℕ) (z X : State 2 → ℝ) (b c i : State 2)
    (hplane : ∑ j, scaledPoint X j = 0) (hXb : X b = 0)
    (hX : ∀ j, j ≠ b → X j ≠ 0) (hcb : c ≠ b) (hib : i ≠ b)
    (hL : rowForm (lastTable z) X 0 c ≠ 0) :
    exceptionalRow m z X c i / scaledPoint X i =
      headFactor z X c * ((3 : ℝ) ^ m - cancellationFactor m z c *
        (z i * (1 + if i = c then 1 else 0) +
          activeCoefficient m * ((∑ j, z j) + z c - z b))) := by
  have hYi := scaledPoint_ne_zero X i (hX i hib)
  have hpower := old_kernel_power_action X b hplane hXb hX (exceptionalInput m z X c)
    (exceptionalInput_inactive m z X b c hXb) m i
  unfold exceptionalRow
  rw [hpower]
  calc
    (exceptionalInput m z X c i + activeCoefficient m *
        (∑ a, exceptionalInput m z X c a / scaledPoint X a) * scaledPoint X i) /
        scaledPoint X i =
      exceptionalInput m z X c i / scaledPoint X i + activeCoefficient m *
        (∑ a, exceptionalInput m z X c a / scaledPoint X a) := by
          field_simp [hYi]
    _ = _ := by
      rw [exceptionalInput_div m z X c i (hX i hib) hL,
        exceptionalInput_sum_div m z X b c hcb hXb hX hL]
      unfold activeCoefficient
      ring

end

end PanelMoments.SourceEndpointCoalescenceKernel
