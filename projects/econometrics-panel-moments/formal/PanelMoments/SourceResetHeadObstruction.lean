import PanelMoments.SourceFirstBlockCancellation

set_option autoImplicit false

/-!
# An actual one-block reset coefficient-head obstruction

Use the actual table `firstTable 2 3 = (I + 11ᵀ) diag(1,2,3)` on
`2 X₀ + X₁ + X₂ = 0`. The scalar fractions are `f_c = X_c/L_c`,
the outgoing rows use the existing kernel, and the incoming rows are
`J_c = -A(c,0) f_c (2 X₀,X₁,X₂)`.

The canonical edge reset of each fraction has an explicit constant-coefficient
expansion in its actual outgoing row, incoming row, and the polynomial row.
Scaling by `-A(c,0)` gives the resets of the actual divided incoming scalars.
Their coefficient heads have determinant `31/24640`; subtracting the canonical
`s₀ e₀` leaves a lower two-by-two minor `-31/3080`.

These are heads of the displayed source coefficients, including the polynomial
row's coefficient times `(2,1,1)`. No abstract map is declared to be an actual
head map. No source independence, existence of such a map, or all-length rank
claim is made. Each row identity states its actual row-form unit hypothesis.
-/

namespace PanelMoments.SourceResetHeadObstruction

open SourceHomogeneous SourceFirstBlockCancellation

noncomputable section

def edge : State 2 → (State 2 → ℝ) :=
  ![![0, 1, -1], ![1, 0, -2], ![1, -2, 0]]

def fraction (c : State 2) (X : State 2 → ℝ) : ℝ :=
  X c / rowForm (firstTable 2 3) X 0 c

def outgoingRow (c : State 2) (X : State 2 → ℝ) : State 2 → ℝ :=
  fun j => X c * ((if c = j then 1 else 0) - kernel (firstTable 2 3) X 0 c j)

def incomingScalar (c : State 2) (X : State 2 → ℝ) : ℝ :=
  -(firstTable 2 3 0 c 0) * fraction c X

def incomingRow (c : State 2) (X : State 2 → ℝ) : State 2 → ℝ :=
  incomingScalar c X • newStateRow X

/-- The explicit canonical triple `(s₀,k,s₂)` from the three edge values. -/
def resetData (h : (State 2 → ℝ) → ℝ) : State 2 → ℝ :=
  ![(2 * h (edge 0) - 3 * h (edge 1) + h (edge 2)) / 4,
    (h (edge 0) - 6 * h (edge 1) + h (edge 2)) / 4,
    (h (edge 0) - 3 * h (edge 1) + 2 * h (edge 2)) / 4]

/-- The canonical reset row after eliminating the edge-normalization constants. -/
def resetRow (h : (State 2 → ℝ) → ℝ) (X : State 2 → ℝ) : State 2 → ℝ :=
  (X 0 / 4) •
    ![2 * h X - 3 * h (edge 1) + h (edge 2),
      -3 * h X + 3 * h (edge 1), h X - h (edge 2)]

def fractionEdges : Matrix (State 2) (State 2) ℝ :=
  ![![0, -1 / 4, -1 / 2], ![1, 0, 2 / 7], ![1 / 4, 2 / 11, 0]]

def fractionData : Matrix (State 2) (State 2) ℝ :=
  ![![1 / 16, 1 / 4, -1 / 16], ![4 / 7, 9 / 28, 11 / 28],
    ![-1 / 88, -37 / 176, -13 / 176]]

def outgoingCoefficient : State 2 → ℝ := ![1 / 16, 4 / 35, -1 / 66]

def incomingCoefficient : State 2 → ℝ := ![-5 / 32, -43 / 140, -8 / 33]

def polynomialCoefficient : State 2 → ℝ := ![0, 1 / 28, -3 / 44]

def incomingScale : State 2 → ℝ := ![-2, -1, -1]

theorem outgoingRow_eq_singleBlockVector (c : State 2) (X : State 2 → ℝ) :
    outgoingRow c X = singleBlockVector (firstTable 2 3) X (0 : Fin 1) c := by
  rfl

theorem incomingScale_eq (c : State 2) :
    incomingScale c = -(firstTable 2 3 0 c 0) := by
  fin_cases c <;>
    norm_num [incomingScale, firstTable, SourceTimeScaling.scaledTable,
      SourceScalarPrependAlgebra.preservingTable, firstTime]

theorem incomingScalar_function (c : State 2) :
    incomingScalar c = fun X => incomingScale c * fraction c X := by
  funext X
  rw [incomingScalar, incomingScale_eq]

/-- Dividing the actual incoming row's middle output gives its signed scalar. -/
theorem incomingRow_selected_scalar (c : State 2) (X : State 2 → ℝ)
    (hX1 : X 1 ≠ 0) :
    incomingRow c X 1 / X 1 = incomingScalar c X := by
  simp [incomingRow, newStateRow, hX1]

theorem fraction_edge_values (c j : State 2) :
    fraction c (edge j) = fractionEdges c j := by
  fin_cases c <;> fin_cases j <;>
    norm_num [fraction, edge, fractionEdges, firstTable_rowForm, firstTime]

theorem fraction_resetData (c : State 2) :
    resetData (fraction c) = fractionData c := by
  funext j
  fin_cases c <;> fin_cases j <;>
    norm_num [resetData, fraction_edge_values, fractionEdges, fractionData]

theorem resetData_smul (a : ℝ) (h : (State 2 → ℝ) → ℝ) :
    resetData (fun X => a * h X) = a • resetData h := by
  funext j
  fin_cases j <;> simp [resetData] <;> ring

theorem resetRow_smul (a : ℝ) (h : (State 2 → ℝ) → ℝ) (X : State 2 → ℝ) :
    resetRow (fun Y => a * h Y) X = a • resetRow h X := by
  funext j
  fin_cases j <;> simp [resetRow] <;> ring

/-- All three expansions use the actual one-block kernel and signed incoming rows. -/
theorem fraction_resetRow_expansion (c : State 2) (X : State 2 → ℝ)
    (hplane : 2 * X 0 + X 1 + X 2 = 0)
    (hL : rowForm (firstTable 2 3) X 0 c ≠ 0) :
    resetRow (fraction c) X =
      outgoingCoefficient c • outgoingRow c X +
      incomingCoefficient c • incomingRow c X +
      polynomialCoefficient c • newStateRow X := by
  have hX2 : X 2 = -2 * X 0 - X 1 := by linarith
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases c <;> fin_cases j <;>
    norm_num [resetRow, fraction_edge_values, fractionEdges, outgoingCoefficient,
      incomingCoefficient, polynomialCoefficient, outgoingRow, incomingRow,
      incomingScalar, fraction, newStateRow, kernel, rowForm, firstTable,
      SourceTimeScaling.scaledTable, SourceScalarPrependAlgebra.preservingTable,
      firstTime, edge, Fin.sum_univ_succ, hX2] at hL ⊢ <;>
    ring_nf at hL ⊢ <;>
    field_simp [hL] <;> ring

theorem incoming_resetData (c : State 2) :
    resetData (incomingScalar c) = incomingScale c • fractionData c := by
  rw [incomingScalar_function, resetData_smul, fraction_resetData]

/-- The input is the actual divided incoming scalar, including its negative sign. -/
theorem incoming_resetRow_expansion (c : State 2) (X : State 2 → ℝ)
    (hplane : 2 * X 0 + X 1 + X 2 = 0)
    (hL : rowForm (firstTable 2 3) X 0 c ≠ 0) :
    resetRow (incomingScalar c) X =
      (incomingScale c * outgoingCoefficient c) • outgoingRow c X +
      (incomingScale c * incomingCoefficient c) • incomingRow c X +
      (incomingScale c * polynomialCoefficient c) • newStateRow X := by
  rw [incomingScalar_function, resetRow_smul, fraction_resetRow_expansion c X hplane hL]
  simp only [smul_add, smul_smul]

/-- Column `c` is the outgoing coefficient times `e_c` plus the polynomial
coefficient times `(2,1,1)`, in the displayed incoming reset expansion. -/
def coefficientHeadMatrix : Matrix (State 2) (State 2) ℝ :=
  fun j c => incomingScale c * outgoingCoefficient c * (if c = j then 1 else 0) +
    incomingScale c * polynomialCoefficient c * (![2, 1, 1] : State 2 → ℝ) j

def correctedCoefficientHeadMatrix : Matrix (State 2) (State 2) ℝ :=
  fun j c => coefficientHeadMatrix j c -
    resetData (incomingScalar c) 0 * (if j = 0 then 1 else 0)

theorem coefficientHeadMatrix_eq :
    coefficientHeadMatrix =
      ![![-1 / 8, -1 / 14, 3 / 22], ![0, -3 / 20, 3 / 44], ![0, -1 / 28, 1 / 12]] := by
  ext j c
  fin_cases j <;> fin_cases c <;>
    norm_num [coefficientHeadMatrix, incomingScale, outgoingCoefficient, polynomialCoefficient]

theorem coefficientHeadMatrix_det :
    coefficientHeadMatrix.det = (31 / 24640 : ℝ) := by
  rw [Matrix.det_fin_three coefficientHeadMatrix]
  norm_num [coefficientHeadMatrix_eq]

theorem coefficientHeadMatrix_det_ne_zero : coefficientHeadMatrix.det ≠ 0 := by
  rw [coefficientHeadMatrix_det]
  norm_num

theorem correctedCoefficientHeadMatrix_eq :
    correctedCoefficientHeadMatrix =
      ![![0, 1 / 2, 1 / 8], ![0, -3 / 20, 3 / 44], ![0, -1 / 28, 1 / 12]] := by
  ext j c
  fin_cases j <;> fin_cases c <;>
    norm_num [correctedCoefficientHeadMatrix, coefficientHeadMatrix_eq,
      incoming_resetData, incomingScale, fractionData]

theorem corrected_lower_minor :
    correctedCoefficientHeadMatrix 1 1 * correctedCoefficientHeadMatrix 2 2 -
      correctedCoefficientHeadMatrix 1 2 * correctedCoefficientHeadMatrix 2 1 =
        -(31 / 3080 : ℝ) := by
  norm_num [correctedCoefficientHeadMatrix_eq]

theorem corrected_lower_minor_ne_zero :
    correctedCoefficientHeadMatrix 1 1 * correctedCoefficientHeadMatrix 2 2 -
      correctedCoefficientHeadMatrix 1 2 * correctedCoefficientHeadMatrix 2 1 ≠ 0 := by
  rw [corrected_lower_minor]
  norm_num

/-- The selected actual incoming scalar is `-f₁`, so its response has this sign. -/
theorem incoming_one_corrected_difference :
    correctedCoefficientHeadMatrix 1 1 - correctedCoefficientHeadMatrix 2 1 =
      -(4 / 35 : ℝ) := by
  norm_num [correctedCoefficientHeadMatrix_eq]

theorem incoming_one_corrected_difference_ne_zero :
    correctedCoefficientHeadMatrix 1 1 - correctedCoefficientHeadMatrix 2 1 ≠ 0 := by
  rw [incoming_one_corrected_difference]
  norm_num

end

end PanelMoments.SourceResetHeadObstruction
