import PanelMoments.SourceHomogeneous
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# Explicit cubic matrix and ordinary observations

The rational matrix K is identified with the actual homogeneous kernel for
G=I+11ᵀ and X=(x,1,1). We define U, V, S and Y by the displayed matrix
formulas, prove their values and actual entrywise derivatives at x=1, and
evaluate the ordinary three-observation determinant. The derivatives are
proved using the quotient, sum and product rules, not supplied as premises.

The same observations have a nonzero determinant on the displayed empty
source matrix diag(X)(I-K). Thus the cubic observation certificate alone
does not give observations annihilating those sources. No theorem here
identifies the cubic expression with a time-Taylor coefficient or proves
a source-family rank or quotient-rank claim.
-/

namespace PanelMoments.SourceConfluentCubicAlgebra

open scoped BigOperators

noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def G : Mat := ![![2, 1, 1], ![1, 2, 1], ![1, 1, 2]]
def X (x : ℝ) : Fin 3 → ℝ := ![x, 1, 1]
def actualTable : Table 2 := fun _ i j => G i j
def numeratorSlope : Mat := ![![2, 0, 0], ![1, 0, 0], ![1, 0, 0]]
def numeratorConstant : Mat := ![![0, 1, 1], ![0, 2, 1], ![0, 1, 2]]
def denominatorSlope : Fin 3 → ℝ := ![2, 1, 1]
def denominatorConstant : Fin 3 → ℝ := ![2, 3, 3]

def K (x : ℝ) : Mat := fun i j =>
  (numeratorSlope i j * x + numeratorConstant i j) /
    (denominatorSlope i * x + denominatorConstant i)

def D : Mat := Matrix.diagonal ![0, 1, 0]
def E : Mat := Matrix.diagonal ![0, 0, 1]
def xSlope : Mat := Matrix.diagonal ![1, 0, 0]
def columnDiag (M : Mat) (j : Fin 3) : Mat := Matrix.diagonal (fun i => M i j)
def comm (M N : Mat) : Mat := M * N - N * M
def diagonalX (x : ℝ) : Mat := Matrix.diagonal (X x)

def U (x : ℝ) : Mat := K x * D - columnDiag (K x) 1 * K x
def V (x : ℝ) : Mat :=
  K x * E - columnDiag (K x) 2 * K x - columnDiag (K x) 1 * U x
def S (x : ℝ) : Mat :=
  comm (K x) (U x) * K x * V x + comm (U x) (V x) * (K x * K x) +
    comm (V x) (K x) * K x * U x
def Y (x : ℝ) : Mat := diagonalX x * S x
def emptySources (x : ℝ) : Mat := diagonalX x * (1 - K x)

def KValue : Mat := ![![2/4, 1/4, 1/4], ![1/4, 2/4, 1/4], ![1/4, 1/4, 2/4]]
def KDerivative : Mat :=
  ![![4/16, -2/16, -2/16], ![3/16, -2/16, -1/16], ![3/16, -1/16, -2/16]]
def UValue : Mat :=
  ![![-2/16, 3/16, -1/16], ![-2/16, 4/16, -2/16], ![-1/16, 3/16, -2/16]]
def UDerivative : Mat :=
  ![![0, -4/64, 4/64], ![-4/64, 0, 4/64], ![-2/64, -2/64, 4/64]]
def VValue : Mat :=
  ![![-6/64, -7/64, 13/64], ![0, -16/64, 16/64], ![-7/64, -11/64, 18/64]]
def VDerivative : Mat :=
  ![![-4/256, 26/256, -22/256], ![-4/256, 24/256, -20/256],
    ![-15/256, 21/256, -6/256]]
def YValue : Mat :=
  ![![6/4096, -13/4096, 7/4096], ![7/4096, -12/4096, 5/4096],
    ![5/4096, -11/4096, 6/4096]]
def SDerivative : Mat :=
  ![![24/65536, -53/65536, 29/65536], ![29/65536, -64/65536, 35/65536],
    ![23/65536, -63/65536, 40/65536]]
def YDerivative : Mat :=
  ![![120/65536, -261/65536, 141/65536], ![29/65536, -64/65536, 35/65536],
    ![23/65536, -63/65536, 40/65536]]

theorem K_eq_homogeneous (x : ℝ) :
    K x = SourceHomogeneous.kernel actualTable (X x) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, numeratorSlope, numeratorConstant, denominatorSlope, denominatorConstant,
      SourceHomogeneous.kernel, SourceHomogeneous.rowForm, actualTable, X, G,
      Fin.sum_univ_succ]

/-- Both fields are proved for the actual function; no derivative is assumed. -/
structure HasMatrixJet (f : ℝ → Mat) (value derivative : Mat) : Prop where
  value_eq : f 1 = value
  hasDerivAt : ∀ i j, HasDerivAt (fun x => f x i j) (derivative i j) 1

theorem HasMatrixJet.const (M : Mat) : HasMatrixJet (fun _ => M) M 0 := by
  refine ⟨rfl, ?_⟩
  intro i j
  exact hasDerivAt_const 1 (M i j)

theorem HasMatrixJet.add {f g : ℝ → Mat} {v w d e : Mat}
    (hf : HasMatrixJet f v d) (hg : HasMatrixJet g w e) :
    HasMatrixJet (fun x => f x + g x) (v + w) (d + e) := by
  refine ⟨by rw [hf.value_eq, hg.value_eq], ?_⟩
  intro i j
  exact (hf.hasDerivAt i j).add (hg.hasDerivAt i j)

theorem HasMatrixJet.sub {f g : ℝ → Mat} {v w d e : Mat}
    (hf : HasMatrixJet f v d) (hg : HasMatrixJet g w e) :
    HasMatrixJet (fun x => f x - g x) (v - w) (d - e) := by
  refine ⟨by rw [hf.value_eq, hg.value_eq], ?_⟩
  intro i j
  exact (hf.hasDerivAt i j).sub (hg.hasDerivAt i j)

theorem HasMatrixJet.mul {f g : ℝ → Mat} {v w d e : Mat}
    (hf : HasMatrixJet f v d) (hg : HasMatrixJet g w e) :
    HasMatrixJet (fun x => f x * g x) (v * w) (d * w + v * e) := by
  refine ⟨by rw [hf.value_eq, hg.value_eq], ?_⟩
  intro i j
  change HasDerivAt (fun x => ∑ k, f x i k * g x k j)
    ((∑ k, d i k * w k j) + ∑ k, v i k * e k j) 1
  simpa only [hf.value_eq, hg.value_eq, Finset.sum_add_distrib] using
    (HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) =>
      (hf.hasDerivAt i k).fun_mul (hg.hasDerivAt k j)))

theorem HasMatrixJet.columnDiag {f : ℝ → Mat} {v d : Mat}
    (hf : HasMatrixJet f v d) (c : Fin 3) :
    HasMatrixJet (fun x => columnDiag (f x) c) (columnDiag v c) (columnDiag d c) := by
  refine ⟨by rw [hf.value_eq], ?_⟩
  intro i j
  by_cases h : i = j
  · subst j
    simpa [SourceConfluentCubicAlgebra.columnDiag] using hf.hasDerivAt i c
  · simpa [SourceConfluentCubicAlgebra.columnDiag, Matrix.diagonal_apply, h] using
      hasDerivAt_const (1 : ℝ) (0 : ℝ)

theorem HasMatrixJet.comm {f g : ℝ → Mat} {v w d e : Mat}
    (hf : HasMatrixJet f v d) (hg : HasMatrixJet g w e) :
    HasMatrixJet (fun x => comm (f x) (g x)) (comm v w)
      (d * w + v * e - (e * v + w * d)) :=
  (hf.mul hg).sub (hg.mul hf)

private theorem affine_quotient_hasDerivAt (a b c d : ℝ) (h : c + d ≠ 0) :
    HasDerivAt (fun x : ℝ => (a * x + b) / (c * x + d))
      ((a * (c + d) - (a + b) * c) / (c + d) ^ 2) 1 := by
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id (1 : ℝ)).const_mul a).add_const b).fun_div
      (((hasDerivAt_id (1 : ℝ)).const_mul c).add_const d) (by simpa using h)

theorem K_hasMatrixJet : HasMatrixJet K KValue KDerivative := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [K, KValue, numeratorSlope, numeratorConstant, denominatorSlope, denominatorConstant]
  · intro i j
    have hu : denominatorSlope i + denominatorConstant i ≠ 0 := by
      fin_cases i <;> norm_num [denominatorSlope, denominatorConstant]
    have h := affine_quotient_hasDerivAt (numeratorSlope i j) (numeratorConstant i j)
      (denominatorSlope i) (denominatorConstant i) hu
    change HasDerivAt (fun x => (numeratorSlope i j * x + numeratorConstant i j) /
      (denominatorSlope i * x + denominatorConstant i)) (KDerivative i j) 1
    convert h using 1
    fin_cases i <;> fin_cases j <;>
      norm_num [KDerivative, numeratorSlope, numeratorConstant, denominatorSlope, denominatorConstant]

theorem U_hasMatrixJet : HasMatrixJet U UValue UDerivative := by
  have h := (K_hasMatrixJet.mul (HasMatrixJet.const D)).sub
    ((K_hasMatrixJet.columnDiag 1).mul K_hasMatrixJet)
  convert h using 1
  · rfl
  all_goals
    ext i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply,
      Fin.sum_univ_succ]
    fin_cases i <;> fin_cases j <;>
      norm_num [U, UValue, UDerivative, KValue, KDerivative, D, columnDiag,
        Matrix.diagonal_apply]

theorem V_hasMatrixJet : HasMatrixJet V VValue VDerivative := by
  have h := ((K_hasMatrixJet.mul (HasMatrixJet.const E)).sub
    ((K_hasMatrixJet.columnDiag 2).mul K_hasMatrixJet)).sub
      ((K_hasMatrixJet.columnDiag 1).mul U_hasMatrixJet)
  convert h using 1
  · rfl
  all_goals
    ext i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply,
      Fin.sum_univ_succ]
    fin_cases i <;> fin_cases j <;>
      norm_num [V, VValue, VDerivative, UValue, UDerivative, KValue, KDerivative, E,
        columnDiag, Matrix.diagonal_apply]

theorem S_hasMatrixJet : HasMatrixJet S YValue SDerivative := by
  have h := ((((K_hasMatrixJet.comm U_hasMatrixJet).mul K_hasMatrixJet).mul
    V_hasMatrixJet).add ((U_hasMatrixJet.comm V_hasMatrixJet).mul
      (K_hasMatrixJet.mul K_hasMatrixJet))).add
        (((V_hasMatrixJet.comm K_hasMatrixJet).mul K_hasMatrixJet).mul U_hasMatrixJet)
  convert h using 1
  · rfl
  all_goals
    ext i j
    simp only [comm, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_succ]
    fin_cases i <;> fin_cases j <;>
      norm_num [S, YValue, SDerivative, comm, KValue, KDerivative, UValue, UDerivative,
        VValue, VDerivative]

theorem diagonalX_hasMatrixJet : HasMatrixJet diagonalX 1 xSlope := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [diagonalX, X, Matrix.one_apply]
  · intro i j
    fin_cases i <;> fin_cases j
    · change HasDerivAt (fun x : ℝ => x) 1 1
      exact hasDerivAt_id 1
    · change HasDerivAt (fun _ : ℝ => 0) 0 1
      exact hasDerivAt_const 1 0
    · change HasDerivAt (fun _ : ℝ => 0) 0 1
      exact hasDerivAt_const 1 0
    · change HasDerivAt (fun _ : ℝ => 0) 0 1
      exact hasDerivAt_const 1 0
    · change HasDerivAt (fun _ : ℝ => 1) 0 1
      exact hasDerivAt_const 1 1
    · change HasDerivAt (fun _ : ℝ => 0) 0 1
      exact hasDerivAt_const 1 0
    · change HasDerivAt (fun _ : ℝ => 0) 0 1
      exact hasDerivAt_const 1 0
    · change HasDerivAt (fun _ : ℝ => 0) 0 1
      exact hasDerivAt_const 1 0
    · change HasDerivAt (fun _ : ℝ => 1) 0 1
      exact hasDerivAt_const 1 1

theorem Y_hasMatrixJet : HasMatrixJet Y YValue YDerivative := by
  have h := diagonalX_hasMatrixJet.mul S_hasMatrixJet
  convert h using 1
  · rfl
  all_goals
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_succ]
    fin_cases i <;> fin_cases j <;>
      norm_num [Y, YValue, YDerivative, SDerivative, xSlope, Matrix.diagonal_apply]

theorem Y_one : Y 1 = YValue := Y_hasMatrixJet.value_eq

theorem Y_hasDerivAt (i j : Fin 3) :
    HasDerivAt (fun x => Y x i j) (YDerivative i j) 1 :=
  Y_hasMatrixJet.hasDerivAt i j

theorem Y_deriv (i j : Fin 3) : deriv (fun x => Y x i j) 1 = YDerivative i j :=
  (Y_hasDerivAt i j).deriv

def observationMatrix (value derivative : Mat) : Mat :=
  ![(fun i => value i 1), (fun i => value i 2), (fun i => derivative i 1)]

def cubicObservation : Mat :=
  observationMatrix (Y 1) (fun i j => deriv (fun x => Y x i j) 1)

theorem cubicObservation_eq : cubicObservation = observationMatrix YValue YDerivative := by
  simp only [cubicObservation, Y_one, Y_deriv]

theorem cubicObservation_det : cubicObservation.det = 397 / (2 : ℝ) ^ 37 := by
  rw [cubicObservation_eq, Matrix.det_fin_three]
  norm_num [observationMatrix, YValue, YDerivative]

theorem cubicObservation_det_ne_zero : cubicObservation.det ≠ 0 := by
  rw [cubicObservation_det]
  norm_num

def emptyValue : Mat := 1 - KValue
def emptyDerivative : Mat := xSlope * (1 - KValue) - KDerivative

theorem emptySources_hasMatrixJet : HasMatrixJet emptySources emptyValue emptyDerivative := by
  have h := diagonalX_hasMatrixJet.mul ((HasMatrixJet.const 1).sub K_hasMatrixJet)
  convert h using 1
  · rfl
  all_goals
    ext i j
    simp only [emptyValue, emptyDerivative, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.zero_apply, Matrix.one_apply, Fin.sum_univ_succ]
    fin_cases i <;> fin_cases j <;>
      norm_num [emptySources, emptyValue, emptyDerivative, xSlope, KValue, KDerivative,
        Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem emptySources_hasDerivAt (i j : Fin 3) :
    HasDerivAt (fun x => emptySources x i j) (emptyDerivative i j) 1 :=
  emptySources_hasMatrixJet.hasDerivAt i j

def emptyObservation : Mat := observationMatrix (emptySources 1)
  (fun i j => deriv (fun x => emptySources x i j) 1)

theorem emptyObservation_eq : emptyObservation =
    ![![-1/4, 1/2, -1/4], ![-1/4, -1/4, 1/2], ![-1/8, 1/8, 1/16]] := by
  have hd (i j : Fin 3) : deriv (fun x => emptySources x i j) 1 = emptyDerivative i j :=
    (emptySources_hasDerivAt i j).deriv
  rw [emptyObservation, emptySources_hasMatrixJet.value_eq]
  simp only [hd]
  ext i j
  simp only [observationMatrix, emptyValue, emptyDerivative, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    norm_num [observationMatrix, emptyValue, emptyDerivative, xSlope, KValue, KDerivative,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem emptyObservation_det : emptyObservation.det = 3 / 256 := by
  rw [Matrix.det_fin_three emptyObservation, emptyObservation_eq]
  norm_num

theorem emptyObservation_det_ne_zero : emptyObservation.det ≠ 0 := by
  rw [emptyObservation_det]
  norm_num

end

end PanelMoments.SourceConfluentCubicAlgebra
