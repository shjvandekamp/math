import PanelMoments.SourceInvariantTailBaseData
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# Kernel-checked nonzero determinants of the displayed finite matrices

Every scalar data identity and inverse identity below is checked with
`decide +kernel`. The integer and rational determinant conclusions follow
from determinant functoriality and the checked column scalings. No external
determinant value is trusted. The bridge from actual Q(r) functions to the
displayed coefficient matrices remains external to this formalization.
-/

namespace PanelMoments.SourceInvariantTailBase

local instance : Fact (1 < 1000003) := ⟨by decide⟩

theorem integer_det_ne_zero_of_modular_inverse {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (M B : Matrix (Fin n) (Fin n) (ZMod 1000003))
    (hmap : A.map (Int.castRingHom (ZMod 1000003)) = M)
    (hinv : M * B = 1) : A.det ≠ 0 := by
  have hm : M.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hinv
  intro hzero
  apply hm
  calc
    M.det = (A.map (Int.castRingHom (ZMod 1000003))).det :=
      congrArg Matrix.det hmap.symm
    _ = (Int.castRingHom (ZMod 1000003)) A.det :=
      ((Int.castRingHom (ZMod 1000003)).map_det A).symm
    _ = 0 := by rw [hzero, map_zero]

theorem rational_det_ne_zero_of_integer_column_scaling {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (scales : Fin n → ℤ) (hA : A.det ≠ 0)
    (hscale : A.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j => (scales j : ℚ) * Q i j)) : Q.det ≠ 0 := by
  have hcast : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    have hd : (A.det : ℚ) = (A.map (Int.castRingHom ℚ)).det :=
      (Int.castRingHom ℚ).map_det A
    rw [← hd]
    exact Int.cast_ne_zero.mpr hA
  intro hzero
  apply hcast
  rw [hscale, Matrix.det_mul_row, hzero, mul_zero]

theorem stage3_mod_row_0 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 0 = residueMatrix3 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_0 :
    (residueMatrix3 * inverseMatrix3) 0 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_0 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 0 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 0 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_1 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 1 = residueMatrix3 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_1 :
    (residueMatrix3 * inverseMatrix3) 1 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_1 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 1 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 1 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_2 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 2 = residueMatrix3 2 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_2 :
    (residueMatrix3 * inverseMatrix3) 2 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 2 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_2 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 2 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 2 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_3 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 3 = residueMatrix3 3 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_3 :
    (residueMatrix3 * inverseMatrix3) 3 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 3 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_3 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 3 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 3 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_4 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 4 = residueMatrix3 4 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_4 :
    (residueMatrix3 * inverseMatrix3) 4 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 4 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_4 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 4 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 4 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_5 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 5 = residueMatrix3 5 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_5 :
    (residueMatrix3 * inverseMatrix3) 5 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 5 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_5 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 5 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 5 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_6 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 6 = residueMatrix3 6 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_6 :
    (residueMatrix3 * inverseMatrix3) 6 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 6 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_6 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 6 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 6 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_7 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 7 = residueMatrix3 7 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_7 :
    (residueMatrix3 * inverseMatrix3) 7 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 7 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_7 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 7 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 7 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_8 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 8 = residueMatrix3 8 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_8 :
    (residueMatrix3 * inverseMatrix3) 8 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 8 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_8 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 8 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 8 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_mod_row_9 :
    (integerMatrix3.map (Int.castRingHom (ZMod 1000003))) 9 = residueMatrix3 9 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_inverse_row_9 :
    (residueMatrix3 * inverseMatrix3) 9 =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 1000003)) 9 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage3_scaled_row_9 :
    (integerMatrix3.map (Int.castRingHom ℚ)) 9 =
      (fun j => (columnScales3 j : ℚ) * coefficientMatrix3 9 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem integerMatrix3_mod :
    integerMatrix3.map (Int.castRingHom (ZMod 1000003)) = residueMatrix3 := by
  funext i
  fin_cases i
  · exact stage3_mod_row_0
  · exact stage3_mod_row_1
  · exact stage3_mod_row_2
  · exact stage3_mod_row_3
  · exact stage3_mod_row_4
  · exact stage3_mod_row_5
  · exact stage3_mod_row_6
  · exact stage3_mod_row_7
  · exact stage3_mod_row_8
  · exact stage3_mod_row_9

theorem residueMatrix3_inverse :
    residueMatrix3 * inverseMatrix3 = 1 := by
  funext i
  fin_cases i
  · exact stage3_inverse_row_0
  · exact stage3_inverse_row_1
  · exact stage3_inverse_row_2
  · exact stage3_inverse_row_3
  · exact stage3_inverse_row_4
  · exact stage3_inverse_row_5
  · exact stage3_inverse_row_6
  · exact stage3_inverse_row_7
  · exact stage3_inverse_row_8
  · exact stage3_inverse_row_9

theorem integerMatrix3_scaled :
    integerMatrix3.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j => (columnScales3 j : ℚ) * coefficientMatrix3 i j) := by
  funext i
  fin_cases i
  · exact stage3_scaled_row_0
  · exact stage3_scaled_row_1
  · exact stage3_scaled_row_2
  · exact stage3_scaled_row_3
  · exact stage3_scaled_row_4
  · exact stage3_scaled_row_5
  · exact stage3_scaled_row_6
  · exact stage3_scaled_row_7
  · exact stage3_scaled_row_8
  · exact stage3_scaled_row_9

theorem integerMatrix3_det_ne_zero : integerMatrix3.det ≠ 0 :=
  integer_det_ne_zero_of_modular_inverse integerMatrix3 residueMatrix3 inverseMatrix3
    integerMatrix3_mod residueMatrix3_inverse

/-- The exact displayed length-3 rational matrix has nonzero determinant.
Its identification with the actual scalar functions is not formalized here. -/
theorem coefficientMatrix3_det_ne_zero : coefficientMatrix3.det ≠ 0 :=
  rational_det_ne_zero_of_integer_column_scaling coefficientMatrix3 integerMatrix3
    columnScales3 integerMatrix3_det_ne_zero integerMatrix3_scaled

theorem stage4_mod_row_0 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 0 = residueMatrix4 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_0 :
    (residueMatrix4 * inverseMatrix4) 0 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_0 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 0 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 0 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_1 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 1 = residueMatrix4 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_1 :
    (residueMatrix4 * inverseMatrix4) 1 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_1 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 1 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 1 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_2 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 2 = residueMatrix4 2 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_2 :
    (residueMatrix4 * inverseMatrix4) 2 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 2 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_2 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 2 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 2 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_3 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 3 = residueMatrix4 3 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_3 :
    (residueMatrix4 * inverseMatrix4) 3 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 3 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_3 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 3 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 3 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_4 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 4 = residueMatrix4 4 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_4 :
    (residueMatrix4 * inverseMatrix4) 4 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 4 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_4 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 4 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 4 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_5 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 5 = residueMatrix4 5 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_5 :
    (residueMatrix4 * inverseMatrix4) 5 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 5 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_5 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 5 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 5 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_6 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 6 = residueMatrix4 6 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_6 :
    (residueMatrix4 * inverseMatrix4) 6 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 6 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_6 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 6 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 6 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_7 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 7 = residueMatrix4 7 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_7 :
    (residueMatrix4 * inverseMatrix4) 7 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 7 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_7 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 7 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 7 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_8 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 8 = residueMatrix4 8 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_8 :
    (residueMatrix4 * inverseMatrix4) 8 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 8 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_8 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 8 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 8 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_9 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 9 = residueMatrix4 9 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_9 :
    (residueMatrix4 * inverseMatrix4) 9 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 9 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_9 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 9 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 9 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_10 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 10 = residueMatrix4 10 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_10 :
    (residueMatrix4 * inverseMatrix4) 10 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 10 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_10 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 10 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 10 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_11 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 11 = residueMatrix4 11 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_11 :
    (residueMatrix4 * inverseMatrix4) 11 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 11 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_11 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 11 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 11 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_mod_row_12 :
    (integerMatrix4.map (Int.castRingHom (ZMod 1000003))) 12 = residueMatrix4 12 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_inverse_row_12 :
    (residueMatrix4 * inverseMatrix4) 12 =
      (1 : Matrix (Fin 13) (Fin 13) (ZMod 1000003)) 12 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage4_scaled_row_12 :
    (integerMatrix4.map (Int.castRingHom ℚ)) 12 =
      (fun j => (columnScales4 j : ℚ) * coefficientMatrix4 12 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem integerMatrix4_mod :
    integerMatrix4.map (Int.castRingHom (ZMod 1000003)) = residueMatrix4 := by
  funext i
  fin_cases i
  · exact stage4_mod_row_0
  · exact stage4_mod_row_1
  · exact stage4_mod_row_2
  · exact stage4_mod_row_3
  · exact stage4_mod_row_4
  · exact stage4_mod_row_5
  · exact stage4_mod_row_6
  · exact stage4_mod_row_7
  · exact stage4_mod_row_8
  · exact stage4_mod_row_9
  · exact stage4_mod_row_10
  · exact stage4_mod_row_11
  · exact stage4_mod_row_12

theorem residueMatrix4_inverse :
    residueMatrix4 * inverseMatrix4 = 1 := by
  funext i
  fin_cases i
  · exact stage4_inverse_row_0
  · exact stage4_inverse_row_1
  · exact stage4_inverse_row_2
  · exact stage4_inverse_row_3
  · exact stage4_inverse_row_4
  · exact stage4_inverse_row_5
  · exact stage4_inverse_row_6
  · exact stage4_inverse_row_7
  · exact stage4_inverse_row_8
  · exact stage4_inverse_row_9
  · exact stage4_inverse_row_10
  · exact stage4_inverse_row_11
  · exact stage4_inverse_row_12

theorem integerMatrix4_scaled :
    integerMatrix4.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j => (columnScales4 j : ℚ) * coefficientMatrix4 i j) := by
  funext i
  fin_cases i
  · exact stage4_scaled_row_0
  · exact stage4_scaled_row_1
  · exact stage4_scaled_row_2
  · exact stage4_scaled_row_3
  · exact stage4_scaled_row_4
  · exact stage4_scaled_row_5
  · exact stage4_scaled_row_6
  · exact stage4_scaled_row_7
  · exact stage4_scaled_row_8
  · exact stage4_scaled_row_9
  · exact stage4_scaled_row_10
  · exact stage4_scaled_row_11
  · exact stage4_scaled_row_12

theorem integerMatrix4_det_ne_zero : integerMatrix4.det ≠ 0 :=
  integer_det_ne_zero_of_modular_inverse integerMatrix4 residueMatrix4 inverseMatrix4
    integerMatrix4_mod residueMatrix4_inverse

/-- The exact displayed length-4 rational matrix has nonzero determinant.
Its identification with the actual scalar functions is not formalized here. -/
theorem coefficientMatrix4_det_ne_zero : coefficientMatrix4.det ≠ 0 :=
  rational_det_ne_zero_of_integer_column_scaling coefficientMatrix4 integerMatrix4
    columnScales4 integerMatrix4_det_ne_zero integerMatrix4_scaled

theorem stage5_mod_row_0 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 0 = residueMatrix5 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_0 :
    (residueMatrix5 * inverseMatrix5) 0 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_0 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 0 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 0 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_1 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 1 = residueMatrix5 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_1 :
    (residueMatrix5 * inverseMatrix5) 1 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_1 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 1 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 1 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_2 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 2 = residueMatrix5 2 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_2 :
    (residueMatrix5 * inverseMatrix5) 2 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 2 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_2 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 2 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 2 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_3 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 3 = residueMatrix5 3 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_3 :
    (residueMatrix5 * inverseMatrix5) 3 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 3 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_3 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 3 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 3 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_4 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 4 = residueMatrix5 4 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_4 :
    (residueMatrix5 * inverseMatrix5) 4 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 4 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_4 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 4 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 4 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_5 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 5 = residueMatrix5 5 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_5 :
    (residueMatrix5 * inverseMatrix5) 5 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 5 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_5 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 5 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 5 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_6 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 6 = residueMatrix5 6 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_6 :
    (residueMatrix5 * inverseMatrix5) 6 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 6 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_6 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 6 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 6 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_7 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 7 = residueMatrix5 7 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_7 :
    (residueMatrix5 * inverseMatrix5) 7 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 7 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_7 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 7 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 7 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_8 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 8 = residueMatrix5 8 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_8 :
    (residueMatrix5 * inverseMatrix5) 8 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 8 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_8 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 8 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 8 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_9 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 9 = residueMatrix5 9 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_9 :
    (residueMatrix5 * inverseMatrix5) 9 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 9 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_9 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 9 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 9 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_10 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 10 = residueMatrix5 10 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_10 :
    (residueMatrix5 * inverseMatrix5) 10 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 10 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_10 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 10 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 10 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_11 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 11 = residueMatrix5 11 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_11 :
    (residueMatrix5 * inverseMatrix5) 11 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 11 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_11 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 11 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 11 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_12 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 12 = residueMatrix5 12 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_12 :
    (residueMatrix5 * inverseMatrix5) 12 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 12 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_12 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 12 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 12 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_13 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 13 = residueMatrix5 13 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_13 :
    (residueMatrix5 * inverseMatrix5) 13 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 13 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_13 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 13 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 13 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_14 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 14 = residueMatrix5 14 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_14 :
    (residueMatrix5 * inverseMatrix5) 14 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 14 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_14 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 14 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 14 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_mod_row_15 :
    (integerMatrix5.map (Int.castRingHom (ZMod 1000003))) 15 = residueMatrix5 15 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_inverse_row_15 :
    (residueMatrix5 * inverseMatrix5) 15 =
      (1 : Matrix (Fin 16) (Fin 16) (ZMod 1000003)) 15 := by
  funext j
  fin_cases j <;> decide +kernel

theorem stage5_scaled_row_15 :
    (integerMatrix5.map (Int.castRingHom ℚ)) 15 =
      (fun j => (columnScales5 j : ℚ) * coefficientMatrix5 15 j) := by
  funext j
  fin_cases j <;> decide +kernel

theorem integerMatrix5_mod :
    integerMatrix5.map (Int.castRingHom (ZMod 1000003)) = residueMatrix5 := by
  funext i
  fin_cases i
  · exact stage5_mod_row_0
  · exact stage5_mod_row_1
  · exact stage5_mod_row_2
  · exact stage5_mod_row_3
  · exact stage5_mod_row_4
  · exact stage5_mod_row_5
  · exact stage5_mod_row_6
  · exact stage5_mod_row_7
  · exact stage5_mod_row_8
  · exact stage5_mod_row_9
  · exact stage5_mod_row_10
  · exact stage5_mod_row_11
  · exact stage5_mod_row_12
  · exact stage5_mod_row_13
  · exact stage5_mod_row_14
  · exact stage5_mod_row_15

theorem residueMatrix5_inverse :
    residueMatrix5 * inverseMatrix5 = 1 := by
  funext i
  fin_cases i
  · exact stage5_inverse_row_0
  · exact stage5_inverse_row_1
  · exact stage5_inverse_row_2
  · exact stage5_inverse_row_3
  · exact stage5_inverse_row_4
  · exact stage5_inverse_row_5
  · exact stage5_inverse_row_6
  · exact stage5_inverse_row_7
  · exact stage5_inverse_row_8
  · exact stage5_inverse_row_9
  · exact stage5_inverse_row_10
  · exact stage5_inverse_row_11
  · exact stage5_inverse_row_12
  · exact stage5_inverse_row_13
  · exact stage5_inverse_row_14
  · exact stage5_inverse_row_15

theorem integerMatrix5_scaled :
    integerMatrix5.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j => (columnScales5 j : ℚ) * coefficientMatrix5 i j) := by
  funext i
  fin_cases i
  · exact stage5_scaled_row_0
  · exact stage5_scaled_row_1
  · exact stage5_scaled_row_2
  · exact stage5_scaled_row_3
  · exact stage5_scaled_row_4
  · exact stage5_scaled_row_5
  · exact stage5_scaled_row_6
  · exact stage5_scaled_row_7
  · exact stage5_scaled_row_8
  · exact stage5_scaled_row_9
  · exact stage5_scaled_row_10
  · exact stage5_scaled_row_11
  · exact stage5_scaled_row_12
  · exact stage5_scaled_row_13
  · exact stage5_scaled_row_14
  · exact stage5_scaled_row_15

theorem integerMatrix5_det_ne_zero : integerMatrix5.det ≠ 0 :=
  integer_det_ne_zero_of_modular_inverse integerMatrix5 residueMatrix5 inverseMatrix5
    integerMatrix5_mod residueMatrix5_inverse

/-- The exact displayed length-5 rational matrix has nonzero determinant.
Its identification with the actual scalar functions is not formalized here. -/
theorem coefficientMatrix5_det_ne_zero : coefficientMatrix5.det ≠ 0 :=
  rational_det_ne_zero_of_integer_column_scaling coefficientMatrix5 integerMatrix5
    columnScales5 integerMatrix5_det_ne_zero integerMatrix5_scaled

end PanelMoments.SourceInvariantTailBase
