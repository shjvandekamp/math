import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Explicit polynomial algebra for the endpoint Hermite quotient

The polynomial numerator identity is the cancellation displayed in
SOURCE24_NONZERO_H_WEAK_TRANSFER.md, (NH64)--(NH65). The quadratic factor
J has constant coefficient -a*z*(1-A*z), which proves that it is a nonzero
polynomial under the three stated unit hypotheses. Its product with the
displayed nonconstant linear factor is also nonzero.

The last two theorems check the determinant of the explicit three-by-three
scalar coefficient matrix in (NH57)--(NH58). No actual endpoint-jet map,
analytic continuation, source-space identification, quotient dimension,
or independence theorem is formalized here.
-/

namespace PanelMoments.SourceWeakHermitePolynomial

noncomputable section

def nodeNumerator (a A z : ℝ) : ℝ :=
  a - 2 * A + A * z * (2 * a - A)

def basicNumerator (b z : ℝ) : Polynomial ℝ :=
  Polynomial.C b * Polynomial.X ^ 2 +
    Polynomial.C (2 * b * z - 2) * Polynomial.X - Polynomial.C z

/-- The quadratic J in the high cubic C = (linear factor) * J. -/
def highQuadratic (a A z : ℝ) : Polynomial ℝ :=
  Polynomial.C (a * A * (1 - A * z)) * Polynomial.X ^ 2 +
    Polynomial.C
      (-2 * a + (3 * A ^ 2 - 2 * A * a + 3 * a ^ 2) * z -
        2 * a * A ^ 2 * z ^ 2) * Polynomial.X -
    Polynomial.C (a * z * (1 - A * z))

def highCubic (a A B b bprev z : ℝ) : Polynomial ℝ :=
  (Polynomial.C (b - bprev) * Polynomial.X +
    Polynomial.C (b / A - bprev / B)) * highQuadratic a A z

theorem highQuadratic_eval (a A z r : ℝ) :
    (highQuadratic a A z).eval r =
      a * A * (1 - A * z) * r ^ 2 +
        (-2 * a + (3 * A ^ 2 - 2 * A * a + 3 * a ^ 2) * z -
          2 * a * A ^ 2 * z ^ 2) * r -
        a * z * (1 - A * z) := by
  simp [highQuadratic]

/-- The exact identity before cancelling the factor 1-A*r in (NH65). -/
theorem numerator_identity (a A z : ℝ) :
    -Polynomial.C (nodeNumerator a A z) *
        (1 - Polynomial.C a * Polynomial.X) * basicNumerator A z +
      Polynomial.C (A - a) * basicNumerator a z *
        (Polynomial.C (A + 2 * A ^ 2 * z) * Polynomial.X -
          Polynomial.C (2 + A * z)) =
      (1 - Polynomial.C A * Polynomial.X) * highQuadratic a A z := by
  simp only [nodeNumerator, basicNumerator, highQuadratic,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

theorem highQuadratic_coeff_zero (a A z : ℝ) :
    (highQuadratic a A z).coeff 0 = -(a * z * (1 - A * z)) := by
  simp [highQuadratic]

theorem highQuadratic_coeff_zero_ne_zero (a A z : ℝ)
    (ha : a ≠ 0) (hz : z ≠ 0) (hAz : 1 - A * z ≠ 0) :
    (highQuadratic a A z).coeff 0 ≠ 0 := by
  rw [highQuadratic_coeff_zero]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hz) hAz)

/-- The constant coefficient witnesses nonvanishing as a polynomial;
this is not a claim that every evaluation is nonzero. -/
theorem highQuadratic_ne_zero (a A z : ℝ)
    (ha : a ≠ 0) (hz : z ≠ 0) (hAz : 1 - A * z ≠ 0) :
    highQuadratic a A z ≠ 0 := by
  intro hzero
  apply highQuadratic_coeff_zero_ne_zero a A z ha hz hAz
  simp [hzero]

/-- A nonzero slope of the displayed linear factor gives a nonzero product
polynomial; no nonvanishing of its evaluations is asserted. -/
theorem highCubic_ne_zero (a A B b bprev z : ℝ)
    (ha : a ≠ 0) (hz : z ≠ 0) (hAz : 1 - A * z ≠ 0)
    (hb : b ≠ bprev) :
    highCubic a A B b bprev z ≠ 0 := by
  unfold highCubic
  apply mul_ne_zero _ (highQuadratic_ne_zero a A z ha hz hAz)
  intro hzero
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff 1) hzero
  have hdiff : b - bprev = 0 := by
    simpa [Polynomial.coeff_C_mul_X] using hc
  exact (sub_ne_zero.mpr hb) hdiff

/-- The three observation rows in (NH57), with the first row divided by z. -/
def baseJetCoefficientMatrix (A C β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![β / (A * C) * (-3 * (A - 3 * C) / 8),
      β / (A * C) * (3 * (A - C) / 4),
      β / (A * C) * (-3 * (A - C) / 4)],
    ![β / (A * C) * (-1 / 2), β / (A * C), β / (A * C)],
    ![β * (C - 5 * A) / (2 * C * (A - C) * (2 * C - A) * (C - 2 * A)),
      0, -3 * β / (C ^ 2 * (2 * C - A))]]

/-- The scalar coefficient of z in the displayed determinant, without
asserting the analytic expansion of an actual observation matrix. -/
theorem baseJetCoefficientMatrix_det (A C β : ℝ)
    (hA : A ≠ 0) (hC : C ≠ 0) (hAC : A - C ≠ 0)
    (h2CA : 2 * C - A ≠ 0) (hC2A : C - 2 * A ≠ 0) :
    (baseJetCoefficientMatrix A C β).det =
      3 * β ^ 3 / (4 * A ^ 2 * C ^ 3 * (2 * A - C)) := by
  have h2AC : 2 * A - C ≠ 0 := by
    simpa only [neg_sub] using neg_ne_zero.mpr hC2A
  have h2CA' : C * 2 - A ≠ 0 := by simpa only [mul_comm] using h2CA
  have hC2A' : C - A * 2 ≠ 0 := by simpa only [mul_comm] using hC2A
  have h2AC' : A * 2 - C ≠ 0 := by simpa only [mul_comm] using h2AC
  rw [Matrix.det_fin_three (baseJetCoefficientMatrix A C β)]
  simp [baseJetCoefficientMatrix]
  field_simp [hA, hC, hAC, h2CA, hC2A, h2AC, h2CA', hC2A', h2AC']
  ring

theorem baseJetCoefficientMatrix_det_ne_zero (A C β : ℝ)
    (hA : A ≠ 0) (hC : C ≠ 0) (hβ : β ≠ 0) (hAC : A - C ≠ 0)
    (h2CA : 2 * C - A ≠ 0) (hC2A : C - 2 * A ≠ 0) :
    (baseJetCoefficientMatrix A C β).det ≠ 0 := by
  have h2AC : 2 * A - C ≠ 0 := by
    simpa only [neg_sub] using neg_ne_zero.mpr hC2A
  rw [baseJetCoefficientMatrix_det A C β hA hC hAC h2CA hC2A]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hβ))
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hA)) (pow_ne_zero 3 hC))
      h2AC)

end

end PanelMoments.SourceWeakHermitePolynomial
