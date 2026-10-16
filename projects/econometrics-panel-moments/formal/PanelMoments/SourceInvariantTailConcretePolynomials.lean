import PanelMoments.SourceInvariantTailPolynomialExtension
import PanelMoments.SourceWeakTransferInterpolation

set_option autoImplicit false

/-!
# Concrete normalized polynomials for the invariant tail

Put n=m-2, U=(1-aX)V, xi=1/A, p0=2/A, and p1=1/(2A).
The displayed transfer is F*P + C(P(xi))*K. Its three additional columns
are B*n0, B*n1, B*barN2, where B=ell*cScale*X^n*V and cScale is the
actual scalar (-3)^m times the product of the old a parameters.

The coefficients of n2 and barN2 use the equivalent expressions
1/(3Q(xi))=A(A-a)/xiNumerator, z/Q(p0)=3zA(A-2a)/pole0Numerator,
and 1/Q(p1)=6A(2A-a)/pole1Numerator. Thus barN2 replaces n2 by
n2 + z*n0/Q(p0) + n1/Q(p1), a unitriangular scalar column operation.
The Q-value identities are checked below. No column rescaling is hidden.

The explicit factor hypotheses imply every polynomial evaluation condition
in SourceInvariantTailPolynomialExtension. The resulting injectivity is
therefore a theorem about these displayed polynomials, with no rank premise.
Identifying the normalized polynomials with actual source words and proving
their finite-length initialization remain separate formal obligations.
-/

namespace PanelMoments.SourceInvariantTailConcretePolynomials

noncomputable section

open Polynomial
open SourceInvariantTailPolynomialExtension

def xi (A : ℝ) : ℝ := 1 / A
def pole0 (A : ℝ) : ℝ := 2 / A
def pole1 (A : ℝ) : ℝ := 1 / (2 * A)

def numeratorValue (a z r : ℝ) : ℝ :=
  a * r ^ 2 + (2 * a * z - 2) * r - z

def numerator (a z : ℝ) : Polynomial ℝ :=
  C a * X ^ 2 + C (2 * a * z - 2) * X - C z

def qValue (a z r : ℝ) : ℝ := numeratorValue a z r / (3 * (1 - a * r))

def xiNumerator (a A z : ℝ) : ℝ := a - 2 * A + A * z * (2 * a - A)
def pole0Numerator (a A z : ℝ) : ℝ := 4 * (a - A) + A * z * (4 * a - A)
def pole1Numerator (a A z : ℝ) : ℝ := a - 4 * A + 4 * A * z * (a - A)

def form0 (A : ℝ) : Polynomial ℝ := C 2 - C A * X
def form1 (A : ℝ) : Polynomial ℝ := 1 - C (2 * A) * X
def form2 (A : ℝ) : Polynomial ℝ := 1 - C A * X

def oldProduct (a : ℝ) (V : Polynomial ℝ) : Polynomial ℝ := form2 a * V

def commonFactor (n : ℕ) (ell cScale : ℝ) (V : Polynomial ℝ) : Polynomial ℝ :=
  C (ell * cScale) * X ^ n * V

def n0 (a A z : ℝ) : Polynomial ℝ :=
  C (2 / 3 : ℝ) * numerator a z * form1 A * form2 A

def n1 (a A z : ℝ) : Polynomial ℝ :=
  C (-1 / 3 : ℝ) * X * numerator a z * form0 A * form2 A

def n2 (a A z : ℝ) : Polynomial ℝ :=
  -C A * X * form2 a * numerator A z +
    C (A * (A - a) / xiNumerator a A z) *
      (X - C z) * numerator a z * form0 A * form1 A

def barN2 (a A z : ℝ) : Polynomial ℝ :=
  n2 a A z + C (3 * z * A * (A - 2 * a) / pole0Numerator a A z) * n0 a A z +
    C (6 * A * (2 * A - a) / pole1Numerator a A z) * n1 a A z

def transferFactor (A z b : ℝ) : Polynomial ℝ :=
  C (4 * b / 3) * (X - C z) * form0 A * form1 A

def transferCorrection (n : ℕ) (a A z ell : ℝ) (V : Polynomial ℝ) : Polynomial ℝ :=
  C (ell * A * (xi A - z) / ((xi A) ^ (n + 1) * (oldProduct a V).eval (xi A))) *
    X ^ (n + 1) * oldProduct a V * numerator A z

theorem numerator_eval (a z r : ℝ) : (numerator a z).eval r = numeratorValue a z r := by
  simp [numerator, numeratorValue]

theorem numerator_eval_xi (a A z : ℝ) (hA : A ≠ 0) :
    (numerator a z).eval (xi A) = xiNumerator a A z / A ^ 2 := by
  simp [numerator, xi]
  field_simp [hA]
  unfold xiNumerator
  ring

theorem numerator_eval_pole0 (a A z : ℝ) (hA : A ≠ 0) :
    (numerator a z).eval (pole0 A) = pole0Numerator a A z / A ^ 2 := by
  simp [numerator, pole0]
  field_simp [hA]
  unfold pole0Numerator
  ring

theorem numerator_eval_pole1 (a A z : ℝ) (hA : A ≠ 0) :
    (numerator a z).eval (pole1 A) = pole1Numerator a A z / (4 * A ^ 2) := by
  simp [numerator, pole1]
  field_simp [hA]
  unfold pole1Numerator
  ring

theorem qValue_xi (a A z : ℝ) (hA : A ≠ 0) (hAa : A - a ≠ 0) :
    qValue a z (xi A) = xiNumerator a A z / (3 * A * (A - a)) := by
  unfold qValue numeratorValue xi xiNumerator
  field_simp [hA, hAa]
  ring

theorem qValue_pole0 (a A z : ℝ) (hA : A ≠ 0) (hAa : A - 2 * a ≠ 0) :
    qValue a z (pole0 A) = pole0Numerator a A z / (3 * A * (A - 2 * a)) := by
  have hAa' : A - a * 2 ≠ 0 := by simpa only [mul_comm] using hAa
  unfold qValue numeratorValue pole0 pole0Numerator
  field_simp [hA, hAa, hAa']
  ring

theorem qValue_pole1 (a A z : ℝ) (hA : A ≠ 0) (hAa : 2 * A - a ≠ 0) :
    qValue a z (pole1 A) = pole1Numerator a A z / (6 * A * (2 * A - a)) := by
  have hAa' : A * 2 - a ≠ 0 := by simpa only [mul_comm] using hAa
  unfold qValue numeratorValue pole1 pole1Numerator
  field_simp [hA, hAa, hAa']
  ring

theorem n2_eq_qValue (a A z : ℝ) (hA : A ≠ 0) (hAa : A - a ≠ 0)
    (hN : xiNumerator a A z ≠ 0) :
    n2 a A z = -C A * X * form2 a * numerator A z +
      C (1 / (3 * qValue a z (xi A))) *
        (X - C z) * numerator a z * form0 A * form1 A := by
  have hc : 1 / (3 * qValue a z (xi A)) = A * (A - a) / xiNumerator a A z := by
    rw [qValue_xi a A z hA hAa]
    field_simp [hA, hAa, hN]
  simp only [n2, hc]

/-- The third new column is obtained by the stated unitriangular operation;
the first two columns are unchanged. -/
theorem barN2_eq_qValue (a A z : ℝ) (hA : A ≠ 0)
    (hAa0 : A - 2 * a ≠ 0) (hAa1 : 2 * A - a ≠ 0)
    (hN0 : pole0Numerator a A z ≠ 0) (hN1 : pole1Numerator a A z ≠ 0) :
    barN2 a A z = n2 a A z + C (z / qValue a z (pole0 A)) * n0 a A z +
      C (1 / qValue a z (pole1 A)) * n1 a A z := by
  have h0 : z / qValue a z (pole0 A) = 3 * z * A * (A - 2 * a) / pole0Numerator a A z := by
    rw [qValue_pole0 a A z hA hAa0]
    field_simp [hA, hAa0, hN0]
  have h1 : 1 / qValue a z (pole1 A) = 6 * A * (2 * A - a) / pole1Numerator a A z := by
    rw [qValue_pole1 a A z hA hAa1]
    field_simp [hA, hAa1, hN1]
  simp only [barN2, h0, h1]

theorem form2_eval_xi (A : ℝ) (hA : A ≠ 0) : (form2 A).eval (xi A) = 0 := by
  simp [form2, xi, hA]

theorem form0_eval_pole0 (A : ℝ) (hA : A ≠ 0) : (form0 A).eval (pole0 A) = 0 := by
  simp [form0, pole0]
  field_simp [hA]
  ring

theorem form1_eval_pole1 (A : ℝ) (hA : A ≠ 0) : (form1 A).eval (pole1 A) = 0 := by
  simp [form1, pole1]
  field_simp [hA]
  ring

theorem n0_eval_xi (a A z : ℝ) (hA : A ≠ 0) : (n0 a A z).eval (xi A) = 0 := by
  simp [n0, form2_eval_xi A hA]

theorem n1_eval_xi (a A z : ℝ) (hA : A ≠ 0) : (n1 a A z).eval (xi A) = 0 := by
  simp [n1, form2_eval_xi A hA]

theorem n2_eval_xi (a A z : ℝ) (hA : A ≠ 0)
    (hN : xiNumerator a A z ≠ 0) : (n2 a A z).eval (xi A) = 0 := by
  simp [n2, numerator, form0, form1, form2, xi]
  field_simp [hA, hN]
  unfold xiNumerator
  ring

theorem barN2_eval_xi (a A z : ℝ) (hA : A ≠ 0)
    (hN : xiNumerator a A z ≠ 0) : (barN2 a A z).eval (xi A) = 0 := by
  simp [barN2, n0_eval_xi a A z hA, n1_eval_xi a A z hA, n2_eval_xi a A z hA hN]

theorem n0_eval_pole1 (a A z : ℝ) (hA : A ≠ 0) : (n0 a A z).eval (pole1 A) = 0 := by
  simp [n0, form1_eval_pole1 A hA]

theorem n1_eval_pole0 (a A z : ℝ) (hA : A ≠ 0) : (n1 a A z).eval (pole0 A) = 0 := by
  simp [n1, form0_eval_pole0 A hA]

theorem n0_eval_pole0 (a A z : ℝ) (hA : A ≠ 0) :
    (n0 a A z).eval (pole0 A) = 2 * pole0Numerator a A z / A ^ 2 := by
  simp [n0, numerator, form1, form2, pole0]
  field_simp [hA]
  unfold pole0Numerator
  ring

theorem n1_eval_pole1 (a A z : ℝ) (hA : A ≠ 0) :
    (n1 a A z).eval (pole1 A) = -pole1Numerator a A z / (32 * A ^ 3) := by
  simp [n1, numerator, form0, form2, pole1]
  field_simp [hA]
  unfold pole1Numerator
  ring

theorem n2_eval_pole0 (a A z : ℝ) (hA : A ≠ 0) :
    (n2 a A z).eval (pole0 A) = -6 * z * (1 - 2 * a / A) := by
  simp [n2, form0_eval_pole0 A hA]
  simp [numerator, form2, pole0]
  field_simp [hA]
  ring

theorem n2_eval_pole1 (a A z : ℝ) (hA : A ≠ 0) :
    (n2 a A z).eval (pole1 A) = 3 * (1 - a / (2 * A)) / (8 * A) := by
  simp [n2, form1_eval_pole1 A hA]
  simp [numerator, form2, pole1]
  field_simp [hA]
  ring

theorem barN2_eval_pole0 (a A z : ℝ) (hA : A ≠ 0)
    (hN : pole0Numerator a A z ≠ 0) : (barN2 a A z).eval (pole0 A) = 0 := by
  simp [barN2, n0_eval_pole0 a A z hA, n1_eval_pole0 a A z hA,
    n2_eval_pole0 a A z hA]
  field_simp [hA, hN]
  ring

theorem barN2_eval_pole1 (a A z : ℝ) (hA : A ≠ 0)
    (hN : pole1Numerator a A z ≠ 0) : (barN2 a A z).eval (pole1 A) = 0 := by
  simp [barN2, n0_eval_pole1 a A z hA, n1_eval_pole1 a A z hA,
    n2_eval_pole1 a A z hA]
  field_simp [hA, hN]
  ring

theorem barN2_eval_z (a A z : ℝ)
    (hN0 : pole0Numerator a A z ≠ 0) (hN1 : pole1Numerator a A z ≠ 0) :
    (barN2 a A z).eval z =
      -3 * A * z ^ 2 * SourceWeakTransferInterpolation.positiveFactor a A *
        (1 - a * z) * (2 - A * z) * (1 - 2 * A * z) * (1 - A * z) /
          (pole0Numerator a A z * pole1Numerator a A z) := by
  simp [barN2, n0, n1, n2, numerator, form0, form1, form2]
  field_simp [hN0, hN1]
  unfold pole0Numerator pole1Numerator SourceWeakTransferInterpolation.positiveFactor
  ring

theorem transferFactor_eval_xi (A z b : ℝ) (hA : A ≠ 0) :
    (transferFactor A z b).eval (xi A) = -(4 * b / 3) * (xi A - z) := by
  simp [transferFactor, form0, form1, xi]
  field_simp [hA]
  ring

theorem transferCorrection_eval_xi (n : ℕ) (a A z ell : ℝ) (V : Polynomial ℝ)
    (hA : A ≠ 0) (hU : (oldProduct a V).eval (xi A) ≠ 0) :
    (transferCorrection n a A z ell V).eval (xi A) = -ell * A * (xi A - z) ^ 2 := by
  have hxi : xi A ≠ 0 := one_div_ne_zero hA
  have hNA : (numerator A z).eval (xi A) = -(xi A - z) := by
    simp [numerator, xi]
    field_simp [hA]
    ring
  simp only [transferCorrection, eval_mul, eval_C, eval_pow, eval_X]
  rw [hNA]
  field_simp [pow_ne_zero (n + 1) hxi, hU]

theorem evaluation_pivot (n : ℕ) (a A z b ell : ℝ) (V : Polynomial ℝ)
    (hA : A ≠ 0) (hU : (oldProduct a V).eval (xi A) ≠ 0) :
    (transferFactor A z b).eval (xi A) +
        (transferCorrection n a A z ell V).eval (xi A) =
      -(xi A - z) * (4 * b / 3 + ell * (1 - A * z)) := by
  rw [transferFactor_eval_xi A z b hA, transferCorrection_eval_xi n a A z ell V hA hU]
  unfold xi
  field_simp [hA]
  ring

theorem transferFactor_eval_pole0 (A z b : ℝ) (hA : A ≠ 0) :
    (transferFactor A z b).eval (pole0 A) = 0 := by
  simp [transferFactor, form0_eval_pole0 A hA]

theorem transferFactor_eval_pole1 (A z b : ℝ) (hA : A ≠ 0) :
    (transferFactor A z b).eval (pole1 A) = 0 := by
  simp [transferFactor, form1_eval_pole1 A hA]

theorem transferFactor_eval_z (A z b : ℝ) : (transferFactor A z b).eval z = 0 := by
  simp [transferFactor]

/-- Explicit scalar and old-product units, with no independence assumption. -/
structure TailUnits (a A z b ell cScale : ℝ) (V : Polynomial ℝ) : Prop where
  A_ne_zero : A ≠ 0
  b_ne_zero : b ≠ 0
  ell_ne_zero : ell ≠ 0
  cScale_ne_zero : cScale ≠ 0
  z_ne_zero : z ≠ 0
  xi_sub_z_ne_zero : xi A - z ≠ 0
  old_product_at_xi : (oldProduct a V).eval (xi A) ≠ 0
  V_at_pole0 : V.eval (pole0 A) ≠ 0
  V_at_pole1 : V.eval (pole1 A) ≠ 0
  V_at_z : V.eval z ≠ 0
  xi_numerator : xiNumerator a A z ≠ 0
  pole0_numerator : pole0Numerator a A z ≠ 0
  pole1_numerator : pole1Numerator a A z ≠ 0
  positive_factor : SourceWeakTransferInterpolation.positiveFactor a A ≠ 0
  old_z_factor : 1 - a * z ≠ 0
  new_z_factor0 : 2 - A * z ≠ 0
  new_z_factor1 : 1 - 2 * A * z ≠ 0
  new_z_factor2 : 1 - A * z ≠ 0
  eta_ne_zero : 4 * b / 3 + ell * (1 - A * z) ≠ 0

theorem commonFactor_eval_ne_zero (n : ℕ) (ell cScale r : ℝ) (V : Polynomial ℝ)
    (hell : ell ≠ 0) (hC : cScale ≠ 0) (hr : r ≠ 0) (hV : V.eval r ≠ 0) :
    (commonFactor n ell cScale V).eval r ≠ 0 := by
  simpa only [commonFactor, eval_mul, eval_C, eval_pow, eval_X] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero hell hC) (pow_ne_zero n hr)) hV

/-- The displayed normalized actual polynomials satisfy every structural
evaluation hypothesis of the polynomial extension theorem. -/
theorem concreteSeparationConditions (n : ℕ) (a A z b ell cScale : ℝ) (V : Polynomial ℝ)
    (h : TailUnits a A z b ell cScale V) :
    SeparationConditions (transferFactor A z b) (transferCorrection n a A z ell V)
      (commonFactor n ell cScale V * n0 a A z)
      (commonFactor n ell cScale V * n1 a A z)
      (commonFactor n ell cScale V * barN2 a A z)
      (xi A) (pole0 A) (pole1 A) z := by
  have hp0 : pole0 A ≠ 0 := div_ne_zero (by norm_num) h.A_ne_zero
  have hp1 : pole1 A ≠ 0 := one_div_ne_zero (mul_ne_zero (by norm_num) h.A_ne_zero)
  have hB0 := commonFactor_eval_ne_zero n ell cScale (pole0 A) V
    h.ell_ne_zero h.cScale_ne_zero hp0 h.V_at_pole0
  have hB1 := commonFactor_eval_ne_zero n ell cScale (pole1 A) V
    h.ell_ne_zero h.cScale_ne_zero hp1 h.V_at_pole1
  have hBz := commonFactor_eval_ne_zero n ell cScale z V
    h.ell_ne_zero h.cScale_ne_zero h.z_ne_zero h.V_at_z
  have hn0 : (n0 a A z).eval (pole0 A) ≠ 0 := by
    rw [n0_eval_pole0 a A z h.A_ne_zero]
    exact div_ne_zero (mul_ne_zero (by norm_num) h.pole0_numerator)
      (pow_ne_zero 2 h.A_ne_zero)
  have hn1 : (n1 a A z).eval (pole1 A) ≠ 0 := by
    rw [n1_eval_pole1 a A z h.A_ne_zero]
    exact div_ne_zero (neg_ne_zero.mpr h.pole1_numerator)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 h.A_ne_zero))
  have hn2 : (barN2 a A z).eval z ≠ 0 := by
    rw [barN2_eval_z a A z h.pole0_numerator h.pole1_numerator]
    apply div_ne_zero _ (mul_ne_zero h.pole0_numerator h.pole1_numerator)
    simp [h.A_ne_zero, h.z_ne_zero, h.positive_factor, h.old_z_factor,
      h.new_z_factor0, h.new_z_factor1, h.new_z_factor2]
  have hFxi : (transferFactor A z b).eval (xi A) ≠ 0 := by
    rw [transferFactor_eval_xi A z b h.A_ne_zero]
    exact mul_ne_zero
      (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) h.b_ne_zero) (by norm_num)))
      h.xi_sub_z_ne_zero
  refine {
    N0_at_xi := ?_, N1_at_xi := ?_, N2_at_xi := ?_,
    F_at_p0 := transferFactor_eval_pole0 A z b h.A_ne_zero,
    F_at_p1 := transferFactor_eval_pole1 A z b h.A_ne_zero,
    F_at_z := transferFactor_eval_z A z b,
    pivot_ne_zero := ?_, N0_at_p1 := ?_, N1_at_p0 := ?_,
    N2_at_p0 := ?_, N2_at_p1 := ?_,
    N0_at_p0_ne_zero := ?_, N1_at_p1_ne_zero := ?_, N2_at_z_ne_zero := ?_,
    F_ne_zero := ?_ }
  · simp [n0_eval_xi a A z h.A_ne_zero]
  · simp [n1_eval_xi a A z h.A_ne_zero]
  · simp [barN2_eval_xi a A z h.A_ne_zero h.xi_numerator]
  · rw [evaluation_pivot n a A z b ell V h.A_ne_zero h.old_product_at_xi]
    exact mul_ne_zero (neg_ne_zero.mpr h.xi_sub_z_ne_zero) h.eta_ne_zero
  · simp [n0_eval_pole1 a A z h.A_ne_zero]
  · simp [n1_eval_pole0 a A z h.A_ne_zero]
  · simp [barN2_eval_pole0 a A z h.A_ne_zero h.pole0_numerator]
  · simp [barN2_eval_pole1 a A z h.A_ne_zero h.pole1_numerator]
  · simpa only [eval_mul] using mul_ne_zero hB0 hn0
  · simpa only [eval_mul] using mul_ne_zero hB1 hn1
  · simpa only [eval_mul] using mul_ne_zero hBz hn2
  · intro hzero
    apply hFxi
    simp [hzero]

/-- Concrete simultaneous recovery of the three new coefficients and the
old polynomial, rather than an assumed rank of their columns. -/
theorem concreteExtension_injective (n : ℕ) (a A z b ell cScale : ℝ) (V : Polynomial ℝ)
    (h : TailUnits a A z b ell cScale V) :
    Function.Injective
      (combinedExtension (transferFactor A z b) (transferCorrection n a A z ell V)
        (commonFactor n ell cScale V * n0 a A z)
        (commonFactor n ell cScale V * n1 a A z)
        (commonFactor n ell cScale V * barN2 a A z) (xi A)) :=
  combinedExtension_injective (concreteSeparationConditions n a A z b ell cScale V h)

end

end PanelMoments.SourceInvariantTailConcretePolynomials
