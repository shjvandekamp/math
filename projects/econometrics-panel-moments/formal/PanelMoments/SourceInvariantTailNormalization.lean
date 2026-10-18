import PanelMoments.SourceInvariantTailConcretePolynomials

set_option autoImplicit false

/-!
# Rational-to-polynomial normalization of the invariant tail

Put n=m-2. The old coordinate is r(r-z)P(r)/Λ(r), and the determinant
product is C r^(n+2) U(r)/Λ(r), with U=(1-ar)V. This module checks the
literal rational transfer and its three new generators against the
existing concrete normalized polynomials. The denominator Λ is arbitrary;
every cancellation has an explicit nonzero hypothesis.

Reconstruction identities also hold at r=z. Normalization by r(r-z)
additionally requires r-z to be nonzero. Identifying these rational
formulas with the promoted source words remains a separate obligation.
No source-independence or rank assumption occurs here.
-/

namespace PanelMoments.SourceInvariantTailNormalization

noncomputable section

open Polynomial SourceInvariantTailConcretePolynomials
open SourceInvariantTailPolynomialExtension

def rationalCoordinate (Λ : ℝ → ℝ) (z : ℝ) (P : Polynomial ℝ) (r : ℝ) : ℝ :=
  r * (r - z) * P.eval r / Λ r

def determinantProduct (n : ℕ) (a cScale : ℝ) (V : Polynomial ℝ)
    (Λ : ℝ → ℝ) (r : ℝ) : ℝ :=
  cScale * r ^ (n + 2) * (oldProduct a V).eval r / Λ r

def delta (ell z r : ℝ) : ℝ := ell * (r - z) / r

def chi (A z b r : ℝ) : ℝ := 4 * b * (r - z) / (3 * (1 - A * r))

def blockDeterminant (A r : ℝ) : ℝ :=
  -3 * A * r / ((2 - A * r) * (1 - 2 * A * r))

def newDenominator (Λ : ℝ → ℝ) (A r : ℝ) : ℝ :=
  Λ r * (2 - A * r) * (1 - 2 * A * r) * (1 - A * r)

def rationalTransfer (n : ℕ) (a A z b ell cScale : ℝ)
    (V P : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ) : ℝ :=
  chi A z b r * rationalCoordinate Λ z P r -
    delta ell z r *
      (rationalCoordinate Λ z P (xi A) / determinantProduct n a cScale V Λ (xi A)) *
      determinantProduct n a cScale V Λ r * (blockDeterminant A r * qValue A z r)

def beta0 (a A z r : ℝ) : ℝ := 2 * qValue a z r / (2 - A * r)
def beta1 (a A z r : ℝ) : ℝ := -r * qValue a z r / (1 - 2 * A * r)
def beta2 (a A z r : ℝ) : ℝ :=
  blockDeterminant A r * qValue A z r +
    (r - z) * qValue a z r / (qValue a z (xi A) * (1 - A * r))

def barBeta2 (a A z r : ℝ) : ℝ :=
  beta2 a A z r + z / qValue a z (pole0 A) * beta0 a A z r +
    (1 / qValue a z (pole1 A)) * beta1 a A z r

def newLayer (n : ℕ) (a z ell cScale : ℝ) (V : Polynomial ℝ)
    (Λ : ℝ → ℝ) (r β : ℝ) : ℝ :=
  delta ell z r * determinantProduct n a cScale V Λ r * β

def normalizeValue (Λ : ℝ → ℝ) (A z r value : ℝ) : ℝ :=
  newDenominator Λ A r * value / (r * (r - z))

/-- Units at the evaluation point; the old first-block factor is separate. -/
structure EvaluationUnits (Λ : ℝ → ℝ) (A r : ℝ) : Prop where
  r_ne_zero : r ≠ 0
  denominator_ne_zero : Λ r ≠ 0
  form0_ne_zero : 2 - A * r ≠ 0
  form1_ne_zero : 1 - 2 * A * r ≠ 0
  form2_ne_zero : 1 - A * r ≠ 0

theorem newDenominator_ne_zero (Λ : ℝ → ℝ) (A r : ℝ)
    (h : EvaluationUnits Λ A r) : newDenominator Λ A r ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h.denominator_ne_zero
    h.form0_ne_zero) h.form1_ne_zero) h.form2_ne_zero

/-- Cancel the old denominator before performing the transfer calculation. -/
theorem coordinate_div_determinantProduct (n : ℕ) (a z cScale : ℝ)
    (V P : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (hr : r ≠ 0) (hC : cScale ≠ 0) (hΛ : Λ r ≠ 0)
    (hU : (oldProduct a V).eval r ≠ 0) :
    rationalCoordinate Λ z P r / determinantProduct n a cScale V Λ r =
      (r - z) * P.eval r / (cScale * r ^ (n + 1) * (oldProduct a V).eval r) := by
  have hp : r ^ (n + 2) = r ^ (n + 1) * r := by
    simpa only [Nat.add_assoc] using pow_succ r (n + 1)
  unfold rationalCoordinate determinantProduct
  rw [hp]
  field_simp [hr, hC, hΛ, hU, pow_ne_zero (n + 1) hr]

theorem blockDeterminant_mul_qValue (A z r : ℝ)
    (h0 : 2 - A * r ≠ 0) (_h1 : 1 - 2 * A * r ≠ 0)
    (h2 : 1 - A * r ≠ 0) :
    blockDeterminant A r * qValue A z r =
      -A * r * numeratorValue A z r /
        ((2 - A * r) * (1 - 2 * A * r) * (1 - A * r)) := by
  unfold blockDeterminant qValue
  field_simp [h0, _h1, h2]

/-- The literal transfer reconstructs exactly the already defined polynomial map. -/
theorem rationalTransfer_eq_coordinate (n : ℕ) (a A z b ell cScale : ℝ)
    (V P : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (hA : A ≠ 0) (hC : cScale ≠ 0)
    (hΛxi : Λ (xi A) ≠ 0) (hUxi : (oldProduct a V).eval (xi A) ≠ 0) :
    rationalTransfer n a A z b ell cScale V P Λ r =
      rationalCoordinate (newDenominator Λ A) z
        (transferPolynomial (transferFactor A z b)
          (transferCorrection n a A z ell V) (xi A) P) r := by
  have hxi : xi A ≠ 0 := one_div_ne_zero hA
  have hp : r ^ (n + 2) = r ^ (n + 1) * r := by
    simpa only [Nat.add_assoc] using pow_succ r (n + 1)
  unfold rationalTransfer
  rw [coordinate_div_determinantProduct n a z cScale V P Λ (xi A)
    hxi hC hΛxi hUxi,
    blockDeterminant_mul_qValue A z r h.form0_ne_zero h.form1_ne_zero h.form2_ne_zero]
  simp only [rationalCoordinate, determinantProduct, chi, delta, newDenominator,
    transferPolynomial, transferFactor, transferCorrection, form0, form1,
    eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow, numerator_eval]
  rw [hp]
  generalize he0 : 2 - A * r = f0
  generalize he1 : 1 - 2 * A * r = f1
  generalize he2 : 1 - A * r = f2
  have hf0 : f0 ≠ 0 := he0 ▸ h.form0_ne_zero
  have hf1 : f1 ≠ 0 := he1 ▸ h.form1_ne_zero
  have hf2 : f2 ≠ 0 := he2 ▸ h.form2_ne_zero
  field_simp [h.r_ne_zero, h.denominator_ne_zero, hf0, hf1, hf2,
    hC, hUxi, pow_ne_zero (n + 1) hxi]
  ring

theorem normalize_coordinate (Λ : ℝ → ℝ) (A z r : ℝ) (P : Polynomial ℝ)
    (h : EvaluationUnits Λ A r) (hrz : r - z ≠ 0) :
    normalizeValue Λ A z r (rationalCoordinate (newDenominator Λ A) z P r) =
      P.eval r := by
  unfold normalizeValue rationalCoordinate
  field_simp [newDenominator_ne_zero Λ A r h, h.r_ne_zero, hrz]

theorem rationalTransfer_normalized (n : ℕ) (a A z b ell cScale : ℝ)
    (V P : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (hrz : r - z ≠ 0)
    (hA : A ≠ 0) (hC : cScale ≠ 0) (hΛxi : Λ (xi A) ≠ 0)
    (hUxi : (oldProduct a V).eval (xi A) ≠ 0) :
    normalizeValue Λ A z r (rationalTransfer n a A z b ell cScale V P Λ r) =
      (transferPolynomial (transferFactor A z b)
        (transferCorrection n a A z ell V) (xi A) P).eval r := by
  rw [rationalTransfer_eq_coordinate n a A z b ell cScale V P Λ r h hA hC hΛxi hUxi]
  exact normalize_coordinate Λ A z r _ h hrz

theorem newLayer_beta0_eq_coordinate (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (ha : 1 - a * r ≠ 0) :
    newLayer n a z ell cScale V Λ r (beta0 a A z r) =
      rationalCoordinate (newDenominator Λ A) z
        (commonFactor n ell cScale V * n0 a A z) r := by
  simp only [newLayer, delta, determinantProduct, beta0, qValue, rationalCoordinate,
    newDenominator, commonFactor, n0, oldProduct, form1, form2,
    eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_pow, numerator_eval,
    pow_add, pow_two]
  generalize he0 : 2 - A * r = f0
  generalize he1 : 1 - 2 * A * r = f1
  generalize he2 : 1 - A * r = f2
  generalize hea : 1 - a * r = fa
  have hf0 : f0 ≠ 0 := he0 ▸ h.form0_ne_zero
  have hf1 : f1 ≠ 0 := he1 ▸ h.form1_ne_zero
  have hf2 : f2 ≠ 0 := he2 ▸ h.form2_ne_zero
  have hfa : fa ≠ 0 := hea ▸ ha
  field_simp [h.r_ne_zero, h.denominator_ne_zero, hf0, hf1, hf2, hfa]

theorem newLayer_beta1_eq_coordinate (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (ha : 1 - a * r ≠ 0) :
    newLayer n a z ell cScale V Λ r (beta1 a A z r) =
      rationalCoordinate (newDenominator Λ A) z
        (commonFactor n ell cScale V * n1 a A z) r := by
  simp only [newLayer, delta, determinantProduct, beta1, qValue, rationalCoordinate,
    newDenominator, commonFactor, n1, oldProduct, form0, form2,
    eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_pow, numerator_eval,
    pow_add, pow_two]
  generalize he0 : 2 - A * r = f0
  generalize he1 : 1 - 2 * A * r = f1
  generalize he2 : 1 - A * r = f2
  generalize hea : 1 - a * r = fa
  have hf0 : f0 ≠ 0 := he0 ▸ h.form0_ne_zero
  have hf1 : f1 ≠ 0 := he1 ▸ h.form1_ne_zero
  have hf2 : f2 ≠ 0 := he2 ▸ h.form2_ne_zero
  have hfa : fa ≠ 0 := hea ▸ ha
  field_simp [h.r_ne_zero, h.denominator_ne_zero, hf0, hf1, hf2, hfa]

theorem newLayer_beta2_eq_coordinate (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (ha : 1 - a * r ≠ 0)
    (hA : A ≠ 0) (hAa : A - a ≠ 0) (hN : xiNumerator a A z ≠ 0) :
    newLayer n a z ell cScale V Λ r (beta2 a A z r) =
      rationalCoordinate (newDenominator Λ A) z
        (commonFactor n ell cScale V * n2 a A z) r := by
  have hQ : qValue a z (xi A) ≠ 0 := by
    rw [qValue_xi a A z hA hAa]
    exact div_ne_zero hN (mul_ne_zero (mul_ne_zero (by norm_num) hA) hAa)
  rw [n2_eq_qValue a A z hA hAa hN]
  unfold beta2
  rw [blockDeterminant_mul_qValue A z r h.form0_ne_zero h.form1_ne_zero h.form2_ne_zero]
  simp only [newLayer, delta, determinantProduct, rationalCoordinate,
    newDenominator, commonFactor, oldProduct, form0, form1, form2,
    eval_add, eval_neg, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_pow,
    numerator_eval, pow_add, pow_two]
  rw [show qValue a z r = numeratorValue a z r / (3 * (1 - a * r)) from rfl]
  generalize he0 : 2 - A * r = f0
  generalize he1 : 1 - 2 * A * r = f1
  generalize he2 : 1 - A * r = f2
  generalize hea : 1 - a * r = fa
  have hf0 : f0 ≠ 0 := he0 ▸ h.form0_ne_zero
  have hf1 : f1 ≠ 0 := he1 ▸ h.form1_ne_zero
  have hf2 : f2 ≠ 0 := he2 ▸ h.form2_ne_zero
  have hfa : fa ≠ 0 := hea ▸ ha
  field_simp [h.r_ne_zero, h.denominator_ne_zero, hf0, hf1, hf2, hfa, hQ]

/-- The exact unitriangular replacement of the third rational generator is retained. -/
theorem newLayer_barBeta2_eq_coordinate (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (ha : 1 - a * r ≠ 0)
    (hA : A ≠ 0) (hAa : A - a ≠ 0) (hN : xiNumerator a A z ≠ 0)
    (hAa0 : A - 2 * a ≠ 0) (hAa1 : 2 * A - a ≠ 0)
    (hN0 : pole0Numerator a A z ≠ 0) (hN1 : pole1Numerator a A z ≠ 0) :
    newLayer n a z ell cScale V Λ r (barBeta2 a A z r) =
      rationalCoordinate (newDenominator Λ A) z
        (commonFactor n ell cScale V * barN2 a A z) r := by
  have hd : newLayer n a z ell cScale V Λ r (barBeta2 a A z r) =
      newLayer n a z ell cScale V Λ r (beta2 a A z r) +
        z / qValue a z (pole0 A) * newLayer n a z ell cScale V Λ r (beta0 a A z r) +
        (1 / qValue a z (pole1 A)) *
          newLayer n a z ell cScale V Λ r (beta1 a A z r) := by
    unfold newLayer barBeta2
    ring
  rw [hd, newLayer_beta2_eq_coordinate n a A z ell cScale V Λ r h ha hA hAa hN,
    newLayer_beta0_eq_coordinate n a A z ell cScale V Λ r h ha,
    newLayer_beta1_eq_coordinate n a A z ell cScale V Λ r h ha,
    barN2_eq_qValue a A z hA hAa0 hAa1 hN0 hN1]
  simp only [rationalCoordinate, eval_mul, eval_add, eval_C]
  ring

theorem newLayer_beta0_normalized (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (hrz : r - z ≠ 0) (ha : 1 - a * r ≠ 0) :
    normalizeValue Λ A z r (newLayer n a z ell cScale V Λ r (beta0 a A z r)) =
      (commonFactor n ell cScale V * n0 a A z).eval r := by
  rw [newLayer_beta0_eq_coordinate n a A z ell cScale V Λ r h ha]
  exact normalize_coordinate Λ A z r _ h hrz

theorem newLayer_beta1_normalized (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (hrz : r - z ≠ 0) (ha : 1 - a * r ≠ 0) :
    normalizeValue Λ A z r (newLayer n a z ell cScale V Λ r (beta1 a A z r)) =
      (commonFactor n ell cScale V * n1 a A z).eval r := by
  rw [newLayer_beta1_eq_coordinate n a A z ell cScale V Λ r h ha]
  exact normalize_coordinate Λ A z r _ h hrz

theorem newLayer_beta2_normalized (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (hrz : r - z ≠ 0) (ha : 1 - a * r ≠ 0)
    (hA : A ≠ 0) (hAa : A - a ≠ 0) (hN : xiNumerator a A z ≠ 0) :
    normalizeValue Λ A z r (newLayer n a z ell cScale V Λ r (beta2 a A z r)) =
      (commonFactor n ell cScale V * n2 a A z).eval r := by
  rw [newLayer_beta2_eq_coordinate n a A z ell cScale V Λ r h ha hA hAa hN]
  exact normalize_coordinate Λ A z r _ h hrz

theorem newLayer_barBeta2_normalized (n : ℕ) (a A z ell cScale : ℝ)
    (V : Polynomial ℝ) (Λ : ℝ → ℝ) (r : ℝ)
    (h : EvaluationUnits Λ A r) (hrz : r - z ≠ 0) (ha : 1 - a * r ≠ 0)
    (hA : A ≠ 0) (hAa : A - a ≠ 0) (hN : xiNumerator a A z ≠ 0)
    (hAa0 : A - 2 * a ≠ 0) (hAa1 : 2 * A - a ≠ 0)
    (hN0 : pole0Numerator a A z ≠ 0) (hN1 : pole1Numerator a A z ≠ 0) :
    normalizeValue Λ A z r (newLayer n a z ell cScale V Λ r (barBeta2 a A z r)) =
      (commonFactor n ell cScale V * barN2 a A z).eval r := by
  rw [newLayer_barBeta2_eq_coordinate n a A z ell cScale V Λ r h ha hA hAa hN
    hAa0 hAa1 hN0 hN1]
  exact normalize_coordinate Λ A z r _ h hrz

end

end PanelMoments.SourceInvariantTailNormalization
