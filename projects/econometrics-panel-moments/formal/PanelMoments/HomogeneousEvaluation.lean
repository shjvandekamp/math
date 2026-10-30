import PanelMoments.Polynomial
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Evaluation and dehomogenization in a fixed degree

Setting the first homogeneous coordinate to one sends three-variable
homogeneous polynomials to the two-effect polynomial ring used by the model.
Although that substitution is not injective on the full polynomial ring, it is
injective in each fixed homogeneous degree. The proof uses homogeneous scaling
and the polynomial identity theorem on the positive three-dimensional orthant.
-/

namespace PanelMoments.HomogeneousEvaluation

open scoped BigOperators
open MvPolynomial

noncomputable section

abbrev HomogeneousPoly := MvPolynomial (Fin 3) ℝ
abbrev EffectPoly := MvPolynomial (Fin 2) ℝ
abbrev Homogeneous (d : ℕ) := homogeneousSubmodule (Fin 3) ℝ d

/-- Scalar multiplication of every coordinate scales a homogeneous polynomial
by the corresponding power of the scalar, including when that scalar is zero. -/
theorem eval_smul_of_isHomogeneous {Q d : ℕ} {p : MvPolynomial (Fin Q) ℝ}
    (hp : p.IsHomogeneous d) (c : ℝ) (x : Fin Q → ℝ) :
    eval (c • x) p = c ^ d * eval x p := by
  classical
  simp only [eval_eq', Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdegree : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hm)
  have hpower : (∏ i, c ^ m i) = c ^ d := by
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, hdegree]
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [hpower]
  ring

/-- Substitute `1` for `X 0` and retain the other two variables. -/
def dehomogenize : HomogeneousPoly →ₐ[ℝ] EffectPoly :=
  aeval (Fin.cons 1 X)

@[simp]
theorem dehomogenize_X_zero : dehomogenize (X 0) = 1 := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_succ (i : Fin 2) : dehomogenize (X i.succ) = X i := by
  simp [dehomogenize]

theorem dehomogenize_X (i : Fin 3) : dehomogenize (X i) = effectPoly 2 i := by
  simp [dehomogenize, effectPoly]

/-- Evaluating the dehomogenized polynomial is evaluation on the affine chart
whose first homogeneous coordinate equals one. -/
theorem eval_dehomogenize (p : HomogeneousPoly) (η : Fin 2 → ℝ) :
    eval η (dehomogenize p) = eval (Fin.cons 1 η) p := by
  change aeval η (dehomogenize p) = aeval (Fin.cons 1 η) p
  have h : (aeval η).comp dehomogenize = aeval (Fin.cons 1 η) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [dehomogenize]
  exact AlgHom.congr_fun h p

theorem smul_normalized_coordinates (x : Fin 3 → ℝ) (hx : x 0 ≠ 0) :
    x 0 • Fin.cons 1 (fun i : Fin 2 => x i.succ / x 0) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.smul_apply, smul_eq_mul]
  · simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, hx,
      mul_comm, mul_left_comm, mul_assoc]

/-- Evaluate any point whose first coordinate is nonzero through the affine
chart and the degree-dependent scale factor. -/
theorem eval_eq_first_pow_mul_dehomogenize {d : ℕ} {p : HomogeneousPoly}
    (hp : p.IsHomogeneous d) (x : Fin 3 → ℝ) (hx : x 0 ≠ 0) :
    eval x p = (x 0) ^ d *
      eval (fun i : Fin 2 => x i.succ / x 0) (dehomogenize p) := by
  rw [eval_dehomogenize]
  have hscale := eval_smul_of_isHomogeneous (Q := 3) (d := d) (p := p)
    hp (x 0) (Fin.cons 1 (fun i : Fin 2 => x i.succ / x 0))
  rw [smul_normalized_coordinates x hx] at hscale
  exact hscale

/-- A homogeneous polynomial vanishes identically exactly when its
dehomogenization vanishes identically. Here `Q = 3` in the identity theorem
counts all three homogeneous coordinates, not the model's nonbaseline states. -/
theorem dehomogenize_eq_zero_iff {d : ℕ} {p : HomogeneousPoly}
    (hp : p.IsHomogeneous d) : dehomogenize p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply (PanelMoments.polynomial_eq_zero_iff_positive_evaluations (Q := 3) p).mpr
    intro x hx
    rw [eval_eq_first_pow_mul_dehomogenize hp x (ne_of_gt (hx 0)), h, map_zero, mul_zero]
  · rintro rfl
    exact map_zero dehomogenize

theorem dehomogenize_eq_iff {d : ℕ} {p q : HomogeneousPoly}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    dehomogenize p = dehomogenize q ↔ p = q := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply (dehomogenize_eq_zero_iff (hp.sub hq)).mp
    rw [map_sub, h, sub_self]
  · rintro rfl
    rfl

/-- Dehomogenization restricted to a fixed homogeneous degree. -/
def dehomogenizeLinear (d : ℕ) : Homogeneous d →ₗ[ℝ] EffectPoly :=
  dehomogenize.toLinearMap.domRestrict (homogeneousSubmodule (Fin 3) ℝ d)

@[simp]
theorem dehomogenizeLinear_apply (d : ℕ) (p : Homogeneous d) :
    dehomogenizeLinear d p = dehomogenize p.1 := rfl

theorem dehomogenizeLinear_injective (d : ℕ) :
    Function.Injective (dehomogenizeLinear d) := by
  intro p q h
  apply Subtype.ext
  exact (dehomogenize_eq_iff p.2 q.2).mp h

end

end PanelMoments.HomogeneousEvaluation
