import PanelMoments.SourceInvariantTailPolynomialExtension
import PanelMoments.SourceInvariantTailConcretePolynomials
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas

set_option autoImplicit false

/-!
# The degree-bounded invariant-tail extension

Explicit degree bounds put the polynomial extension into a linear map
from three scalars and a polynomial of degree at most d to polynomials
of degree at most d+3. Both spaces have dimension d+4.

The evaluation conditions from SourceInvariantTailPolynomialExtension
prove injectivity. Equality of the two computed dimensions then proves
surjectivity, a linear equivalence, and a unique decomposition of every
bounded target polynomial. No rank hypothesis is assumed.

Application to an actual source family still requires its polynomial
identification and finite initialization. The final part discharges the
degree bounds for the concrete normalized polynomials under the single
old-product bound V.natDegree ≤ n+1 and uses their proved evaluation
conditions to obtain a concrete unique-decomposition theorem.
-/

namespace PanelMoments.SourceInvariantTailBoundedExtension

noncomputable section

open Polynomial
open SourceInvariantTailPolynomialExtension

variable {R : Type*} [Field R]

/-- Bounds on the displayed factors, not on an unknown matrix rank. -/
structure DegreeBounds (d : ℕ) (F K N0 N1 N2 : Polynomial R) : Prop where
  F_degree : F.natDegree ≤ 3
  K_degree : K.natDegree ≤ d + 3
  N0_degree : N0.natDegree ≤ d + 3
  N1_degree : N1.natDegree ≤ d + 3
  N2_degree : N2.natDegree ≤ d + 3

theorem mem_degreeLT_succ_iff_natDegree_le (n : ℕ) (P : Polynomial R) :
    P ∈ degreeLT R (n + 1) ↔ P.natDegree ≤ n := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
  exact natDegree_le_iff_degree_le.symm

theorem extensionPolynomial_natDegree_le
    {d : ℕ} {F K N0 N1 N2 : Polynomial R}
    (h : DegreeBounds d F K N0 N1 N2) (ξ x y w : R)
    (P : Polynomial R) (hP : P.natDegree ≤ d) :
    (extensionPolynomial F K N0 N1 N2 ξ x y w P).natDegree ≤ d + 3 := by
  have hFP : (F * P).natDegree ≤ d + 3 := by
    calc
      (F * P).natDegree ≤ F.natDegree + P.natDegree := natDegree_mul_le
      _ ≤ 3 + d := add_le_add h.F_degree hP
      _ = d + 3 := Nat.add_comm 3 d
  unfold extensionPolynomial transferPolynomial
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        ((natDegree_C_mul_le x N0).trans h.N0_degree)
        ((natDegree_C_mul_le y N1).trans h.N1_degree))
      ((natDegree_C_mul_le w N2).trans h.N2_degree))
    (natDegree_add_le_of_degree_le hFP
      ((natDegree_C_mul_le (P.eval ξ) K).trans h.K_degree))

/-- The already defined polynomial extension, bundled as a linear map. -/
def extensionLinearMap (F K N0 N1 N2 : Polynomial R) (ξ : R) :
    (R × R × R × Polynomial R) →ₗ[R] Polynomial R where
  toFun := combinedExtension F K N0 N1 N2 ξ
  map_add' := by
    rintro ⟨x, y, w, P⟩ ⟨x', y', w', Q⟩
    change extensionPolynomial F K N0 N1 N2 ξ (x + x') (y + y') (w + w') (P + Q) =
      extensionPolynomial F K N0 N1 N2 ξ x y w P +
        extensionPolynomial F K N0 N1 N2 ξ x' y' w' Q
    simp only [extensionPolynomial, transferPolynomial, C_add, eval_add]
    ring
  map_smul' := by
    rintro t ⟨x, y, w, P⟩
    change extensionPolynomial F K N0 N1 N2 ξ (t * x) (t * y) (t * w) (t • P) =
      t • extensionPolynomial F K N0 N1 N2 ξ x y w P
    simp only [extensionPolynomial, transferPolynomial, smul_eq_C_mul, eval_mul, eval_C, C_mul]
    ring

def boundedExtension {d : ℕ} (F K N0 N1 N2 : Polynomial R) (ξ : R)
    (hdegree : DegreeBounds d F K N0 N1 N2) :
    (R × R × R × degreeLT R (d + 1)) →ₗ[R] degreeLT R (d + 4) where
  toFun input :=
    ⟨extensionPolynomial F K N0 N1 N2 ξ input.1 input.2.1 input.2.2.1
        (input.2.2.2 : Polynomial R),
      (mem_degreeLT_succ_iff_natDegree_le (d + 3) _).mpr
        (extensionPolynomial_natDegree_le hdegree ξ input.1 input.2.1 input.2.2.1
          (input.2.2.2 : Polynomial R)
          ((mem_degreeLT_succ_iff_natDegree_le d _).mp input.2.2.2.property))⟩
  map_add' := by
    intro input input'
    apply Subtype.ext
    exact (extensionLinearMap F K N0 N1 N2 ξ).map_add
      (input.1, input.2.1, input.2.2.1, (input.2.2.2 : Polynomial R))
      (input'.1, input'.2.1, input'.2.2.1, (input'.2.2.2 : Polynomial R))
  map_smul' := by
    intro t input
    apply Subtype.ext
    exact (extensionLinearMap F K N0 N1 N2 ξ).map_smul t
      (input.1, input.2.1, input.2.2.1, (input.2.2.2 : Polynomial R))

theorem boundedExtension_apply {d : ℕ}
    (F K N0 N1 N2 : Polynomial R) (ξ : R)
    (hdegree : DegreeBounds d F K N0 N1 N2)
    (input : R × R × R × degreeLT R (d + 1)) :
    (boundedExtension F K N0 N1 N2 ξ hdegree input : Polynomial R) =
      extensionPolynomial F K N0 N1 N2 ξ input.1 input.2.1 input.2.2.1
        (input.2.2.2 : Polynomial R) :=
  rfl

theorem boundedExtension_injective {d : ℕ}
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (hdegree : DegreeBounds d F K N0 N1 N2) :
    Function.Injective (boundedExtension F K N0 N1 N2 ξ hdegree) := by
  rintro ⟨x, y, w, P⟩ ⟨x', y', w', Q⟩ heq
  have heq' :
      extensionPolynomial F K N0 N1 N2 ξ x y w (P : Polynomial R) =
        extensionPolynomial F K N0 N1 N2 ξ x' y' w' (Q : Polynomial R) :=
    congrArg (fun S : degreeLT R (d + 4) => (S : Polynomial R)) heq
  rcases (extensionPolynomial_eq_iff h x y w x' y' w'
    (P : Polynomial R) (Q : Polynomial R)).mp heq' with ⟨hx, hy, hw, hPQ⟩
  exact Prod.ext hx (Prod.ext hy (Prod.ext hw (Subtype.ext hPQ)))

local instance degreeLT_finite (n : ℕ) : FiniteDimensional R (degreeLT R n) :=
  FiniteDimensional.of_injective (degreeLTEquiv R n).toLinearMap (degreeLTEquiv R n).injective

theorem degreeLT_finrank (n : ℕ) : Module.finrank R (degreeLT R n) = n := by
  rw [(degreeLTEquiv R n).finrank_eq]
  exact Module.finrank_fin_fun R

theorem bounded_finrank_eq (d : ℕ) :
    Module.finrank R (R × R × R × degreeLT R (d + 1)) =
      Module.finrank R (degreeLT R (d + 4)) := by
  simp only [Module.finrank_prod, CommSemiring.finrank_self, degreeLT_finrank]
  omega

/-- Surjectivity follows from the proved kernel separation and the computed
dimensions d+4=d+4, not from an assumed rank. -/
theorem boundedExtension_surjective {d : ℕ}
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (hdegree : DegreeBounds d F K N0 N1 N2) :
    Function.Surjective (boundedExtension F K N0 N1 N2 ξ hdegree) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (bounded_finrank_eq (R := R) d)).mp (boundedExtension_injective h hdegree)

def boundedExtensionEquiv {d : ℕ}
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (hdegree : DegreeBounds d F K N0 N1 N2) :
    (R × R × R × degreeLT R (d + 1)) ≃ₗ[R] degreeLT R (d + 4) :=
  LinearEquiv.ofBijective (boundedExtension F K N0 N1 N2 ξ hdegree)
    ⟨boundedExtension_injective h hdegree, boundedExtension_surjective h hdegree⟩

theorem boundedExtensionEquiv_apply {d : ℕ}
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (hdegree : DegreeBounds d F K N0 N1 N2)
    (input : R × R × R × degreeLT R (d + 1)) :
    (boundedExtensionEquiv h hdegree input : Polynomial R) =
      extensionPolynomial F K N0 N1 N2 ξ input.1 input.2.1 input.2.2.1
        (input.2.2.2 : Polynomial R) :=
  rfl

theorem existsUnique_boundedInput {d : ℕ}
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (hdegree : DegreeBounds d F K N0 N1 N2)
    (Q : degreeLT R (d + 4)) :
    ∃! input : R × R × R × degreeLT R (d + 1),
      boundedExtension F K N0 N1 N2 ξ hdegree input = Q := by
  obtain ⟨input, hinput⟩ := boundedExtension_surjective h hdegree Q
  refine ⟨input, hinput, ?_⟩
  intro input' hinput'
  exact boundedExtension_injective h hdegree (hinput'.trans hinput.symm)

section Concrete

open SourceInvariantTailConcretePolynomials

/-- For n=m-2 the old bound is d=3n+3. All concrete target polynomials
have degree at most 3n+6 when V has degree at most n+1. These bounds do
not require denominator nonvanishing or a rank assumption. -/
theorem concreteDegreeBounds (n : ℕ) (a A z b ell cScale : ℝ) (V : Polynomial ℝ)
    (hV : V.natDegree ≤ n + 1) :
    DegreeBounds (3 * n + 3) (transferFactor A z b)
      (transferCorrection n a A z ell V)
      (commonFactor n ell cScale V * n0 a A z)
      (commonFactor n ell cScale V * n1 a A z)
      (commonFactor n ell cScale V * barN2 a A z) := by
  have hX : (X : Polynomial ℝ).natDegree ≤ 1 := natDegree_X_le
  have hlin (c : ℝ) : (X - C c : Polynomial ℝ).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le hX (by simp))
  have hform2 (c : ℝ) : (form2 c).natDegree ≤ 1 := by
    unfold form2
    exact (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans hX))
  have hform0 : (form0 A).natDegree ≤ 1 := by
    unfold form0
    exact (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans hX))
  have hform1 : (form1 A).natDegree ≤ 1 := by
    simpa only [form1, form2] using hform2 (2 * A)
  have hnum (c : ℝ) : (numerator c z).natDegree ≤ 2 := by
    unfold numerator
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le c 2)
        (((natDegree_C_mul_le _ _).trans hX).trans (by omega))
    · simp
  have hU : (oldProduct a V).natDegree ≤ n + 2 := by
    unfold oldProduct
    calc
      (form2 a * V).natDegree ≤ 1 + (n + 1) :=
        natDegree_mul_le_of_le (hform2 a) hV
      _ = n + 2 := by omega
  have hB : (commonFactor n ell cScale V).natDegree ≤ 2 * n + 1 := by
    unfold commonFactor
    calc
      (C (ell * cScale) * X ^ n * V).natDegree ≤ n + (n + 1) :=
        natDegree_mul_le_of_le (natDegree_C_mul_X_pow_le _ n) hV
      _ = 2 * n + 1 := by omega
  have hF : (transferFactor A z b).natDegree ≤ 3 := by
    unfold transferFactor
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans (hlin z)) hform0) hform1
  have hK : (transferCorrection n a A z ell V).natDegree ≤ (3 * n + 3) + 3 := by
    unfold transferCorrection
    calc
      _ ≤ ((n + 1) + (n + 2)) + 2 :=
        natDegree_mul_le_of_le
          (natDegree_mul_le_of_le (natDegree_C_mul_X_pow_le _ (n + 1)) hU) (hnum A)
      _ ≤ (3 * n + 3) + 3 := by omega
  have hN0 : (n0 a A z).natDegree ≤ 4 := by
    unfold n0
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans (hnum a)) hform1)
      (hform2 A)
  have hN1 : (n1 a A z).natDegree ≤ 5 := by
    unfold n1
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le
        (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans hX) (hnum a)) hform0)
      (hform2 A)
  have hN2 : (n2 a A z).natDegree ≤ 5 := by
    have hneg : (-C A * X : Polynomial ℝ).natDegree ≤ 1 := by
      rw [← C_neg]
      exact (natDegree_C_mul_le _ _).trans hX
    unfold n2
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_le_of_le
        (natDegree_mul_le_of_le hneg (hform2 a)) (hnum A)).trans (by omega)
    · exact natDegree_mul_le_of_le
        (natDegree_mul_le_of_le
          (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans (hlin z)) (hnum a))
          hform0) hform1
  have hbar : (barN2 a A z).natDegree ≤ 5 := by
    unfold barN2
    exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hN2
        (((natDegree_C_mul_le _ _).trans hN0).trans (by omega)))
      ((natDegree_C_mul_le _ _).trans hN1)
  have hBN (N : Polynomial ℝ) (hN : N.natDegree ≤ 5) :
      (commonFactor n ell cScale V * N).natDegree ≤ (3 * n + 3) + 3 :=
    (natDegree_mul_le_of_le hB hN).trans (by omega)
  exact ⟨hF, hK, hBN _ (hN0.trans (by omega)), hBN _ hN1, hBN _ hbar⟩

/-- A linear equivalence for the displayed concrete normalized model.
The scalar units are exactly those in the concrete evaluation theorem. -/
def concreteBoundedEquiv (n : ℕ) (a A z b ell cScale : ℝ) (V : Polynomial ℝ)
    (h : TailUnits a A z b ell cScale V) (hV : V.natDegree ≤ n + 1) :
    (ℝ × ℝ × ℝ × degreeLT ℝ (3 * n + 4)) ≃ₗ[ℝ] degreeLT ℝ (3 * n + 7) :=
  boundedExtensionEquiv (concreteSeparationConditions n a A z b ell cScale V h)
    (concreteDegreeBounds n a A z b ell cScale V hV)

/-- Every polynomial of degree at most 3n+6 has a unique decomposition
into the three concrete new columns and a transferred old polynomial
of degree at most 3n+3. -/
theorem concrete_existsUnique_boundedInput
    (n : ℕ) (a A z b ell cScale : ℝ) (V : Polynomial ℝ)
    (h : TailUnits a A z b ell cScale V) (hV : V.natDegree ≤ n + 1)
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ 3 * n + 6) :
    ∃! input : ℝ × ℝ × ℝ × degreeLT ℝ (3 * n + 4),
      extensionPolynomial (transferFactor A z b) (transferCorrection n a A z ell V)
        (commonFactor n ell cScale V * n0 a A z)
        (commonFactor n ell cScale V * n1 a A z)
        (commonFactor n ell cScale V * barN2 a A z)
        (xi A) input.1 input.2.1 input.2.2.1 (input.2.2.2 : Polynomial ℝ) = Q := by
  let Qbounded : degreeLT ℝ (3 * n + 7) :=
    ⟨Q, (mem_degreeLT_succ_iff_natDegree_le (3 * n + 6) Q).mpr hQ⟩
  obtain ⟨input, hinput, hunique⟩ :=
    existsUnique_boundedInput (concreteSeparationConditions n a A z b ell cScale V h)
      (concreteDegreeBounds n a A z b ell cScale V hV) Qbounded
  refine ⟨input, congrArg (fun S : degreeLT ℝ (3 * n + 7) => (S : Polynomial ℝ)) hinput, ?_⟩
  intro input' hinput'
  apply hunique input'
  exact Subtype.ext hinput'

end Concrete

end

end PanelMoments.SourceInvariantTailBoundedExtension
