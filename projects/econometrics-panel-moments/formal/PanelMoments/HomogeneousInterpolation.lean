import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Lean.Elab.Tactic.Omega

/-!
# Finite-point interpolation by homogeneous polynomials

A concrete separating family gives a right inverse to evaluation. Multiplication
by a coordinate nonzero at each target raises the degree without losing the
separation property. The dimension calculation counts degree-`d` monomials in
three variables and then applies rank-nullity; no independence or rank premise
is part of the interpolation hypothesis.
-/

namespace PanelMoments.HomogeneousInterpolation

open scoped BigOperators
open MvPolynomial

noncomputable section

abbrev Point := Fin 3 → ℝ
abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- The vector space of homogeneous degree-`d` polynomials in three variables. -/
abbrev Homogeneous (d : ℕ) := homogeneousSubmodule (Fin 3) ℝ d

instance homogeneous_finiteDimensional (d : ℕ) :
    FiniteDimensional ℝ (Homogeneous d) :=
  (Submodule.fg_iff_finiteDimensional _).mp
    (homogeneousSubmodule_fg (Fin 3) ℝ d)

/-- Degree-`d` homogeneous polynomials are their finitely supported coefficient
vectors, indexed by degree-`d` exponent vectors. -/
def homogeneousCoefficientEquiv (d : ℕ) :
    Homogeneous d ≃ₗ[ℝ] ({a : Fin 3 →₀ ℕ // a.degree = d} →₀ ℝ) :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 3) ℝ d)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp {a : Fin 3 →₀ ℕ | a.degree = d})

/-- The familiar dimension formula is obtained by counting exponent vectors. -/
theorem finrank_homogeneous (d : ℕ) :
    Module.finrank ℝ (Homogeneous d) = (d + 2).choose 2 := by
  classical
  let : Fintype {a : Fin 3 →₀ ℕ // a.degree = d} :=
    (Finsupp.finite_of_degree_eq d).fintype
  let e : {a : Fin 3 →₀ ℕ // a.degree = d} ≃
      ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag d) :=
    Equiv.subtypeEquivRight fun a => by
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  calc
    Module.finrank ℝ (Homogeneous d) =
        Module.finrank ℝ ({a : Fin 3 →₀ ℕ // a.degree = d} →₀ ℝ) :=
      (homogeneousCoefficientEquiv d).finrank_eq
    _ = Fintype.card {a : Fin 3 →₀ ℕ // a.degree = d} :=
      Module.finrank_finsupp_self ℝ
    _ = Fintype.card ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag d) :=
      Fintype.card_congr e
    _ = (3 + d - 1).choose d := by
      rw [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
      simp
    _ = (d + 2).choose 2 := by
      rw [show 3 + d - 1 = d + 2 by omega]
      exact Nat.choose_symm_add

variable {ι : Type*}

/-- Evaluation at a finite or infinite indexed collection of projective-point
representatives, restricted to one homogeneous degree. -/
def evaluation (p : ι → Point) (d : ℕ) : Homogeneous d →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i =>
    (aeval (p i)).toLinearMap.comp (homogeneousSubmodule (Fin 3) ℝ d).subtype

@[simp] theorem evaluation_apply (p : ι → Point) (d : ℕ)
    (f : Homogeneous d) (i : ι) :
    evaluation p d f i = eval (p i) f.1 := rfl

/-- The degree-`d` homogeneous polynomials vanishing at every supplied point. -/
def vanishingSubmodule (p : ι → Point) (d : ℕ) : Submodule ℝ (Homogeneous d) :=
  LinearMap.ker (evaluation p d)

@[simp] theorem mem_vanishingSubmodule (p : ι → Point) (d : ℕ)
    (f : Homogeneous d) :
    f ∈ vanishingSubmodule p d ↔ ∀ i, eval (p i) f.1 = 0 := by
  simp [vanishingSubmodule, LinearMap.mem_ker, funext_iff]

/-- Actual homogeneous separators: each polynomial vanishes at all other points
and takes a nonzero value at its own point. -/
structure SeparatingFamily (p : ι → Point) (d : ℕ) where
  polynomial : ι → Poly
  homogeneous : ∀ i, (polynomial i).IsHomogeneous d
  offDiagonal : ∀ i j, i ≠ j → eval (p i) (polynomial j) = 0
  diagonal : ∀ i, eval (p i) (polynomial i) ≠ 0

namespace SeparatingFamily

variable {p : ι → Point} {d : ℕ} (s : SeparatingFamily p d)

include s

/-- A separator rescaled to have value one at its target. -/
def normalized (i : ι) : Homogeneous d :=
  (eval (p i) (s.polynomial i))⁻¹ • ⟨s.polynomial i, s.homogeneous i⟩

theorem evaluation_normalized [DecidableEq ι] (i j : ι) :
    evaluation p d (s.normalized i) j = if j = i then 1 else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp [normalized, s.diagonal i]
  · simp [normalized, hji, s.offDiagonal j i hji]

/-- Interpolate arbitrary prescribed scalar values by a finite sum of normalized
homogeneous separators. -/
def interpolate [Fintype ι] (b : ι → ℝ) : Homogeneous d :=
  ∑ i, b i • s.normalized i

theorem evaluation_interpolate [Fintype ι] (b : ι → ℝ) :
    evaluation p d (s.interpolate b) = b := by
  classical
  funext j
  change (evaluation p d (∑ i, b i • s.normalized i)) j = b j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, evaluation_normalized]
  simp [mul_ite]

theorem evaluation_surjective [Fintype ι] :
    Function.Surjective (evaluation p d) :=
  fun b => ⟨s.interpolate b, s.evaluation_interpolate b⟩

/-- Multiplying each separator by a power of a coordinate nonzero at its target
raises the degree and preserves all off-diagonal zeros. -/
def pad (c : ι → Fin 3) (hc : ∀ i, p i (c i) ≠ 0) (k : ℕ) :
    SeparatingFamily p (d + k) where
  polynomial i := s.polynomial i * X (c i) ^ k
  homogeneous i := (s.homogeneous i).mul (isHomogeneous_X_pow (c i) k)
  offDiagonal i j hij := by
    simp [s.offDiagonal i j hij]
  diagonal i := by
    simpa using mul_ne_zero (s.diagonal i) (pow_ne_zero k (hc i))

/-- Separators in any higher requested homogeneous degree. -/
def raise (c : ι → Fin 3) (hc : ∀ i, p i (c i) ≠ 0)
    {e : ℕ} (hde : d ≤ e) : SeparatingFamily p e := by
  simpa only [Nat.add_sub_of_le hde] using s.pad c hc (e - d)

theorem evaluation_surjective_of_le [Fintype ι]
    (c : ι → Fin 3) (hc : ∀ i, p i (c i) ≠ 0)
    {e : ℕ} (hde : d ≤ e) :
    Function.Surjective (evaluation p e) :=
  (s.raise c hc hde).evaluation_surjective

/-- Rank-nullity for the homogeneous vanishing space. -/
theorem finrank_vanishing_add_card [Fintype ι] :
    Module.finrank ℝ (vanishingSubmodule p d) + Fintype.card ι =
      (d + 2).choose 2 := by
  have hrange : LinearMap.range (evaluation p d) = ⊤ :=
    LinearMap.range_eq_top.mpr s.evaluation_surjective
  have hdim := (evaluation p d).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_pi, finrank_homogeneous] at hdim
  change Module.finrank ℝ (LinearMap.ker (evaluation p d)) + Fintype.card ι =
    (d + 2).choose 2
  omega

theorem finrank_vanishing [Fintype ι] :
    Module.finrank ℝ (vanishingSubmodule p d) =
      (d + 2).choose 2 - Fintype.card ι := by
  have hdim := s.finrank_vanishing_add_card
  omega

theorem finrank_vanishing_of_le [Fintype ι]
    (c : ι → Fin 3) (hc : ∀ i, p i (c i) ≠ 0)
    {e : ℕ} (hde : d ≤ e) :
    Module.finrank ℝ (vanishingSubmodule p e) =
      (e + 2).choose 2 - Fintype.card ι :=
  (s.raise c hc hde).finrank_vanishing

end SeparatingFamily

end

end PanelMoments.HomogeneousInterpolation
