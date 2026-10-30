import PanelMoments.Geometry
import PanelMoments.LinearFormAlgebra
import PanelMoments.CoordinateSyzygies
import PanelMoments.HomogeneousInterpolation
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Pi

/-!
# Relations among the three cubic block generators

For `L i = X 0 + a i * X 1 + b i * X 2`, the cubic generators are
`X i * ∏ j ≠ i, L j`. Distinct normalized lines, none equal to `X 0`, force
the coefficient of the `i`th cubic in any relation to be divisible by `L i`.
After removing those factors, cancellation of `∏ i, L i` gives precisely a
coordinate relation. The final linear equivalence preserves the homogeneous
degrees needed for a graded dimension calculation.
-/

namespace PanelMoments.CubicRelations

open scoped BigOperators
open MvPolynomial
open LinearFormAlgebra

noncomputable section

abbrev Poly := MvPolynomial (Fin 3) ℝ
abbrev Homogeneous (n : ℕ) := homogeneousSubmodule (Fin 3) ℝ n

/-- The exact excluded line coincidences used in the divisibility argument. -/
structure LineConditions (a b : Fin 3 → ℝ) : Prop where
  nonCoordinate : ∀ i, a i ≠ 0 ∨ b i ≠ 0
  distinct : ∀ i j, i ≠ j → a i ≠ a j ∨ b i ≠ b j

def lines (a b : Fin 3 → ℝ) (i : Fin 3) : Poly := normalizedLine (a i) (b i)

def coordinateCombination (g : Fin 3 → Poly) : Poly := ∑ i, X i * g i

def cubicCombination (a b : Fin 3 → ℝ) (f : Fin 3 → Poly) : Poly :=
  ∑ i, f i * Geometry.blockFactor (lines a b) i

theorem lines_ne_zero (a b : Fin 3 → ℝ) (i : Fin 3) : lines a b i ≠ 0 :=
  (normalizedLine_prime (a i) (b i)).ne_zero

theorem prod_lines_ne_zero (a b : Fin 3 → ℝ) : (∏ i, lines a b i) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ => lines_ne_zero a b i

/-- Multiplying the coefficient of the `i`th cubic by `L i` restores the
common product of all three lines. -/
theorem cubicCombination_multiply_lines (a b : Fin 3 → ℝ) (g : Fin 3 → Poly) :
    cubicCombination a b (fun i => lines a b i * g i) =
      (∏ i, lines a b i) * coordinateCombination g := by
  unfold cubicCombination coordinateCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (lines a b i * g i) * Geometry.blockFactor (lines a b) i =
        (lines a b i * ∏ j ∈ Finset.univ.erase i, lines a b j) * (X i * g i) := by
      unfold Geometry.blockFactor
      ring
    _ = (∏ j, lines a b j) * (X i * g i) := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

theorem cubicCombination_multiply_lines_eq_zero_iff (a b : Fin 3 → ℝ)
    (g : Fin 3 → Poly) :
    cubicCombination a b (fun i => lines a b i * g i) = 0 ↔
      coordinateCombination g = 0 := by
  rw [cubicCombination_multiply_lines, mul_eq_zero]
  simp [prod_lines_ne_zero]

/-- Every other cubic term contains the selected line as a factor. -/
theorem line_dvd_other_term (a b : Fin 3 → ℝ) (f : Fin 3 → Poly)
    {i j : Fin 3} (hij : i ≠ j) :
    lines a b i ∣ f j * Geometry.blockFactor (lines a b) j := by
  have hprod : lines a b i ∣ ∏ k ∈ Finset.univ.erase j, lines a b k :=
    Finset.dvd_prod_of_mem _ (by simp [hij])
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hprod (X j)) (f j)

/-- A cubic relation forces `L i` to divide the coefficient of its own term. -/
theorem cubic_relation_dvd_coefficient (a b : Fin 3 → ℝ)
    (hL : LineConditions a b) (f : Fin 3 → Poly)
    (hf : cubicCombination a b f = 0) (i : Fin 3) : lines a b i ∣ f i := by
  have hrest : lines a b i ∣
      ∑ j ∈ Finset.univ.erase i, f j * Geometry.blockFactor (lines a b) j := by
    apply Finset.dvd_sum
    intro j hj
    exact line_dvd_other_term a b f (Finset.ne_of_mem_erase hj).symm
  have hsum : f i * Geometry.blockFactor (lines a b) i +
      (∑ j ∈ Finset.univ.erase i, f j * Geometry.blockFactor (lines a b) j) = 0 := by
    exact (Finset.add_sum_erase Finset.univ
      (fun j => f j * Geometry.blockFactor (lines a b) j) (Finset.mem_univ i)).trans hf
  have hterm : lines a b i ∣ f i * Geometry.blockFactor (lines a b) i := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact dvd_neg.mpr hrest
  apply normalizedLine_dvd_coefficient (Finset.univ.erase i) a b (hL.nonCoordinate i)
      (fun j hj => hL.distinct i j (Finset.ne_of_mem_erase hj).symm) i (f i)
  simpa only [lines, Geometry.blockFactor, mul_assoc] using hterm

/-- The complete algebraic equivalence between cubic and coordinate relations. -/
theorem cubic_relation_iff (a b : Fin 3 → ℝ) (hL : LineConditions a b)
    (f : Fin 3 → Poly) :
    cubicCombination a b f = 0 ↔
      ∃ g : Fin 3 → Poly, (∀ i, f i = lines a b i * g i) ∧
        coordinateCombination g = 0 := by
  constructor
  · intro hf
    let g : Fin 3 → Poly := fun i =>
      Classical.choose (cubic_relation_dvd_coefficient a b hL f hf i)
    have hg : ∀ i, f i = lines a b i * g i := fun i =>
      Classical.choose_spec (cubic_relation_dvd_coefficient a b hL f hf i)
    refine ⟨g, hg, (cubicCombination_multiply_lines_eq_zero_iff a b g).mp ?_⟩
    simpa only [← funext hg] using hf
  · rintro ⟨g, hg, hcoord⟩
    rw [funext hg]
    exact (cubicCombination_multiply_lines_eq_zero_iff a b g).mpr hcoord

theorem normalizedLine_isHomogeneous (a b : ℝ) :
    (normalizedLine a b).IsHomogeneous 1 :=
  ((isHomogeneous_X ℝ 0).add (isHomogeneous_C_mul_X a 1)).add
    (isHomogeneous_C_mul_X b 2)

theorem blockFactor_isHomogeneous (a b : Fin 3 → ℝ) (i : Fin 3) :
    (Geometry.blockFactor (lines a b) i).IsHomogeneous 3 := by
  have hprod : (∏ j ∈ Finset.univ.erase i, lines a b j).IsHomogeneous 2 := by
    have h := IsHomogeneous.prod (Finset.univ.erase i) (lines a b) (fun _ => 1)
      (fun j _ => normalizedLine_isHomogeneous (a j) (b j))
    simpa [Finset.card_erase_of_mem] using h
  exact (isHomogeneous_X ℝ i).mul hprod

/-- Multiplication by a normalized line shifts homogeneous components by one. -/
theorem homogeneousComponent_normalizedLine_mul_succ (n : ℕ) (a b : ℝ) (p : Poly) :
    homogeneousComponent (n + 1) (normalizedLine a b * p) =
      normalizedLine a b * homogeneousComponent n p := by
  simp only [normalizedLine, add_mul, mul_assoc, map_add,
    homogeneousComponent_C_mul, CoordinateSyzygies.homogeneousComponent_X_mul_succ]

/-- Projecting a polynomial quotient to degree `n` produces a homogeneous
quotient when the original coefficient has degree `n + 1`. -/
theorem homogeneous_line_quotient {n : ℕ} {a b : ℝ} {f g : Poly}
    (hf : f.IsHomogeneous (n + 1)) (hfg : f = normalizedLine a b * g) :
    f = normalizedLine a b * homogeneousComponent n g := by
  have h := congrArg (homogeneousComponent (n + 1)) hfg
  simpa only [homogeneousComponent_eq_self hf,
    homogeneousComponent_normalizedLine_mul_succ] using h

theorem cubic_relation_homogeneous_iff (a b : Fin 3 → ℝ) (hL : LineConditions a b)
    (n : ℕ) (f : Fin 3 → Poly) (hhom : ∀ i, (f i).IsHomogeneous (n + 1)) :
    cubicCombination a b f = 0 ↔
      ∃ g : Fin 3 → Poly, (∀ i, (g i).IsHomogeneous n) ∧
        (∀ i, f i = lines a b i * g i) ∧ coordinateCombination g = 0 := by
  constructor
  · intro hf
    obtain ⟨g, hg, _⟩ := (cubic_relation_iff a b hL f).mp hf
    let g' : Fin 3 → Poly := fun i => homogeneousComponent n (g i)
    have hg' : ∀ i, f i = lines a b i * g' i := fun i =>
      homogeneous_line_quotient (hhom i) (hg i)
    refine ⟨g', fun i => homogeneousComponent_isHomogeneous _ _, hg', ?_⟩
    apply (cubicCombination_multiply_lines_eq_zero_iff a b g').mp
    simpa only [← funext hg'] using hf
  · rintro ⟨g, _, hg, hcoord⟩
    exact (cubic_relation_iff a b hL f).mpr ⟨g, hg, hcoord⟩

/-- The degree-`n + 4` cubic-generator map, with degree-`n + 1` coefficients. -/
def cubicLinearMap (a b : Fin 3 → ℝ) (n : ℕ) :
    (Fin 3 → Homogeneous (n + 1)) →ₗ[ℝ] Homogeneous (n + 4) where
  toFun f := ⟨cubicCombination a b (fun i => (f i).1), by
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.add_assoc] using (f i).2.mul (blockFactor_isHomogeneous a b i)⟩
  map_add' f g := by
    apply Subtype.ext
    simp [cubicCombination, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    simp [cubicCombination, smul_mul_assoc, Finset.smul_sum]

@[simp]
theorem cubicLinearMap_apply (a b : Fin 3 → ℝ) (n : ℕ)
    (f : Fin 3 → Homogeneous (n + 1)) :
    (cubicLinearMap a b n f).1 = cubicCombination a b (fun i => (f i).1) := rfl

/-- Componentwise multiplication by the corresponding normalized line. -/
def homogeneousLineMultiply (a b : Fin 3 → ℝ) (n : ℕ) :
    (Fin 3 → Homogeneous n) →ₗ[ℝ] (Fin 3 → Homogeneous (n + 1)) where
  toFun g i := ⟨lines a b i * (g i).1, by
    change (normalizedLine (a i) (b i) * (g i).1).IsHomogeneous (n + 1)
    simpa only [Nat.add_comm] using
      (normalizedLine_isHomogeneous (a i) (b i)).mul (g i).2⟩
  map_add' g h := by
    funext i
    apply Subtype.ext
    simp [mul_add]
  map_smul' c g := by
    funext i
    apply Subtype.ext
    simp [mul_smul_comm]

@[simp]
theorem homogeneousLineMultiply_apply (a b : Fin 3 → ℝ) (n : ℕ)
    (g : Fin 3 → Homogeneous n) (i : Fin 3) :
    (homogeneousLineMultiply a b n g i).1 = lines a b i * (g i).1 := rfl

theorem cubicLinearMap_lineMultiply_eq_zero_iff (a b : Fin 3 → ℝ) (n : ℕ)
    (g : Fin 3 → Homogeneous n) :
    cubicLinearMap a b n (homogeneousLineMultiply a b n g) = 0 ↔
      CoordinateSyzygies.coordinateLinearMap n g = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    have hval := congrArg Subtype.val h
    change cubicCombination a b (fun i => lines a b i * (g i).1) = 0 at hval
    have hcoord := (cubicCombination_multiply_lines_eq_zero_iff a b
      (fun i => (g i).1)).mp hval
    simpa only [CoordinateSyzygies.coordinateLinearMap_apply,
      coordinateCombination, Fin.sum_univ_three, Submodule.coe_zero] using hcoord
  · intro h
    apply Subtype.ext
    change cubicCombination a b (fun i => lines a b i * (g i).1) = 0
    apply (cubicCombination_multiply_lines_eq_zero_iff a b (fun i => (g i).1)).mpr
    have hval := congrArg Subtype.val h
    simpa only [CoordinateSyzygies.coordinateLinearMap_apply,
      coordinateCombination, Fin.sum_univ_three, Submodule.coe_zero] using hval

/-- The kernel map induced by multiplying each component by its line. -/
def homogeneousKernelLift (a b : Fin 3 → ℝ) (n : ℕ) :
    LinearMap.ker (CoordinateSyzygies.coordinateLinearMap n) →ₗ[ℝ]
      LinearMap.ker (cubicLinearMap a b n) :=
  LinearMap.codRestrict _
    ((homogeneousLineMultiply a b n).domRestrict
      (LinearMap.ker (CoordinateSyzygies.coordinateLinearMap n))) (by
    intro g
    change cubicLinearMap a b n (homogeneousLineMultiply a b n g.1) = 0
    exact (cubicLinearMap_lineMultiply_eq_zero_iff a b n g.1).mpr g.2)

theorem homogeneousKernelLift_injective (a b : Fin 3 → ℝ) (n : ℕ) :
    Function.Injective (homogeneousKernelLift a b n) := by
  intro g h hgh
  apply Subtype.ext
  funext i
  apply Subtype.ext
  have hi := congrArg
    (fun f : LinearMap.ker (cubicLinearMap a b n) => (f.1 i).1) hgh
  change lines a b i * (g.1 i).1 = lines a b i * (h.1 i).1 at hi
  exact mul_left_cancel₀ (lines_ne_zero a b i) hi

theorem homogeneousKernelLift_surjective (a b : Fin 3 → ℝ)
    (hL : LineConditions a b) (n : ℕ) :
    Function.Surjective (homogeneousKernelLift a b n) := by
  intro f
  have hf : cubicCombination a b (fun i => (f.1 i).1) = 0 := by
    have h := congrArg Subtype.val f.2
    exact h
  obtain ⟨g, hhom, hg, hcoord⟩ :=
    (cubic_relation_homogeneous_iff a b hL n (fun i => (f.1 i).1)
      (fun i => (f.1 i).2)).mp hf
  let g' : Fin 3 → Homogeneous n := fun i => ⟨g i, hhom i⟩
  have hg' : CoordinateSyzygies.coordinateLinearMap n g' = 0 := by
    apply Subtype.ext
    simpa only [CoordinateSyzygies.coordinateLinearMap_apply,
      coordinateCombination, Fin.sum_univ_three, Submodule.coe_zero] using hcoord
  refine ⟨⟨g', hg'⟩, ?_⟩
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact (hg i).symm

/-- The degree-preserving kernel equivalence. Its construction uses polynomial
divisibility and homogeneous projection, with no dimension or rank premise. -/
def homogeneousRelationKernelEquiv (a b : Fin 3 → ℝ) (hL : LineConditions a b)
    (n : ℕ) :
    LinearMap.ker (CoordinateSyzygies.coordinateLinearMap n) ≃ₗ[ℝ]
      LinearMap.ker (cubicLinearMap a b n) :=
  LinearEquiv.ofBijective (homogeneousKernelLift a b n)
    ⟨homogeneousKernelLift_injective a b n, homogeneousKernelLift_surjective a b hL n⟩

theorem finrank_homogeneous_triples (n : ℕ) :
    Module.finrank ℝ (Fin 3 → Homogeneous n) = 3 * (n + 2).choose 2 := by
  simp [Module.finrank_pi_fintype, HomogeneousInterpolation.finrank_homogeneous,
    nsmul_eq_mul]

/-- The cubic-generated subspace has codimension six in every homogeneous
degree at least four. The calculation uses the kernel equivalence and the
surjective coordinate map, rather than a rank assumption. -/
theorem finrank_range_cubicLinearMap_add_six (a b : Fin 3 → ℝ)
    (hL : LineConditions a b) (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (cubicLinearMap a b n)) + 6 =
      (n + 6).choose 2 := by
  have hc := (cubicLinearMap a b n).finrank_range_add_finrank_ker
  have hx := (CoordinateSyzygies.coordinateLinearMap n).finrank_range_add_finrank_ker
  have hk := (homogeneousRelationKernelEquiv a b hL n).finrank_eq
  have hrange : LinearMap.range (CoordinateSyzygies.coordinateLinearMap n) = ⊤ :=
    LinearMap.range_eq_top.mpr (CoordinateSyzygies.coordinateLinearMap_surjective n)
  rw [hrange, finrank_top] at hx
  simp only [finrank_homogeneous_triples, HomogeneousInterpolation.finrank_homogeneous,
    Nat.add_assoc, Nat.reduceAdd] at hc hx
  have hbalance :
      Module.finrank ℝ (LinearMap.range (cubicLinearMap a b n)) +
        3 * (n + 2).choose 2 = 4 * (n + 3).choose 2 := by
    omega
  have h₃ := Nat.choose_succ_succ (n + 2) 1
  have h₄ := Nat.choose_succ_succ (n + 3) 1
  have h₅ := Nat.choose_succ_succ (n + 4) 1
  have h₆ := Nat.choose_succ_succ (n + 5) 1
  simp only [Nat.succ_eq_add_one, Nat.choose_one_right, Nat.add_assoc, Nat.reduceAdd]
    at h₃ h₄ h₅ h₆
  omega

end

end PanelMoments.CubicRelations
