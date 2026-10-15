import PanelMoments.BlockExtension
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

/-!
# Products of cubic blocks

The span of one coordinate variable and one cubic generator from each block is
the full homogeneous space vanishing on the six points of every block. The
reverse inclusion uses interpolation to correct the coefficients in a cubic
decomposition before applying induction. All geometric assumptions concern
explicit line or separator values; no rank or dimension premise is used.
-/

namespace PanelMoments.CubicProducts

open scoped BigOperators
open MvPolynomial CubicRelations

noncomputable section

abbrev Point := Fin 3 → ℝ
abbrev Poly := MvPolynomial (Fin 3) ℝ
abbrev Coefficients := ℕ → Fin 3 → ℝ

/-- Choose one cubic generator from each of the first `m` blocks, followed by
one coordinate variable. There are `3 ^ (m + 1)` such choices. -/
def pureProduct (a b : Coefficients) :
    (m : ℕ) → (Fin (m + 1) → Fin 3) → Poly
  | 0, y => X (y 0)
  | m + 1, y =>
      Geometry.blockFactor (lines (a 0) (b 0)) (y 0) *
        pureProduct (a ∘ Nat.succ) (b ∘ Nat.succ) m (Fin.tail y)

/-- The ambient polynomial span of the pure block products. -/
def productSpan (a b : Coefficients) (m : ℕ) : Submodule ℝ Poly :=
  Submodule.span ℝ (Set.range (pureProduct a b m))

theorem pureProduct_mem (a b : Coefficients) (m : ℕ)
    (y : Fin (m + 1) → Fin 3) : pureProduct a b m y ∈ productSpan a b m :=
  Submodule.subset_span ⟨y, rfl⟩

theorem pureProduct_homogeneous (a b : Coefficients) (m : ℕ) :
    ∀ y, (pureProduct a b m y).IsHomogeneous (3 * m + 1) := by
  induction m generalizing a b with
  | zero =>
      intro y
      exact isHomogeneous_X ℝ (y 0)
  | succ m ih =>
      intro y
      change (Geometry.blockFactor (lines (a 0) (b 0)) (y 0) *
        pureProduct (a ∘ Nat.succ) (b ∘ Nat.succ) m (Fin.tail y)).IsHomogeneous
          (3 * (m + 1) + 1)
      convert (blockFactor_isHomogeneous (a 0) (b 0) (y 0)).mul
        (ih (a ∘ Nat.succ) (b ∘ Nat.succ) (Fin.tail y)) using 1 <;> omega

theorem productSpan_le_homogeneous (a b : Coefficients) (m : ℕ) :
    productSpan a b m ≤ homogeneousSubmodule (Fin 3) ℝ (3 * m + 1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨y, rfl⟩
  exact pureProduct_homogeneous a b m y

/-- Finite dimensionality holds for every block configuration, without any
nondegeneracy hypothesis. -/
instance productSpan_finiteDimensional (a b : Coefficients) (m : ℕ) :
    FiniteDimensional ℝ (productSpan a b m) :=
  Submodule.finiteDimensional_of_le (productSpan_le_homogeneous a b m)

theorem productSpan_zero (a b : Coefficients) :
    productSpan a b 0 = homogeneousSubmodule (Fin 3) ℝ 1 := by
  rw [homogeneousSubmodule_one_eq_span_X]
  change Submodule.span ℝ (Set.range (pureProduct a b 0)) =
    Submodule.span ℝ (Set.range (X : Fin 3 → Poly))
  congr 1
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y 0, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨fun _ => r, rfl⟩

/-- The six projective-point representatives for each of the first `m` blocks. -/
def points (a b : Coefficients) (m : ℕ) (ti : Fin m × Fin 6) : Point :=
  GeneralGeometry.sixPoints (CubicIdeal.coefficientVectors (a ti.1) (b ti.1)) ti.2

/-- Homogeneous vanishing is kept in the ambient polynomial ring so that the
induction does not change the type of its polynomial coefficients. -/
def vanishingSpace (a b : Coefficients) (m : ℕ) : Submodule ℝ Poly :=
  homogeneousSubmodule (Fin 3) ℝ (3 * m + 1) ⊓
    LinearMap.ker (LinearMap.pi fun ti : Fin m × Fin 6 =>
      (aeval (points a b m ti)).toLinearMap)

theorem mem_vanishingSpace (a b : Coefficients) (m : ℕ) (f : Poly) :
    f ∈ vanishingSpace a b m ↔
      f.IsHomogeneous (3 * m + 1) ∧
        ∀ (t : Fin m) (i : Fin 6),
          eval (GeneralGeometry.sixPoints
            (CubicIdeal.coefficientVectors (a t) (b t)) i) f = 0 := by
  change (f.IsHomogeneous (3 * m + 1) ∧
    (fun ti : Fin m × Fin 6 => eval (points a b m ti) f) = 0) ↔ _
  constructor
  · rintro ⟨hhom, hzero⟩
    exact ⟨hhom, fun t i => congrFun hzero (t, i)⟩
  · rintro ⟨hhom, hzero⟩
    refine ⟨hhom, ?_⟩
    funext ti
    exact hzero ti.1 ti.2

theorem pureProduct_vanishes (a b : Coefficients) (m : ℕ) :
    ∀ (y : Fin (m + 1) → Fin 3) (t : Fin m) (i : Fin 6),
      eval (GeneralGeometry.sixPoints
        (CubicIdeal.coefficientVectors (a t) (b t)) i) (pureProduct a b m y) = 0 := by
  induction m generalizing a b with
  | zero =>
      intro _ t
      exact Fin.elim0 t
  | succ m ih =>
      intro y t i
      refine Fin.cases ?_ (fun t => ?_) t
      · change eval (GeneralGeometry.sixPoints
          (CubicIdeal.coefficientVectors (a 0) (b 0)) i)
            (Geometry.blockFactor (lines (a 0) (b 0)) (y 0) *
              pureProduct (a ∘ Nat.succ) (b ∘ Nat.succ) m (Fin.tail y)) = 0
        rw [map_mul, CubicIdeal.blockFactor_zero, zero_mul]
      · change eval (GeneralGeometry.sixPoints
          (CubicIdeal.coefficientVectors ((a ∘ Nat.succ) t) ((b ∘ Nat.succ) t)) i)
            (Geometry.blockFactor (lines (a 0) (b 0)) (y 0) *
              pureProduct (a ∘ Nat.succ) (b ∘ Nat.succ) m (Fin.tail y)) = 0
        rw [map_mul, ih (a ∘ Nat.succ) (b ∘ Nat.succ) (Fin.tail y) t i, mul_zero]

theorem productSpan_le_vanishingSpace (a b : Coefficients) (m : ℕ) :
    productSpan a b m ≤ vanishingSpace a b m := by
  apply Submodule.span_le.mpr
  rintro _ ⟨y, rfl⟩
  exact (mem_vanishingSpace a b m _).mpr
    ⟨pureProduct_homogeneous a b m y, pureProduct_vanishes a b m y⟩

/-- Multiplication by a chosen new cubic maps the old product span into the new
one. The proof uses the inverse image of the new span under a linear map. -/
theorem blockFactor_mul_mem_productSpan (a b : Coefficients) (m : ℕ) (r : Fin 3)
    {f : Poly} (hf : f ∈ productSpan (a ∘ Nat.succ) (b ∘ Nat.succ) m) :
    Geometry.blockFactor (lines (a 0) (b 0)) r * f ∈ productSpan a b (m + 1) := by
  have hle : productSpan (a ∘ Nat.succ) (b ∘ Nat.succ) m ≤
      (productSpan a b (m + 1)).comap
        (LinearMap.mulLeft ℝ (Geometry.blockFactor (lines (a 0) (b 0)) r)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change Geometry.blockFactor (lines (a 0) (b 0)) r *
      pureProduct (a ∘ Nat.succ) (b ∘ Nat.succ) m y ∈ productSpan a b (m + 1)
    simpa only [pureProduct, Fin.cons_zero, Fin.tail_cons] using
      pureProduct_mem a b (m + 1) (Fin.cons r y)
  exact hle hf

theorem cubicCombination_mem_productSpan (a b : Coefficients) (m : ℕ)
    (c : Fin 3 → Poly)
    (hc : ∀ i, c i ∈ productSpan (a ∘ Nat.succ) (b ∘ Nat.succ) m) :
    cubicCombination (a 0) (b 0) c ∈ productSpan a b (m + 1) := by
  unfold cubicCombination
  apply (productSpan a b (m + 1)).sum_mem
  intro i _
  simpa only [mul_comm] using blockFactor_mul_mem_productSpan a b m i (hc i)

/-- Induction over the blocks. At the induction step with `n + 1` old blocks,
the correction degree `3*n + 2` is exactly `3*(n + 1) - 1`. -/
theorem vanishingSpace_le_productSpan (m : ℕ) :
    ∀ (a b : Coefficients),
      (∀ t : Fin m, LineConditions (a t) (b t)) →
      (∀ t : Fin m,
        GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t))) →
      GeneralGeometry.CrossNonincident
        (fun t : Fin m => CubicIdeal.coefficientVectors (a t) (b t)) →
      vanishingSpace a b m ≤ productSpan a b m := by
  induction m with
  | zero =>
      intro a b _ _ _ f hf
      rw [productSpan_zero]
      exact ((mem_vanishingSpace a b 0 f).mp hf).1
  | succ m ih =>
      intro a b hL hP hcross f hf
      obtain ⟨hhom, hzero⟩ := (mem_vanishingSpace a b (m + 1) f).mp hf
      cases m with
      | zero =>
          obtain ⟨c, hc_hom, hfc⟩ :=
            CubicIdeal.exists_homogeneous_cubic_decomposition (a 0) (b 0) (hL 0) (hP 0)
              (n := 0) (by simpa using hhom) (hzero 0)
          rw [hfc]
          apply cubicCombination_mem_productSpan a b 0 c
          intro i
          rw [productSpan_zero]
          exact hc_hom i
      | succ n =>
          let a' : Coefficients := a ∘ Nat.succ
          let b' : Coefficients := b ∘ Nat.succ
          let l : Fin (n + 1) → Fin 3 → Point := fun t =>
            CubicIdeal.coefficientVectors (a' t) (b' t)
          let p : Fin (n + 1) × Fin 6 → Point := points a' b' (n + 1)
          have hLtail (t : Fin (n + 1)) : LineConditions (a' t) (b' t) :=
            hL t.succ
          have hPtail (t : Fin (n + 1)) : GeneralGeometry.LocalNondegenerate (l t) :=
            hP t.succ
          have hctail : GeneralGeometry.CrossNonincident l := by
            intro t u htu i r
            exact hcross t.succ u.succ (fun h => htu (Fin.succ_injective _ h)) i r
          have hp (ti : Fin (n + 1) × Fin 6) : p ti ≠ 0 := by
            obtain ⟨r, hr⟩ :=
              GeneralGeometry.sixPoints_coordinate_nonzero (l ti.1) (hPtail ti.1) ti.2
            intro h
            exact hr (congrFun h r)
          have heval : Function.Surjective
              (HomogeneousInterpolation.evaluation p (3 * n + 2)) := by
            apply GeneralGeometry.global_evaluation_surjective l hPtail hctail
            simp only [Fintype.card_fin]
            omega
          have hnewLine (ti : Fin (n + 1) × Fin 6) (i : Fin 3) :
              eval (p ti) (lines (a 0) (b 0) i) ≠ 0 := by
            simpa only [CubicIdeal.linearForm_coefficientVectors, p, points, a', b',
              Function.comp_apply, Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one] using
              hcross ti.1.succ 0 (Fin.succ_ne_zero _) ti.2 i
          have hhom' : f.IsHomogeneous ((3 * n + 2) + 5) := by
            convert hhom using 1 <;> omega
          obtain ⟨c, hc_hom, hc_zero, hfc⟩ :=
            BlockExtension.exists_corrected_cubic_decomposition p (3 * n + 2) hp heval
              (a 0) (b 0) (hL 0) (hP 0) hnewLine hhom'
              (fun ti => hzero ti.1.succ ti.2) (hzero 0)
          rw [hfc]
          apply cubicCombination_mem_productSpan a b (n + 1) c
          intro i
          apply ih a' b' hLtail hPtail hctail
          apply (mem_vanishingSpace a' b' (n + 1) (c i)).mpr
          refine ⟨?_, fun t j => hc_zero i (t, j)⟩
          convert hc_hom i using 1 <;> omega

/-- Pure cubic products exhaust the prescribed homogeneous vanishing space. -/
theorem productSpan_eq_vanishingSpace (a b : Coefficients) (m : ℕ)
    (hL : ∀ t : Fin m, LineConditions (a t) (b t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (a t) (b t))) :
    productSpan a b m = vanishingSpace a b m :=
  le_antisymm (productSpan_le_vanishingSpace a b m)
    (vanishingSpace_le_productSpan m a b hL hP hcross)

theorem mem_productSpan_iff (a b : Coefficients) (m : ℕ)
    (hL : ∀ t : Fin m, LineConditions (a t) (b t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (a t) (b t))) (f : Poly) :
    f ∈ productSpan a b m ↔
      f.IsHomogeneous (3 * m + 1) ∧
        ∀ (t : Fin m) (i : Fin 6),
          eval (GeneralGeometry.sixPoints
            (CubicIdeal.coefficientVectors (a t) (b t)) i) f = 0 := by
  rw [productSpan_eq_vanishingSpace a b m hL hP hcross, mem_vanishingSpace]

/-- Repackage the ambient vanishing subspace as the kernel of evaluation on a
fixed homogeneous component. This equivalence changes no polynomial values. -/
def vanishingSpaceEquiv (a b : Coefficients) (m : ℕ) :
    vanishingSpace a b m ≃ₗ[ℝ]
      HomogeneousInterpolation.vanishingSubmodule (points a b m) (3 * m + 1) where
  toFun f := by
    have hf := (mem_vanishingSpace a b m f.1).mp f.2
    refine ⟨⟨f.1, hf.1⟩, ?_⟩
    rw [HomogeneousInterpolation.mem_vanishingSubmodule]
    intro ti
    exact hf.2 ti.1 ti.2
  invFun f := by
    refine ⟨f.1.1, (mem_vanishingSpace a b m f.1.1).mpr ⟨f.1.2, ?_⟩⟩
    intro t i
    exact (HomogeneousInterpolation.mem_vanishingSubmodule _ _ _).mp f.2 (t, i)
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The additive rank formula follows from the actual span equality and
surjective evaluation at the `6*m` points. This form avoids truncated natural
subtraction when combined with a second rank-nullity identity. -/
theorem finrank_productSpan_add_six_mul (a b : Coefficients) (m : ℕ)
    (hL : ∀ t : Fin m, LineConditions (a t) (b t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (a t) (b t))) :
    Module.finrank ℝ (productSpan a b m) + 6 * m = (3 * m + 3).choose 2 := by
  cases m with
  | zero =>
      rw [productSpan_zero]
      simpa using HomogeneousInterpolation.finrank_homogeneous 1
  | succ n =>
      have heval := GeneralGeometry.global_evaluation_surjective
        (fun t : Fin (n + 1) => CubicIdeal.coefficientVectors (a t) (b t)) hP hcross
        (e := 3 * (n + 1) + 1) (by
          simp only [Fintype.card_fin]
          omega)
      have hrange : LinearMap.range
          (HomogeneousInterpolation.evaluation (points a b (n + 1)) (3 * (n + 1) + 1)) = ⊤ :=
        LinearMap.range_eq_top.mpr heval
      have hdim :=
        (HomogeneousInterpolation.evaluation (points a b (n + 1))
          (3 * (n + 1) + 1)).finrank_range_add_finrank_ker
      rw [hrange, finrank_top, Module.finrank_pi,
        HomogeneousInterpolation.finrank_homogeneous] at hdim
      rw [show (3 * (n + 1) + 1) + 2 = 3 * (n + 1) + 3 by omega] at hdim
      rw [productSpan_eq_vanishingSpace a b (n + 1) hL hP hcross,
        (vanishingSpaceEquiv a b (n + 1)).finrank_eq]
      change Module.finrank ℝ (LinearMap.ker
        (HomogeneousInterpolation.evaluation (points a b (n + 1)) (3 * (n + 1) + 1))) +
          6 * (n + 1) = (3 * (n + 1) + 3).choose 2
      simp only [Fintype.card_prod, Fintype.card_fin] at hdim
      omega

/-- Subtractive form of the product-span dimension formula. -/
theorem finrank_productSpan (a b : Coefficients) (m : ℕ)
    (hL : ∀ t : Fin m, LineConditions (a t) (b t))
    (hP : ∀ t : Fin m,
      GeneralGeometry.LocalNondegenerate (CubicIdeal.coefficientVectors (a t) (b t)))
    (hcross : GeneralGeometry.CrossNonincident
      (fun t : Fin m => CubicIdeal.coefficientVectors (a t) (b t))) :
    Module.finrank ℝ (productSpan a b m) = (3 * m + 3).choose 2 - 6 * m := by
  have hdim := finrank_productSpan_add_six_mul a b m hL hP hcross
  omega

end

end PanelMoments.CubicProducts
