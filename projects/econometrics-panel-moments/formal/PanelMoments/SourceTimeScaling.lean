import PanelMoments.SourceHomogeneousCriterion

set_option autoImplicit false

/-!
# Common time-coordinate scaling of actual homogeneous sources

Multiply every table column `b`, at every time, by the same factor `h b`.
The actual row forms, kernels, and ordered products then equal their original
values at coordinates `h b * X b`. Empty, singleton, and single-block source
vectors acquire precisely the inverse factor of their first state.

For positive factors the coordinate change is a bijection of the positive
domain. Pullback and the nonzero constant column factors preserve independence
of the actual source and reduced families at every fixed length. Neither family
is asserted to be independent, and no determinant nonvanishing is proved.
-/

namespace PanelMoments.SourceTimeScaling

open scoped BigOperators
open SourceHomogeneous SourceHomogeneousCriterion SourceNewIndices

noncomputable section

/-- The same column scaling at every actual time. -/
def scaledTable {Q : ℕ} (A : Table Q) (h : State Q → ℝ) : Table Q :=
  fun t a b => A t a b * h b

def scaledCoordinates {Q : ℕ} (h X : State Q → ℝ) : State Q → ℝ :=
  fun b => h b * X b

theorem scaledTable_pos {Q : ℕ} {A : Table Q} (hA : PositiveTable A)
    {h : State Q → ℝ} (hh : ∀ b, 0 < h b) : PositiveTable (scaledTable A h) :=
  fun t a b => mul_pos (hA t a b) (hh b)

theorem rowForm_scaledTable {Q : ℕ} (A : Table Q) (h X : State Q → ℝ)
    (t : ℕ) (a : State Q) :
    rowForm (scaledTable A h) X t a = rowForm A (scaledCoordinates h X) t a := by
  simp only [rowForm, scaledTable, scaledCoordinates, mul_assoc]

theorem kernel_scaledTable {Q : ℕ} (A : Table Q) (h X : State Q → ℝ) (t : ℕ) :
    kernel (scaledTable A h) X t = kernel A (scaledCoordinates h X) t := by
  ext a b
  simp only [kernel, Matrix.of_apply, rowForm_scaledTable,
    scaledTable, scaledCoordinates, mul_assoc]

/-- The original canonical time indices and their list order are preserved. -/
theorem homogeneousWordProduct_scaledTable {N : ℕ} (A : Table 2)
    (h X : State 2 → ℝ) (w : List (Fin N)) :
    homogeneousWordProduct (scaledTable A h) X w =
      homogeneousWordProduct A (scaledCoordinates h X) w := by
  simp only [homogeneousWordProduct, kernel_scaledTable]

theorem emptyVector_scaledTable {N : ℕ} (A : Table 2) (h X : State 2 → ℝ)
    (s : Fin N) (a : State 2) (ha : h a ≠ 0) :
    emptyVector (scaledTable A h) X s a =
      (h a)⁻¹ • emptyVector A (scaledCoordinates h X) s a := by
  funext c
  simp only [emptyVector, homogeneousWordProduct_scaledTable,
    scaledCoordinates, Pi.smul_apply, smul_eq_mul]
  field_simp [ha]

theorem singletonVector_scaledTable {N : ℕ} (A : Table 2) (h X : State 2 → ℝ)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b : State 2) (ha : h a ≠ 0) :
    singletonVector (scaledTable A h) X t s a b =
      (h a)⁻¹ • singletonVector A (scaledCoordinates h X) t s a b := by
  funext c
  simp only [singletonVector, homogeneousWordProduct_scaledTable, kernel_scaledTable,
    scaledCoordinates, Pi.smul_apply, smul_eq_mul]
  field_simp [ha]

theorem singleBlockVector_scaledTable {N : ℕ} (A : Table 2) (h X : State 2 → ℝ)
    (s : Fin N) (a : State 2) (ha : h a ≠ 0) :
    singleBlockVector (scaledTable A h) X s a =
      (h a)⁻¹ • singleBlockVector A (scaledCoordinates h X) s a := by
  funext c
  simp only [singleBlockVector, kernel_scaledTable,
    scaledCoordinates, Pi.smul_apply, smul_eq_mul]
  field_simp [ha]

/-- The source's first generated label, including the actual singleton convention. -/
def headState {N : ℕ} : NewParameter N → State 2
  | Sum.inl p => p.2
  | Sum.inr p => p.2.2.2

theorem sourceColumn_scaledTable {N : ℕ} (A : Table 2) (h X : State 2 → ℝ)
    (p : NewParameter N) (hh : ∀ a, h a ≠ 0) :
    SourceHomogeneous.sourceColumn (scaledTable A h) X p =
      (h (headState p))⁻¹ • SourceHomogeneous.sourceColumn A (scaledCoordinates h X) p := by
  cases p with
  | inl p => exact emptyVector_scaledTable A h X p.1 p.2 (hh p.2)
  | inr p => exact singletonVector_scaledTable A h X p.1 p.2.1 p.2.2.2 p.2.2.1 (hh _)

theorem reducedColumn_scaledTable {N : ℕ} (A : Table 2) (h X : State 2 → ℝ)
    (p : NewParameter N) (hh : ∀ a, h a ≠ 0) :
    SourceHomogeneous.reducedColumn (scaledTable A h) X p =
      (h (headState p))⁻¹ • SourceHomogeneous.reducedColumn A (scaledCoordinates h X) p := by
  cases p with
  | inl p => exact singleBlockVector_scaledTable A h X p.1 p.2 (hh p.2)
  | inr p => exact singletonVector_scaledTable A h X p.1 p.2.1 p.2.2.2 p.2.2.1 (hh _)

def scaledPositivePoint {Q : ℕ} (h : State Q → ℝ) (hh : ∀ a, 0 < h a)
    (X : PositivePoint Q) : PositivePoint Q :=
  ⟨scaledCoordinates h X.val, fun a => mul_pos (hh a) (X.property a)⟩

/-- Pullback uses constant real scalars and the actual positive coordinate domain. -/
def coordinatePullback (h : State 2 → ℝ) (hh : ∀ a, 0 < h a) :
    HomogeneousImageSpace →ₗ[ℝ] HomogeneousImageSpace where
  toFun f c X := f c (scaledPositivePoint h hh X)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinatePullback_injective (h : State 2 → ℝ) (hh : ∀ a, 0 < h a) :
    Function.Injective (coordinatePullback h hh) := by
  intro f g hfg
  funext c X
  let Y : PositivePoint 2 := ⟨fun a => X.val a / h a,
    fun a => div_pos (X.property a) (hh a)⟩
  have hY : scaledPositivePoint h hh Y = X := by
    apply Subtype.ext
    funext a
    change h a * (X.val a / h a) = X.val a
    field_simp [ne_of_gt (hh a)]
  have heq := congrFun (congrFun hfg c) Y
  change f c (scaledPositivePoint h hh Y) = g c (scaledPositivePoint h hh Y) at heq
  simpa only [hY] using heq

/-- The already defined actual source vectors, restricted to positive coordinates. -/
def positiveSourceColumn {N : ℕ} (A : Table 2) (p : NewParameter N) :
    HomogeneousImageSpace :=
  fun c X => SourceHomogeneous.sourceColumn A X.val p c

theorem positiveSourceColumn_scaledTable {N : ℕ} (A : Table 2)
    (h : State 2 → ℝ) (hh : ∀ a, 0 < h a) (p : NewParameter N) :
    positiveSourceColumn (scaledTable A h) p =
      (h (headState p))⁻¹ • coordinatePullback h hh (positiveSourceColumn A p) := by
  funext c X
  exact congrFun (sourceColumn_scaledTable A h X.val p (fun a => ne_of_gt (hh a))) c

theorem homogeneousReducedColumn_scaledTable {N : ℕ} (A : Table 2)
    (h : State 2 → ℝ) (hh : ∀ a, 0 < h a) (p : NewParameter N) :
    homogeneousReducedColumn (scaledTable A h) p =
      (h (headState p))⁻¹ • coordinatePullback h hh (homogeneousReducedColumn A p) := by
  funext c X
  exact congrFun (reducedColumn_scaledTable A h X.val p (fun a => ne_of_gt (hh a))) c

/-- Common positive time scaling preserves independence of the actual E/F family. -/
theorem linearIndependent_sourceColumn_scaledTable_iff {N : ℕ} (A : Table 2)
    (h : State 2 → ℝ) (hh : ∀ a, 0 < h a) :
    LinearIndependent ℝ (positiveSourceColumn (scaledTable A h) :
      NewParameter N → HomogeneousImageSpace) ↔
        LinearIndependent ℝ (positiveSourceColumn A :
          NewParameter N → HomogeneousImageSpace) := by
  have hker : LinearMap.ker (coordinatePullback h hh) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (coordinatePullback_injective h hh)
  have hmap := (coordinatePullback h hh).linearIndependent_iff
    (v := positiveSourceColumn A (N := N)) hker
  have hscale := LinearIndependent.units_smul_iff
    (fun p : NewParameter N => coordinatePullback h hh (positiveSourceColumn A p))
    (fun p => Units.mk0 (h (headState p))⁻¹ (inv_ne_zero (ne_of_gt (hh _))))
  have hfamily : (positiveSourceColumn (scaledTable A h) :
      NewParameter N → HomogeneousImageSpace) =
      fun p => (h (headState p))⁻¹ • coordinatePullback h hh (positiveSourceColumn A p) :=
    funext (positiveSourceColumn_scaledTable A h hh)
  rw [hfamily]
  exact hscale.trans hmap

/-- The same equivalence applies to the actual reduced-family induction premise. -/
theorem linearIndependent_reducedColumn_scaledTable_iff {N : ℕ} (A : Table 2)
    (h : State 2 → ℝ) (hh : ∀ a, 0 < h a) :
    LinearIndependent ℝ (homogeneousReducedColumn (scaledTable A h) :
      NewParameter N → HomogeneousImageSpace) ↔
        LinearIndependent ℝ (homogeneousReducedColumn A :
          NewParameter N → HomogeneousImageSpace) := by
  have hker : LinearMap.ker (coordinatePullback h hh) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (coordinatePullback_injective h hh)
  have hmap := (coordinatePullback h hh).linearIndependent_iff
    (v := homogeneousReducedColumn A (N := N)) hker
  have hscale := LinearIndependent.units_smul_iff
    (fun p : NewParameter N => coordinatePullback h hh (homogeneousReducedColumn A p))
    (fun p => Units.mk0 (h (headState p))⁻¹ (inv_ne_zero (ne_of_gt (hh _))))
  have hfamily : (homogeneousReducedColumn (scaledTable A h) :
      NewParameter N → HomogeneousImageSpace) =
      fun p => (h (headState p))⁻¹ • coordinatePullback h hh (homogeneousReducedColumn A p) :=
    funext (homogeneousReducedColumn_scaledTable A h hh)
  rw [hfamily]
  exact hscale.trans hmap

end

end PanelMoments.SourceTimeScaling
