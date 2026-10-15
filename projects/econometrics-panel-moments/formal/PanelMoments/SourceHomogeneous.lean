import PanelMoments.SourceSingleBlock

set_option autoImplicit false

/-!
# Homogeneous coordinates for the actual source kernels and columns

Normalize positive coordinates by `η_j = X_{j+1}/X_0`. The homogeneous
row form is `L_{t,a}(X) = ∑ᵢ A_{t,a,i} X_i`, and the kernel entry is
`A_{t,a,i} X_i / L_{t,a}(X)`. This kernel equals the actual model transition
matrix after normalization, with its exact time and state indices.

The three-state empty, singleton, and reduced source columns become the
displayed homogeneous vectors after multiplication by `X_0`. Kernels and
their ordered products have degree zero under positive scaling; the column
vectors have degree one. No residue or independence assertion is made here.
-/

namespace PanelMoments.SourceHomogeneous

open scoped BigOperators
open SourceTransferOrders SourceNewIndices

noncomputable section

def PositiveCoordinates {Q : ℕ} (X : State Q → ℝ) : Prop := ∀ q, 0 < X q

abbrev PositivePoint (Q : ℕ) := {X : State Q → ℝ // PositiveCoordinates X}

def normalizedEffects {Q : ℕ} (X : State Q → ℝ) : Fin Q → ℝ :=
  fun q => X q.succ / X 0

theorem normalizedEffects_pos {Q : ℕ} {X : State Q → ℝ} (hX : PositiveCoordinates X) :
    PositiveEffects (normalizedEffects X) :=
  fun q => div_pos (hX q.succ) (hX 0)

def normalizedPoint {Q : ℕ} (X : PositivePoint Q) : SourceConditional.PositiveEffectPoint Q :=
  ⟨normalizedEffects X.val, normalizedEffects_pos X.property⟩

theorem effect_normalized {Q : ℕ} {X : State Q → ℝ} (hX : PositiveCoordinates X)
    (q : State Q) : effect (normalizedEffects X) q = X q / X 0 := by
  refine Fin.cases ?_ (fun i => ?_) q
  · simp [ne_of_gt (hX 0)]
  · rfl

theorem coordinate_mul_effect {Q : ℕ} {X : State Q → ℝ} (hX : PositiveCoordinates X)
    (q : State Q) : X 0 * effect (normalizedEffects X) q = X q := by
  rw [effect_normalized hX]
  field_simp [ne_of_gt (hX 0)]

/-- The homogeneous linear denominator at the actual time and previous state. -/
def rowForm {Q : ℕ} (A : Table Q) (X : State Q → ℝ) (t : ℕ) (a : State Q) : ℝ :=
  ∑ i : State Q, A t a i * X i

theorem rowForm_pos {Q : ℕ} {A : Table Q} {X : State Q → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) (a : State Q) :
    0 < rowForm A X t a :=
  Finset.sum_pos (fun i _ => mul_pos (hA t a i) (hX i)) Finset.univ_nonempty

theorem denominator_normalized {Q : ℕ} (A : Table Q) {X : State Q → ℝ}
    (hX : PositiveCoordinates X) (t : ℕ) (a : State Q) :
    denominator A (normalizedEffects X) t a = rowForm A X t a / X 0 := by
  simp only [denominator, rowForm, effect_normalized hX, div_eq_mul_inv,
    Finset.sum_mul, mul_assoc]

def kernel {Q : ℕ} (A : Table Q) (X : State Q → ℝ) (t : ℕ) :
    Matrix (State Q) (State Q) ℝ :=
  Matrix.of (fun a i => A t a i * X i / rowForm A X t a)

theorem transition_normalized {Q : ℕ} {A : Table Q} {X : State Q → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) (a i : State Q) :
    transition A (normalizedEffects X) t a i = kernel A X t a i := by
  rw [transition, effect_normalized hX, denominator_normalized A hX]
  change A t a i * (X i / X 0) / (rowForm A X t a / X 0) =
    A t a i * X i / rowForm A X t a
  field_simp [ne_of_gt (hX 0), ne_of_gt (rowForm_pos hA hX t a)]

/-- The homogeneous kernel is the actual model matrix, not an assumed analogue. -/
theorem kernel_eq_transitionMatrix {Q : ℕ} {A : Table Q} {X : State Q → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) :
    kernel A X t = KernelProducts.transitionMatrix A (normalizedEffects X) t := by
  ext a i
  exact (transition_normalized hA hX t a i).symm

theorem kernel_pos {Q : ℕ} {A : Table Q} {X : State Q → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) (a i : State Q) :
    0 < kernel A X t a i :=
  div_pos (mul_pos (hA t a i) (hX i)) (rowForm_pos hA hX t a)

theorem kernel_row_sum {Q : ℕ} {A : Table Q} {X : State Q → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) (a : State Q) :
    ∑ i : State Q, kernel A X t a i = 1 := by
  simp only [← transition_normalized hA hX]
  exact transition_sum hA (normalizedEffects_pos hX) t a

theorem positiveCoordinates_smul {Q : ℕ} {X : State Q → ℝ}
    (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar) :
    PositiveCoordinates (scalar • X) := fun i => mul_pos hscalar (hX i)

theorem normalizedEffects_smul {Q : ℕ} {X : State Q → ℝ}
    (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar) :
    normalizedEffects (scalar • X) = normalizedEffects X := by
  funext q
  change (scalar * X q.succ) / (scalar * X 0) = X q.succ / X 0
  field_simp [ne_of_gt hscalar, ne_of_gt (hX 0)]

theorem rowForm_smul {Q : ℕ} (A : Table Q) (X : State Q → ℝ) (scalar : ℝ)
    (t : ℕ) (a : State Q) : rowForm A (scalar • X) t a = scalar * rowForm A X t a := by
  simp only [rowForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kernel_smul {Q : ℕ} {A : Table Q} {X : State Q → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar) (t : ℕ) :
    kernel A (scalar • X) t = kernel A X t := by
  rw [kernel_eq_transitionMatrix hA (positiveCoordinates_smul hX hscalar),
    normalizedEffects_smul hX hscalar, kernel_eq_transitionMatrix hA hX]

/-- The canonical source tail indices still refer to time `u.val + 2`. -/
def homogeneousWordProduct {N : ℕ} (A : Table 2) (X : State 2 → ℝ) (w : List (Fin N)) :
    Matrix (State 2) (State 2) ℝ :=
  (w.map (fun u => kernel A X (u.val + 2))).prod

theorem homogeneousWordProduct_eq_wordProduct {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (w : List (Fin N)) :
    homogeneousWordProduct A X w = wordProduct A (normalizedEffects X) w := by
  simp only [homogeneousWordProduct, wordProduct, kernel_eq_transitionMatrix hA hX]

theorem homogeneousWordProduct_smul {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar)
    (w : List (Fin N)) :
    homogeneousWordProduct A (scalar • X) w = homogeneousWordProduct A X w := by
  simp only [homogeneousWordProduct, kernel_smul hA hX hscalar]

def emptyVector {N : ℕ} (A : Table 2) (X : State 2 → ℝ) (s : Fin N) (a : State 2) :
    State 2 → ℝ :=
  fun c => X a * ((if a = c then 1 else 0) - homogeneousWordProduct A X (emptyWord s) a c)

/-- `a` is the shared label and `b` is the divergent label. -/
def singletonVector {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b : State 2) : State 2 → ℝ :=
  fun c => X a * kernel A X (t.val + 2) a b *
    ((if b = c then 1 else 0) - homogeneousWordProduct A X (singletonWord t s.val) b c)

def singleBlockVector {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (s : Fin N) (a : State 2) : State 2 → ℝ :=
  fun c => X a * ((if a = c then 1 else 0) - kernel A X (s.val + 2) a c)

theorem emptyColumn_homogeneous {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (X : PositivePoint 2) (r : State 2) (hN : 2 ≤ N) (s : Fin N) (a c : State 2) :
    X.val 0 * SourceSingleBlock.emptyColumn A r hN s a c (normalizedPoint X) =
      emptyVector A X.val s a c := by
  rw [SourceSingleBlock.emptyColumn_apply hA]
  change X.val 0 * (effect (normalizedEffects X.val) a *
    ((if a = c then 1 else 0) - wordProduct A (normalizedEffects X.val) (emptyWord s) a c)) = _
  rw [← mul_assoc, coordinate_mul_effect X.property,
    ← homogeneousWordProduct_eq_wordProduct hA X.property]
  rfl

theorem singletonColumn_homogeneous {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (X : PositivePoint 2) (r : State 2) (hN : 2 ≤ N)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b c : State 2) :
    X.val 0 * SourceSingleBlock.singletonColumn A r hN t s a b c (normalizedPoint X) =
      singletonVector A X.val t s a b c := by
  rw [SourceSingleBlock.singletonColumn_apply hA]
  change X.val 0 * (effect (normalizedEffects X.val) a *
    transition A (normalizedEffects X.val) (t.val + 2) a b *
      ((if b = c then 1 else 0) -
        wordProduct A (normalizedEffects X.val) (singletonWord t s.val) b c)) = _
  rw [← mul_assoc, ← mul_assoc, coordinate_mul_effect X.property,
    transition_normalized hA X.property,
    ← homogeneousWordProduct_eq_wordProduct hA X.property]
  rfl

theorem singleBlockColumn_homogeneous {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (X : PositivePoint 2) (s : Fin N) (a c : State 2) :
    X.val 0 * SourceSingleBlock.singleBlockColumn A s a c (normalizedPoint X) =
      singleBlockVector A X.val s a c := by
  change X.val 0 * (effect (normalizedEffects X.val) a *
    ((if a = c then 1 else 0) - transition A (normalizedEffects X.val) (s.val + 2) a c)) = _
  rw [← mul_assoc, coordinate_mul_effect X.property, transition_normalized hA X.property]
  rfl

def sourceColumn {N : ℕ} (A : Table 2) (X : State 2 → ℝ) : NewParameter N → State 2 → ℝ
  | Sum.inl p => emptyVector A X p.1 p.2
  | Sum.inr p => singletonVector A X p.1 p.2.1 p.2.2.2 p.2.2.1

def reducedColumn {N : ℕ} (A : Table 2) (X : State 2 → ℝ) : NewParameter N → State 2 → ℝ
  | Sum.inl p => singleBlockVector A X p.1 p.2
  | Sum.inr p => singletonVector A X p.1 p.2.1 p.2.2.2 p.2.2.1

/-- The complete actual normalized new-source family has homogeneous degree one. -/
theorem sourceColumn_homogeneous {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (X : PositivePoint 2) (r : State 2) (hN : 2 ≤ N) (p : NewParameter N) (c : State 2) :
    X.val 0 * SourceSingleBlock.sourceColumn A r hN p c (normalizedPoint X) =
      sourceColumn A X.val p c := by
  cases p with
  | inl p => exact emptyColumn_homogeneous hA X r hN p.1 p.2 c
  | inr p => exact singletonColumn_homogeneous hA X r hN p.1 p.2.1 p.2.2.2 p.2.2.1 c

/-- The same scaling transports the reduced family used by the induction criterion. -/
theorem reducedColumn_homogeneous {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (X : PositivePoint 2) (r : State 2) (hN : 2 ≤ N) (p : NewParameter N) (c : State 2) :
    X.val 0 * SourceSingleBlock.reducedColumn A r hN p c (normalizedPoint X) =
      reducedColumn A X.val p c := by
  cases p with
  | inl p => exact singleBlockColumn_homogeneous hA X p.1 p.2 c
  | inr p => exact singletonColumn_homogeneous hA X r hN p.1 p.2.1 p.2.2.2 p.2.2.1 c

theorem emptyVector_smul {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar)
    (s : Fin N) (a : State 2) : emptyVector A (scalar • X) s a = scalar • emptyVector A X s a := by
  funext c
  simp only [emptyVector, homogeneousWordProduct_smul hA hX hscalar,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem singletonVector_smul {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b : State 2) :
    singletonVector A (scalar • X) t s a b = scalar • singletonVector A X t s a b := by
  funext c
  simp only [singletonVector, homogeneousWordProduct_smul hA hX hscalar,
    kernel_smul hA hX hscalar, Pi.smul_apply, smul_eq_mul]
  ring

theorem singleBlockVector_smul {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar)
    (s : Fin N) (a : State 2) :
    singleBlockVector A (scalar • X) s a = scalar • singleBlockVector A X s a := by
  funext c
  simp only [singleBlockVector, kernel_smul hA hX hscalar, Pi.smul_apply, smul_eq_mul]
  ring

theorem sourceColumn_smul {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar)
    (p : NewParameter N) : sourceColumn A (scalar • X) p = scalar • sourceColumn A X p := by
  cases p with
  | inl p => exact emptyVector_smul hA hX hscalar p.1 p.2
  | inr p => exact singletonVector_smul hA hX hscalar p.1 p.2.1 p.2.2.2 p.2.2.1

theorem reducedColumn_smul {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) {scalar : ℝ} (hscalar : 0 < scalar)
    (p : NewParameter N) : reducedColumn A (scalar • X) p = scalar • reducedColumn A X p := by
  cases p with
  | inl p => exact singleBlockVector_smul hA hX hscalar p.1 p.2
  | inr p => exact singletonVector_smul hA hX hscalar p.1 p.2.1 p.2.2.2 p.2.2.1

end

end PanelMoments.SourceHomogeneous
