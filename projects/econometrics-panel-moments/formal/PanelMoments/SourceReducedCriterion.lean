import PanelMoments.SourceSingleBlock

set_option autoImplicit false

/-!
# Reduction of the actual new-image independence premise

The exact empty/singleton parameter equivalence reindexes the actual new
source moments. Their normalized columns differ from the joint images by
one common positive denominator and a nonzero constant for each column.
These operations preserve real linear independence. Composing this bridge
with the empty-column replacement gives an induction criterion stated
directly in terms of the reduced columns.

No independence of the reduced columns is assumed implicitly or proved here.
-/

namespace PanelMoments.SourceReducedCriterion

open SourceNewIndices SourceSingleBlock SourceJointImage

noncomputable section

/-- Multiplication by the first transition denominator is common to all
columns and to all first-state coordinates. -/
def denominatorScale (A : Table 2) (r : State 2) : ImageSpace →ₗ[ℝ] ImageSpace where
  toFun f c η := denominator A η.val 0 r * f c η
  map_add' f g := by
    funext c η
    exact mul_add _ _ _
  map_smul' x f := by
    funext c η
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem denominatorScale_injective {A : Table 2} (hA : PositiveTable A)
    (r : State 2) : Function.Injective (denominatorScale A r) := by
  intro f g h
  funext c η
  have hcoord := congrFun (congrFun h c) η
  exact mul_left_cancel₀ (ne_of_gt (denominator_pos hA η.property 0 r)) hcoord

/-- The actual joint images, reindexed by the exact empty/singleton parameters. -/
def jointColumn {N : ℕ} (A : Table 2) (r : State 2) (hN : 2 ≤ N)
    (p : NewParameter N) : ImageSpace :=
  jointFirst (T := N + 1) A r
    (SourceFamily.sourceMoment A r (parameterEquiv hN p).val)

/-- This coefficient depends on the column but not on the effects or the
coordinate at which the image function is evaluated. -/
def columnFactor {N : ℕ} (A : Table 2) (r : State 2) (hN : 2 ≤ N)
    (p : NewParameter N) : ℝ :=
  A 0 r (SourceTransfer.firstGeneratedState (parameterEquiv hN p).val)

theorem columnFactor_pos {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) (p : NewParameter N) :
    0 < columnFactor A r hN p :=
  hA 0 r (SourceTransfer.firstGeneratedState (parameterEquiv hN p).val)

theorem sourceColumn_normalized {N : ℕ} (A : Table 2) (r : State 2)
    (hN : 2 ≤ N) (p : NewParameter N) (c : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    sourceColumn A r hN p c η =
      (denominator A η.val 0 r / columnFactor A r hN p) * jointColumn A r hN p c η := by
  cases p with
  | inl p => rfl
  | inr p => rfl

theorem denominatorScale_jointColumn {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) (p : NewParameter N) :
    denominatorScale A r (jointColumn A r hN p) =
      columnFactor A r hN p • sourceColumn A r hN p := by
  funext c η
  change denominator A η.val 0 r * jointColumn A r hN p c η =
    columnFactor A r hN p * sourceColumn A r hN p c η
  rw [sourceColumn_normalized]
  field_simp [ne_of_gt (columnFactor_pos hA r hN p)]

/-- Common positive function scaling and separate nonzero real column
scalings preserve exactly the linear relations relevant to independence. -/
theorem linearIndependent_jointColumn_iff {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (jointColumn A r hN) ↔
      LinearIndependent ℝ (sourceColumn A r hN) := by
  have hker : LinearMap.ker (denominatorScale A r) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (denominatorScale_injective hA r)
  have hscale := (denominatorScale A r).linearIndependent_iff
    (v := jointColumn A r hN) hker
  change LinearIndependent ℝ (fun p => denominatorScale A r (jointColumn A r hN p)) ↔
    LinearIndependent ℝ (jointColumn A r hN) at hscale
  have hconstant :
      LinearIndependent ℝ (fun p => columnFactor A r hN p • sourceColumn A r hN p) ↔
        LinearIndependent ℝ (sourceColumn A r hN) := by
    exact LinearIndependent.units_smul_iff (sourceColumn A r hN)
      (fun p => Units.mk0 (columnFactor A r hN p)
        (ne_of_gt (columnFactor_pos hA r hN p)))
  have hscaled :
      (fun p => denominatorScale A r (jointColumn A r hN p)) =
        (fun p => columnFactor A r hN p • sourceColumn A r hN p) :=
    funext (denominatorScale_jointColumn hA r hN)
  rw [hscaled] at hscale
  exact hscale.symm.trans hconstant

/-- The joint-image independence premise on the actual new source indices
is equivalent to independence of the normalized source columns. -/
theorem linearIndependent_newJoint_iff_sourceColumn {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (fun i : NewIndex N =>
      jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val)) ↔
      LinearIndependent ℝ (sourceColumn A r hN) := by
  have hreindex : LinearIndependent ℝ (jointColumn A r hN) ↔
      LinearIndependent ℝ (fun i : NewIndex N =>
        jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val)) :=
    linearIndependent_equiv (R := ℝ)
      (f := fun i : NewIndex N =>
        jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val))
      (parameterEquiv hN)
  exact hreindex.symm.trans (linearIndependent_jointColumn_iff hA r hN)

/-- The empty-column replacement is therefore valid for the actual new
joint images, with all normalization and index transport justified. -/
theorem linearIndependent_newJoint_iff_reducedColumn {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (fun i : NewIndex N =>
      jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val)) ↔
      LinearIndependent ℝ (reducedColumn A r hN) :=
  (linearIndependent_newJoint_iff_sourceColumn hA r hN).trans
    (linearIndependent_sourceColumn_iff hA r hN)

/-- A conditional induction step for the full canonical source family.
Independence of the reduced new columns remains an explicit premise. -/
theorem linearIndependent_source_of_reducedColumns {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ))
    (hnew : LinearIndependent ℝ (reducedColumn A r hN)) :
    LinearIndependent ℝ (SourceFamily.sourceMoment A r :
      SourceFamily.SourceIndex (N + 1) → Path 2 (N + 1 + 1) → ℝ) := by
  apply linearIndependent_source_of_jointImages hA r hshort
  exact (linearIndependent_newJoint_iff_reducedColumn hA r hN).mpr hnew

end

end PanelMoments.SourceReducedCriterion
