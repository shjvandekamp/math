import PanelMoments.SourceHomogeneous
import PanelMoments.SourceReducedCriterion

set_option autoImplicit false

/-!
# The homogeneous reduced family in the actual source induction criterion

The lift multiplies a normalized image by `X_0` and evaluates it at
`η_j = X_{j+1}/X_0`. Its section is `X = (1,η)`, so the lift is injective.
The homogeneous reduced columns are exactly the images of the already
normalized reduced columns. Their independence is therefore equivalent to
the actual new joint-image independence premise.

The final induction theorem keeps homogeneous reduced-column independence
as an explicit hypothesis; this module does not prove that premise.
-/

namespace PanelMoments.SourceHomogeneousCriterion

open SourceHomogeneous

noncomputable section

abbrev HomogeneousImageSpace := State 2 → PositivePoint 2 → ℝ

/-- The positive homogeneous representative with zeroth coordinate one. -/
def sectionPoint {Q : ℕ} (η : SourceConditional.PositiveEffectPoint Q) : PositivePoint Q :=
  ⟨effect η.val, effect_pos η.property⟩

theorem normalizedPoint_section {Q : ℕ} (η : SourceConditional.PositiveEffectPoint Q) :
    normalizedPoint (sectionPoint η) = η := by
  apply Subtype.ext
  funext q
  change effect η.val q.succ / effect η.val 0 = η.val q
  simp

/-- The lift is linear over constant real scalars. -/
def homogeneousLift : SourceSingleBlock.ImageSpace →ₗ[ℝ] HomogeneousImageSpace where
  toFun f c X := X.val 0 * f c (normalizedPoint X)
  map_add' f g := by
    funext c X
    exact mul_add _ _ _
  map_smul' a f := by
    funext c X
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem homogeneousLift_section (f : SourceSingleBlock.ImageSpace) (c : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    homogeneousLift f c (sectionPoint η) = f c η := by
  change 1 * f c (normalizedPoint (sectionPoint η)) = f c η
  rw [normalizedPoint_section, one_mul]

theorem homogeneousLift_injective : Function.Injective homogeneousLift := by
  intro f g h
  funext c η
  have hsection := congrFun (congrFun h c) (sectionPoint η)
  simpa only [homogeneousLift_section] using hsection

/-- The actual homogeneous reduced vectors, as functions of positive coordinates. -/
def homogeneousReducedColumn {N : ℕ} (A : Table 2) (p : SourceNewIndices.NewParameter N) :
    HomogeneousImageSpace :=
  fun c X => SourceHomogeneous.reducedColumn A X.val p c

theorem homogeneousLift_reducedColumn {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) (p : SourceNewIndices.NewParameter N) :
    homogeneousLift (SourceSingleBlock.reducedColumn A r hN p) =
      homogeneousReducedColumn A p := by
  funext c X
  exact reducedColumn_homogeneous hA X r hN p c

theorem linearIndependent_homogeneousReduced_iff {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (homogeneousReducedColumn A :
      SourceNewIndices.NewParameter N → HomogeneousImageSpace) ↔
        LinearIndependent ℝ (SourceSingleBlock.reducedColumn A r hN) := by
  have hker : LinearMap.ker homogeneousLift = ⊥ :=
    LinearMap.ker_eq_bot_of_injective homogeneousLift_injective
  have h := homogeneousLift.linearIndependent_iff
    (v := SourceSingleBlock.reducedColumn A r hN) hker
  change LinearIndependent ℝ
      (fun p => homogeneousLift (SourceSingleBlock.reducedColumn A r hN p)) ↔
    LinearIndependent ℝ (SourceSingleBlock.reducedColumn A r hN) at h
  simpa only [homogeneousLift_reducedColumn hA r hN] using h

theorem linearIndependent_newJoint_iff_homogeneousReduced {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (fun i : SourceNewIndices.NewIndex N =>
      SourceJointImage.jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val)) ↔
        LinearIndependent ℝ (homogeneousReducedColumn A :
          SourceNewIndices.NewParameter N → HomogeneousImageSpace) :=
  (SourceReducedCriterion.linearIndependent_newJoint_iff_reducedColumn hA r hN).trans
    (linearIndependent_homogeneousReduced_iff hA r hN).symm

/-- Conditional induction for the actual canonical source moments, with the
remaining new-family independence premise stated on positive homogeneous coordinates. -/
theorem linearIndependent_source_of_homogeneousReduced {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ))
    (hnew : LinearIndependent ℝ (homogeneousReducedColumn A :
      SourceNewIndices.NewParameter N → HomogeneousImageSpace)) :
    LinearIndependent ℝ (SourceFamily.sourceMoment A r :
      SourceFamily.SourceIndex (N + 1) → Path 2 (N + 1 + 1) → ℝ) := by
  apply SourceReducedCriterion.linearIndependent_source_of_reducedColumns hA r hN hshort
  exact (linearIndependent_homogeneousReduced_iff hA r hN).mp hnew

end

end PanelMoments.SourceHomogeneousCriterion
