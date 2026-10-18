import PanelMoments.SourceConditional

set_option autoImplicit false

/-!
# The joint first-state image and conditional-tail image

The joint image uses the full path likelihood. It differs from conditional
tail expectation by the first transition probability in each coordinate.
For positive tables this is an injective real-linear multiplication map,
so it preserves precisely the linear relations between image functions.
This does not identify either image with the rational transfer formulas.
-/

namespace PanelMoments.SourceJointImage

open scoped BigOperators
open SourceConditional

noncomputable section

def jointFirst {Q T : ℕ} (A : Table Q) (r : State Q) :
    (Path Q (T + 1) → ℝ) →ₗ[ℝ] (State Q → PositiveEffectPoint Q → ℝ) where
  toFun m a η := ∑ z : Path Q T,
    m (Fin.cons a z) * likelihood A η.val (T + 1) r (Fin.cons a z)
  map_add' m n := by
    funext a η
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c m := by
    funext a η
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

theorem jointFirst_eq_path_sum {Q T : ℕ} (A : Table Q) (r a : State Q)
    (m : Path Q (T + 1) → ℝ) (η : PositiveEffectPoint Q) :
    jointFirst A r m a η = ∑ y : Path Q (T + 1),
      if y 0 = a then m y * likelihood A η.val (T + 1) r y else 0 := by
  classical
  rw [sum_paths_succ]
  simp [jointFirst]

def transitionScale {Q : ℕ} (A : Table Q) (r : State Q) :
    (State Q → PositiveEffectPoint Q → ℝ) →ₗ[ℝ]
      (State Q → PositiveEffectPoint Q → ℝ) where
  toFun f a η := transition A η.val 0 r a * f a η
  map_add' f g := by
    funext a η
    exact mul_add _ _ _
  map_smul' c f := by
    funext a η
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem jointFirst_eq_scaled_tail {Q T : ℕ} (A : Table Q) (r : State Q)
    (m : Path Q (T + 1) → ℝ) :
    jointFirst A r m = transitionScale A r (conditionalTail A m) := by
  funext a η
  change (∑ z : Path Q T,
    m (Fin.cons a z) * likelihood A η.val (T + 1) r (Fin.cons a z)) =
      transition A η.val 0 r a *
        ∑ z : Path Q T, m (Fin.cons a z) * likelihood (shift A) η.val T a z
  simp only [likelihood, Fin.cons_zero, Fin.tail_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem transitionScale_injective {Q : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) : Function.Injective (transitionScale A r) := by
  intro f g h
  funext a η
  have hcoord := congrFun (congrFun h a) η
  exact mul_left_cancel₀ (ne_of_gt (transition_pos hA η.property 0 r a)) hcoord

theorem jointFirst_eq_zero_iff {Q T : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (m : Path Q (T + 1) → ℝ) :
    jointFirst A r m = 0 ↔ conditionalTail A m = 0 := by
  rw [jointFirst_eq_scaled_tail]
  constructor
  · intro h
    apply transitionScale_injective hA r
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

theorem linearIndependent_jointFirst_iff {Q T : ℕ} {ι : Type*}
    {A : Table Q} (hA : PositiveTable A) (r : State Q)
    (v : ι → Path Q (T + 1) → ℝ) :
    LinearIndependent ℝ (fun i => jointFirst A r (v i)) ↔
      LinearIndependent ℝ (fun i => conditionalTail A (v i)) := by
  have hker : LinearMap.ker (transitionScale A r) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (transitionScale_injective hA r)
  have h := (transitionScale A r).linearIndependent_iff
    (v := fun i => conditionalTail A (v i)) hker
  change LinearIndependent ℝ (fun i => transitionScale A r (conditionalTail A (v i))) ↔
    LinearIndependent ℝ (fun i => conditionalTail A (v i)) at h
  simpa only [← jointFirst_eq_scaled_tail] using h

/-- The induction criterion can equivalently use full joint first-state images.
The new-image independence premise remains explicit and unresolved. -/
theorem linearIndependent_source_of_jointImages {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ))
    (hnew : LinearIndependent ℝ (fun i : SourceNewIndices.NewIndex N =>
      jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val))) :
    LinearIndependent ℝ (SourceFamily.sourceMoment A r :
      SourceFamily.SourceIndex (N + 1) → Path 2 (N + 1 + 1) → ℝ) := by
  apply linearIndependent_source_of_conditional hA r hshort
  exact (linearIndependent_jointFirst_iff hA r
    (fun i : SourceNewIndices.NewIndex N => SourceFamily.sourceMoment A r i.val)).mp hnew

end

end PanelMoments.SourceJointImage
