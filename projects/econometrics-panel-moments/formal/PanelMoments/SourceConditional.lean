import PanelMoments.SourceLifts
import PanelMoments.SourceNewIndices
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

/-!
# Conditional tail expectations and the source-family induction criterion

The linear map here takes the actual conditional tail expectation of a path
function, at every first outcome and every positive fixed-effect vector. Its
kernel consists exactly of functions whose first-outcome slices are shorter
moments. The inherited canonical source moments lie in this kernel.

The final theorem is conditional: independence of the shorter source families,
together with independence of the conditional images of the new indices,
implies independence of the full longer source family. Independence of these
new images is an explicit hypothesis, not a conclusion of this module.
-/

namespace PanelMoments.SourceConditional

open scoped BigOperators

noncomputable section

abbrev PositiveEffectPoint (Q : ℕ) := {η : Fin Q → ℝ // PositiveEffects η}

/-- Conditional tail expectation given the first observed state, as a linear
map into functions of that state and the positive fixed-effect vector. -/
def conditionalTail {Q T : ℕ} (A : Table Q) :
    (Path Q (T + 1) → ℝ) →ₗ[ℝ] (State Q → PositiveEffectPoint Q → ℝ) where
  toFun m a η := ∑ z : Path Q T,
    m (Fin.cons a z : Path Q (T + 1)) * likelihood (shift A) η.val T a z
  map_add' m n := by
    funext a η
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c m := by
    funext a η
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

theorem conditionalTail_apply {Q T : ℕ} (A : Table Q) (m : Path Q (T + 1) → ℝ)
    (a : State Q) (η : PositiveEffectPoint Q) :
    conditionalTail A m a η = ∑ z : Path Q T,
      m (Fin.cons a z : Path Q (T + 1)) * likelihood (shift A) η.val T a z := rfl

theorem conditionalTail_eq_zero_iff {Q T : ℕ} (A : Table Q)
    (m : Path Q (T + 1) → ℝ) :
    conditionalTail A m = 0 ↔
      ∀ a : State Q, IsMoment (shift A) T a
        (fun z => m (Fin.cons a z : Path Q (T + 1))) := by
  constructor
  · intro hm a η hη
    exact congrFun (congrFun hm a) ⟨η, hη⟩
  · intro hm
    funext a η
    exact hm a η.val η.property

/-- Exact kernel characterization, without a rank or completeness assumption. -/
theorem mem_ker_conditionalTail_iff {Q T : ℕ} (A : Table Q)
    (m : Path Q (T + 1) → ℝ) :
    m ∈ LinearMap.ker (conditionalTail (T := T) A) ↔
      ∀ a : State Q, IsMoment (shift A) T a
        (fun z => m (Fin.cons a z : Path Q (T + 1))) := by
  rw [LinearMap.mem_ker, conditionalTail_eq_zero_iff]

theorem conditionalTail_firstStateLift_apply {Q T : ℕ} (A : Table Q)
    (a b : State Q) (m : Path Q T → ℝ) (η : PositiveEffectPoint Q) :
    conditionalTail A (MomentLifts.firstStateLift a m) b η =
      if b = a then ∑ z : Path Q T, m z * likelihood (shift A) η.val T a z else 0 := by
  by_cases hba : b = a
  · subst b
    simp [conditionalTail_apply, MomentLifts.firstStateLift_cons]
  · simp [conditionalTail_apply, MomentLifts.firstStateLift_cons, hba]

theorem conditionalTail_firstStateLift_eq_zero {Q T : ℕ} (A : Table Q)
    (a : State Q) (m : Path Q T → ℝ) (hm : IsMoment (shift A) T a m) :
    conditionalTail A (MomentLifts.firstStateLift a m) = 0 := by
  funext b η
  rw [conditionalTail_firstStateLift_apply, hm η.val η.property]
  simp

/-- Source validity places every inherited canonical moment in the kernel. -/
theorem conditionalTail_liftIndex_eq_zero {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r a : State 2) (i : SourceFamily.SourceIndex N) :
    conditionalTail (T := N + 1) A
      (SourceFamily.sourceMoment A r (SourceRecursion.liftIndex a i)) = 0 := by
  rw [SourceLifts.sourceMoment_liftIndex hA r a i]
  exact conditionalTail_firstStateLift_eq_zero A a _
    (SourceFamily.sourceMoment_isMoment (shift_pos hA) a i)

theorem conditionalTail_zeroIndex_eq_zero {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (i : SourceRecursion.ZeroIndex N) :
    conditionalTail (T := N + 1) A (SourceFamily.sourceMoment A r i.val) = 0 := by
  obtain ⟨p, hp, _⟩ := SourceRecursion.exists_unique_liftIndex i.val i.property
  rw [← hp]
  exact conditionalTail_liftIndex_eq_zero hA r p.1 p.2

/-- The unresolved new-image independence statement is exactly a sufficient
induction hypothesis, once the shorter source families are independent. -/
theorem linearIndependent_source_of_conditional {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ))
    (hnew : LinearIndependent ℝ (fun i : SourceNewIndices.NewIndex N =>
      conditionalTail (T := N + 1) A (SourceFamily.sourceMoment A r i.val))) :
    LinearIndependent ℝ (SourceFamily.sourceMoment A r :
      SourceFamily.SourceIndex (N + 1) → Path 2 (N + 1 + 1) → ℝ) := by
  classical
  have hinherited := SourceLifts.linearIndependent_zeroIndex hA r hshort
  apply (linearIndependent_equiv (Equiv.sumCompl
    (fun i : SourceFamily.SourceIndex (N + 1) => (0 : Fin (N + 1)) ∈ i.1.val))).mp
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmap := congrArg (conditionalTail (T := N + 1) A) hc
  have hnewrel : ∑ i : SourceNewIndices.NewIndex N,
      c (Sum.inr i) • conditionalTail (T := N + 1) A
        (SourceFamily.sourceMoment A r i.val) = 0 := by
    simpa only [map_add, map_sum, map_smul, map_zero, RingHom.id_apply, Function.comp_apply,
      Fintype.sum_sum_type, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
      conditionalTail_zeroIndex_eq_zero hA r, smul_zero, Finset.sum_const_zero,
      zero_add] using hmap
  have hcnew : ∀ i : SourceNewIndices.NewIndex N, c (Sum.inr i) = 0 :=
    Fintype.linearIndependent_iff.mp hnew (fun i => c (Sum.inr i)) hnewrel
  have hinheritedrel : ∑ i : SourceRecursion.ZeroIndex N,
      c (Sum.inl i) • SourceFamily.sourceMoment A r i.val = 0 := by
    simpa only [Function.comp_apply, Fintype.sum_sum_type,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, hcnew, zero_smul,
      Finset.sum_const_zero, add_zero] using hc
  have hcinherited : ∀ i : SourceRecursion.ZeroIndex N, c (Sum.inl i) = 0 :=
    Fintype.linearIndependent_iff.mp hinherited (fun i => c (Sum.inl i)) hinheritedrel
  intro i
  cases i with
  | inl i => exact hcinherited i
  | inr i => exact hcnew i

/-- The same criterion expressed in the explicit empty/singleton coordinates
of the new indices. No independence of these images is asserted here. -/
theorem linearIndependent_source_of_newParameters {N : ℕ} (hN : 2 ≤ N)
    {A : Table 2} (hA : PositiveTable A) (r : State 2)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ))
    (hnew : LinearIndependent ℝ (fun p : SourceNewIndices.NewParameter N =>
      conditionalTail (T := N + 1) A
        (SourceFamily.sourceMoment A r (SourceNewIndices.parameterIndex hN p).val))) :
    LinearIndependent ℝ (SourceFamily.sourceMoment A r :
      SourceFamily.SourceIndex (N + 1) → Path 2 (N + 1 + 1) → ℝ) := by
  apply linearIndependent_source_of_conditional hA r hshort
  exact (linearIndependent_equiv (SourceNewIndices.parameterEquiv hN)).mp hnew

end

end PanelMoments.SourceConditional
