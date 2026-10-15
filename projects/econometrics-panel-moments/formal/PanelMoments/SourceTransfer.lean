import PanelMoments.SourceJointImage
import PanelMoments.SourceNewIndices

set_option autoImplicit false

/-!
# Actual source joint images as transition-kernel marginals

The kernel product below is the product of the actual model transitions after
the first generated outcome. Multiplication by the source likelihood cancels
the scale ratio, and fixing the generated prefix factors out the initial
transition. This gives the exact initial-row normalization of the source joint
image, with no rank assumption.

For the new empty and singleton shared sets, the first marginal is evaluated
explicitly. The second marginal remains a finite sum of the canonical ordered
kernel products. Identifying that sum with a matrix product is a further step;
no residue formula or independence claim is asserted here.
-/

namespace PanelMoments.SourceTransfer

open scoped BigOperators
open PermutationMoments SourceFamily SourceNewIndices SourceJointImage

noncomputable section

/-- The actual transition kernels after the first outcome in generation order. -/
def kernelProduct {Q N : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (o : Equiv.Perm (Fin (N + 1))) (y : Path Q (N + 1)) : ℝ :=
  ∏ j : Fin N, transition A η ((o j.castSucc).val + 1)
    (y (o j.castSucc)) (y (o j.succ))

/-- A marginal of the kernel product with a prescribed generated prefix. -/
def kernelMarginal {Q N k : ℕ} (A : Table Q) (η : Fin Q → ℝ) (hk : k ≤ N)
    (o : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1)) (a : State Q) : ℝ :=
  ∑ y : Path Q (N + 1), if y 0 = a then
    prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o j))) *
      kernelProduct A η o y else 0

/-- The fixed initial generated state is the only initial-row factor. -/
theorem prefixWeightedChain_eq {Q N k : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (hk : k ≤ N) (r : State Q) (o : Equiv.Perm (Fin (N + 1)))
    (q : Path Q (k + 1)) (y : Path Q (N + 1)) :
    prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o j))) *
        PermutationMoments.transformedChain A η r o y =
      transition A η 0 r (q 0) *
        (prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o j))) *
          kernelProduct A η o y) := by
  classical
  by_cases hp : pathPrefix (Nat.succ_le_succ hk) (fun j => y (o j)) = q
  · have hzero : y (o 0) = q 0 := by
      simpa [pathPrefix] using congrFun hp 0
    simp only [prefixIndicator, hp, ite_true, one_mul, transformedChain_product,
      hzero, kernelProduct]
  · simp only [prefixIndicator, hp, ite_false, zero_mul, mul_zero]

/-- The joint image of a permutation source contrast uses the actual kernels. -/
theorem jointFirst_sourceMoment {Q N k : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (hlast₁ : o₁ (Fin.last N) = Fin.last N)
    (hlast₂ : o₂ (Fin.last N) = Fin.last N) (q : Path Q (k + 1))
    (a : State Q) (η : SourceConditional.PositiveEffectPoint Q) :
    jointFirst A r (PermutationMoments.sourceMoment A r hk o₁ o₂ q) a η =
      transition A η.val 0 r (q 0) *
        (kernelMarginal A η.val hk o₁ q a - kernelMarginal A η.val hk o₂ q a) := by
  classical
  rw [jointFirst_eq_path_sum]
  calc
    _ = ∑ y : Path Q (N + 1), if y 0 = a then
        prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o₁ j))) *
            PermutationMoments.transformedChain A η.val r o₁ y -
          prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o₂ j))) *
            PermutationMoments.transformedChain A η.val r o₂ y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs with hy
      · simp only [PermutationMoments.sourceMoment, contrast, sub_mul, mul_assoc,
          PermutationMoments.scaleRatio_mul_likelihood hA η.property r o₁ hlast₁,
          PermutationMoments.scaleRatio_mul_likelihood hA η.property r o₂ hlast₂]
      · rfl
    _ = _ := by
      simp only [kernelMarginal, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs with hy
      · rw [prefixWeightedChain_eq A η.val hk r o₁ q y,
          prefixWeightedChain_eq A η.val hk r o₂ q y]
      · simp

theorem sum_kernelMarginal {Q N k : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (hk : k ≤ N) (o : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1)) :
    ∑ a : State Q, kernelMarginal A η hk o q a =
      ∑ y : Path Q (N + 1),
        prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o j))) *
          kernelProduct A η o y := by
  classical
  simp only [kernelMarginal]
  rw [Finset.sum_comm]
  simp

/-- Total mass of the constrained kernel marginal is the shorter prefix chain. -/
theorem sum_kernelMarginal_eq_prefix {Q N k : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (hk : k ≤ N)
    (r : State Q) (o : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1)) :
    ∑ a : State Q, kernelMarginal A η hk o q a =
      likelihood (shift (generationTable A o)) η k (q 0) (Fin.tail q) := by
  classical
  apply mul_left_cancel₀ (ne_of_gt (transition_pos hA hη 0 r (q 0)))
  calc
    _ = ∑ y : Path Q (N + 1),
        prefixIndicator q (pathPrefix (Nat.succ_le_succ hk) (fun j => y (o j))) *
          PermutationMoments.transformedChain A η r o y := by
      rw [sum_kernelMarginal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      exact (prefixWeightedChain_eq A η hk r o q y).symm
    _ = ∑ z : Path Q (k + 1), prefixIndicator q z *
        likelihood (generationTable A o) η (k + 1) r z :=
      transformedChain_prefix_sum hA hη (Nat.succ_le_succ hk) r o (prefixIndicator q)
    _ = likelihood (generationTable A o) η (k + 1) r q := by
      simp [prefixIndicator]
    _ = _ := by
      simp only [likelihood, transition, denominator, generationTable_zero]

/-- Shared prefixes have equal total kernel mass, directly from the established
weighted transformed-chain identity. -/
theorem sharedPrefix_kernelMarginal_sum {Q N k : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (hk : k ≤ N)
    (r : State Q) {o₁ o₂ : Equiv.Perm (Fin (N + 1))}
    (hprefix : SharedPrefix k o₁ o₂) (q : Path Q (k + 1)) :
    ∑ a : State Q, kernelMarginal A η hk o₁ q a =
      ∑ a : State Q, kernelMarginal A η hk o₂ q a := by
  apply mul_left_cancel₀ (ne_of_gt (transition_pos hA hη 0 r (q 0)))
  simp only [sum_kernelMarginal, Finset.mul_sum]
  have h := sharedPrefix_weightedChain_sum hA hη hk r hprefix (prefixIndicator q)
  simpa only [prefixWeightedChain_eq A η hk r] using h

/-- A coordinate included in the prescribed prefix has a deterministic value. -/
theorem kernelMarginal_of_fixed {Q N k : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (hk : k ≤ N)
    (r : State Q) (o : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1))
    (j : Fin (k + 1)) (hj : o (Fin.castLE (Nat.succ_le_succ hk) j) = 0)
    (a : State Q) :
    kernelMarginal A η hk o q a =
      if q j = a then likelihood (shift (generationTable A o)) η k (q 0) (Fin.tail q)
      else 0 := by
  classical
  rw [← sum_kernelMarginal_eq_prefix hA hη hk r o q, sum_kernelMarginal]
  by_cases hqa : q j = a
  · rw [ite_eq_left hqa]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hp : pathPrefix (Nat.succ_le_succ hk) (fun i => y (o i)) = q
    · have hy : y 0 = a := by
        have h := congrFun hp j
        simpa only [pathPrefix, hj, hqa] using h
      simp only [hy, ite_true]
    · simp only [prefixIndicator, hp, ite_false, zero_mul, ite_self]
  · rw [ite_eq_right hqa]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y 0 = a
    · have hp : pathPrefix (Nat.succ_le_succ hk) (fun i => y (o i)) ≠ q := by
        intro hp
        apply hqa
        have h := congrFun hp j
        simpa only [pathPrefix, hj, hy] using h.symm
      simp only [hy, ite_true, prefixIndicator, hp, ite_false, zero_mul]
    · simp only [hy, ite_false]

/-- The first generated label of the actual canonical source index. -/
def firstGeneratedState {N : ℕ} (i : SourceFamily.SourceIndex N) : State 2 :=
  (Fin.snoc i.2.2.2 i.2.2.1 : Path 2 (i.1.val.card + 1)) 0

/-- Its kernel image retains both canonical generation orders exactly. -/
def sourceKernelImage {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (i : SourceFamily.SourceIndex N) (a : State 2) : ℝ :=
  kernelMarginal A η (shared_card_le i.1) (firstOrder i.1 i.2.1)
      (Fin.snoc i.2.2.2 i.2.2.1) a -
    kernelMarginal A η (shared_card_le i.1) (secondOrder i.1 i.2.1)
      (Fin.snoc i.2.2.2 i.2.2.1) a

theorem jointFirst_sourceFamily {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (i : SourceFamily.SourceIndex N) (a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    jointFirst A r (SourceFamily.sourceMoment A r i) a η =
      transition A η.val 0 r (firstGeneratedState i) * sourceKernelImage A η.val i a := by
  rw [sourceMoment_eq_permutationMoment]
  exact jointFirst_sourceMoment hA r (shared_card_le i.1) _ _
    (firstOrder_last _ _) (secondOrder_last _ _) _ a η

/-- The source scalar normalization: a common initial denominator and one
positive, fixed initial-row coefficient per column. -/
theorem normalized_jointFirst {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (i : SourceFamily.SourceIndex N) (a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r (firstGeneratedState i)) *
        jointFirst A r (SourceFamily.sourceMoment A r i) a η =
      effect η.val (firstGeneratedState i) * sourceKernelImage A η.val i a := by
  rw [jointFirst_sourceFamily hA]
  unfold transition
  field_simp [ne_of_gt (hA 0 r (firstGeneratedState i)),
    ne_of_gt (denominator_pos hA η.property 0 r)]

theorem sourceKernelImage_sum_eq_zero {N : ℕ} {A : Table 2} {η : Fin 2 → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State 2)
    (i : SourceFamily.SourceIndex N) : ∑ a : State 2, sourceKernelImage A η i a = 0 := by
  simp only [sourceKernelImage, Finset.sum_sub_distrib]
  rw [sharedPrefix_kernelMarginal_sum hA hη (shared_card_le i.1) r
    (orders_sharedPrefix _ _), sub_self]

/-- The probability of the fixed shared/divergent prefix after its initial draw. -/
def sourcePrefixMass {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (i : SourceFamily.SourceIndex N) : ℝ :=
  likelihood (shift (generationTable A (firstOrder i.1 i.2.1))) η i.1.val.card
    (firstGeneratedState i)
      (Fin.tail (Fin.snoc i.2.2.2 i.2.2.1 : Path 2 (i.1.val.card + 1)))

/-- For every new canonical index, slot zero is the first divergent slot. -/
theorem sourceKernelImage_newIndex {N : ℕ} {A : Table 2} {η : Fin 2 → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State 2)
    (i : NewIndex N) (a : State 2) :
    sourceKernelImage A η i.val a =
      (if i.val.2.2.1 = a then sourcePrefixMass A η i.val else 0) -
        kernelMarginal A η (shared_card_le i.val.1) (secondOrder i.val.1 i.val.2.1)
          (Fin.snoc i.val.2.2.2 i.val.2.2.1) a := by
  unfold sourceKernelImage
  rw [kernelMarginal_of_fixed hA hη (shared_card_le i.val.1) r _ _
    (Fin.last i.val.1.val.card)]
  · simp only [Fin.snoc_last, sourcePrefixMass, firstGeneratedState]
  · change firstOrder i.val.1 i.val.2.1
      ⟨i.val.1.val.card, Nat.lt_succ_of_le (shared_card_le i.val.1)⟩ = 0
    rw [firstOrder_divergent, firstSlot_newIndex]
    rfl

@[simp] theorem firstGeneratedState_empty {N : ℕ} (hN : 2 ≤ N)
    (s : Fin N) (q₀ : State 2) :
    firstGeneratedState (emptyIndex hN s q₀).val = q₀ := rfl

@[simp] theorem firstGeneratedState_singleton {N : ℕ} (hN : 2 ≤ N)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    firstGeneratedState (singletonIndex hN t s q₀ q₁).val = q₁ := rfl

@[simp] theorem sourcePrefixMass_empty {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (hN : 2 ≤ N) (s : Fin N) (q₀ : State 2) :
    sourcePrefixMass A η (emptyIndex hN s q₀).val = 1 := rfl

@[simp] theorem sourcePrefixMass_singleton {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (hN : 2 ≤ N) (t : Fin N) (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    sourcePrefixMass A η (singletonIndex hN t s q₀ q₁).val =
      transition A η (t.val + 2) q₁ q₀ := by
  have ho : firstOrder (singletonShared hN t) (singletonSecond hN t s) 0 =
      t.succ.castSucc := by
    simpa only [sharedSlot_singleton] using
      firstOrder_shared (singletonShared hN t) (singletonSecond hN t s) 0 (by simp)
  have htable : shift (generationTable A
      (firstOrder (singletonShared hN t) (singletonSecond hN t s))) 0 =
      A (t.val + 2) := by
    simpa only [shift, Fin.val_zero, zero_add, Fin.castSucc_zero, ho,
      Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using
      generationTable_succ A
        (firstOrder (singletonShared hN t) (singletonSecond hN t s)) (0 : Fin (N + 1))
  change transition (shift (generationTable A
      (firstOrder (singletonShared hN t) (singletonSecond hN t s)))) η 0 q₁ q₀ * 1 = _
  simp only [mul_one, transition, denominator, htable]

/-- Empty new indices: the first branch is the point mass at the divergent label. -/
theorem normalized_jointFirst_empty {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (hN : 2 ≤ N) (r : State 2) (s : Fin N) (q₀ a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r q₀) *
        jointFirst A r (SourceFamily.sourceMoment A r (emptyIndex hN s q₀).val) a η =
      effect η.val q₀ * ((if q₀ = a then 1 else 0) -
        kernelMarginal A η.val (shared_card_le (emptyShared hN))
          (secondOrder (emptyShared hN) (emptySecond hN s)) (Fin.snoc Fin.elim0 q₀) a) := by
  have h := normalized_jointFirst hA r (emptyIndex hN s q₀).val a η
  rw [sourceKernelImage_newIndex hA η.property r] at h
  rw [firstGeneratedState_empty, sourcePrefixMass_empty] at h
  exact h

/-- Singleton new indices: the first branch contains the actual transition from
the shared outcome to the divergent outcome, at table `t + 2`. -/
theorem normalized_jointFirst_singleton {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (hN : 2 ≤ N) (r : State 2) (t : Fin N) (s : {s : Fin N // s ≠ t})
    (q₀ q₁ a : State 2) (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r q₁) *
        jointFirst A r
          (SourceFamily.sourceMoment A r (singletonIndex hN t s q₀ q₁).val) a η =
      effect η.val q₁ * ((if q₀ = a then transition A η.val (t.val + 2) q₁ q₀ else 0) -
        kernelMarginal A η.val (shared_card_le (singletonShared hN t))
          (secondOrder (singletonShared hN t) (singletonSecond hN t s))
          (Fin.snoc (fun _ => q₁) q₀) a) := by
  have h := normalized_jointFirst hA r (singletonIndex hN t s q₀ q₁).val a η
  rw [sourceKernelImage_newIndex hA η.property r] at h
  rw [firstGeneratedState_singleton, sourcePrefixMass_singleton] at h
  exact h

end

end PanelMoments.SourceTransfer
