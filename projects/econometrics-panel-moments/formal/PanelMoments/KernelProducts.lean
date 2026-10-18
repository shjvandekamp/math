import PanelMoments.SourceTransfer
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

/-!
# Finite Markov marginals and ordered transition-matrix products

Every matrix in this module is an actual model transition matrix. The finite
path sums are proved equal to their ordered matrix products before applying
the identity to the canonical source orders. No independence premise is used.
-/

namespace PanelMoments.KernelProducts

open scoped BigOperators
open PermutationMoments SourceFamily SourceNewIndices SourceTransfer SourceJointImage

noncomputable section

def transitionMatrix {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ) (t : ℕ) :
    Matrix (State Q) (State Q) ℝ := Matrix.of (transition A η t)

/-- The ordered product of the next `n` transition matrices. -/
def transitionProduct {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ) :
    ℕ → Matrix (State Q) (State Q) ℝ
  | 0 => 1
  | n + 1 => transitionMatrix A η 0 * transitionProduct (shift A) η n

/-- Drop initial transition tables, preserving their order. -/
def dropTable {Q : ℕ} (A : Table Q) : ℕ → Table Q
  | 0 => A
  | n + 1 => dropTable (shift A) n

theorem dropTable_apply {Q : ℕ} (A : Table Q) (n t : ℕ) :
    dropTable A n t = A (t + n) := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => simp only [dropTable, ih, shift, Nat.add_assoc]

theorem transitionProduct_eq_list_prod {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (n : ℕ) :
    transitionProduct A η n = ((List.range n).map (transitionMatrix A η)).prod := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
      simp only [transitionProduct, ih, List.range_succ_eq_map, List.map_cons,
        List.map_map, List.prod_cons]
      rfl

/-- The final state after a finite path; an empty path leaves its initial state. -/
def terminal {Q : ℕ} : (T : ℕ) → State Q → Path Q T → State Q
  | 0, r, _ => r
  | T + 1, _, y => terminal T (y 0) (Fin.tail y)

theorem terminal_eq_last {Q T : ℕ} (r : State Q) (y : Path Q (T + 1)) :
    terminal (T + 1) r y = y (Fin.last T) := by
  induction T generalizing r with
  | zero => rfl
  | succ T ih =>
      rw [terminal, ih]
      rfl

/-- Summing the actual path likelihood at its endpoint is matrix multiplication. -/
theorem endpoint_sum {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (T : ℕ) (r a : State Q) :
    (∑ y : Path Q T, if terminal T r y = a then likelihood A η T r y else 0) =
      transitionProduct A η T r a := by
  classical
  induction T generalizing A r with
  | zero =>
      simp [terminal, likelihood, transitionProduct, Matrix.one_apply]
      rfl
  | succ T ih =>
      rw [sum_paths_succ]
      change (∑ b : State Q, ∑ y : Path Q T,
          if terminal T b y = a then transition A η 0 r b *
            likelihood (shift A) η T b y else 0) =
        ∑ b : State Q, transition A η 0 r b * transitionProduct (shift A) η T b a
      apply Finset.sum_congr rfl
      intro b _
      calc
        _ = transition A η 0 r b * ∑ y : Path Q T,
            if terminal T b y = a then likelihood (shift A) η T b y else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> simp
        _ = _ := congrArg (fun x : ℝ => transition A η 0 r b * x) (ih (shift A) b)

/-- A prescribed prefix contributes its own likelihood, followed by the
ordered transition product from its last state to the endpoint. -/
theorem fixedPrefix_endpoint_sum {Q T k : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (hk : k ≤ T) (r a : State Q) (q : Path Q k) :
    (∑ y : Path Q T, if pathPrefix hk y = q then
      (if terminal T r y = a then likelihood A η T r y else 0) else 0) =
      likelihood A η k r q * transitionProduct (dropTable A k) η (T - k)
        (terminal k r q) a := by
  classical
  induction T generalizing k A r with
  | zero =>
      have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      have he : ∀ y : Path Q 0, pathPrefix hk y = q := fun _ => Subsingleton.elim _ _
      simp only [he, ite_true, likelihood, dropTable, terminal, Nat.sub_zero, one_mul]
      exact endpoint_sum A η 0 r a
  | succ T ih =>
      cases k with
      | zero =>
          simp only [Subsingleton.elim (pathPrefix hk _) q, ite_true, likelihood,
            dropTable, Nat.sub_zero, terminal, one_mul]
          exact endpoint_sum A η (T + 1) r a
      | succ k =>
          obtain ⟨b, u, rfl⟩ := Fin.exists_cons q
          have hk' : k ≤ T := Nat.succ_le_succ_iff.mp hk
          rw [sum_paths_succ]
          simp only [prefix_cons, Fin.cons_inj, terminal, likelihood,
            Fin.cons_zero, Fin.tail_cons, dropTable, Nat.add_sub_add_right]
          calc
            _ = transition A η 0 r b *
                ∑ y : Path Q T, if pathPrefix hk' y = u then
                  (if terminal T b y = a then likelihood (shift A) η T b y else 0)
                  else 0 := by
              rw [Finset.sum_eq_single b]
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                simp only [true_and]
                split_ifs <;> simp_all
              · intro x _ hxb
                simp only [hxb, false_and, ite_false, Finset.sum_const_zero]
              · simp
            _ = _ := by
              rw [ih (shift A) hk' b u]
              ring

theorem pathPrefix_comp {Q k p T : ℕ} (hkp : k ≤ p) (hpT : p ≤ T)
    (y : Path Q T) :
    pathPrefix hkp (pathPrefix hpT y) = pathPrefix (hkp.trans hpT) y := by
  rfl

/-- The target coordinate may occur at any generation position at or after
the fixed prefix. The later chain sums to one. -/
theorem kernelMarginal_eq_product {Q N k p : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (hk : k ≤ N)
    (hkp : k ≤ p) (hpN : p ≤ N) (r a : State Q)
    (o : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1))
    (hposition : o ⟨p, Nat.lt_succ_of_le hpN⟩ = 0) :
    kernelMarginal A η hk o q a =
      likelihood (shift (generationTable A o)) η k (q 0) (Fin.tail q) *
        transitionProduct (dropTable (generationTable A o) (k + 1)) η (p - k)
          (q (Fin.last k)) a := by
  classical
  let w : Path Q (p + 1) → ℝ := fun z =>
    if z (Fin.last p) = a then
      prefixIndicator q (pathPrefix (Nat.succ_le_succ hkp) z) else 0
  apply mul_left_cancel₀ (ne_of_gt (transition_pos hA hη 0 r (q 0)))
  calc
    _ = ∑ y : Path Q (N + 1),
        w (pathPrefix (Nat.succ_le_succ hpN) (fun j => y (o j))) *
          PermutationMoments.transformedChain A η r o y := by
      simp only [kernelMarginal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      have ht : pathPrefix (Nat.succ_le_succ hpN) (fun j => y (o j)) (Fin.last p) =
          y 0 := by
        change y (o ⟨p, Nat.lt_succ_of_le hpN⟩) = y 0
        rw [hposition]
      simp only [w, ht, pathPrefix_comp]
      split_ifs with hy
      · exact (prefixWeightedChain_eq A η hk r o q y).symm
      · simp
    _ = ∑ z : Path Q (p + 1), w z *
        likelihood (generationTable A o) η (p + 1) r z :=
      transformedChain_prefix_sum hA hη (Nat.succ_le_succ hpN) r o w
    _ = likelihood (generationTable A o) η (k + 1) r q *
        transitionProduct (dropTable (generationTable A o) (k + 1)) η (p - k)
          (q (Fin.last k)) a := by
      calc
        _ = ∑ z : Path Q (p + 1), if pathPrefix (Nat.succ_le_succ hkp) z = q then
            (if z (Fin.last p) = a then likelihood (generationTable A o) η (p + 1) r z
              else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          simp only [w, prefixIndicator]
          split_ifs <;> simp_all
        _ = _ := by
          have h := fixedPrefix_endpoint_sum (generationTable A o) η
            (Nat.succ_le_succ hkp) r a q
          simp only [Nat.succ_sub_succ, terminal_eq_last] at h
          exact h
    _ = _ := by
      simp only [likelihood, transition, denominator, generationTable_zero]
      ring

/-- The second canonical order puts the first divergent slot immediately before
the final observation, as follows from its actual defining list. -/
theorem secondOrder_penultimate {N : ℕ} (S : SharedSet (N + 1)) (s : SecondSlot S) :
    secondOrder S s (Fin.last N).castSucc = (firstSlot S).castSucc := by
  simp only [secondOrder, appendLast_castSucc]
  apply congrArg Fin.castSucc
  rw [coreOrder_apply]
  let entries : List (Fin (N + 1)) :=
    S.val.sort (· ≤ ·) ++ s.val :: (remaining S.val s.val (firstSlot S)).sort (· ≤ ·)
  have hlength : entries.length = N := by
    have h := coreList_length S.val s.val (firstSlot S) s.property.1
      (firstSlot_not_mem S) s.property.2
    change (entries ++ [firstSlot S]).length = N + 1 at h
    simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using h
  change (entries ++ [firstSlot S])[N]'_ = firstSlot S
  erw [List.getElem_append_right (by omega)]
  simp only [hlength, Nat.sub_self, List.getElem_cons_zero]

theorem secondOrder_prefixMass {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (i : SourceFamily.SourceIndex N) :
    likelihood (shift (generationTable A (secondOrder i.1 i.2.1))) η i.1.val.card
        (firstGeneratedState i)
        (Fin.tail (Fin.snoc i.2.2.2 i.2.2.1 : Path 2 (i.1.val.card + 1))) =
      sourcePrefixMass A η i := by
  unfold sourcePrefixMass
  apply likelihood_congr
  intro t ht
  change generationTable A (secondOrder i.1 i.2.1) (t + 1) =
    generationTable A (firstOrder i.1 i.2.1) (t + 1)
  exact (generationTable_prefix_eq A (shared_card_le i.1) (orders_sharedPrefix _ _)
    (t + 1) (by omega)).symm

/-- The remaining matrix product in the actual canonical second order. Its
factors start after the prescribed prefix and end on reaching original slot
zero; the transition after slot zero has already been summed out. -/
def newTransferProduct {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ) (i : NewIndex N) :
    Matrix (State 2) (State 2) ℝ :=
  transitionProduct
    (dropTable (generationTable A (secondOrder i.val.1 i.val.2.1)) (i.val.1.val.card + 1))
    η (N - i.val.1.val.card)

/-- This is an ordered product of the actual generation-table transitions. -/
theorem newTransferProduct_eq_list_prod {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (i : NewIndex N) :
    newTransferProduct A η i =
      ((List.range (N - i.val.1.val.card)).map (fun j =>
        transitionMatrix (generationTable A (secondOrder i.val.1 i.val.2.1)) η
          (j + (i.val.1.val.card + 1)))).prod := by
  rw [newTransferProduct, transitionProduct_eq_list_prod]
  congr 1
  apply List.map_congr_left
  intro j _
  ext a b
  simp only [transitionMatrix, Matrix.of_apply, transition, denominator, dropTable_apply]

/-- The negative source branch is the fixed-prefix probability multiplied by
the proved canonical ordered transition product. -/
theorem kernelMarginal_secondOrder {N : ℕ} {A : Table 2} {η : Fin 2 → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State 2)
    (i : NewIndex N) (a : State 2) :
    kernelMarginal A η (shared_card_le i.val.1) (secondOrder i.val.1 i.val.2.1)
        (Fin.snoc i.val.2.2.2 i.val.2.2.1) a =
      sourcePrefixMass A η i.val * newTransferProduct A η i i.val.2.2.1 a := by
  have hk : i.val.1.val.card ≤ N := by
    have h := i.val.1.property.1
    omega
  have hposition : secondOrder i.val.1 i.val.2.1
      ⟨N, Nat.lt_succ_of_le (Nat.le_succ N)⟩ = 0 := by
    change secondOrder i.val.1 i.val.2.1 (Fin.last N).castSucc = 0
    rw [secondOrder_penultimate, firstSlot_newIndex]
    rfl
  have h := kernelMarginal_eq_product hA hη (shared_card_le i.val.1) hk
    (Nat.le_succ N) r a (secondOrder i.val.1 i.val.2.1)
    (Fin.snoc i.val.2.2.2 i.val.2.2.1) hposition
  rw [Fin.snoc_last] at h
  change kernelMarginal A η (shared_card_le i.val.1) (secondOrder i.val.1 i.val.2.1)
      (Fin.snoc i.val.2.2.2 i.val.2.2.1) a =
    likelihood (shift (generationTable A (secondOrder i.val.1 i.val.2.1))) η
        i.val.1.val.card (firstGeneratedState i.val)
        (Fin.tail (Fin.snoc i.val.2.2.2 i.val.2.2.1 : Path 2 (i.val.1.val.card + 1))) *
      newTransferProduct A η i i.val.2.2.1 a at h
  rw [secondOrder_prefixMass] at h
  exact h

theorem sourceKernelImage_newIndex_eq_product {N : ℕ} {A : Table 2} {η : Fin 2 → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State 2)
    (i : NewIndex N) (a : State 2) :
    sourceKernelImage A η i.val a = sourcePrefixMass A η i.val *
      ((if i.val.2.2.1 = a then 1 else 0) - newTransferProduct A η i i.val.2.2.1 a) := by
  rw [sourceKernelImage_newIndex hA hη r, kernelMarginal_secondOrder hA hη r]
  split_ifs <;> ring

/-- Exact matrix-product image of every new canonical source column. -/
theorem normalized_jointFirst_newIndex {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (i : NewIndex N) (a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r (firstGeneratedState i.val)) *
        jointFirst A r (SourceFamily.sourceMoment A r i.val) a η =
      effect η.val (firstGeneratedState i.val) * sourcePrefixMass A η.val i.val *
        ((if i.val.2.2.1 = a then 1 else 0) -
          newTransferProduct A η.val i i.val.2.2.1 a) := by
  rw [normalized_jointFirst hA, sourceKernelImage_newIndex_eq_product hA η.property r]
  ring

/-- Empty shared-set columns give the actual `X_q e_q (I - P)` formula. -/
theorem normalized_jointFirst_empty_product {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (hN : 2 ≤ N) (r : State 2) (s : Fin N) (q₀ a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r q₀) *
        jointFirst A r (SourceFamily.sourceMoment A r (emptyIndex hN s q₀).val) a η =
      effect η.val q₀ * ((if q₀ = a then 1 else 0) -
        newTransferProduct A η.val (emptyIndex hN s q₀) q₀ a) := by
  have h := normalized_jointFirst_newIndex hA r (emptyIndex hN s q₀) a η
  rw [firstGeneratedState_empty, sourcePrefixMass_empty, mul_one] at h
  exact h

/-- Singleton shared-set columns give the actual
`X_q₁ K_(t+2)(q₁,q₀) e_q₀ (I - P)` formula. -/
theorem normalized_jointFirst_singleton_product {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (hN : 2 ≤ N) (r : State 2)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (q₀ q₁ a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r q₁) *
        jointFirst A r
          (SourceFamily.sourceMoment A r (singletonIndex hN t s q₀ q₁).val) a η =
      effect η.val q₁ * transition A η.val (t.val + 2) q₁ q₀ *
        ((if q₀ = a then 1 else 0) -
          newTransferProduct A η.val (singletonIndex hN t s q₀ q₁) q₀ a) := by
  have h := normalized_jointFirst_newIndex hA r (singletonIndex hN t s q₀ q₁) a η
  rw [firstGeneratedState_singleton, sourcePrefixMass_singleton] at h
  exact h

end

end PanelMoments.KernelProducts
