import PanelMoments.KernelProducts

set_option autoImplicit false

/-!
# The explicit canonical order of the source transfer products

The actual second generation order places the selected second slot first
after the fixed shared prefix, followed by the remaining slots in increasing
order. For the new empty and singleton families, deleting original slot zero
and decrementing the other slots gives the tail words used below. Their
transition tables are exactly `u.val + 2`.
-/

namespace PanelMoments.SourceTransferOrders

open scoped BigOperators
open PermutationMoments SourceFamily SourceNewIndices SourceTransfer
open KernelProducts SourceJointImage

noncomputable section

/-- The second order between the shared prefix and the first divergent slot. -/
def middleSlots {N : ℕ} (S : SharedSet (N + 1)) (s : SecondSlot S) :
    List (Fin (N + 1)) :=
  s.val :: (remaining S.val s.val (firstSlot S)).sort (· ≤ ·)

theorem middleSlots_length {N : ℕ} (S : SharedSet (N + 1)) (s : SecondSlot S) :
    (middleSlots S s).length = N - S.val.card := by
  have h := coreList_length S.val s.val (firstSlot S) s.property.1
    (firstSlot_not_mem S) s.property.2
  change ((S.val.sort (· ≤ ·) ++ middleSlots S s) ++ [firstSlot S]).length = N + 1 at h
  simp only [List.length_append, Finset.length_sort, List.length_singleton] at h
  omega

theorem middleSlot_bound {N : ℕ} (S : SharedSet (N + 1)) (s : SecondSlot S)
    (j : Fin (middleSlots S s).length) : S.val.card + j.val < N + 1 := by
  have hj := j.isLt
  have hlength := middleSlots_length S s
  omega

/-- The list entries are proved equal to the actual permutation entries. -/
theorem secondOrder_middle {N : ℕ} (S : SharedSet (N + 1)) (s : SecondSlot S)
    (j : Fin (middleSlots S s).length) :
    secondOrder S s (⟨S.val.card + j.val, middleSlot_bound S s j⟩ : Fin (N + 1)).castSucc =
      ((middleSlots S s)[j.val]).castSucc := by
  simp only [secondOrder, appendLast_castSucc]
  apply congrArg Fin.castSucc
  rw [coreOrder_apply]
  change ((S.val.sort (· ≤ ·) ++ middleSlots S s) ++ [firstSlot S])[S.val.card + j.val]'_ =
    (middleSlots S s)[j.val]
  erw [List.getElem_append_left (by
    simp only [List.length_append, Finset.length_sort]
    exact Nat.add_lt_add_left j.isLt _)]
  erw [List.getElem_append_right (by simp only [Finset.length_sort]; omega)]
  simp only [Finset.length_sort, Nat.add_sub_cancel_left]

theorem generationTable_middle {Q N : ℕ} (A : Table Q)
    (S : SharedSet (N + 1)) (s : SecondSlot S) (j : Fin (middleSlots S s).length) :
    generationTable A (secondOrder S s) (j.val + (S.val.card + 1)) =
      A (((middleSlots S s)[j.val]).val + 1) := by
  calc
    _ = generationTable A (secondOrder S s) ((S.val.card + j.val) + 1) := by
      congr 1
      omega
    _ = A ((secondOrder S s
        (⟨S.val.card + j.val, middleSlot_bound S s j⟩ : Fin (N + 1)).castSucc).val + 1) :=
      generationTable_succ A (secondOrder S s)
        ⟨S.val.card + j.val, middleSlot_bound S s j⟩
    _ = _ := by rw [secondOrder_middle]; rfl

/-- Exact list rewrite of the product, with no assumed order matching. -/
theorem newTransferProduct_eq_middleSlots {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (i : NewIndex N) :
    newTransferProduct A η i =
      ((middleSlots i.val.1 i.val.2.1).map
        (fun u => transitionMatrix A η (u.val + 1))).prod := by
  rw [newTransferProduct_eq_list_prod]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, middleSlots_length]
  · intro j hj₁ hj₂
    have hj : j < (middleSlots i.val.1 i.val.2.1).length := by
      simpa only [List.length_map] using hj₂
    simp only [List.getElem_map, List.getElem_range]
    have htable := generationTable_middle A i.val.1 i.val.2.1 ⟨j, hj⟩
    ext a b
    simp only [transitionMatrix, Matrix.of_apply, transition, denominator, htable]

/-- Move `s` first and keep every other tail index in increasing order. -/
def emptyWord {N : ℕ} (s : Fin N) : List (Fin N) :=
  s :: (Finset.univ.erase s).sort (· ≤ ·)

/-- Omit the shared tail index `t`, move `s` first, and sort the others. -/
def singletonWord {N : ℕ} (t s : Fin N) : List (Fin N) :=
  s :: ((Finset.univ.erase t).erase s).sort (· ≤ ·)

/-- Product of tail matrices in the given explicit order. -/
def wordProduct {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ) (w : List (Fin N)) :
    Matrix (State 2) (State 2) ℝ :=
  (w.map (fun u => transitionMatrix A η (u.val + 2))).prod

theorem remaining_empty {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    remaining (emptyShared hN).val (emptySecond hN s).val (firstSlot (emptyShared hN)) =
      (Finset.univ.erase s).map (Fin.succEmb N) := by
  simp only [emptyShared_val, emptySecond, firstSlot_empty]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [remaining]
  · simp [remaining]

theorem remaining_singleton {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) :
    remaining (singletonShared hN t).val (singletonSecond hN t s).val
        (firstSlot (singletonShared hN t)) =
      ((Finset.univ.erase t).erase s.val).map (Fin.succEmb N) := by
  simp only [singletonShared_val, singletonSecond, firstSlot_singleton]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [remaining]
  · simp [remaining, and_comm]

theorem middleSlots_empty {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    middleSlots (emptyShared hN) (emptySecond hN s) = (emptyWord s).map Fin.succ := by
  rw [middleSlots, remaining_empty, SourceLifts.sort_map_succ]
  rfl

theorem middleSlots_singleton {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) :
    middleSlots (singletonShared hN t) (singletonSecond hN t s) =
      (singletonWord t s.val).map Fin.succ := by
  rw [middleSlots, remaining_singleton, SourceLifts.sort_map_succ]
  rfl

theorem map_succ_product {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ) (w : List (Fin N)) :
    ((w.map Fin.succ).map (fun u => transitionMatrix A η (u.val + 1))).prod =
      wordProduct A η w := by
  simp only [wordProduct, List.map_map, Function.comp_def, Fin.val_succ, Nat.add_assoc]

theorem newTransferProduct_empty {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (hN : 2 ≤ N) (s : Fin N) (q₀ : State 2) :
    newTransferProduct A η (emptyIndex hN s q₀) = wordProduct A η (emptyWord s) := by
  rw [newTransferProduct_eq_middleSlots]
  change ((middleSlots (emptyShared hN) (emptySecond hN s)).map
    (fun u => transitionMatrix A η (u.val + 1))).prod = _
  rw [middleSlots_empty, map_succ_product]

theorem newTransferProduct_singleton {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (hN : 2 ≤ N) (t : Fin N) (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    newTransferProduct A η (singletonIndex hN t s q₀ q₁) =
      wordProduct A η (singletonWord t s.val) := by
  rw [newTransferProduct_eq_middleSlots]
  change ((middleSlots (singletonShared hN t) (singletonSecond hN t s)).map
    (fun u => transitionMatrix A η (u.val + 1))).prod = _
  rw [middleSlots_singleton, map_succ_product]

theorem emptyWord_nodup {N : ℕ} (s : Fin N) : (emptyWord s).Nodup := by
  simp [emptyWord]

theorem singletonWord_nodup {N : ℕ} (t s : Fin N) : (singletonWord t s).Nodup := by
  simp [singletonWord]

theorem mem_emptyWord {N : ℕ} (s u : Fin N) : u ∈ emptyWord s := by
  by_cases h : u = s <;> simp [emptyWord, h]

theorem mem_singletonWord {N : ℕ} (t s u : Fin N) (hst : s ≠ t) :
    u ∈ singletonWord t s ↔ u ≠ t := by
  by_cases h : u = s
  · subst u
    simp [singletonWord, hst]
  · simp [singletonWord, h]

/-- The empty source image with its precise ascending tail order. -/
theorem normalized_jointFirst_empty_word {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (hN : 2 ≤ N) (r : State 2) (s : Fin N) (q₀ a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r q₀) *
        jointFirst A r (SourceFamily.sourceMoment A r (emptyIndex hN s q₀).val) a η =
      effect η.val q₀ * ((if q₀ = a then 1 else 0) - wordProduct A η.val (emptyWord s) q₀ a) := by
  rw [normalized_jointFirst_empty_product hA hN, newTransferProduct_empty]

/-- The singleton source image omits exactly the shared block from its suffix. -/
theorem normalized_jointFirst_singleton_word {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (hN : 2 ≤ N) (r : State 2)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (q₀ q₁ a : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    (denominator A η.val 0 r / A 0 r q₁) *
        jointFirst A r
          (SourceFamily.sourceMoment A r (singletonIndex hN t s q₀ q₁).val) a η =
      effect η.val q₁ * transition A η.val (t.val + 2) q₁ q₀ *
        ((if q₀ = a then 1 else 0) - wordProduct A η.val (singletonWord t s.val) q₀ a) := by
  rw [normalized_jointFirst_singleton_product hA hN, newTransferProduct_singleton]

end

end PanelMoments.SourceTransferOrders
