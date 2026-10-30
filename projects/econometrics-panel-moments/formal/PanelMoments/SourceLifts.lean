import PanelMoments.SourceRecursion
import PanelMoments.PermutationLifts

set_option autoImplicit false

/-!
# Exact first-state lifts of the canonical source moments

The canonical generation orders commute with inserting a shared initial slot.
Consequently, the source-index recursion is also an exact recursion of moment
functions. Independence of every shorter initial-state family therefore implies
independence of the longer subfamily whose shared set contains zero. The
independence hypothesis is explicit; the remaining longer indices are not
covered by this theorem.
-/

namespace PanelMoments.SourceLifts

open SourceFamily SourceRecursion PermutationLifts

noncomputable section

theorem remaining_lift {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) :
    remaining (liftRaw S) a.succ b.succ =
      (remaining S a b).map (Fin.succEmb N) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [remaining]
  · simp [remaining]

theorem sort_map_succ {N : ℕ} (S : Finset (Fin N)) :
    (S.map (Fin.succEmb N)).sort (· ≤ ·) = (S.sort (· ≤ ·)).map Fin.succ :=
  (Finset.map_sort (Fin.succEmb N) S (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => Fin.succ_le_succ_iff.symm)).symm

/-- The footnote-7 list acquires one initial zero and shifts every old entry. -/
theorem coreList_lift {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) :
    coreList (liftRaw S) a.succ b.succ = 0 :: (coreList S a b).map Fin.succ := by
  simp [coreList, sort_liftRaw, remaining_lift, sort_map_succ]

/-- The list-defined permutation has the same explicit recursion. -/
theorem coreOrder_lift {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    coreOrder (liftRaw S) a.succ b.succ
      (by simpa only [succ_mem_liftRaw] using ha)
      (by simpa only [succ_mem_liftRaw] using hb)
      (fun h => hab (Fin.succ_inj.mp h)) =
      prependFirst (coreOrder S a b ha hb hab) := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [coreOrder_apply, coreList_lift, prependFirst_zero, Fin.val_zero,
      List.getElem_cons_zero]
  · simp only [coreOrder_apply, coreList_lift, prependFirst_succ, Fin.val_succ,
      List.getElem_cons_succ, List.getElem_map]

theorem appendLast_prependFirst {N : ℕ} (p : Equiv.Perm (Fin N)) :
    appendLast (prependFirst p) = prependFirst (appendLast p) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change appendLast (prependFirst p) (Fin.last (N + 1)) =
      prependFirst (appendLast p) (Fin.last N).succ
    simp only [appendLast_last, prependFirst_succ]
    rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · change appendLast (prependFirst p) (0 : Fin (N + 1)).castSucc =
        prependFirst (appendLast p) 0
      simp only [appendLast_castSucc, prependFirst_zero]
      rfl
    · change appendLast (prependFirst p) k.succ.castSucc =
        prependFirst (appendLast p) k.castSucc.succ
      simp only [appendLast_castSucc, prependFirst_succ]
      rfl

/-- Exact transport of the first canonical order, including its final fixed slot. -/
theorem firstOrder_lift {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    firstOrder (liftShared S) (liftSecond S s) = prependFirst (firstOrder S s) := by
  calc
    _ = appendLast (prependFirst (coreOrder S.val (firstSlot S) s.val
        (firstSlot_not_mem S) s.property.1 (Ne.symm s.property.2))) := by
      simpa only [firstOrder, liftShared_val, liftSecond_val, firstSlot_lift] using
        congrArg appendLast (coreOrder_lift S.val (firstSlot S) s.val
          (firstSlot_not_mem S) s.property.1 (Ne.symm s.property.2))
    _ = _ := appendLast_prependFirst _

/-- Exact transport of the swapped canonical order. -/
theorem secondOrder_lift {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    secondOrder (liftShared S) (liftSecond S s) = prependFirst (secondOrder S s) := by
  calc
    _ = appendLast (prependFirst (coreOrder S.val s.val (firstSlot S)
        s.property.1 (firstSlot_not_mem S) s.property.2)) := by
      simpa only [secondOrder, liftShared_val, liftSecond_val, firstSlot_lift] using
        congrArg appendLast (coreOrder_lift S.val s.val (firstSlot S)
          s.property.1 (firstSlot_not_mem S) s.property.2)
    _ = _ := appendLast_prependFirst _

/-- Reindex a prefix vector after proving equality of its lengths. -/
theorem snoc_cast {β : Type*} {k l : ℕ} (h : k = l)
    (q : Fin k → β) (b : β) :
    (fun i : Fin (l + 1) => (Fin.snoc q b : Fin (k + 1) → β)
      (Fin.cast (congrArg (fun n => n + 1) h).symm i)) =
      (Fin.snoc (fun j : Fin l => q (Fin.cast h.symm j)) b : Fin (l + 1) → β) := by
  subst l
  rfl

theorem prefixVector_lift {N : ℕ} (S : SharedSet N) (a q₀ : State 2)
    (q : Fin S.val.card → State 2) :
    (fun i : Fin (S.val.card + 1 + 1) =>
      (Fin.snoc (liftLabels S a q) q₀ : Fin ((liftShared S).val.card + 1) → State 2)
        (Fin.cast (congrArg (fun n => n + 1) (card_liftShared S)).symm i)) =
      (Fin.cons a (Fin.snoc q q₀) : Fin (S.val.card + 1 + 1) → State 2) := by
  rw [snoc_cast (card_liftShared S)]
  have hlabels : (fun j : Fin (S.val.card + 1) =>
      liftLabels S a q (Fin.cast (card_liftShared S).symm j)) =
      (Fin.cons a q : Fin (S.val.card + 1) → State 2) := by
    funext j
    rfl
  rw [hlabels, ← Fin.cons_snoc_eq_snoc_cons]

/-- Changing only a proved prefix length does not change its moment. -/
theorem permutationSourceMoment_cast {Q N k l : ℕ} (h : k = l)
    (A : Table Q) (r : State Q) (hk : k ≤ N) (hl : l ≤ N)
    (o₁ o₂ : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1)) :
    PermutationMoments.sourceMoment A r hk o₁ o₂ q =
      PermutationMoments.sourceMoment A r hl o₁ o₂
        (fun i => q (Fin.cast (congrArg (fun n => n + 1) h).symm i)) := by
  subst l
  rfl

/-- An inherited canonical equation-(24) moment is exactly the corresponding
shorter moment restricted to the slice with the specified first outcome. -/
theorem sourceMoment_liftIndex {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r a : State 2) (i : SourceFamily.SourceIndex N) :
    SourceFamily.sourceMoment A r (liftIndex a i) =
      MomentLifts.firstStateLift a (SourceFamily.sourceMoment (shift A) a i) := by
  rcases i with ⟨S, s, q₀, q⟩
  rw [liftIndex_apply, SourceFamily.sourceMoment_eq_permutationMoment,
    SourceFamily.sourceMoment_eq_permutationMoment]
  change PermutationMoments.sourceMoment A r (shared_card_le (liftShared S))
      (firstOrder (liftShared S) (liftSecond S s))
      (secondOrder (liftShared S) (liftSecond S s)) (Fin.snoc (liftLabels S a q) q₀) =
    MomentLifts.firstStateLift a (PermutationMoments.sourceMoment (shift A) a
      (shared_card_le S) (firstOrder S s) (secondOrder S s) (Fin.snoc q q₀))
  rw [firstOrder_lift, secondOrder_lift,
    permutationSourceMoment_cast (card_liftShared S) A r
      (shared_card_le (liftShared S)) (Nat.succ_le_succ (shared_card_le S)),
    prefixVector_lift]
  exact sourceMoment_prepend hA r a (shared_card_le S)
    (firstOrder S s) (secondOrder S s) (Fin.snoc q q₀)

/-- Conditional independence of the actual canonical inherited subfamily.
The assumption concerns each shorter initial-state family and does not assert
independence of the new, non-inherited indices at the longer horizon. -/
theorem linearIndependent_zeroIndex {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ)) :
    LinearIndependent ℝ (fun i : ZeroIndex N => SourceFamily.sourceMoment A r i.val) := by
  apply (linearIndependent_equiv (liftIndexEquiv N)).mp
  have hfamily : (fun i : ZeroIndex N => SourceFamily.sourceMoment A r i.val) ∘
        liftIndexEquiv N =
      (fun p : State 2 × SourceFamily.SourceIndex N =>
        MomentLifts.firstStateLift p.1 (SourceFamily.sourceMoment (shift A) p.1 p.2)) := by
    funext p
    exact sourceMoment_liftIndex hA r p.1 p.2
  rw [hfamily]
  exact MomentLifts.linearIndependent_firstStateLift
    (fun a i => SourceFamily.sourceMoment (shift A) a i) hshort

end

end PanelMoments.SourceLifts
