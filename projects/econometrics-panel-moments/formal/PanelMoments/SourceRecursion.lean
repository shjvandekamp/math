import PanelMoments.SourceCounting

set_option autoImplicit false

/-!
# The initial-slot recursion of the canonical source indices

Adding a shared initial slot gives an explicit equivalence between a state
together with a horizon-`N + 1` source index and a horizon-`N + 2` source index
whose shared set contains zero. The remaining slots are shifted by `Fin.succ`,
the first and second divergent slots shift with them, and the added state is
the first ordered shared label. This module concerns the indices themselves;
it does not assert independence or equality of the associated moments.
-/

namespace PanelMoments.SourceRecursion

open SourceFamily

noncomputable section

/-- Insert the initial slot and shift every old slot forward by one. -/
def liftRaw {N : ℕ} (S : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  insert 0 (S.map (Fin.succEmb N))

/-- Remove the initial slot and shift every other slot back by one. -/
def dropRaw {N : ℕ} (U : Finset (Fin (N + 1))) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.succ ∈ U)

@[simp] theorem zero_mem_liftRaw {N : ℕ} (S : Finset (Fin N)) :
    (0 : Fin (N + 1)) ∈ liftRaw S := by
  simp [liftRaw]

@[simp] theorem succ_mem_liftRaw {N : ℕ} (S : Finset (Fin N)) (i : Fin N) :
    i.succ ∈ liftRaw S ↔ i ∈ S := by
  simp [liftRaw]

@[simp] theorem mem_dropRaw {N : ℕ} (U : Finset (Fin (N + 1))) (i : Fin N) :
    i ∈ dropRaw U ↔ i.succ ∈ U := by
  simp [dropRaw]

@[simp] theorem card_liftRaw {N : ℕ} (S : Finset (Fin N)) :
    (liftRaw S).card = S.card + 1 := by
  simp [liftRaw]

@[simp] theorem dropRaw_liftRaw {N : ℕ} (S : Finset (Fin N)) :
    dropRaw (liftRaw S) = S := by
  ext i
  simp

theorem liftRaw_dropRaw {N : ℕ} (U : Finset (Fin (N + 1)))
    (hzero : (0 : Fin (N + 1)) ∈ U) : liftRaw (dropRaw U) = U := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hzero]
  · simp

theorem card_dropRaw_add_one {N : ℕ} (U : Finset (Fin (N + 1)))
    (hzero : (0 : Fin (N + 1)) ∈ U) : (dropRaw U).card + 1 = U.card := by
  simpa only [card_liftRaw] using congrArg Finset.card (liftRaw_dropRaw U hzero)

/-- The footnote-8 restriction is preserved by adding the first shared slot. -/
def liftShared {N : ℕ} (S : SharedSet N) : SharedSet (N + 1) :=
  ⟨liftRaw S.val, by
    constructor
    · rw [card_liftRaw]
      have h := S.property.1
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro _
        exact zero_mem_liftRaw S.val
      · intro hj
        apply (succ_mem_liftRaw S.val j).mpr
        apply S.property.2 j
        rw [card_liftRaw] at hj
        simp only [Fin.val_succ] at hj
        omega⟩

@[simp] theorem liftShared_val {N : ℕ} (S : SharedSet N) :
    (liftShared S).val = liftRaw S.val := rfl

@[simp] theorem zero_mem_liftShared {N : ℕ} (S : SharedSet N) :
    (0 : Fin (N + 1)) ∈ (liftShared S).val := zero_mem_liftRaw S.val

@[simp] theorem succ_mem_liftShared {N : ℕ} (S : SharedSet N) (i : Fin N) :
    i.succ ∈ (liftShared S).val ↔ i ∈ S.val := succ_mem_liftRaw S.val i

@[simp] theorem card_liftShared {N : ℕ} (S : SharedSet N) :
    (liftShared S).val.card = S.val.card + 1 := card_liftRaw S.val

/-- Removing a shared initial slot preserves the exact admissibility condition. -/
def dropShared {N : ℕ} (U : SharedSet (N + 1))
    (hzero : (0 : Fin (N + 1)) ∈ U.val) : SharedSet N :=
  ⟨dropRaw U.val, by
    have hcard := card_dropRaw_add_one U.val hzero
    constructor
    · have h := U.property.1
      omega
    · intro i hi
      apply (mem_dropRaw U.val i).mpr
      apply U.property.2 i.succ
      simp only [Fin.val_succ]
      omega⟩

@[simp] theorem dropShared_liftShared {N : ℕ} (S : SharedSet N) :
    dropShared (liftShared S) (zero_mem_liftShared S) = S := by
  apply Subtype.ext
  exact dropRaw_liftRaw S.val

theorem liftShared_dropShared {N : ℕ} (U : SharedSet (N + 1))
    (hzero : (0 : Fin (N + 1)) ∈ U.val) : liftShared (dropShared U hzero) = U := by
  apply Subtype.ext
  exact liftRaw_dropRaw U.val hzero

abbrev SharedZero (N : ℕ) :=
  {U : SharedSet (N + 1) // (0 : Fin (N + 1)) ∈ U.val}

/-- The shared-set part of the recursion, with an explicit delete-zero inverse. -/
def sharedLiftEquiv (N : ℕ) : SharedSet N ≃ SharedZero N where
  toFun S := ⟨liftShared S, zero_mem_liftShared S⟩
  invFun U := dropShared U.val U.property
  left_inv S := dropShared_liftShared S
  right_inv U := Subtype.ext (liftShared_dropShared U.val U.property)

/-- The minimum nonshared slot shifts by one. -/
theorem firstSlot_lift {N : ℕ} (S : SharedSet N) :
    firstSlot (liftShared S) = (firstSlot S).succ := by
  apply le_antisymm
  · apply firstSlot_le
    simpa only [succ_mem_liftShared] using firstSlot_not_mem S
  · have hmin : ∀ i : Fin (N + 1), i ∉ (liftShared S).val →
        (firstSlot S).succ ≤ i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        exact (hi (zero_mem_liftShared S)).elim
      · intro hj
        apply Fin.succ_le_succ_iff.mpr
        exact firstSlot_le S j (by simpa only [succ_mem_liftShared] using hj)
    exact hmin _ (firstSlot_not_mem (liftShared S))

/-- Transport the second divergent slot by the same shift. -/
def liftSecond {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    SecondSlot (liftShared S) :=
  ⟨s.val.succ, by
    constructor
    · simpa only [succ_mem_liftShared] using s.property.1
    · rw [firstSlot_lift]
      intro h
      exact s.property.2 (Fin.succ_inj.mp h)⟩

@[simp] theorem liftSecond_val {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    (liftSecond S s).val = s.val.succ := rfl

theorem liftSecond_injective {N : ℕ} (S : SharedSet N) :
    Function.Injective (liftSecond S) := by
  intro s t h
  apply Subtype.ext
  exact Fin.succ_inj.mp (congrArg Subtype.val h)

theorem liftSecond_surjective {N : ℕ} (S : SharedSet N) :
    Function.Surjective (liftSecond S) := by
  intro s
  have hne : s.val ≠ 0 := by
    intro h
    exact s.property.1 (h ▸ zero_mem_liftShared S)
  obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero hne
  have hin : i ∉ S.val := by
    have h := s.property.1
    rw [hi] at h
    simpa only [succ_mem_liftShared] using h
  have hine : i ≠ firstSlot S := by
    intro h
    apply s.property.2
    rw [hi, h, firstSlot_lift]
  refine ⟨⟨i, hin, hine⟩, ?_⟩
  apply Subtype.ext
  exact hi.symm

def secondSlotLiftEquiv {N : ℕ} (S : SharedSet N) :
    SecondSlot S ≃ SecondSlot (liftShared S) :=
  Equiv.ofBijective (liftSecond S) ⟨liftSecond_injective S, liftSecond_surjective S⟩

@[simp] theorem secondSlotLiftEquiv_apply {N : ℕ} (S : SharedSet N)
    (s : SecondSlot S) : secondSlotLiftEquiv S s = liftSecond S s := rfl

/-- Sorting commutes with the shift, with zero as the new first element. -/
theorem sort_liftRaw {N : ℕ} (S : Finset (Fin N)) :
    (liftRaw S).sort (· ≤ ·) = 0 :: (S.sort (· ≤ ·)).map Fin.succ := by
  unfold liftRaw
  rw [Finset.sort_insert (· ≤ ·) (fun _ _ => Fin.zero_le _) (by simp)]
  congr 1
  exact (Finset.map_sort (Fin.succEmb N) S (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => Fin.succ_le_succ_iff.symm)).symm

theorem sharedSlot_lift_zero {N : ℕ} (S : SharedSet N) :
    sharedSlot (liftShared S)
      (Fin.cast (card_liftShared S).symm (0 : Fin (S.val.card + 1))) = 0 := by
  unfold sharedSlot
  rw [Finset.orderEmbOfFin_apply]
  simp only [liftShared_val, sort_liftRaw, Fin.getElem_fin]
  rfl

theorem sharedSlot_lift_succ {N : ℕ} (S : SharedSet N) (i : Fin S.val.card) :
    sharedSlot (liftShared S) (Fin.cast (card_liftShared S).symm i.succ) =
      (sharedSlot S i).succ := by
  unfold sharedSlot
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [liftShared_val, sort_liftRaw, Fin.getElem_fin]
  change ((S.val.sort (· ≤ ·)).map Fin.succ)[i.val]'(by
    rw [List.length_map, Finset.length_sort]
    exact i.isLt) =
    ((S.val.sort (· ≤ ·))[i.val]'(by
      rw [Finset.length_sort]
      exact i.isLt)).succ
  rw [List.getElem_map]

/-- Prepend the newly shared outcome, with the exact cardinality transport. -/
def liftLabels {N : ℕ} (S : SharedSet N) (a : State 2)
    (q : Fin S.val.card → State 2) : Fin (liftShared S).val.card → State 2 :=
  fun i => (Fin.cons a q : Fin (S.val.card + 1) → State 2)
    (Fin.cast (card_liftShared S) i)

def labelLiftEquiv {N : ℕ} (S : SharedSet N) :
    (State 2 × (Fin S.val.card → State 2)) ≃
      (Fin (liftShared S).val.card → State 2) :=
  (Fin.consEquiv (fun _ : Fin (S.val.card + 1) => State 2)).trans
    (Equiv.arrowCongr (finCongr (card_liftShared S).symm) (Equiv.refl (State 2)))

@[simp] theorem labelLiftEquiv_apply {N : ℕ} (S : SharedSet N)
    (a : State 2) (q : Fin S.val.card → State 2) :
    labelLiftEquiv S (a, q) = liftLabels S a q := rfl

@[simp] theorem liftLabels_zero {N : ℕ} (S : SharedSet N) (a : State 2)
    (q : Fin S.val.card → State 2) :
    liftLabels S a q (Fin.cast (card_liftShared S).symm (0 : Fin (S.val.card + 1))) = a := by
  change (Fin.cons a q : Fin (S.val.card + 1) → State 2) 0 = a
  rfl

@[simp] theorem liftLabels_succ {N : ℕ} (S : SharedSet N) (a : State 2)
    (q : Fin S.val.card → State 2) (i : Fin S.val.card) :
    liftLabels S a q (Fin.cast (card_liftShared S).symm i.succ) = q i := by
  change (Fin.cons a q : Fin (S.val.card + 1) → State 2) i.succ = q i
  exact Fin.cons_succ _ _ _

abbrev Payload {N : ℕ} (S : SharedSet N) :=
  SecondSlot S × State 2 × (Fin S.val.card → State 2)

abbrev ZeroIndex (N : ℕ) :=
  {i : SourceFamily.SourceIndex (N + 1) // (0 : Fin (N + 1)) ∈ i.1.val}

def indexSharedZeroEquiv (N : ℕ) :
    ZeroIndex N ≃ (Σ U : SharedZero N, Payload U.val) where
  toFun i := ⟨⟨i.val.1, i.property⟩, i.val.2⟩
  invFun i := ⟨⟨i.1.val, i.2⟩, i.1.property⟩
  left_inv i := by cases i; rfl
  right_inv i := by rcases i with ⟨⟨U, hU⟩, p⟩; rfl

def payloadReorder {N : ℕ} (S : SharedSet N) :
    State 2 × Payload S ≃
      SecondSlot S × State 2 × (State 2 × (Fin S.val.card → State 2)) where
  toFun p := (p.2.1, p.2.2.1, p.1, p.2.2.2)
  invFun p := (p.2.2.1, p.1, p.2.1, p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def payloadLiftEquiv {N : ℕ} (S : SharedSet N) :
    State 2 × Payload S ≃ Payload (liftShared S) :=
  (payloadReorder S).trans
    (Equiv.prodCongr (secondSlotLiftEquiv S)
      (Equiv.prodCongr (Equiv.refl (State 2)) (labelLiftEquiv S)))

def stateSigmaEquiv (N : ℕ) :
    State 2 × SourceFamily.SourceIndex N ≃ (Σ S : SharedSet N, State 2 × Payload S) where
  toFun p := ⟨p.2.1, p.1, p.2.2⟩
  invFun p := (p.2.1, ⟨p.1, p.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact initial-slot index recursion, in the constructive lifting direction. -/
def liftIndexEquiv (N : ℕ) : State 2 × SourceFamily.SourceIndex N ≃ ZeroIndex N :=
  (stateSigmaEquiv N).trans
    ((Equiv.sigmaCongr (sharedLiftEquiv N) (fun S => payloadLiftEquiv S)).trans
      (indexSharedZeroEquiv N).symm)

/-- Every canonical index sharing slot zero has one unique conditioning outcome
and one unique lower-horizon canonical index. This holds also for the empty
small-horizon index types. -/
def indexRecursionEquiv (N : ℕ) : ZeroIndex N ≃ State 2 × SourceFamily.SourceIndex N :=
  (liftIndexEquiv N).symm

/-- The index map, without the redundant proof that its shared set contains zero. -/
def liftIndex {N : ℕ} (a : State 2) (i : SourceFamily.SourceIndex N) :
    SourceFamily.SourceIndex (N + 1) :=
  (liftIndexEquiv N (a, i)).val

theorem liftIndex_apply {N : ℕ} (a : State 2) (S : SharedSet N)
    (s : SecondSlot S) (q₀ : State 2) (q : Fin S.val.card → State 2) :
    liftIndex a ⟨S, s, q₀, q⟩ =
      ⟨liftShared S, liftSecond S s, q₀, liftLabels S a q⟩ := rfl

theorem zero_mem_liftIndex {N : ℕ} (a : State 2) (i : SourceFamily.SourceIndex N) :
    (0 : Fin (N + 1)) ∈ (liftIndex a i).1.val :=
  (liftIndexEquiv N (a, i)).property

theorem liftIndex_injective (N : ℕ) :
    Function.Injective (fun p : State 2 × SourceFamily.SourceIndex N =>
      liftIndex p.1 p.2) := by
  intro p q h
  apply (liftIndexEquiv N).injective
  exact Subtype.ext h

theorem exists_unique_liftIndex {N : ℕ} (i : SourceFamily.SourceIndex (N + 1))
    (hzero : (0 : Fin (N + 1)) ∈ i.1.val) :
    ∃! p : State 2 × SourceFamily.SourceIndex N, liftIndex p.1 p.2 = i := by
  obtain ⟨p, hp⟩ := (liftIndexEquiv N).surjective ⟨i, hzero⟩
  refine ⟨p, congrArg Subtype.val hp, ?_⟩
  intro q hq
  apply liftIndex_injective N
  exact hq.trans (congrArg Subtype.val hp).symm

theorem card_zeroIndex (N : ℕ) :
    Fintype.card (ZeroIndex N) = 3 * Fintype.card (SourceFamily.SourceIndex N) := by
  rw [Fintype.card_congr (indexRecursionEquiv N), Fintype.card_prod]
  simp [State]

end

end PanelMoments.SourceRecursion
