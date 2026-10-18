import PanelMoments.PermutationMoments
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false

/-!
# The canonical three-choice family in equation (24)

The horizon is `N + 1`, and the possible shared slots lie in `Fin N`.
`SharedSet` includes exactly the restriction in footnote 8 for three choices:
a shared set of size `j` must contain the first `j - 1` slots. Its complement
has at least two elements. The first divergent slot is the minimum complement
element, and the second is any other complement element.

The generation orders below implement footnote 7 literally: the shared slots
in increasing order, the first divergent slot, the remaining slots in increasing
order, the second divergent slot, and the final observation. Swapping the two
divergent slots gives the second order. Validity is proved for every positive
table and every initial state. Independence and the closed cardinality formula
are not asserted in this module.
-/

namespace PanelMoments.SourceFamily

open scoped BigOperators

noncomputable section

/-- Admissible shared sets for three alternatives. The first condition is
`j ≤ T - 3`, written without truncated subtraction. -/
abbrev SharedSet (N : ℕ) :=
  {S : Finset (Fin N) // S.card + 2 ≤ N ∧
    ∀ i : Fin N, i.val < S.card - 1 → i ∈ S}

theorem shared_card_le {N : ℕ} (S : SharedSet N) : S.val.card ≤ N := by
  have h := S.property.1
  omega

theorem complement_nonempty {N : ℕ} (S : SharedSet N) :
    (Finset.univ \ S.val).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S.val), Finset.card_univ,
    Fintype.card_fin]
  have h := S.property.1
  omega

/-- The slot `s₁` in equation (24), in zero-based coordinates. -/
def firstSlot {N : ℕ} (S : SharedSet N) : Fin N :=
  (Finset.univ \ S.val).min' (complement_nonempty S)

theorem firstSlot_not_mem {N : ℕ} (S : SharedSet N) : firstSlot S ∉ S.val := by
  have h := Finset.min'_mem (Finset.univ \ S.val) (complement_nonempty S)
  exact (Finset.mem_sdiff.mp h).2

theorem firstSlot_le {N : ℕ} (S : SharedSet N) (i : Fin N) (hi : i ∉ S.val) :
    firstSlot S ≤ i :=
  Finset.min'_le _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)

abbrev SecondSlot {N : ℕ} (S : SharedSet N) :=
  {i : Fin N // i ∉ S.val ∧ i ≠ firstSlot S}

/-- Indices are `(shared set, second divergent slot, q₀, shared outcome values)`.
Shared values are indexed in increasing order of the shared slots. -/
abbrev SourceIndex (N : ℕ) :=
  Σ S : SharedSet N, SecondSlot S × State 2 × (Fin S.val.card → State 2)

/-- The increasingly ordered shared slots. -/
def sharedSlot {N : ℕ} (S : SharedSet N) : Fin S.val.card → Fin N :=
  S.val.orderEmbOfFin rfl

@[simp] theorem sharedSlot_mem {N : ℕ} (S : SharedSet N) (i : Fin S.val.card) :
    sharedSlot S i ∈ S.val := Finset.orderEmbOfFin_mem _ rfl _

theorem sharedSlot_strictMono {N : ℕ} (S : SharedSet N) :
    StrictMono (sharedSlot S) := (S.val.orderEmbOfFin rfl).strictMono

/-- Slots between the first and second divergent slots in footnote 7. -/
def remaining {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i ∉ S ∧ i ≠ a ∧ i ≠ b)

@[simp] theorem mem_remaining {N : ℕ} (S : Finset (Fin N)) (a b i : Fin N) :
    i ∈ remaining S a b ↔ i ∉ S ∧ i ≠ a ∧ i ≠ b := by
  simp [remaining]

theorem remaining_swap {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) :
    remaining S a b = remaining S b a := by
  ext i
  simp only [mem_remaining, and_assoc, and_comm]

/-- The nonfinal part of the exact generation order from footnote 7. -/
def coreList {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) : List (Fin N) :=
  (S.sort (· ≤ ·) ++ a :: (remaining S a b).sort (· ≤ ·)) ++ [b]

theorem coreList_nodup {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) : (coreList S a b).Nodup := by
  unfold coreList
  rw [List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.nodup_append]
    refine ⟨S.sort_nodup _, ?_, ?_⟩
    · rw [List.nodup_cons]
      constructor
      · simp
      · exact (remaining S a b).sort_nodup _
    · intro x hx y hy
      have hxS : x ∈ S := (Finset.mem_sort _).mp hx
      simp only [List.mem_cons, Finset.mem_sort, mem_remaining] at hy
      rcases hy with rfl | hy
      · exact fun h => ha (h ▸ hxS)
      · exact fun h => hy.1 (h ▸ hxS)
  · intro x hx y hy
    have hyb : y = b := by simpa using hy
    subst y
    simp only [List.mem_append, Finset.mem_sort, List.mem_cons, mem_remaining] at hx
    rcases hx with hx | rfl | hx
    · exact fun h => hb (h ▸ hx)
    · exact hab
    · exact hx.2.2

theorem mem_coreList {N : ℕ} (S : Finset (Fin N)) (a b x : Fin N) :
    x ∈ coreList S a b := by
  by_cases hxS : x ∈ S
  · simp [coreList, hxS]
  by_cases hxa : x = a
  · simp [coreList, hxa]
  by_cases hxb : x = b
  · simp [coreList, hxb]
  simp [coreList, hxS, hxa, hxb]

theorem coreList_length {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    (coreList S a b).length = N := by
  let e : Fin (coreList S a b).length ≃ Fin N :=
    (coreList_nodup S a b ha hb hab).getEquivOfForallMemList _ (mem_coreList S a b)
  simpa only [Fintype.card_fin] using Fintype.card_congr e

/-- The list construction is a permutation, proved from its explicit entries. -/
def coreOrder {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) : Equiv.Perm (Fin N) :=
  (finCongr (coreList_length S a b ha hb hab).symm).trans
    ((coreList_nodup S a b ha hb hab).getEquivOfForallMemList _ (mem_coreList S a b))

theorem coreOrder_apply {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) (i : Fin N) :
    coreOrder S a b ha hb hab i =
      (coreList S a b)[i.val]'(by rw [coreList_length S a b ha hb hab]; exact i.isLt) :=
  rfl

theorem coreOrder_shared {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) (i : Fin N) (hi : i.val < S.card) :
    coreOrder S a b ha hb hab i = S.orderEmbOfFin rfl ⟨i.val, hi⟩ := by
  rw [coreOrder_apply, Finset.orderEmbOfFin_apply]
  unfold coreList
  rw [List.getElem_append_left (by
    simp only [List.length_append, List.length_cons, Finset.length_sort]
    omega)]
  rw [List.getElem_append_left (by simpa only [Finset.length_sort] using hi)]
  rfl

theorem coreOrder_divergent {N : ℕ} (S : Finset (Fin N)) (a b : Fin N)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) (hS : S.card < N) :
    coreOrder S a b ha hb hab ⟨S.card, hS⟩ = a := by
  rw [coreOrder_apply]
  unfold coreList
  rw [List.getElem_append_left (by
    simp only [List.length_append, List.length_cons, Finset.length_sort]
    omega)]
  rw [List.getElem_append_right (by simp only [Finset.length_sort]; exact le_rfl)]
  simp

/-- Extend a permutation by fixing the final slot. -/
def appendLast {N : ℕ} (p : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N + 1)) where
  toFun := Fin.lastCases (Fin.last N) (fun i => (p i).castSucc)
  invFun := Fin.lastCases (Fin.last N) (fun i => (p.symm i).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem appendLast_last {N : ℕ} (p : Equiv.Perm (Fin N)) :
    appendLast p (Fin.last N) = Fin.last N := by simp [appendLast]

@[simp] theorem appendLast_castSucc {N : ℕ} (p : Equiv.Perm (Fin N)) (i : Fin N) :
    appendLast p i.castSucc = (p i).castSucc := by simp [appendLast]

/-- First exact generation order from footnote 7. -/
def firstOrder {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    Equiv.Perm (Fin (N + 1)) :=
  appendLast (coreOrder S.val (firstSlot S) s.val (firstSlot_not_mem S)
    s.property.1 (Ne.symm s.property.2))

/-- Second exact generation order, swapping the two divergent slots. -/
def secondOrder {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    Equiv.Perm (Fin (N + 1)) :=
  appendLast (coreOrder S.val s.val (firstSlot S) s.property.1
    (firstSlot_not_mem S) s.property.2)

@[simp] theorem firstOrder_last {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    firstOrder S s (Fin.last N) = Fin.last N := appendLast_last _

@[simp] theorem secondOrder_last {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    secondOrder S s (Fin.last N) = Fin.last N := appendLast_last _

theorem firstOrder_shared {N : ℕ} (S : SharedSet N) (s : SecondSlot S)
    (i : Fin (N + 1)) (hi : i.val < S.val.card) :
    firstOrder S s i = (sharedSlot S ⟨i.val, hi⟩).castSucc := by
  have hiN : i.val < N := Nat.lt_of_lt_of_le hi (shared_card_le S)
  have heq : (⟨i.val, hiN⟩ : Fin N).castSucc = i := Fin.ext rfl
  conv_lhs => rw [← heq]
  simp only [firstOrder, appendLast_castSucc, sharedSlot]
  exact congrArg Fin.castSucc (coreOrder_shared S.val (firstSlot S) s.val
    (firstSlot_not_mem S) s.property.1 (Ne.symm s.property.2) ⟨i.val, hiN⟩ hi)

theorem secondOrder_shared {N : ℕ} (S : SharedSet N) (s : SecondSlot S)
    (i : Fin (N + 1)) (hi : i.val < S.val.card) :
    secondOrder S s i = (sharedSlot S ⟨i.val, hi⟩).castSucc := by
  have hiN : i.val < N := Nat.lt_of_lt_of_le hi (shared_card_le S)
  have heq : (⟨i.val, hiN⟩ : Fin N).castSucc = i := Fin.ext rfl
  conv_lhs => rw [← heq]
  simp only [secondOrder, appendLast_castSucc, sharedSlot]
  exact congrArg Fin.castSucc (coreOrder_shared S.val s.val (firstSlot S)
    s.property.1 (firstSlot_not_mem S) s.property.2 ⟨i.val, hiN⟩ hi)

theorem firstOrder_divergent {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    firstOrder S s ⟨S.val.card, Nat.lt_succ_of_le (shared_card_le S)⟩ =
      (firstSlot S).castSucc := by
  have hS : S.val.card < N := by have h := S.property.1; omega
  change appendLast _ (⟨S.val.card, hS⟩ : Fin N).castSucc = _
  rw [appendLast_castSucc, coreOrder_divergent]

theorem secondOrder_divergent {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    secondOrder S s ⟨S.val.card, Nat.lt_succ_of_le (shared_card_le S)⟩ = s.val.castSucc := by
  have hS : S.val.card < N := by have h := S.property.1; omega
  change appendLast _ (⟨S.val.card, hS⟩ : Fin N).castSucc = _
  rw [appendLast_castSucc, coreOrder_divergent]

theorem orders_sharedPrefix {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    PermutationMoments.SharedPrefix S.val.card (firstOrder S s) (secondOrder S s) := by
  intro i hi
  rw [firstOrder_shared S s i hi, secondOrder_shared S s i hi]

theorem orders_diverge {N : ℕ} (S : SharedSet N) (s : SecondSlot S) :
    firstOrder S s ⟨S.val.card, Nat.lt_succ_of_le (shared_card_le S)⟩ ≠
      secondOrder S s ⟨S.val.card, Nat.lt_succ_of_le (shared_card_le S)⟩ := by
  rw [firstOrder_divergent, secondOrder_divergent]
  exact fun h => s.property.2 (Fin.castSucc_inj.mp h).symm

/-- The ordinary scalar indicator, usable over any coefficient ring. -/
def indicator {R : Type*} [Zero R] [One R] (a b : State 2) : R :=
  if a = b then 1 else 0

/-- The product of the shared-outcome indicators in equation (24). -/
def sharedWeight {R : Type*} [CommRing R] {N : ℕ} (i : SourceIndex N)
    (y : Path 2 (N + 1)) : R :=
  ∏ j : Fin i.1.val.card, indicator (y (sharedSlot i.1 j).castSucc) (i.2.2.2 j)

/-- The exact polynomial numerator of the canonical equation-(24) moment. -/
def sourceNumerator {R : Type*} [CommRing R] {N : ℕ}
    (A : ℕ → State 2 → State 2 → R) (r : State 2) (i : SourceIndex N)
    (y : Path 2 (N + 1)) : R :=
  sharedWeight i y *
    (indicator (y (firstSlot i.1).castSucc) i.2.2.1 *
        PermutationMoments.transformedScale A r (firstOrder i.1 i.2.1) y -
      indicator (y i.2.1.val.castSucc) i.2.2.1 *
        PermutationMoments.transformedScale A r (secondOrder i.1 i.2.1) y)

/-- Equation (24), with the common positive path scale divided out. -/
def sourceMoment {N : ℕ} (A : Table 2) (r : State 2) (i : SourceIndex N)
    (y : Path 2 (N + 1)) : ℝ :=
  sourceNumerator A r i y / PermutationMoments.originalScale A r y

theorem prefixIndicator_eq_product {R : Type*} [CommRing R] {k : ℕ}
    (q z : Path 2 (k + 1)) :
    (PermutationMoments.prefixIndicator q z : R) =
      ∏ j : Fin (k + 1), indicator (z j) (q j) := by
  simp only [PermutationMoments.prefixIndicator, indicator, Fintype.prod_ite_zero,
    Finset.prod_const_one]
  simp only [funext_iff]

theorem first_prefixIndicator {R : Type*} [CommRing R] {N : ℕ}
    (i : SourceIndex N) (y : Path 2 (N + 1)) :
    (PermutationMoments.prefixIndicator (Fin.snoc i.2.2.2 i.2.2.1)
        (PermutationMoments.pathPrefix (Nat.succ_le_succ (shared_card_le i.1))
          (fun j => y (firstOrder i.1 i.2.1 j))) : R) =
      sharedWeight i y * indicator (y (firstSlot i.1).castSucc) i.2.2.1 := by
  rw [prefixIndicator_eq_product, Fin.prod_univ_castSucc]
  simp only [PermutationMoments.pathPrefix, Fin.snoc_castSucc, Fin.snoc_last]
  have hshared (j : Fin i.1.val.card) :
      firstOrder i.1 i.2.1
          (Fin.castLE (Nat.succ_le_succ (shared_card_le i.1)) j.castSucc) =
        (sharedSlot i.1 j).castSucc := firstOrder_shared _ _ _ j.isLt
  simp only [hshared]
  have hdivergent :
      firstOrder i.1 i.2.1
          (Fin.castLE (Nat.succ_le_succ (shared_card_le i.1)) (Fin.last i.1.val.card)) =
        (firstSlot i.1).castSucc := firstOrder_divergent _ _
  rw [hdivergent]
  rfl

theorem second_prefixIndicator {R : Type*} [CommRing R] {N : ℕ}
    (i : SourceIndex N) (y : Path 2 (N + 1)) :
    (PermutationMoments.prefixIndicator (Fin.snoc i.2.2.2 i.2.2.1)
        (PermutationMoments.pathPrefix (Nat.succ_le_succ (shared_card_le i.1))
          (fun j => y (secondOrder i.1 i.2.1 j))) : R) =
      sharedWeight i y * indicator (y i.2.1.val.castSucc) i.2.2.1 := by
  rw [prefixIndicator_eq_product, Fin.prod_univ_castSucc]
  simp only [PermutationMoments.pathPrefix, Fin.snoc_castSucc, Fin.snoc_last]
  have hshared (j : Fin i.1.val.card) :
      secondOrder i.1 i.2.1
          (Fin.castLE (Nat.succ_le_succ (shared_card_le i.1)) j.castSucc) =
        (sharedSlot i.1 j).castSucc := secondOrder_shared _ _ _ j.isLt
  simp only [hshared]
  have hdivergent :
      secondOrder i.1 i.2.1
          (Fin.castLE (Nat.succ_le_succ (shared_card_le i.1)) (Fin.last i.1.val.card)) =
        i.2.1.val.castSucc := secondOrder_divergent _ _
  rw [hdivergent]
  rfl

theorem sourceNumerator_eq_permutationNumerator {R : Type*} [CommRing R] {N : ℕ}
    (A : ℕ → State 2 → State 2 → R) (r : State 2) (i : SourceIndex N)
    (y : Path 2 (N + 1)) :
    sourceNumerator A r i y =
      PermutationMoments.sourceNumerator A r (shared_card_le i.1)
        (firstOrder i.1 i.2.1) (secondOrder i.1 i.2.1)
        (Fin.snoc i.2.2.2 i.2.2.1) y := by
  simp only [sourceNumerator, PermutationMoments.sourceNumerator,
    PermutationMoments.contrastNumerator, first_prefixIndicator, second_prefixIndicator]
  ring

theorem sourceMoment_eq_permutationMoment {N : ℕ} (A : Table 2) (r : State 2)
    (i : SourceIndex N) :
    sourceMoment A r i =
      PermutationMoments.sourceMoment A r (shared_card_le i.1)
        (firstOrder i.1 i.2.1) (secondOrder i.1 i.2.1)
        (Fin.snoc i.2.2.2 i.2.2.1) := by
  funext y
  rw [sourceMoment, sourceNumerator_eq_permutationNumerator,
    PermutationMoments.sourceMoment_eq_numerator_div]

@[simp] theorem map_sourceNumerator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {N : ℕ} (A : ℕ → State 2 → State 2 → R)
    (r : State 2) (i : SourceIndex N) (y : Path 2 (N + 1)) :
    f (sourceNumerator A r i y) =
      sourceNumerator (fun t a b => f (A t a b)) r i y := by
  rw [sourceNumerator_eq_permutationNumerator, PermutationMoments.map_sourceNumerator,
    sourceNumerator_eq_permutationNumerator]

/-- Every member of the exact canonical family is a fixed-effect-free moment,
for every positive transition table and every initial outcome. -/
theorem sourceMoment_isMoment {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (i : SourceIndex N) :
    IsMoment A (N + 1) r (sourceMoment A r i) := by
  rw [sourceMoment_eq_permutationMoment]
  exact PermutationMoments.sourceMoment_isMoment hA r (shared_card_le i.1)
    (firstOrder i.1 i.2.1) (secondOrder i.1 i.2.1)
    (firstOrder_last _ _) (secondOrder_last _ _) (orders_sharedPrefix _ _)
    (Fin.snoc i.2.2.2 i.2.2.1)

end

end PanelMoments.SourceFamily
