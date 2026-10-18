import PanelMoments.SourceFamily
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Exact counting of the canonical three-choice source family

Every nonempty admissible shared set of size `j` consists of the first `j - 1`
slots and one extra slot. This classification counts the actual `SourceFamily.SourceIndex`
from `SourceFamily`; it does not substitute an independently chosen family.
-/

namespace PanelMoments.SourceCounting

open scoped BigOperators
open SourceFamily

noncomputable section

def initialSegment (N j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val < j)

@[simp] theorem mem_initialSegment {N j : ℕ} (i : Fin N) :
    i ∈ initialSegment N j ↔ i.val < j := by simp [initialSegment]

theorem card_initialSegment {N j : ℕ} (hj : j ≤ N) :
    (initialSegment N j).card = j := by
  rw [initialSegment, Fin.card_filter_val_lt, Nat.min_eq_right hj]

theorem initialSegment_subset {N : ℕ} (S : SharedSet N) :
    initialSegment N (S.val.card - 1) ⊆ S.val := by
  intro i hi
  exact S.property.2 i ((mem_initialSegment i).mp hi)

/-- Exact form of the footnote-8 restriction: a nonempty shared set has only
one slot outside its forced initial segment. -/
theorem sharedSet_decomposition {N : ℕ} (S : SharedSet N) (hS : 0 < S.val.card) :
    ∃ k : Fin N, S.val.card - 1 ≤ k.val ∧
      S.val = insert k (initialSegment N (S.val.card - 1)) := by
  have hcard : (S.val \ initialSegment N (S.val.card - 1)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (initialSegment_subset S),
      card_initialSegment (by have h := shared_card_le S; omega)]
    omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hmem : k ∈ S.val \ initialSegment N (S.val.card - 1) := by rw [hk]; simp
  have hkge : S.val.card - 1 ≤ k.val := by
    have hn := (Finset.mem_sdiff.mp hmem).2
    simpa only [mem_initialSegment, not_lt] using hn
  refine ⟨k, hkge, ?_⟩
  calc
    S.val = initialSegment N (S.val.card - 1) ∪
        (S.val \ initialSegment N (S.val.card - 1)) :=
      (Finset.union_sdiff_of_subset (initialSegment_subset S)).symm
    _ = insert k (initialSegment N (S.val.card - 1)) := by rw [hk]; ext i; simp

/-- Omitting the initial slot leaves only the empty and singleton levels. -/
theorem card_le_one_of_no_initial {N : ℕ} (S : SharedSet N)
    (hzero : ∀ i : Fin N, i.val = 0 → i ∉ S.val) : S.val.card ≤ 1 := by
  by_contra h
  have hcard : 2 ≤ S.val.card := by omega
  have hN : 0 < N := by have h := S.property.1; omega
  have hm := S.property.2 ⟨0, hN⟩ (by simp; omega)
  exact hzero ⟨0, hN⟩ rfl hm

abbrev SizedShared (N j : ℕ) := {S : SharedSet N // S.val.card = j}
abbrev ExtraSlot (N j : ℕ) := {k : Fin N // j - 1 ≤ k.val}

def sharedOfExtra {N j : ℕ} (hj : 1 ≤ j) (hjN : j + 2 ≤ N)
    (k : ExtraSlot N j) : SizedShared N j := by
  have hk : k.val ∉ initialSegment N (j - 1) := by
    simpa only [mem_initialSegment, not_lt] using k.property
  have hcard : (insert k.val (initialSegment N (j - 1))).card = j := by
    rw [Finset.card_insert_of_notMem hk, card_initialSegment (by omega)]
    omega
  refine ⟨⟨insert k.val (initialSegment N (j - 1)), ?_⟩, hcard⟩
  constructor
  · simpa only [hcard] using hjN
  · intro i hi
    apply Finset.mem_insert_of_mem
    rw [mem_initialSegment]
    simpa only [hcard] using hi

theorem sharedOfExtra_injective {N j : ℕ} (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    Function.Injective (sharedOfExtra hj hjN) := by
  intro a b h
  have hset : insert a.val (initialSegment N (j - 1)) =
      insert b.val (initialSegment N (j - 1)) :=
    congrArg (fun S : SizedShared N j => S.val.val) h
  apply Subtype.ext
  have hamem : a.val ∈ insert b.val (initialSegment N (j - 1)) := by
    rw [← hset]
    simp
  rcases Finset.mem_insert.mp hamem with hab | ha
  · exact hab
  · have halt := (mem_initialSegment a.val).mp ha
    have hage := a.property
    omega

theorem sharedOfExtra_surjective {N j : ℕ} (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    Function.Surjective (sharedOfExtra hj hjN) := by
  intro S
  have hpos : 0 < S.val.val.card := by rw [S.property]; omega
  obtain ⟨k, hk, hset⟩ := sharedSet_decomposition S.val hpos
  refine ⟨⟨k, by simpa only [S.property] using hk⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change insert k (initialSegment N (j - 1)) = S.val.val
  simpa only [S.property] using hset.symm

def sizedSharedEquivExtra {N j : ℕ} (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    SizedShared N j ≃ ExtraSlot N j :=
  (Equiv.ofBijective (sharedOfExtra hj hjN)
    ⟨sharedOfExtra_injective hj hjN, sharedOfExtra_surjective hj hjN⟩).symm

theorem card_extraSlot {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    Fintype.card (ExtraSlot N j) = N - j + 1 := by
  have hneg : Fintype.card (ExtraSlot N j) =
      Fintype.card {k : Fin N // ¬ k.val < j - 1} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => not_lt.symm)
  rw [hneg, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right (by omega)]
  omega

theorem card_sizedShared_pos {N j : ℕ} (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    Fintype.card (SizedShared N j) = N - j + 1 := by
  rw [Fintype.card_congr (sizedSharedEquivExtra hj hjN)]
  exact card_extraSlot hj (by omega)

def emptyShared {N : ℕ} (hN : 2 ≤ N) : SharedSet N :=
  ⟨∅, by simpa using hN, by simp⟩

def sizedZeroEquivUnit {N : ℕ} (hN : 2 ≤ N) : SizedShared N 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨emptyShared hN, rfl⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Finset.card_eq_zero.mp S.property).symm
  right_inv u := by cases u; rfl

theorem card_sizedShared_zero {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (SizedShared N 0) = 1 := by
  simpa using Fintype.card_congr (sizedZeroEquivUnit hN)

/-- Every shared set leaves exactly this many choices of `s₂`. -/
theorem card_secondSlot {N : ℕ} (S : SharedSet N) :
    Fintype.card (SecondSlot S) = N - S.val.card - 1 := by
  rw [Fintype.card_subtype]
  have hfilter : Finset.univ.filter (fun i : Fin N => i ∉ S.val ∧ i ≠ firstSlot S) =
      (Finset.univ \ S.val).erase (firstSlot S) := by
    ext i
    simp [and_comm]
  rw [hfilter, Finset.card_erase_of_mem (by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, firstSlot_not_mem S⟩)]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S.val), Finset.card_univ,
    Fintype.card_fin]

/-- The actual family cardinality, initially grouped by its shared set. -/
theorem card_sourceIndex_by_sharedSet (N : ℕ) :
    Fintype.card (SourceFamily.SourceIndex N) =
      ∑ S : SharedSet N, (N - S.val.card - 1) * 3 ^ (S.val.card + 1) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  simp [Fintype.card_prod, card_secondSlot, State, pow_succ, Nat.mul_comm]

def sizeIndex {N : ℕ} (S : SharedSet N) : Fin (N - 1) :=
  ⟨S.val.card, by have h := S.property.1; omega⟩

def allSizedSharedEquiv (N : ℕ) :
    (Σ j : Fin (N - 1), SizedShared N j.val) ≃ SharedSet N :=
  (Equiv.sigmaCongrRight (fun j =>
    (Equiv.subtypeEquivRight (fun S : SharedSet N =>
      show S.val.card = j.val ↔ sizeIndex S = j by
        rw [Fin.ext_iff]; rfl)))).trans (Equiv.sigmaFiberEquiv sizeIndex)

@[simp] theorem allSizedSharedEquiv_apply {N : ℕ}
    (j : Fin (N - 1)) (S : SizedShared N j.val) :
    allSizedSharedEquiv N ⟨j, S⟩ = S.val := rfl

theorem sum_by_size (N : ℕ) (f : ℕ → ℕ) :
    (∑ S : SharedSet N, f S.val.card) =
      ∑ j : Fin (N - 1), Fintype.card (SizedShared N j.val) * f j.val := by
  rw [← Equiv.sum_comp (allSizedSharedEquiv N), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [allSizedSharedEquiv_apply]
  calc
    (∑ S : SizedShared N j.val, f S.val.val.card) =
        ∑ _S : SizedShared N j.val, f j.val := by
      apply Finset.sum_congr rfl
      intro S _
      rw [S.property]
    _ = _ := by simp

/-- Exact finite-sum cardinality of the canonical index family. Here `m + 3`
is the observation horizon, so the formula includes the three-period base. -/
theorem card_sourceIndex_sum (m : ℕ) :
    Fintype.card (SourceFamily.SourceIndex (m + 2)) = 3 * (m + 1) +
      ∑ j : Fin m, (m + 2 - j.val) * (m - j.val) * 3 ^ (j.val + 2) := by
  rw [card_sourceIndex_by_sharedSet,
    sum_by_size (m + 2) (fun j => (m + 2 - j - 1) * 3 ^ (j + 1))]
  change (∑ j : Fin (m + 1), Fintype.card (SizedShared (m + 2) j.val) *
    ((m + 2 - j.val - 1) * 3 ^ (j.val + 1))) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  change Fintype.card (SizedShared (m + 2) 0) * ((m + 2 - 0 - 1) * 3 ^ (0 + 1)) +
    (∑ j : Fin m, Fintype.card (SizedShared (m + 2) (j.val + 1)) *
      ((m + 2 - (j.val + 1) - 1) * 3 ^ (j.val + 1 + 1))) = _
  rw [card_sizedShared_zero (N := m + 2) (by omega)]
  simp only [Nat.sub_zero, Nat.zero_add, pow_one, one_mul]
  rw [show m + 2 - 1 = m + 1 by omega, Nat.mul_comm (m + 1) 3]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [card_sizedShared_pos (N := m + 2) (j := j.val + 1)
    (by omega) (by have h := j.isLt; omega)]
  have h₁ : m + 2 - (j.val + 1) + 1 = m + 2 - j.val := by
    have h := j.isLt
    omega
  have h₂ : m + 2 - (j.val + 1) - 1 = m - j.val := by
    have h := j.isLt
    omega
  rw [h₁, h₂]
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_assoc]

/-- The cardinality recurrence for the actual source indices. In observation
horizons this is the old count multiplied by three, plus the new-index count. -/
theorem card_sourceIndex_recurrence (m : ℕ) :
    Fintype.card (SourceFamily.SourceIndex (m + 3)) =
      3 * Fintype.card (SourceFamily.SourceIndex (m + 2)) +
        3 * (m + 2) * (3 * m + 4) := by
  rw [card_sourceIndex_sum (m + 1), card_sourceIndex_sum m, Fin.sum_univ_succ]
  have htail :
      (∑ j : Fin m, (m + 1 + 2 - j.succ.val) * (m + 1 - j.succ.val) *
        3 ^ (j.succ.val + 2)) =
      3 * ∑ j : Fin m, (m + 2 - j.val) * (m - j.val) * 3 ^ (j.val + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h₁ : m + 1 + 2 - j.succ.val = m + 2 - j.val := by
      simp only [Fin.val_succ]
      omega
    have h₂ : m + 1 - j.succ.val = m - j.val := by
      simp only [Fin.val_succ]
      omega
    rw [h₁, h₂]
    simp only [Fin.val_succ]
    rw [show j.val + 1 + 2 = (j.val + 2) + 1 by omega, pow_succ]
    ring
  rw [htail]
  simp only [Fin.val_zero, Nat.sub_zero, Nat.zero_add, pow_two]
  ring

theorem twice_choose (m : ℕ) :
    2 * (3 * (m + 3)).choose 2 = (3 * (m + 3)) * (3 * m + 8) := by
  have h := Nat.add_one_mul_choose_eq (3 * m + 8) 1
  simp only [Nat.choose_one_right, Nat.reduceAdd] at h
  rw [show 3 * m + 8 + 1 = 3 * (m + 3) by ring] at h
  simpa only [Nat.mul_comm] using h.symm

/-- A subtraction-free exact count, in the same form as the structural
moment-space dimension theorem. -/
theorem card_sourceIndex_add_choose (m : ℕ) :
    Fintype.card (SourceFamily.SourceIndex (m + 2)) + (3 * (m + 3)).choose 2 =
      3 ^ (m + 3) + 6 * (m + 2) := by
  induction m with
  | zero =>
      rw [card_sourceIndex_sum 0]
      norm_num [Nat.choose]
  | succ m ih =>
      change Fintype.card (SourceFamily.SourceIndex (m + 3)) + (3 * (m + 4)).choose 2 =
        3 ^ (m + 4) + 6 * (m + 3)
      have hc₀ := twice_choose m
      have hc₁ := twice_choose (m + 1)
      have hpow : 3 ^ (m + 4) = 3 * 3 ^ (m + 3) := by
        rw [show m + 4 = (m + 3) + 1 by omega, pow_succ]
        ring
      rw [card_sourceIndex_recurrence, hpow]
      nlinarith

theorem card_sourceIndex_add_choose_of_ge_two {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (SourceFamily.SourceIndex N) + (3 * (N + 1)).choose 2 =
      3 ^ (N + 1) + 6 * N := by
  have h₂ : N - 2 + 2 = N := by omega
  have h₃ : N - 2 + 3 = N + 1 := by omega
  simpa only [h₂, h₃] using card_sourceIndex_add_choose (N - 2)

/-- The exact size claimed for the three-choice equation-(24) family. -/
theorem card_sourceIndex {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (SourceFamily.SourceIndex N) =
      (3 ^ (N + 1) + 6 * N) - (3 * (N + 1)).choose 2 := by
  have h := card_sourceIndex_add_choose_of_ge_two hN
  omega

theorem card_sourceIndex_succ {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (SourceFamily.SourceIndex (N + 1)) =
      3 * Fintype.card (SourceFamily.SourceIndex N) + 3 * N * (3 * N - 2) := by
  have h₂ : N - 2 + 2 = N := by omega
  have h₃ : N - 2 + 3 = N + 1 := by omega
  have hnew : 3 * (N - 2) + 4 = 3 * N - 2 := by omega
  simpa only [h₂, h₃, hnew] using card_sourceIndex_recurrence (N - 2)

theorem five_period_source_count : Fintype.card (SourceFamily.SourceIndex 4) = 162 := by
  rw [card_sourceIndex (by decide)]
  norm_num [Nat.choose]

theorem six_period_source_count : Fintype.card (SourceFamily.SourceIndex 5) = 606 := by
  rw [card_sourceIndex (by decide)]
  norm_num [Nat.choose]

end

end PanelMoments.SourceCounting
