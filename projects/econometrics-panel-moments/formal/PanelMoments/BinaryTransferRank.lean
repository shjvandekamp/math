import PanelMoments.BinaryTransferIndependence
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

/-!
# Rank parity for the actual auxiliary binary move-first words

Each word below is an actual reordering of a coefficient list: the chosen
position moves to the front, and all other positions keep their order. Its
two columns are the ordered `Q` and `R` transfer sums on that list.

The word-to-defect identities are proved before identifying their spans.
All spans and dimensions are over constant real scalars in the space of
functions on nonzero reals. This concerns the auxiliary binary construction,
not the source equation-(24) family.
-/

noncomputable section

namespace PanelMoments.BinaryTransferRank

open scoped BigOperators

abbrev FunctionSpace := BinaryTransferSpan.FunctionSpace
abbrev NonzeroReal := BinaryTransferSpan.NonzeroReal

/-- The actual word with the selected list position moved to the front. -/
def movedWord (cs : List ℝ) (i : Fin cs.length) : List ℝ :=
  cs[i.val] :: (cs.take i.val ++ cs.drop (i.val + 1))

def wordQ (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length) : FunctionSpace :=
  BinaryTransferSpan.baselineQ ρ (movedWord cs i)

def wordR (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length) : FunctionSpace :=
  BinaryTransferSpan.baselineR ρ (movedWord cs i)

def wordColumn (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length × Bool) : FunctionSpace :=
  if i.2 then wordQ ρ cs i.1 else wordR ρ cs i.1

def wordSpan (ρ : ℝ) (cs : List ℝ) : Submodule ℝ FunctionSpace :=
  Submodule.span ℝ (Set.range (wordColumn ρ cs))

def baselineColumn (ρ : ℝ) (cs : List ℝ) (b : Bool) : FunctionSpace :=
  if b then BinaryTransferSpan.baselineQ ρ cs else BinaryTransferSpan.baselineR ρ cs

def blockColumn (ρ c : ℝ) (b : Bool) : FunctionSpace :=
  if b then BinaryTransferSpan.blockQ ρ c else BinaryTransferSpan.blockR ρ c

theorem prefixH_moveFirst (ρ c z : ℝ) (cs : List ℝ) :
    BinaryTransferAlgebra.prefixH ρ (c :: cs) z =
      BinaryTransferAlgebra.prefixH ρ (cs ++ [c]) z := by
  simp only [BinaryTransferAlgebra.prefixH, BinaryTransferAlgebra.prefixH_append]
  ring

theorem wordQ_sub_baseline (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length)
    (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0) :
    wordQ ρ cs i - BinaryTransferSpan.baselineQ ρ cs =
      BinaryTransferSpan.prefixDefect ρ cs i := by
  have hsplit : (cs.take i.val ++ [cs[i.val]]) ++ cs.drop (i.val + 1) = cs := by
    rw [List.take_append_getElem i.isLt, List.take_append_drop]
  funext z
  change BinaryTransferAlgebra.prefixQ ρ
    ((cs[i.val] :: cs.take i.val) ++ cs.drop (i.val + 1)) z.val -
      BinaryTransferAlgebra.prefixQ ρ cs z.val = _
  have hbase := congrArg (fun ds => BinaryTransferAlgebra.prefixQ ρ ds z.val) hsplit.symm
  rw [hbase, BinaryTransferAlgebra.prefixQ_append, BinaryTransferAlgebra.prefixQ_append,
    prefixH_moveFirst]
  calc
    _ = BinaryTransferAlgebra.prefixQ ρ (cs[i.val] :: cs.take i.val) z.val -
        BinaryTransferAlgebra.prefixQ ρ (cs.take i.val ++ [cs[i.val]]) z.val := by ring
    _ = _ := BinaryTransferAlgebra.prefixQ_moveFirst ρ z.val cs[i.val] (cs.take i.val)
      hρ (hcs _ (List.getElem_mem i.isLt)) z.property
      (fun c hc => hcs c (List.mem_of_mem_take hc))

theorem wordR_sub_baseline (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length)
    (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0) :
    wordR ρ cs i - BinaryTransferSpan.baselineR ρ cs =
      -BinaryTransferSpan.mulZ (BinaryTransferSpan.prefixDefect ρ cs i) := by
  have hsplit : (cs.take i.val ++ [cs[i.val]]) ++ cs.drop (i.val + 1) = cs := by
    rw [List.take_append_getElem i.isLt, List.take_append_drop]
  funext z
  change BinaryTransferAlgebra.prefixR ρ
    ((cs[i.val] :: cs.take i.val) ++ cs.drop (i.val + 1)) z.val -
      BinaryTransferAlgebra.prefixR ρ cs z.val =
        -(z.val * BinaryTransferAlgebra.moveFirst ρ (cs.take i.val) cs[i.val] z.val)
  have hbase := congrArg (fun ds => BinaryTransferAlgebra.prefixR ρ ds z.val) hsplit.symm
  rw [hbase, BinaryTransferAlgebra.prefixR_append, BinaryTransferAlgebra.prefixR_append,
    prefixH_moveFirst]
  calc
    _ = BinaryTransferAlgebra.prefixR ρ (cs[i.val] :: cs.take i.val) z.val -
        BinaryTransferAlgebra.prefixR ρ (cs.take i.val ++ [cs[i.val]]) z.val := by ring
    _ = _ := by
      simpa only [neg_mul] using BinaryTransferAlgebra.prefixR_moveFirst
        ρ z.val cs[i.val] (cs.take i.val) hρ (hcs _ (List.getElem_mem i.isLt)) z.property
        (fun c hc => hcs c (List.mem_of_mem_take hc))

theorem movedWord_zero (cs : List ℝ) (hlen : 0 < cs.length) :
    movedWord cs ⟨0, hlen⟩ = cs := by
  simpa only [movedWord, List.take_zero, List.nil_append, List.drop_zero] using
    List.getElem_cons_drop hlen

theorem baseline_mem_wordSpan (ρ : ℝ) (cs : List ℝ) (hlen : 0 < cs.length) (b : Bool) :
    baselineColumn ρ cs b ∈ wordSpan ρ cs := by
  apply Submodule.subset_span
  refine ⟨(⟨0, hlen⟩, b), ?_⟩
  cases b <;> simp only [wordColumn, baselineColumn, wordQ, wordR, movedWord_zero,
    Bool.false_eq_true, ↓reduceIte]

theorem pairedSpan_le_wordSpan (ρ : ℝ) (cs : List ℝ) (hlen : 0 < cs.length)
    (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0) :
    BinaryTransferSpan.pairedSpan ρ cs ≤ wordSpan ρ cs := by
  apply Submodule.span_le.mpr
  rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · rw [← wordQ_sub_baseline ρ cs i hρ hcs]
    exact (wordSpan ρ cs).sub_mem (Submodule.subset_span ⟨(i, true), rfl⟩)
      (baseline_mem_wordSpan ρ cs hlen true)
  · have hmem := (wordSpan ρ cs).sub_mem (Submodule.subset_span ⟨(i, false), rfl⟩)
      (baseline_mem_wordSpan ρ cs hlen false)
    change wordR ρ cs i - BinaryTransferSpan.baselineR ρ cs ∈ wordSpan ρ cs at hmem
    rw [wordR_sub_baseline ρ cs i hρ hcs] at hmem
    have hpos := (wordSpan ρ cs).neg_mem hmem
    rw [neg_neg] at hpos
    exact hpos

/-- Exact span identity for the actual words, before using parity. -/
theorem wordSpan_eq_paired_sup_baseline (ρ : ℝ) (cs : List ℝ) (hlen : 0 < cs.length)
    (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0) :
    wordSpan ρ cs = BinaryTransferSpan.pairedSpan ρ cs ⊔
      Submodule.span ℝ (Set.range (baselineColumn ρ cs)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, b⟩, rfl⟩
    have hbase (b : Bool) : baselineColumn ρ cs b ∈
        BinaryTransferSpan.pairedSpan ρ cs ⊔
          Submodule.span ℝ (Set.range (baselineColumn ρ cs)) :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
    have hdef : BinaryTransferSpan.prefixDefect ρ cs i ∈ BinaryTransferSpan.pairedSpan ρ cs :=
      Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    have hzdef : BinaryTransferSpan.mulZ (BinaryTransferSpan.prefixDefect ρ cs i) ∈
        BinaryTransferSpan.pairedSpan ρ cs := Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    cases b with
    | true =>
      have heq := sub_eq_iff_eq_add.mp (wordQ_sub_baseline ρ cs i hρ hcs)
      change wordQ ρ cs i ∈ _
      rw [heq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hdef) (hbase true)
    | false =>
      have heq := sub_eq_iff_eq_add.mp (wordR_sub_baseline ρ cs i hρ hcs)
      change wordR ρ cs i ∈ _
      rw [heq]
      exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.mem_sup_left hzdef)) (hbase false)
  · apply sup_le
    · exact pairedSpan_le_wordSpan ρ cs hlen hρ hcs
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact baseline_mem_wordSpan ρ cs hlen b

private theorem sup_span_range_eq_of_sub_mem {ι : Type*} (P : Submodule ℝ FunctionSpace)
    (f g : ι → FunctionSpace) (h : ∀ i, f i - g i ∈ P) :
    P ⊔ Submodule.span ℝ (Set.range f) = P ⊔ Submodule.span ℝ (Set.range g) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hm := Submodule.add_mem (P ⊔ Submodule.span ℝ (Set.range g))
      (Submodule.mem_sup_left (h i)) (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
    rw [sub_add_cancel] at hm
    exact hm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hm := Submodule.sub_mem (P ⊔ Submodule.span ℝ (Set.range f))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)) (Submodule.mem_sup_left (h i))
    rw [sub_sub_cancel] at hm
    exact hm

abbrev AugmentedIndex (cs : List ℝ) := BinaryTransferIndependence.PairIndex cs ⊕ Bool

def augmentedColumn (ρ : ℝ) (cs : List ℝ) (c : ℝ) : AugmentedIndex cs → FunctionSpace :=
  Sum.elim (BinaryTransferIndependence.pairedDefect ρ cs) (blockColumn ρ c)

def augmentedSpan (ρ : ℝ) (cs : List ℝ) (c : ℝ) : Submodule ℝ FunctionSpace :=
  Submodule.span ℝ (Set.range (augmentedColumn ρ cs c))

theorem augmentedSpan_eq_sup (ρ : ℝ) (cs : List ℝ) (c : ℝ) :
    augmentedSpan ρ cs c = BinaryTransferSpan.pairedSpan ρ cs ⊔
      Submodule.span ℝ (Set.range (blockColumn ρ c)) := by
  rw [BinaryTransferIndependence.pairedSpan_eq_span_pairedDefect]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    | inr b => exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr b, rfl⟩

theorem wordSpan_even (ρ c : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y))
    (heven : (cs.length + 1) % 2 = 0) :
    wordSpan ρ (cs ++ [c]) = BinaryTransferSpan.pairedSpan ρ (cs ++ [c]) := by
  have hall : ∀ d ∈ cs ++ [c], d ≠ 0 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hcs d hd
    · rcases List.mem_singleton.mp hd with rfl
      exact hc
  rw [wordSpan_eq_paired_sup_baseline ρ (cs ++ [c]) (by simp) hρ hall]
  apply sup_eq_left.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  cases b with
  | false =>
    simpa [baselineColumn, heven] using
      BinaryTransferSpan.baselineR_sub_parity_mem ρ c cs hρ hcs hc hadj
  | true =>
    simpa [baselineColumn, heven] using
      BinaryTransferSpan.baselineQ_sub_parity_mem ρ c cs hρ hcs hc hadj

theorem wordSpan_odd (ρ c : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y))
    (hodd : (cs.length + 1) % 2 = 1) :
    wordSpan ρ (cs ++ [c]) = augmentedSpan ρ (cs ++ [c]) c := by
  have hall : ∀ d ∈ cs ++ [c], d ≠ 0 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hcs d hd
    · rcases List.mem_singleton.mp hd with rfl
      exact hc
  rw [wordSpan_eq_paired_sup_baseline ρ (cs ++ [c]) (by simp) hρ hall, augmentedSpan_eq_sup]
  apply sup_span_range_eq_of_sub_mem
  intro b
  cases b with
  | false =>
    simpa [baselineColumn, blockColumn, hodd] using
      BinaryTransferSpan.baselineR_sub_parity_mem ρ c cs hρ hcs hc hadj
  | true =>
    simpa [baselineColumn, blockColumn, hodd] using
      BinaryTransferSpan.baselineQ_sub_parity_mem ρ c cs hρ hcs hc hadj

theorem block_combination_eq_affine (ρ c a b : ℝ) (hρ : ρ ≠ 1) (hc : c ≠ 0) :
    a • BinaryTransferSpan.blockQ ρ c + b • BinaryTransferSpan.blockR ρ c =
      BinaryTransferIndependence.affine ((a * c + b) / ((ρ - 1) * c))
        ((a * ρ * c + b) / (ρ - 1)) := by
  funext z
  change a * BinaryTransferAlgebra.Q ρ c z.val + b * BinaryTransferAlgebra.R ρ c z.val =
    (a * c + b) / ((ρ - 1) * c) + ((a * ρ * c + b) / (ρ - 1)) * z.val
  unfold BinaryTransferAlgebra.Q BinaryTransferAlgebra.R
  field_simp [sub_ne_zero.mpr hρ, hc]
  ring

theorem block_coefficients_eq_zero (ρ c a b : ℝ) (hρ : ρ ≠ 1) (hc : c ≠ 0)
    (hconst : (a * c + b) / ((ρ - 1) * c) = 0)
    (hslope : (a * ρ * c + b) / (ρ - 1) = 0) : a = 0 ∧ b = 0 := by
  have hn0 : a * c + b = 0 :=
    (div_eq_zero_iff.mp hconst).resolve_right (mul_ne_zero (sub_ne_zero.mpr hρ) hc)
  have hn1 : a * ρ * c + b = 0 :=
    (div_eq_zero_iff.mp hslope).resolve_right (sub_ne_zero.mpr hρ)
  have hmul : a * (c * (ρ - 1)) = 0 := by
    calc
      _ = (a * ρ * c + b) - (a * c + b) := by ring
      _ = 0 := by rw [hn0, hn1, sub_self]
  have ha : a = 0 := (mul_eq_zero.mp hmul).resolve_right (mul_ne_zero hc (sub_ne_zero.mpr hρ))
  exact ⟨ha, by simpa only [ha, zero_mul, zero_add] using hn0⟩

/-- Adding the two final affine blocks to the actual paired defects preserves
independence. This statement itself does not require odd length. -/
theorem linearIndependent_augmentedColumn (ρ c : ℝ) (cs : List ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    LinearIndependent ℝ (augmentedColumn ρ cs c) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Fintype.sum_bool] at hg
  change (∑ i, g (Sum.inl i) • BinaryTransferIndependence.pairedDefect ρ cs i) +
    (g (Sum.inr true) • BinaryTransferSpan.blockQ ρ c +
      g (Sum.inr false) • BinaryTransferSpan.blockR ρ c) = 0 at hg
  rw [block_combination_eq_affine ρ c _ _ hρ hc] at hg
  have h := BinaryTransferIndependence.paired_relation_with_affine ρ cs (fun i => g (Sum.inl i))
    ((g (Sum.inr true) * c + g (Sum.inr false)) / ((ρ - 1) * c))
    ((g (Sum.inr true) * ρ * c + g (Sum.inr false)) / (ρ - 1)) hρ0 hρ hcs hadj hg
  have hb := block_coefficients_eq_zero ρ c (g (Sum.inr true)) (g (Sum.inr false))
    hρ hc h.2.1 h.2.2
  intro i
  cases i with
  | inl i => exact h.1 i
  | inr b => cases b with
    | false => exact hb.2
    | true => exact hb.1

theorem card_activeSlot (cs : List ℝ) :
    Fintype.card (BinaryTransferIndependence.ActiveSlot cs) = cs.length - 1 := by
  classical
  unfold BinaryTransferIndependence.ActiveSlot
  cases cs.length with
  | zero => simp
  | succ n => simp [Fin.val_eq_zero_iff]

theorem card_pairIndex (cs : List ℝ) :
    Fintype.card (BinaryTransferIndependence.PairIndex cs) = 2 * (cs.length - 1) := by
  classical
  change Fintype.card (BinaryTransferIndependence.ActiveSlot cs × Bool) = _
  rw [Fintype.card_prod, Fintype.card_bool, card_activeSlot, Nat.mul_comm]

theorem finrank_pairedSpan (ρ : ℝ) (cs : List ℝ) (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1)
    (hcs : ∀ c ∈ cs, c ≠ 0) (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Module.finrank ℝ (BinaryTransferSpan.pairedSpan ρ cs) = 2 * (cs.length - 1) := by
  rw [BinaryTransferIndependence.pairedSpan_eq_span_pairedDefect,
    finrank_span_eq_card (BinaryTransferIndependence.linearIndependent_pairedDefect
      ρ cs hρ0 hρ hcs hadj), card_pairIndex]

theorem finrank_augmentedSpan (ρ c : ℝ) (cs : List ℝ) (hlen : 0 < cs.length)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Module.finrank ℝ (augmentedSpan ρ cs c) = 2 * cs.length := by
  unfold augmentedSpan
  rw [finrank_span_eq_card (linearIndependent_augmentedColumn ρ c cs hρ0 hρ hcs hc hadj)]
  change Fintype.card (BinaryTransferIndependence.PairIndex cs ⊕ Bool) = _
  rw [Fintype.card_sum, Fintype.card_bool, card_pairIndex]
  omega

theorem finrank_wordSpan_even (ρ c : ℝ) (cs : List ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y))
    (heven : (cs.length + 1) % 2 = 0) :
    Module.finrank ℝ (wordSpan ρ (cs ++ [c])) = 2 * (cs.length + 1) - 2 := by
  have hall : ∀ d ∈ cs ++ [c], d ≠ 0 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hcs d hd
    · rcases List.mem_singleton.mp hd with rfl
      exact hc
  rw [wordSpan_even ρ c cs hρ hcs hc hadj heven,
    finrank_pairedSpan ρ (cs ++ [c]) hρ0 hρ hall hadj]
  simp only [List.length_append, List.length_singleton]
  omega

theorem finrank_wordSpan_odd (ρ c : ℝ) (cs : List ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y))
    (hodd : (cs.length + 1) % 2 = 1) :
    Module.finrank ℝ (wordSpan ρ (cs ++ [c])) = 2 * (cs.length + 1) := by
  have hall : ∀ d ∈ cs ++ [c], d ≠ 0 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hcs d hd
    · rcases List.mem_singleton.mp hd with rfl
      exact hc
  rw [wordSpan_odd ρ c cs hρ hcs hc hadj hodd,
    finrank_augmentedSpan ρ c (cs ++ [c]) (by simp) hρ0 hρ hall hc hadj]
  simp only [List.length_append, List.length_singleton]

/-- Exact rank parity of the two actual ordered word columns at every position
of a nonempty coefficient list. This is an auxiliary binary rank theorem. -/
theorem finrank_wordSpan_parity (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Module.finrank ℝ (wordSpan ρ cs) =
      if cs.length % 2 = 1 then 2 * cs.length else 2 * cs.length - 2 := by
  induction cs using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton cs c _ih =>
    have hc : c ≠ 0 := hcs c (by simp)
    have hcs' : ∀ d ∈ cs, d ≠ 0 := fun d hd => hcs d (by simp [hd])
    have hcases : (cs.length + 1) % 2 = 0 ∨ (cs.length + 1) % 2 = 1 := by omega
    rcases hcases with heven | hodd
    · have hnodd : (cs ++ [c]).length % 2 ≠ 1 := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [ite_eq_right hnodd]
      simpa only [List.length_append, List.length_singleton] using
        finrank_wordSpan_even ρ c cs hρ0 hρ hcs' hc hadj heven
    · have hodd' : (cs ++ [c]).length % 2 = 1 := by
        simpa only [List.length_append, List.length_singleton] using hodd
      rw [ite_eq_left hodd']
      simpa only [List.length_append, List.length_singleton] using
        finrank_wordSpan_odd ρ c cs hρ0 hρ hcs' hc hadj hodd

end PanelMoments.BinaryTransferRank
