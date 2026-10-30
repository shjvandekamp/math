import PanelMoments.SourceTransferOrders
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

set_option autoImplicit false

/-!
# Exact reduction of the empty-prefix source columns

Choose the least tail index different from `s`. Its singleton word is exactly
the increasing suffix of the empty word starting at `s`. The identity
`I - K * P = (I - K) + K * (I - P)` then expresses each normalized empty
source column as its single-block column plus a sum of actual normalized
singleton source columns. All coefficients in this replacement are constant.

The replacement preserves the span and linear independence of the full finite
new-column family. Neither family is asserted to be linearly independent.
-/

namespace PanelMoments.SourceSingleBlock

open scoped BigOperators
open SourceNewIndices SourceTransferOrders SourceJointImage KernelProducts

noncomputable section

abbrev ImageSpace := State 2 → SourceConditional.PositiveEffectPoint 2 → ℝ

theorem remaining_nonempty {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    (Finset.univ.erase s).Nonempty := by
  apply Finset.card_pos.mp
  simp only [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The paper's least remaining tail index, with its required inequality. -/
def firstRemaining {N : ℕ} (hN : 2 ≤ N) (s : Fin N) : {u : Fin N // u ≠ s} :=
  ⟨(Finset.univ.erase s).min' (remaining_nonempty hN s),
    (Finset.mem_erase.mp (Finset.min'_mem _ (remaining_nonempty hN s))).1⟩

theorem firstRemaining_mem {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    (firstRemaining hN s).val ∈ Finset.univ.erase s :=
  Finset.min'_mem _ (remaining_nonempty hN s)

theorem firstRemaining_le {N : ℕ} (hN : 2 ≤ N) (s u : Fin N)
    (hu : u ∈ Finset.univ.erase s) : (firstRemaining hN s).val ≤ u :=
  Finset.min'_le _ _ hu

theorem sorted_remaining_eq_singletonWord {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    (Finset.univ.erase s).sort (· ≤ ·) = singletonWord s (firstRemaining hN s).val := by
  unfold singletonWord
  have hle : ∀ u ∈ (Finset.univ.erase s).erase (firstRemaining hN s).val,
      (firstRemaining hN s).val ≤ u := by
    intro u hu
    exact firstRemaining_le hN s u (Finset.mem_erase.mp hu).2
  rw [← Finset.sort_insert (· ≤ ·) hle (by simp)]
  rw [Finset.insert_erase (firstRemaining_mem hN s)]

theorem emptyWord_split {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    emptyWord s = s :: singletonWord s (firstRemaining hN s).val := by
  rw [emptyWord, sorted_remaining_eq_singletonWord hN s]

theorem wordProduct_empty_split {N : ℕ} (A : Table 2) (η : Fin 2 → ℝ)
    (hN : 2 ≤ N) (s : Fin N) :
    wordProduct A η (emptyWord s) = transitionMatrix A η (s.val + 2) *
      wordProduct A η (singletonWord s (firstRemaining hN s).val) := by
  rw [emptyWord_split hN s]
  simp only [wordProduct, List.map_cons, List.prod_cons]

/-- The actual normalized empty shared-set source column. -/
def emptyColumn {N : ℕ} (A : Table 2) (r : State 2) (hN : 2 ≤ N)
    (s : Fin N) (a : State 2) : ImageSpace := fun c η =>
  (denominator A η.val 0 r / A 0 r a) *
    jointFirst A r (SourceFamily.sourceMoment A r (emptyIndex hN s a).val) c η

/-- The actual normalized singleton source column; `a` is the shared label
and `b` the divergent label. -/
def singletonColumn {N : ℕ} (A : Table 2) (r : State 2) (hN : 2 ≤ N)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b : State 2) : ImageSpace := fun c η =>
  (denominator A η.val 0 r / A 0 r a) *
    jointFirst A r (SourceFamily.sourceMoment A r (singletonIndex hN t s b a).val) c η

/-- The single-block vector `X_a e_a (I - K_s)`. -/
def singleBlockColumn {N : ℕ} (A : Table 2) (s : Fin N) (a : State 2) : ImageSpace :=
  fun c η => effect η.val a * ((if a = c then 1 else 0) - transition A η.val (s.val + 2) a c)

theorem emptyColumn_apply {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) (s : Fin N) (a c : State 2)
    (η : SourceConditional.PositiveEffectPoint 2) :
    emptyColumn A r hN s a c η = effect η.val a *
      ((if a = c then 1 else 0) - wordProduct A η.val (emptyWord s) a c) :=
  normalized_jointFirst_empty_word hA hN r s a c η

theorem singletonColumn_apply {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) (t : Fin N) (s : {s : Fin N // s ≠ t})
    (a b c : State 2) (η : SourceConditional.PositiveEffectPoint 2) :
    singletonColumn A r hN t s a b c η =
      effect η.val a * transition A η.val (t.val + 2) a b *
        ((if b = c then 1 else 0) - wordProduct A η.val (singletonWord t s.val) b c) :=
  normalized_jointFirst_singleton_word hA hN r t s b a c η

/-- The finite-matrix identity uses only scalar coefficients `1` in the sum. -/
theorem matrix_column_reduction (x : ℝ) (K P : Matrix (State 2) (State 2) ℝ)
    (a c : State 2) :
    x * ((if a = c then 1 else 0) - (K * P) a c) =
      x * ((if a = c then 1 else 0) - K a c) +
        ∑ b : State 2, x * K a b * ((if b = c then 1 else 0) - P b c) := by
  classical
  have hdelta : (∑ b : State 2, K a b * (if b = c then 1 else 0)) = K a c := by
    simp
  change x * ((if a = c then 1 else 0) - ∑ b : State 2, K a b * P b c) = _
  simp only [mul_sub, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hdelta]
  ring

/-- Exact source-function reduction, before any independence or residue argument. -/
theorem emptyColumn_reduction {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) (s : Fin N) (a : State 2) :
    emptyColumn A r hN s a = singleBlockColumn A s a +
      ∑ b : State 2, singletonColumn A r hN s (firstRemaining hN s) a b := by
  funext c η
  simp only [Pi.add_apply, Finset.sum_apply, emptyColumn_apply hA,
    singletonColumn_apply hA, singleBlockColumn]
  rw [wordProduct_empty_split A η.val hN s]
  exact matrix_column_reduction (effect η.val a) (transitionMatrix A η.val (s.val + 2))
    (wordProduct A η.val (singletonWord s (firstRemaining hN s).val)) a c

/-- The full normalized new source family, on its exact empty/singleton indices. -/
def sourceColumn {N : ℕ} (A : Table 2) (r : State 2) (hN : 2 ≤ N) :
    NewParameter N → ImageSpace
  | Sum.inl p => emptyColumn A r hN p.1 p.2
  | Sum.inr p => singletonColumn A r hN p.1 p.2.1 p.2.2.2 p.2.2.1

/-- Replace just the empty columns by their single-block vectors. -/
def reducedColumn {N : ℕ} (A : Table 2) (r : State 2) (hN : 2 ≤ N) :
    NewParameter N → ImageSpace
  | Sum.inl p => singleBlockColumn A p.1 p.2
  | Sum.inr p => singletonColumn A r hN p.1 p.2.1 p.2.2.2 p.2.2.1

theorem span_sourceColumn_eq_reducedColumn {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) :
    Submodule.span ℝ (Set.range (sourceColumn A r hN)) =
      Submodule.span ℝ (Set.range (reducedColumn A r hN)) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    cases p with
    | inl p =>
        change emptyColumn A r hN p.1 p.2 ∈ _
        rw [emptyColumn_reduction hA r hN p.1 p.2]
        apply Submodule.add_mem
        · exact Submodule.subset_span ⟨Sum.inl p, rfl⟩
        · apply Submodule.sum_mem
          intro b _
          exact Submodule.subset_span
            ⟨Sum.inr ⟨p.1, firstRemaining hN p.1, b, p.2⟩, rfl⟩
    | inr p => exact Submodule.subset_span ⟨Sum.inr p, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    cases p with
    | inl p =>
        change singleBlockColumn A p.1 p.2 ∈ _
        have hsingle : singleBlockColumn A p.1 p.2 = emptyColumn A r hN p.1 p.2 -
            ∑ b : State 2, singletonColumn A r hN p.1 (firstRemaining hN p.1) p.2 b :=
          eq_sub_of_add_eq (emptyColumn_reduction hA r hN p.1 p.2).symm
        rw [hsingle]
        apply Submodule.sub_mem
        · exact Submodule.subset_span ⟨Sum.inl p, rfl⟩
        · apply Submodule.sum_mem
          intro b _
          exact Submodule.subset_span
            ⟨Sum.inr ⟨p.1, firstRemaining hN p.1, b, p.2⟩, rfl⟩
    | inr p => exact Submodule.subset_span ⟨Sum.inr p, rfl⟩

/-- The finite column replacement is reversible for independence; this is an
equivalence, not an assertion that either family is independent. -/
theorem linearIndependent_sourceColumn_iff {N : ℕ} {A : Table 2} (hA : PositiveTable A)
    (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (sourceColumn A r hN) ↔
      LinearIndependent ℝ (reducedColumn A r hN) := by
  classical
  simp only [linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  have hdim := congrArg (fun U : Submodule ℝ ImageSpace => Module.finrank ℝ U)
    (span_sourceColumn_eq_reducedColumn hA r hN)
  exact (congrArg (fun d : ℕ => Fintype.card (NewParameter N) = d) hdim).to_iff

end

end PanelMoments.SourceSingleBlock
