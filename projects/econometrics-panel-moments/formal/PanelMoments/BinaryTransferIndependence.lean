import PanelMoments.BinaryTransferEndpoints
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Independence of the actual paired binary transfer defects

The vector space consists of functions on nonzero real arguments, with
constant real scalar coefficients. Polynomial clearing bounds put every
earlier defect pair in the space required by the endpoint-separation theorem.
The finite coefficient argument eliminates actual list positions from last
to first. The identically zero initial defect is excluded from the index type.
-/

noncomputable section

namespace PanelMoments.BinaryTransferIndependence

open Polynomial
open scoped BigOperators

abbrev FunctionSpace := BinaryTransferSpan.FunctionSpace
abbrev NonzeroReal := BinaryTransferSpan.NonzeroReal

/-- Functions whose multiplication by `z^k` is a polynomial of degree at
most `d`. This is a real submodule, with no dependence of scalars on `z`. -/
def clearedSpace (k d : ℕ) : Submodule ℝ FunctionSpace where
  carrier := {f | ∃ p : ℝ[X], p.natDegree ≤ d ∧
    ∀ z : NonzeroReal, p.eval z.val = z.val ^ k * f z}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨p, hp, hpf⟩ ⟨q, hq, hqg⟩
    refine ⟨p + q, natDegree_add_le_of_degree_le hp hq, ?_⟩
    intro z
    simp only [eval_add, hpf z, hqg z, Pi.add_apply, mul_add]
  smul_mem' := by
    rintro a f ⟨p, hp, hpf⟩
    refine ⟨C a * p, ?_, ?_⟩
    · simpa only [zero_add] using
        natDegree_mul_le_of_le (show (C a).natDegree ≤ 0 by simp) hp
    · intro z
      simp only [eval_mul, eval_C, hpf z, Pi.smul_apply, smul_eq_mul]
      ring

theorem clearedSpace_mono (k : ℕ) {d e : ℕ} (hde : d ≤ e) :
    clearedSpace k d ≤ clearedSpace k e := by
  rintro f ⟨p, hp, hpf⟩
  exact ⟨p, hp.trans hde, hpf⟩

theorem mulZ_mem_clearedSpace {k d : ℕ} {f : FunctionSpace}
    (hf : f ∈ clearedSpace k d) : BinaryTransferSpan.mulZ f ∈ clearedSpace k (d + 1) := by
  rcases hf with ⟨p, hp, hpf⟩
  refine ⟨X * p, ?_, ?_⟩
  · simpa only [Nat.add_comm] using
      natDegree_mul_le_of_le (show (X : ℝ[X]).natDegree ≤ 1 by simp) hp
  · intro z
    simp only [eval_mul, eval_X, hpf z]
    change z.val * (z.val ^ k * f z) = z.val ^ k * (z.val * f z)
    ring

theorem prefixDefect_mem_clearedSpace (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length)
    (k : ℕ) (hik : i.val ≤ k) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0) :
    BinaryTransferSpan.prefixDefect ρ cs i ∈ clearedSpace k (2 * k) := by
  have hlen : (cs.take i.val).length = i.val := List.length_take_of_le (Nat.le_of_lt i.isLt)
  have htake : ∀ c ∈ cs.take i.val, c ≠ 0 :=
    fun c hc => hcs c (List.mem_of_mem_take hc)
  refine ⟨X ^ (k - i.val) * BinaryTransferEndpoints.defectPolynomial ρ (cs.take i.val) cs[i.val],
    ?_, ?_⟩
  · have hd := natDegree_mul_le_of_le
      (show (X ^ (k - i.val) : ℝ[X]).natDegree ≤ k - i.val by simp)
      (BinaryTransferEndpoints.defectPolynomial_natDegree_le ρ cs[i.val] (cs.take i.val))
    rw [hlen] at hd
    omega
  · intro z
    simp only [eval_mul, eval_pow, eval_X,
      BinaryTransferEndpoints.defectPolynomial_eval ρ cs[i.val] z.val (cs.take i.val)
        hρ (hcs _ (List.getElem_mem i.isLt)) z.property htake, hlen]
    change z.val ^ (k - i.val) * (z.val ^ i.val *
      BinaryTransferAlgebra.moveFirst ρ (cs.take i.val) cs[i.val] z.val) =
        z.val ^ k * BinaryTransferAlgebra.moveFirst ρ (cs.take i.val) cs[i.val] z.val
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hik]

/-- Every actual paired defect in a list of at most `k+1` coefficients has
a common clearing polynomial with degree at most `2*k+1`. -/
theorem pairedSpan_le_clearedSpace (ρ : ℝ) (cs : List ℝ) (k : ℕ)
    (hsize : cs.length ≤ k + 1) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0) :
    BinaryTransferSpan.pairedSpan ρ cs ≤ clearedSpace k (2 * k + 1) := by
  apply Submodule.span_le.mpr
  rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact clearedSpace_mono k (by omega)
      (prefixDefect_mem_clearedSpace ρ cs i k (by have := i.isLt; omega) hρ hcs)
  · exact mulZ_mem_clearedSpace
      (prefixDefect_mem_clearedSpace ρ cs i k (by have := i.isLt; omega) hρ hcs)

def affine (a b : ℝ) : FunctionSpace := fun z => a + b * z.val

theorem affine_mem_clearedSpace (k : ℕ) (a b : ℝ) :
    affine a b ∈ clearedSpace k (2 * k + 1) := by
  refine ⟨X ^ k * (C a + C b * X), ?_, ?_⟩
  · have hlin : (C a + C b * X).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le (by simp)
        (by simpa using (natDegree_mul_le_of_le (show (C b).natDegree ≤ 0 by simp)
          (show (X : ℝ[X]).natDegree ≤ 1 by simp)))
    have hd := natDegree_mul_le_of_le (show (X ^ k : ℝ[X]).natDegree ≤ k by simp) hlin
    omega
  · intro z
    simp only [eval_mul, eval_pow, eval_X, eval_add, eval_C, affine]

theorem affine_eq_zero_iff (a b : ℝ) : affine a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hp := congr_fun h (⟨1, by norm_num⟩ : NonzeroReal)
    have hm := congr_fun h (⟨-1, by norm_num⟩ : NonzeroReal)
    simp only [affine, Pi.zero_apply] at hp hm
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    funext z
    simp [affine]

def slotTerm (ρ : ℝ) (cs : List ℝ) (a b : Fin cs.length → ℝ)
    (i : Fin cs.length) : FunctionSpace :=
  a i • BinaryTransferSpan.prefixDefect ρ cs i +
    b i • BinaryTransferSpan.mulZ (BinaryTransferSpan.prefixDefect ρ cs i)

/-- The finite relation argument is made on actual list positions. Coefficients
at the zero initial defect are fixed to zero; every other coefficient and
both affine coefficients must then vanish. -/
theorem slot_relation_with_affine (ρ : ℝ) (cs : List ℝ)
    (a b : Fin cs.length → ℝ) (u v : ℝ) (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1)
    (hcs : ∀ c ∈ cs, c ≠ 0) (hadj : cs.IsChain (fun x y : ℝ => x ≠ y))
    (hinitial : ∀ i : Fin cs.length, i.val = 0 → a i = 0 ∧ b i = 0)
    (hrel : (∑ i, slotTerm ρ cs a b i) + affine u v = 0) :
    (∀ i, a i = 0 ∧ b i = 0) ∧ u = 0 ∧ v = 0 := by
  classical
  have hkill : ∀ n : ℕ, n ≤ cs.length →
      (∀ i : Fin cs.length, n ≤ i.val → a i = 0 ∧ b i = 0) →
      ∀ i, a i = 0 ∧ b i = 0 := by
    intro n
    induction n with
    | zero => intro _ hs i; exact hs i (Nat.zero_le _)
    | succ n ih =>
      intro hn hs
      cases n with
      | zero =>
        apply ih (by omega)
        intro i _
        by_cases hi : i.val = 0
        · exact hinitial i hi
        · exact hs i (by omega)
      | succ k =>
        let j : Fin cs.length := ⟨k + 1, by omega⟩
        let rest : FunctionSpace :=
          (∑ i ∈ Finset.univ.erase j, slotTerm ρ cs a b i) + affine u v
        have hrest : rest ∈ clearedSpace k (2 * k + 1) := by
          apply (clearedSpace k (2 * k + 1)).add_mem
          · apply (clearedSpace k (2 * k + 1)).sum_mem
            intro i hi
            have hij : i ≠ j := (Finset.mem_erase.mp hi).1
            by_cases hik : i.val ≤ k
            · exact (clearedSpace k (2 * k + 1)).add_mem
                ((clearedSpace k (2 * k + 1)).smul_mem (a i)
                  (clearedSpace_mono k (by omega)
                    (prefixDefect_mem_clearedSpace ρ cs i k hik hρ hcs)))
                ((clearedSpace k (2 * k + 1)).smul_mem (b i)
                  (mulZ_mem_clearedSpace
                    (prefixDefect_mem_clearedSpace ρ cs i k hik hρ hcs)))
            · have hival : i.val ≠ k + 1 := by
                intro heq
                apply hij
                exact Fin.ext heq
              obtain ⟨hai, hbi⟩ := hs i (by omega)
              simp only [slotTerm, hai, hbi, zero_smul, zero_add]
              exact (clearedSpace k (2 * k + 1)).zero_mem
          · exact affine_mem_clearedSpace k u v
        rcases hrest with ⟨p, hp, hrep⟩
        have hk : k < cs.length := by omega
        have hk1 : k + 1 < cs.length := by omega
        have hlen : (cs.take k).length = k := List.length_take_of_le (by omega)
        have hprefix : ∀ d ∈ cs.take k, d ≠ 0 :=
          fun d hd => hcs d (List.mem_of_mem_take hd)
        have hdiff : cs[k] ≠ cs[k + 1] := List.isChain_iff_getElem.mp hadj k hk1
        have hdefect : BinaryTransferSpan.prefixDefect ρ cs j =
            BinaryTransferSpan.defect ρ (cs.take k ++ [cs[k]]) cs[k + 1] := by
          change BinaryTransferSpan.defect ρ (cs.take (k + 1)) cs[k + 1] = _
          rw [List.take_succ_eq_append_getElem hk]
        have hlastrel : a j • BinaryTransferSpan.defect ρ (cs.take k ++ [cs[k]]) cs[k + 1] +
            b j • BinaryTransferSpan.mulZ
              (BinaryTransferSpan.defect ρ (cs.take k ++ [cs[k]]) cs[k + 1]) + rest = 0 := by
          rw [← hdefect]
          change slotTerm ρ cs a b j +
            ((∑ i ∈ Finset.univ.erase j, slotTerm ρ cs a b i) + affine u v) = 0
          rw [← add_assoc, Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          exact hrel
        obtain ⟨haj, hbj, _⟩ := BinaryTransferEndpoints.separate_actual_pair
          ρ cs[k] cs[k + 1] (cs.take k) p (a j) (b j) rest hρ0 hρ hprefix
          (hcs _ (List.getElem_mem hk)) (hcs _ (List.getElem_mem hk1)) hdiff
          (by simpa only [hlen] using hp) (by simpa only [hlen] using hrep) hlastrel
        apply ih (by omega)
        intro i hi
        by_cases heq : i = j
        · simpa only [heq] using And.intro haj hbj
        · have hival : i.val ≠ k + 1 := fun hh => heq (Fin.ext hh)
          exact hs i (by omega)
  have hcoeff := hkill cs.length le_rfl (fun i hi => False.elim (by have := i.isLt; omega))
  have hzero : affine u v = 0 := by
    have hsum : (∑ i, slotTerm ρ cs a b i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [slotTerm, (hcoeff i).1, (hcoeff i).2, zero_smul, zero_add]
    simpa only [hsum, zero_add] using hrel
  exact ⟨hcoeff, (affine_eq_zero_iff u v).mp hzero⟩

/-- The actual noninitial list positions; slot zero has identically zero defect. -/
abbrev ActiveSlot (cs : List ℝ) := {i : Fin cs.length // i.val ≠ 0}

abbrev PairIndex (cs : List ℝ) := ActiveSlot cs × Bool

/-- `true` selects `hᵢ`, and `false` selects `z hᵢ`. -/
def pairedDefect (ρ : ℝ) (cs : List ℝ) (i : PairIndex cs) : FunctionSpace :=
  if i.2 then BinaryTransferSpan.prefixDefect ρ cs i.1.val
  else BinaryTransferSpan.mulZ (BinaryTransferSpan.prefixDefect ρ cs i.1.val)

/-- The indexed actual family generates exactly the previously defined paired span. -/
theorem pairedSpan_eq_span_pairedDefect (ρ : ℝ) (cs : List ℝ) :
    BinaryTransferSpan.pairedSpan ρ cs = Submodule.span ℝ (Set.range (pairedDefect ρ cs)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · by_cases hi : i.val = 0
      · have hz : BinaryTransferSpan.prefixDefect ρ cs i = 0 := by
          simp [BinaryTransferSpan.prefixDefect, hi]
        rw [hz]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨(⟨i, hi⟩, true), rfl⟩
    · by_cases hi : i.val = 0
      · have hz : BinaryTransferSpan.prefixDefect ρ cs i = 0 := by
          simp [BinaryTransferSpan.prefixDefect, hi]
        change BinaryTransferSpan.mulZ (BinaryTransferSpan.prefixDefect ρ cs i) ∈ _
        rw [hz, map_zero]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨(⟨i, hi⟩, false), rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨⟨i, b⟩, rfl⟩
    cases b with
    | false => exact Or.inr ⟨i.val, rfl⟩
    | true => exact Or.inl ⟨i.val, rfl⟩

def extendCoefficients (cs : List ℝ) (g : PairIndex cs → ℝ) (b : Bool)
    (i : Fin cs.length) : ℝ :=
  if hi : i.val ≠ 0 then g (⟨i, hi⟩, b) else 0

theorem paired_sum_eq_slot_sum (ρ : ℝ) (cs : List ℝ) (g : PairIndex cs → ℝ) :
    (∑ i, g i • pairedDefect ρ cs i) =
      ∑ i, slotTerm ρ cs (extendCoefficients cs g true) (extendCoefficients cs g false) i := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  change (∑ i : ActiveSlot cs,
      (g (i, true) • BinaryTransferSpan.prefixDefect ρ cs i.val +
      g (i, false) • BinaryTransferSpan.mulZ (BinaryTransferSpan.prefixDefect ρ cs i.val))) = _
  refine Fintype.sum_of_injective (fun i : ActiveSlot cs => i.val) Subtype.val_injective
    _ _ ?_ ?_
  · intro i hi
    have hzero : i.val = 0 := by
      by_contra hne
      exact hi ⟨⟨i, hne⟩, rfl⟩
    simp [slotTerm, extendCoefficients, hzero]
  · intro i
    simp [slotTerm, extendCoefficients, i.property]

/-- A relation among the actual paired defects and an affine function has
only zero coefficients. -/
theorem paired_relation_with_affine (ρ : ℝ) (cs : List ℝ) (g : PairIndex cs → ℝ)
    (a b : ℝ) (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y))
    (hrel : (∑ i, g i • pairedDefect ρ cs i) + affine a b = 0) :
    (∀ i, g i = 0) ∧ a = 0 ∧ b = 0 := by
  classical
  rw [paired_sum_eq_slot_sum] at hrel
  have h := slot_relation_with_affine ρ cs (extendCoefficients cs g true)
    (extendCoefficients cs g false) a b hρ0 hρ hcs hadj
    (by intro i hi; simp [extendCoefficients, hi]) hrel
  refine ⟨?_, h.2⟩
  rintro ⟨i, b⟩
  cases b with
  | false => simpa only [extendCoefficients, dite_eq_left i.property] using (h.1 i.val).2
  | true => simpa only [extendCoefficients, dite_eq_left i.property] using (h.1 i.val).1

/-- Independence of `h₂,z h₂,…,hₘ,z hₘ` as actual real-valued functions. -/
theorem linearIndependent_pairedDefect (ρ : ℝ) (cs : List ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    LinearIndependent ℝ (pairedDefect ρ cs) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hz : affine 0 0 = 0 := (affine_eq_zero_iff 0 0).mpr ⟨rfl, rfl⟩
  exact (paired_relation_with_affine ρ cs g 0 0 hρ0 hρ hcs hadj
    (by simpa only [hz, add_zero] using hg)).1

/-- No nonzero affine function belongs to the span of the actual paired defects. -/
theorem affine_mem_pairedSpan_iff (ρ : ℝ) (cs : List ℝ) (a b : ℝ)
    (hρ0 : ρ ≠ 0) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    affine a b ∈ BinaryTransferSpan.pairedSpan ρ cs ↔ a = 0 ∧ b = 0 := by
  classical
  constructor
  · intro hf
    rw [pairedSpan_eq_span_pairedDefect] at hf
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
    have hrel : (∑ i, g i • pairedDefect ρ cs i) + affine (-a) (-b) = 0 := by
      rw [hg]
      funext z
      simp only [Pi.add_apply, Pi.zero_apply, affine]
      ring
    have h := paired_relation_with_affine ρ cs g (-a) (-b) hρ0 hρ hcs hadj hrel
    exact ⟨neg_eq_zero.mp h.2.1, neg_eq_zero.mp h.2.2⟩
  · intro hab
    rw [(affine_eq_zero_iff a b).mpr hab]
    exact Submodule.zero_mem _

end PanelMoments.BinaryTransferIndependence
