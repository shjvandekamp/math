import PanelMoments.BinaryTransferAlgebra
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Induction
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Constant-coefficient spans for the auxiliary binary transfer functions

All vectors in this module are real-valued functions on the nonzero reals.
Their span is over `ℝ`: coefficients cannot depend on the evaluation variable.
For a list of length `m`, the indexed defects are `h₁, …, hₘ`; the first
defect is zero, so their span is exactly the span of `h₂, …, hₘ`.

The parity theorem applies to the actual ordered prefix sums. The two baseline
remainders are then zero at even length and the last block at odd length,
modulo the paired real span. These conclusions use only nonzero list entries,
adjacent distinctness, and `ρ ≠ 1`. No independence or rank is asserted.
-/

noncomputable section

namespace PanelMoments.BinaryTransferSpan

abbrev NonzeroReal := {z : ℝ // z ≠ 0}
abbrev FunctionSpace := NonzeroReal → ℝ

/-- A real constant, viewed as a function of the evaluation variable. -/
def constant (a : ℝ) : FunctionSpace := fun _ => a

@[simp] theorem constant_zero : constant 0 = 0 := rfl

/-- The defect caused by moving an appended coefficient to the front. -/
def defect (ρ : ℝ) (cs : List ℝ) (c : ℝ) : FunctionSpace :=
  fun z => BinaryTransferAlgebra.moveFirst ρ cs c z.val

/-- The prefix function denoted `Φₖ(c)` in the parity recurrence. -/
def prefixF (ρ : ℝ) (cs : List ℝ) (c : ℝ) : FunctionSpace :=
  fun z => BinaryTransferAlgebra.prefixF ρ cs c z.val

/-- The defect associated with an actual position in the coefficient list. -/
def prefixDefect (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length) : FunctionSpace :=
  defect ρ (cs.take i.val) cs[i.val]

/-- The finite span uses real scalar coefficients, not functions of `z`. -/
def defectSpan (ρ : ℝ) (cs : List ℝ) : Submodule ℝ FunctionSpace :=
  Submodule.span ℝ (Set.range (prefixDefect ρ cs))

@[simp] theorem defect_nil (ρ c : ℝ) : defect ρ [] c = 0 := by
  funext z
  exact BinaryTransferAlgebra.moveFirst_nil ρ c z.val

@[simp] theorem prefixF_nil (ρ c : ℝ) : prefixF ρ [] c = 0 := by
  funext z
  exact BinaryTransferAlgebra.prefixF_nil ρ c z.val

@[simp] theorem prefixDefect_zero (ρ c : ℝ) (cs : List ℝ) :
    prefixDefect ρ (c :: cs) 0 = 0 := by
  simp [prefixDefect]

theorem prefixDefect_append (ρ : ℝ) (cs ds : List ℝ) (i : Fin cs.length) :
    prefixDefect ρ (cs ++ ds)
      ⟨i.val, by simp only [List.length_append]; omega⟩ = prefixDefect ρ cs i := by
  simp only [prefixDefect, List.take_append_of_le_length (Nat.le_of_lt i.isLt),
    List.getElem_append_left i.isLt]

/-- Appending coefficients preserves every earlier defect and its scalar span. -/
theorem defectSpan_le_append (ρ : ℝ) (cs ds : List ℝ) :
    defectSpan ρ cs ≤ defectSpan ρ (cs ++ ds) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.val, by simp only [List.length_append]; omega⟩,
    prefixDefect_append ρ cs ds i⟩

theorem defect_mem_append_span (ρ c : ℝ) (cs : List ℝ) :
    defect ρ cs c ∈ defectSpan ρ (cs ++ [c]) := by
  apply Submodule.subset_span
  refine ⟨⟨cs.length, by simp⟩, ?_⟩
  simp [prefixDefect, List.getElem_append_right]

/-- Omitting the identically zero first defect leaves precisely the same span. -/
theorem defectSpan_eq_span_noninitial (ρ : ℝ) (cs : List ℝ) :
    defectSpan ρ cs = Submodule.span ℝ
      (Set.range (fun i : {i : Fin cs.length // i.val ≠ 0} => prefixDefect ρ cs i.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val = 0
    · have hz : prefixDefect ρ cs i = 0 := by simp [prefixDefect, hi]
      rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩

/-- The function-space version of the universal scalar recurrence. -/
theorem prefixF_append (ρ e c : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (he : e ≠ 0) (hc : c ≠ 0) (hec : e ≠ c) (hcs : ∀ d ∈ cs, d ≠ 0) :
    prefixF ρ (cs ++ [e]) c = constant 1 - prefixF ρ cs e +
      ((ρ - 1) / (e - c)) •
        (e • defect ρ cs e - c • defect ρ (cs ++ [e]) c) := by
  funext z
  exact BinaryTransferAlgebra.prefixF_append ρ z.val e c cs hρ he hc z.property hec hcs

theorem parity_succ (n : ℕ) :
    (((n + 1) % 2 : ℕ) : ℝ) = 1 - ((n % 2 : ℕ) : ℝ) := by
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hcases with h | h
  · have hs : (n + 1) % 2 = 1 := by omega
    simp [h, hs]
  · have hs : (n + 1) % 2 = 0 := by omega
    simp [h, hs]

/-- Modulo the real scalar span of the prefix defects, `Φₖ(c)` is the
constant parity of `k`. The appended coefficient contributes the last defect. -/
theorem prefixF_sub_parity_mem (ρ c : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ d ∈ cs, d ≠ 0) (hc : c ≠ 0)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y)) :
    prefixF ρ cs c - constant ((cs.length % 2 : ℕ) : ℝ) ∈
      defectSpan ρ (cs ++ [c]) := by
  induction cs using List.reverseRecOn generalizing c with
  | nil =>
    simpa only [List.length_nil, Nat.zero_mod, Nat.cast_zero, prefixF_nil,
      constant_zero, sub_self, List.nil_append] using (defectSpan ρ [c]).zero_mem
  | append_singleton cs e ih =>
    have he : e ≠ 0 := hcs e (by simp)
    have hcs' : ∀ d ∈ cs, d ≠ 0 := fun d hd => hcs d (by simp [hd])
    have hchain : (cs ++ [e]).IsChain (fun x y : ℝ => x ≠ y) ∧ e ≠ c := by
      have h := List.isChain_append_cons_cons.mp
        (show (cs ++ e :: c :: []).IsChain (fun x y : ℝ => x ≠ y) from
          by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hadj)
      exact ⟨h.1, h.2.1⟩
    have hold := defectSpan_le_append ρ (cs ++ [e]) [c]
      (ih e hcs' he hchain.1)
    have he_mem := defectSpan_le_append ρ (cs ++ [e]) [c]
      (defect_mem_append_span ρ e cs)
    have hc_mem := defect_mem_append_span ρ c (cs ++ [e])
    have hcomb := (defectSpan ρ ((cs ++ [e]) ++ [c])).add_mem
      ((defectSpan ρ ((cs ++ [e]) ++ [c])).neg_mem hold)
      ((defectSpan ρ ((cs ++ [e]) ++ [c])).smul_mem ((ρ - 1) / (e - c))
        ((defectSpan ρ ((cs ++ [e]) ++ [c])).sub_mem
          ((defectSpan ρ ((cs ++ [e]) ++ [c])).smul_mem e he_mem)
          ((defectSpan ρ ((cs ++ [e]) ++ [c])).smul_mem c hc_mem)))
    convert hcomb using 1
    rw [prefixF_append ρ e c cs hρ he hc hchain.2 hcs']
    funext z
    simp only [List.length_append, List.length_singleton, parity_succ, constant,
      Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Multiplication by the evaluation variable is a real linear map. -/
def mulZ : FunctionSpace →ₗ[ℝ] FunctionSpace where
  toFun f := fun z => z.val * f z
  map_add' f g := by funext z; exact mul_add z.val (f z) (g z)
  map_smul' a f := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The real span of the actual pairs `hᵢ, z hᵢ`. -/
def pairedSpan (ρ : ℝ) (cs : List ℝ) : Submodule ℝ FunctionSpace :=
  Submodule.span ℝ (Set.range (prefixDefect ρ cs) ∪
    Set.range (fun i => mulZ (prefixDefect ρ cs i)))

theorem defectSpan_le_pairedSpan (ρ : ℝ) (cs : List ℝ) :
    defectSpan ρ cs ≤ pairedSpan ρ cs :=
  Submodule.span_mono Set.subset_union_left

theorem mulZ_mem_pairedSpan (ρ : ℝ) (cs : List ℝ) {f : FunctionSpace}
    (hf : f ∈ defectSpan ρ cs) : mulZ f ∈ pairedSpan ρ cs := by
  have hle : defectSpan ρ cs ≤ (pairedSpan ρ cs).comap mulZ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  exact hle hf

/-- Multiplying a scalar-span remainder by an affine function of `z` uses
only constant real combinations of the paired defects. -/
theorem affine_mul_mem_pairedSpan (ρ a b : ℝ) (cs : List ℝ) {f : FunctionSpace}
    (hf : f ∈ defectSpan ρ cs) :
    (fun z => (a + b * z.val) * f z) ∈ pairedSpan ρ cs := by
  have h := (pairedSpan ρ cs).add_mem
    ((pairedSpan ρ cs).smul_mem a (defectSpan_le_pairedSpan ρ cs hf))
    ((pairedSpan ρ cs).smul_mem b (mulZ_mem_pairedSpan ρ cs hf))
  convert h using 1
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulZ, LinearMap.coe_mk,
    AddHom.coe_mk]
  ring

def blockQ (ρ c : ℝ) : FunctionSpace := fun z => BinaryTransferAlgebra.Q ρ c z.val
def blockR (ρ c : ℝ) : FunctionSpace := fun z => BinaryTransferAlgebra.R ρ c z.val

theorem blockQ_mul_mem_pairedSpan (ρ c : ℝ) (cs : List ℝ) {f : FunctionSpace}
    (hf : f ∈ defectSpan ρ cs) : blockQ ρ c * f ∈ pairedSpan ρ cs := by
  convert affine_mul_mem_pairedSpan ρ (1 / (ρ - 1)) (ρ * c / (ρ - 1)) cs hf using 1
  funext z
  simp only [Pi.mul_apply, blockQ, BinaryTransferAlgebra.Q, div_eq_mul_inv]
  ring

theorem blockR_mul_mem_pairedSpan (ρ c : ℝ) (cs : List ℝ) {f : FunctionSpace}
    (hf : f ∈ defectSpan ρ cs) : blockR ρ c * f ∈ pairedSpan ρ cs := by
  convert affine_mul_mem_pairedSpan ρ (1 / ((ρ - 1) * c))
    (c / ((ρ - 1) * c)) cs hf using 1
  funext z
  simp only [Pi.mul_apply, blockR, BinaryTransferAlgebra.R, div_eq_mul_inv]
  ring

def outerRemainder (ρ : ℝ) (cs : List ℝ) (c d : ℝ) : FunctionSpace := fun z =>
  BinaryTransferAlgebra.outerS ρ (BinaryTransferAlgebra.prefixQ ρ cs z.val)
    (BinaryTransferAlgebra.prefixR ρ cs z.val) c d z.val

theorem outerRemainder_eq_prefixF_sub_defect (ρ c d : ℝ) (cs : List ℝ)
    (hρ : ρ ≠ 1) (hc : c ≠ 0) (hcd : c ≠ d) :
    outerRemainder ρ cs c d = prefixF ρ cs c -
      (c * (ρ - 1) / (c - d)) • defect ρ cs c := by
  funext z
  exact BinaryTransferAlgebra.outerS_eq_F_sub_moveDefect ρ
    (BinaryTransferAlgebra.prefixQ ρ cs z.val) (BinaryTransferAlgebra.prefixR ρ cs z.val)
    c d z.val hρ hc z.property hcd

theorem outerRemainder_sub_parity_mem (ρ c d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hc : c ≠ 0) (hcd : c ≠ d)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y)) :
    outerRemainder ρ cs c d - constant ((cs.length % 2 : ℕ) : ℝ) ∈
      defectSpan ρ (cs ++ [c]) := by
  have h := (defectSpan ρ (cs ++ [c])).sub_mem
    (prefixF_sub_parity_mem ρ c cs hρ hcs hc hadj)
    ((defectSpan ρ (cs ++ [c])).smul_mem (c * (ρ - 1) / (c - d))
      (defect_mem_append_span ρ c cs))
  convert h using 1
  rw [outerRemainder_eq_prefixF_sub_defect ρ c d cs hρ hc hcd]
  funext z
  simp only [Pi.sub_apply]
  ring

def baselineQ (ρ : ℝ) (cs : List ℝ) : FunctionSpace :=
  fun z => BinaryTransferAlgebra.prefixQ ρ cs z.val

def baselineR (ρ : ℝ) (cs : List ℝ) : FunctionSpace :=
  fun z => BinaryTransferAlgebra.prefixR ρ cs z.val

private theorem prefixQ_snoc (ρ c z : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hz : z ≠ 0) (hcs : ∀ e ∈ cs, e ≠ 0) :
    BinaryTransferAlgebra.prefixQ ρ (cs ++ [c]) z =
      BinaryTransferAlgebra.appendQ ρ (BinaryTransferAlgebra.prefixQ ρ cs z)
        (BinaryTransferAlgebra.prefixR ρ cs z) c z := by
  rw [BinaryTransferAlgebra.prefixQ_append, BinaryTransferAlgebra.prefixQ_singleton,
    BinaryTransferAlgebra.prefixH_eq_one_add_prefixQ_add_prefixR ρ z cs hρ hz hcs]
  rfl

private theorem prefixR_snoc (ρ c z : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hz : z ≠ 0) (hcs : ∀ e ∈ cs, e ≠ 0) :
    BinaryTransferAlgebra.prefixR ρ (cs ++ [c]) z =
      BinaryTransferAlgebra.appendR ρ (BinaryTransferAlgebra.prefixQ ρ cs z)
        (BinaryTransferAlgebra.prefixR ρ cs z) c z := by
  rw [BinaryTransferAlgebra.prefixR_append, BinaryTransferAlgebra.prefixR_singleton,
    BinaryTransferAlgebra.prefixH_eq_one_add_prefixQ_add_prefixR ρ z cs hρ hz hcs]
  rfl

/-- The outer-peeling identity evaluated on the actual ordered baseline. -/
theorem baselineQ_outer_peel (ρ c d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d) :
    baselineQ ρ (cs ++ [c, d]) -
      (fun z => (d * (1 + ρ * c * z.val) / (c - d)) * defect ρ (cs ++ [c]) d z) =
      blockQ ρ d * outerRemainder ρ cs c d := by
  funext z
  change BinaryTransferAlgebra.prefixQ ρ (cs ++ [c, d]) z.val -
    (d * (1 + ρ * c * z.val) / (c - d)) *
      BinaryTransferAlgebra.moveFirst ρ (cs ++ [c]) d z.val = _
  unfold BinaryTransferAlgebra.moveFirst
  rw [prefixQ_snoc ρ c z.val cs hρ z.property hcs,
    prefixR_snoc ρ c z.val cs hρ z.property hcs,
    BinaryTransferAlgebra.prefixQ_append,
    BinaryTransferAlgebra.prefixH_eq_one_add_prefixQ_add_prefixR ρ z.val cs hρ z.property hcs]
  simpa only [BinaryTransferAlgebra.prefixQ, mul_zero, add_zero, Pi.mul_apply,
    blockQ, outerRemainder] using
    BinaryTransferAlgebra.outer_peel_Q ρ (BinaryTransferAlgebra.prefixQ ρ cs z.val)
      (BinaryTransferAlgebra.prefixR ρ cs z.val) c d z.val hρ hc hd z.property hcd

theorem baselineR_outer_peel (ρ c d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d) :
    baselineR ρ (cs ++ [c, d]) -
      (fun z => ((1 + c * z.val) / (c - d)) * defect ρ (cs ++ [c]) d z) =
      blockR ρ d * outerRemainder ρ cs c d := by
  funext z
  change BinaryTransferAlgebra.prefixR ρ (cs ++ [c, d]) z.val -
    ((1 + c * z.val) / (c - d)) *
      BinaryTransferAlgebra.moveFirst ρ (cs ++ [c]) d z.val = _
  unfold BinaryTransferAlgebra.moveFirst
  rw [prefixQ_snoc ρ c z.val cs hρ z.property hcs,
    prefixR_snoc ρ c z.val cs hρ z.property hcs,
    BinaryTransferAlgebra.prefixR_append,
    BinaryTransferAlgebra.prefixH_eq_one_add_prefixQ_add_prefixR ρ z.val cs hρ z.property hcs]
  simpa only [BinaryTransferAlgebra.prefixR, mul_zero, add_zero, Pi.mul_apply,
    blockR, outerRemainder] using
    BinaryTransferAlgebra.outer_peel_R ρ (BinaryTransferAlgebra.prefixQ ρ cs z.val)
      (BinaryTransferAlgebra.prefixR ρ cs z.val) c d z.val hρ hc hd z.property hcd

theorem baselineQ_two_last_sub_parity_mem (ρ c d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y)) :
    baselineQ ρ (cs ++ [c, d]) - ((cs.length % 2 : ℕ) : ℝ) • blockQ ρ d ∈
      pairedSpan ρ (cs ++ [c, d]) := by
  have hspan : defectSpan ρ (cs ++ [c]) ≤ defectSpan ρ (cs ++ [c, d]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      defectSpan_le_append ρ (cs ++ [c]) [d]
  have hrem := blockQ_mul_mem_pairedSpan ρ d (cs ++ [c, d])
    (hspan (outerRemainder_sub_parity_mem ρ c d cs hρ hcs hc hcd hadj))
  have hlast : defect ρ (cs ++ [c]) d ∈ defectSpan ρ (cs ++ [c, d]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      defect_mem_append_span ρ d (cs ++ [c])
  have houter : (fun z => (d * (1 + ρ * c * z.val) / (c - d)) *
      defect ρ (cs ++ [c]) d z) ∈ pairedSpan ρ (cs ++ [c, d]) := by
    convert affine_mul_mem_pairedSpan ρ (d / (c - d))
      (d * ρ * c / (c - d)) (cs ++ [c, d]) hlast using 1
    funext z
    simp only [div_eq_mul_inv]
    ring
  have hsum := (pairedSpan ρ (cs ++ [c, d])).add_mem houter hrem
  convert hsum using 1
  have hp := baselineQ_outer_peel ρ c d cs hρ hcs hc hd hcd
  funext z
  have hpz := congr_fun hp z
  simp only [Pi.sub_apply, Pi.mul_apply] at hpz
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    constant]
  rw [sub_eq_iff_eq_add.mp hpz]
  ring

theorem baselineR_two_last_sub_parity_mem (ρ c d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d)
    (hadj : (cs ++ [c]).IsChain (fun x y : ℝ => x ≠ y)) :
    baselineR ρ (cs ++ [c, d]) - ((cs.length % 2 : ℕ) : ℝ) • blockR ρ d ∈
      pairedSpan ρ (cs ++ [c, d]) := by
  have hspan : defectSpan ρ (cs ++ [c]) ≤ defectSpan ρ (cs ++ [c, d]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      defectSpan_le_append ρ (cs ++ [c]) [d]
  have hrem := blockR_mul_mem_pairedSpan ρ d (cs ++ [c, d])
    (hspan (outerRemainder_sub_parity_mem ρ c d cs hρ hcs hc hcd hadj))
  have hlast : defect ρ (cs ++ [c]) d ∈ defectSpan ρ (cs ++ [c, d]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      defect_mem_append_span ρ d (cs ++ [c])
  have houter : (fun z => ((1 + c * z.val) / (c - d)) *
      defect ρ (cs ++ [c]) d z) ∈ pairedSpan ρ (cs ++ [c, d]) := by
    convert affine_mul_mem_pairedSpan ρ (1 / (c - d))
      (c / (c - d)) (cs ++ [c, d]) hlast using 1
    funext z
    simp only [div_eq_mul_inv]
    ring
  have hsum := (pairedSpan ρ (cs ++ [c, d])).add_mem houter hrem
  convert hsum using 1
  have hp := baselineR_outer_peel ρ c d cs hρ hcs hc hd hcd
  funext z
  have hpz := congr_fun hp z
  simp only [Pi.sub_apply, Pi.mul_apply] at hpz
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    constant]
  rw [sub_eq_iff_eq_add.mp hpz]
  ring

/-- For every nonempty coefficient list, the baseline `Q` remainder is zero
at even length and the final block `Q` at odd length, in the paired real span. -/
theorem baselineQ_sub_parity_mem (ρ d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hd : d ≠ 0)
    (hadj : (cs ++ [d]).IsChain (fun x y : ℝ => x ≠ y)) :
    baselineQ ρ (cs ++ [d]) - (((cs.length + 1) % 2 : ℕ) : ℝ) • blockQ ρ d ∈
      pairedSpan ρ (cs ++ [d]) := by
  induction cs using List.reverseRecOn with
  | nil =>
    have hb : baselineQ ρ [d] = blockQ ρ d := by
      funext z
      exact BinaryTransferAlgebra.prefixQ_singleton ρ d z.val
    simpa only [List.length_nil, zero_add, show (1 : ℕ) % 2 = 1 from rfl, Nat.cast_one,
      List.nil_append, hb, one_smul, sub_self] using (pairedSpan ρ [d]).zero_mem
  | append_singleton cs c _ih =>
    have hc : c ≠ 0 := hcs c (by simp)
    have hcs' : ∀ e ∈ cs, e ≠ 0 := fun e he => hcs e (by simp [he])
    have hchain := List.isChain_append_cons_cons.mp
      (show (cs ++ c :: d :: []).IsChain (fun x y : ℝ => x ≠ y) from
        by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hadj)
    have hparity : (cs.length + 1 + 1) % 2 = cs.length % 2 := by omega
    simpa only [List.length_append, List.length_singleton, hparity,
      List.append_assoc, List.cons_append, List.nil_append] using
      baselineQ_two_last_sub_parity_mem ρ c d cs hρ hcs' hc hd hchain.2.1 hchain.1

/-- The analogous exact baseline `R` remainder. -/
theorem baselineR_sub_parity_mem (ρ d : ℝ) (cs : List ℝ) (hρ : ρ ≠ 1)
    (hcs : ∀ e ∈ cs, e ≠ 0) (hd : d ≠ 0)
    (hadj : (cs ++ [d]).IsChain (fun x y : ℝ => x ≠ y)) :
    baselineR ρ (cs ++ [d]) - (((cs.length + 1) % 2 : ℕ) : ℝ) • blockR ρ d ∈
      pairedSpan ρ (cs ++ [d]) := by
  induction cs using List.reverseRecOn with
  | nil =>
    have hb : baselineR ρ [d] = blockR ρ d := by
      funext z
      exact BinaryTransferAlgebra.prefixR_singleton ρ d z.val
    simpa only [List.length_nil, zero_add, show (1 : ℕ) % 2 = 1 from rfl, Nat.cast_one,
      List.nil_append, hb, one_smul, sub_self] using (pairedSpan ρ [d]).zero_mem
  | append_singleton cs c _ih =>
    have hc : c ≠ 0 := hcs c (by simp)
    have hcs' : ∀ e ∈ cs, e ≠ 0 := fun e he => hcs e (by simp [he])
    have hchain := List.isChain_append_cons_cons.mp
      (show (cs ++ c :: d :: []).IsChain (fun x y : ℝ => x ≠ y) from
        by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hadj)
    have hparity : (cs.length + 1 + 1) % 2 = cs.length % 2 := by omega
    simpa only [List.length_append, List.length_singleton, hparity,
      List.append_assoc, List.cons_append, List.nil_append] using
      baselineR_two_last_sub_parity_mem ρ c d cs hρ hcs' hc hd hchain.2.1 hchain.1

end PanelMoments.BinaryTransferSpan
