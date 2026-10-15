import PanelMoments.SourceHomogeneous
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

/-!
# Polynomial clearing of the actual homogeneous source kernels

For three states, the row forms and the product of the three row forms are
polynomials in the actual homogeneous coordinates. Multiplying each kernel
entry by that product gives the polynomial matrix defined below. Evaluation
commutes with the ordered matrix products, using the canonical tail time
`u.val + 2`.

The empty, singleton, and reduced source vectors share one common denominator:
the product of the block denominators over all distinct tail slots. In the
singleton case the shared block is absent from the ordered tail word, so no
block denominator is repeated. These are identities for the existing source
vectors; no residue or independence assertion is made.
-/

namespace PanelMoments.SourcePolynomialKernels

open scoped BigOperators
open SourceHomogeneous SourceTransferOrders SourceNewIndices

noncomputable section

abbrev Poly := MvPolynomial (Fin 3) ℝ

def rowPolynomial (A : Table 2) (t : ℕ) (a : State 2) : Poly :=
  ∑ i : State 2, MvPolynomial.C (A t a i) * MvPolynomial.X i

def blockDenominator (A : Table 2) (t : ℕ) : Poly :=
  ∏ a : State 2, rowPolynomial A t a

def clearedKernel (A : Table 2) (t : ℕ) : Matrix (State 2) (State 2) Poly :=
  Matrix.of (fun a i => MvPolynomial.C (A t a i) * MvPolynomial.X i *
    ∏ b ∈ Finset.univ.erase a, rowPolynomial A t b)

def evalMatrix (X : State 2 → ℝ) :
    Matrix (State 2) (State 2) Poly →+* Matrix (State 2) (State 2) ℝ :=
  (MvPolynomial.eval X).mapMatrix

@[simp] theorem evalMatrix_apply (X : State 2 → ℝ)
    (M : Matrix (State 2) (State 2) Poly) (a i : State 2) :
    evalMatrix X M a i = MvPolynomial.eval X (M a i) := rfl

theorem rowPolynomial_eval (A : Table 2) (X : State 2 → ℝ) (t : ℕ) (a : State 2) :
    MvPolynomial.eval X (rowPolynomial A t a) = rowForm A X t a := by
  simp only [rowPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, rowForm]

theorem blockDenominator_eval (A : Table 2) (X : State 2 → ℝ) (t : ℕ) :
    MvPolynomial.eval X (blockDenominator A t) = ∏ a : State 2, rowForm A X t a := by
  simp only [blockDenominator, map_prod, rowPolynomial_eval]

theorem blockDenominator_eval_pos {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) :
    0 < MvPolynomial.eval X (blockDenominator A t) := by
  rw [blockDenominator_eval]
  exact Finset.prod_pos (fun a _ => rowForm_pos hA hX t a)

/-- Denominator clearing holds wherever the actual row forms are nonzero. -/
theorem clearedKernel_eval_of_nonzero (A : Table 2) (X : State 2 → ℝ) (t : ℕ)
    (hL : ∀ a, rowForm A X t a ≠ 0) :
    evalMatrix X (clearedKernel A t) =
      MvPolynomial.eval X (blockDenominator A t) • kernel A X t := by
  ext a i
  simp only [evalMatrix_apply, clearedKernel, Matrix.of_apply, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, rowPolynomial_eval,
    Matrix.smul_apply, smul_eq_mul, blockDenominator_eval, kernel, Matrix.of_apply]
  rw [← Finset.mul_prod_erase Finset.univ (fun b => rowForm A X t b) (Finset.mem_univ a)]
  field_simp [hL a]

theorem clearedKernel_eval {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) :
    evalMatrix X (clearedKernel A t) =
      MvPolynomial.eval X (blockDenominator A t) • kernel A X t :=
  clearedKernel_eval_of_nonzero A X t (fun a => ne_of_gt (rowForm_pos hA hX t a))

theorem clearedKernel_entry_eval {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : ℕ) (a i : State 2) :
    MvPolynomial.eval X (clearedKernel A t a i) =
      MvPolynomial.eval X (blockDenominator A t) * kernel A X t a i :=
  congrArg (fun M => M a i) (clearedKernel_eval hA hX t)

def wordDenominator {N : ℕ} (A : Table 2) (w : List (Fin N)) : Poly :=
  (w.map (fun u => blockDenominator A (u.val + 2))).prod

def clearedWordProduct {N : ℕ} (A : Table 2) (w : List (Fin N)) :
    Matrix (State 2) (State 2) Poly :=
  (w.map (fun u => clearedKernel A (u.val + 2))).prod

/-- Polynomial evaluation preserves the actual order of every matrix factor. -/
theorem clearedWordProduct_eval_of_nonzero {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (w : List (Fin N)) (hL : ∀ u ∈ w, ∀ a, rowForm A X (u.val + 2) a ≠ 0) :
    evalMatrix X (clearedWordProduct A w) =
      MvPolynomial.eval X (wordDenominator A w) • homogeneousWordProduct A X w := by
  revert hL
  induction w with
  | nil =>
      intro _
      simp [clearedWordProduct, wordDenominator, homogeneousWordProduct]
  | cons u w ih =>
      intro hL
      have hu := clearedKernel_eval_of_nonzero A X (u.val + 2)
        (hL u (by simp))
      have hw := ih (fun v hv => hL v (by simp [hv]))
      change evalMatrix X (clearedKernel A (u.val + 2) * clearedWordProduct A w) =
        MvPolynomial.eval X (blockDenominator A (u.val + 2) * wordDenominator A w) •
          (kernel A X (u.val + 2) * homogeneousWordProduct A X w)
      rw [map_mul, hu, hw, map_mul, smul_mul_smul_comm]

theorem clearedWordProduct_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (w : List (Fin N)) :
    evalMatrix X (clearedWordProduct A w) =
      MvPolynomial.eval X (wordDenominator A w) • homogeneousWordProduct A X w :=
  clearedWordProduct_eval_of_nonzero A X w
    (fun u _ a => ne_of_gt (rowForm_pos hA hX (u.val + 2) a))

theorem clearedWordProduct_entry_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (w : List (Fin N)) (a i : State 2) :
    MvPolynomial.eval X (clearedWordProduct A w a i) =
      MvPolynomial.eval X (wordDenominator A w) * homogeneousWordProduct A X w a i :=
  congrArg (fun M => M a i) (clearedWordProduct_eval hA hX w)

/-- The evaluated product is also the actual model product at normalized effects. -/
theorem clearedWordProduct_eval_actual {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (w : List (Fin N)) :
    evalMatrix X (clearedWordProduct A w) =
      MvPolynomial.eval X (wordDenominator A w) • wordProduct A (normalizedEffects X) w := by
  rw [clearedWordProduct_eval hA hX, homogeneousWordProduct_eq_wordProduct hA hX]

/-- Each distinct tail block contributes exactly its three row forms. -/
def tailDenominator {N : ℕ} (A : Table 2) : Poly :=
  ∏ u : Fin N, blockDenominator A (u.val + 2)

def tailDenominatorExcept {N : ℕ} (A : Table 2) (t : Fin N) : Poly :=
  ∏ u ∈ Finset.univ.erase t, blockDenominator A (u.val + 2)

theorem emptyWord_toFinset {N : ℕ} (s : Fin N) : (emptyWord s).toFinset = Finset.univ := by
  ext u
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_emptyWord s u

theorem singletonWord_toFinset {N : ℕ} (t : Fin N) (s : {s : Fin N // s ≠ t}) :
    (singletonWord t s.val).toFinset = Finset.univ.erase t := by
  ext u
  simp only [List.mem_toFinset, mem_singletonWord t s.val u s.property,
    Finset.mem_erase, Finset.mem_univ, and_true]

theorem wordDenominator_empty {N : ℕ} (A : Table 2) (s : Fin N) :
    wordDenominator A (emptyWord s) = tailDenominator (N := N) A := by
  rw [wordDenominator, ← List.prod_toFinset _ (emptyWord_nodup s), emptyWord_toFinset]
  rfl

theorem wordDenominator_singleton {N : ℕ} (A : Table 2) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) :
    wordDenominator A (singletonWord t s.val) = tailDenominatorExcept A t := by
  rw [wordDenominator, ← List.prod_toFinset _ (singletonWord_nodup t s.val),
    singletonWord_toFinset t s]
  rfl

theorem blockDenominator_mul_except {N : ℕ} (A : Table 2) (t : Fin N) :
    blockDenominator A (t.val + 2) * tailDenominatorExcept A t =
      tailDenominator (N := N) A :=
  Finset.mul_prod_erase Finset.univ (fun u : Fin N => blockDenominator A (u.val + 2))
    (Finset.mem_univ t)

theorem blockDenominator_mul_singleton {N : ℕ} (A : Table 2) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) :
    blockDenominator A (t.val + 2) * wordDenominator A (singletonWord t s.val) =
      tailDenominator (N := N) A := by
  rw [wordDenominator_singleton, blockDenominator_mul_except]

theorem tailDenominator_eval_pos {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) :
    0 < MvPolynomial.eval X (tailDenominator (N := N) A) := by
  simp only [tailDenominator, map_prod]
  exact Finset.prod_pos (fun u _ => blockDenominator_eval_pos hA hX (u.val + 2))

def clearedEmptyVector {N : ℕ} (A : Table 2) (s : Fin N) (a c : State 2) : Poly :=
  MvPolynomial.X a * (tailDenominator (N := N) A * (if a = c then 1 else 0) -
    clearedWordProduct A (emptyWord s) a c)

def clearedSingletonVector {N : ℕ} (A : Table 2) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (a b c : State 2) : Poly :=
  MvPolynomial.X a * clearedKernel A (t.val + 2) a b *
    (wordDenominator A (singletonWord t s.val) * (if b = c then 1 else 0) -
      clearedWordProduct A (singletonWord t s.val) b c)

def clearedSingleBlockVector {N : ℕ} (A : Table 2) (s : Fin N) (a c : State 2) : Poly :=
  MvPolynomial.X a * tailDenominatorExcept A s *
    (blockDenominator A (s.val + 2) * (if a = c then 1 else 0) -
      clearedKernel A (s.val + 2) a c)

theorem clearedEmptyVector_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (s : Fin N) (a c : State 2) :
    MvPolynomial.eval X (clearedEmptyVector A s a c) =
      MvPolynomial.eval X (tailDenominator (N := N) A) * emptyVector A X s a c := by
  simp only [clearedEmptyVector, map_mul, map_sub, MvPolynomial.eval_X, apply_ite,
    map_one, map_zero, clearedWordProduct_entry_eval hA hX, wordDenominator_empty, emptyVector]
  split_ifs <;> ring

theorem clearedSingletonVector_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (a b c : State 2) :
    MvPolynomial.eval X (clearedSingletonVector A t s a b c) =
      MvPolynomial.eval X (tailDenominator (N := N) A) * singletonVector A X t s a b c := by
  rw [← blockDenominator_mul_singleton A t s]
  simp only [clearedSingletonVector, map_mul, map_sub, MvPolynomial.eval_X, apply_ite,
    map_one, map_zero, clearedKernel_entry_eval hA hX,
    clearedWordProduct_entry_eval hA hX, singletonVector]
  split_ifs <;> ring

theorem clearedSingleBlockVector_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (s : Fin N) (a c : State 2) :
    MvPolynomial.eval X (clearedSingleBlockVector A s a c) =
      MvPolynomial.eval X (tailDenominator (N := N) A) * singleBlockVector A X s a c := by
  rw [← blockDenominator_mul_except A s]
  simp only [clearedSingleBlockVector, map_mul, map_sub, MvPolynomial.eval_X, apply_ite,
    map_one, map_zero, clearedKernel_entry_eval hA hX, singleBlockVector]
  split_ifs <;> ring

def clearedSourceColumn {N : ℕ} (A : Table 2) : NewParameter N → State 2 → Poly
  | Sum.inl p => clearedEmptyVector A p.1 p.2
  | Sum.inr p => clearedSingletonVector A p.1 p.2.1 p.2.2.2 p.2.2.1

def clearedReducedColumn {N : ℕ} (A : Table 2) : NewParameter N → State 2 → Poly
  | Sum.inl p => clearedSingleBlockVector A p.1 p.2
  | Sum.inr p => clearedSingletonVector A p.1 p.2.1 p.2.2.2 p.2.2.1

theorem clearedSourceColumn_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (p : NewParameter N) (c : State 2) :
    MvPolynomial.eval X (clearedSourceColumn A p c) =
      MvPolynomial.eval X (tailDenominator (N := N) A) * SourceHomogeneous.sourceColumn A X p c := by
  cases p with
  | inl p => exact clearedEmptyVector_eval hA hX p.1 p.2 c
  | inr p => exact clearedSingletonVector_eval hA hX p.1 p.2.1 p.2.2.2 p.2.2.1 c

theorem clearedReducedColumn_eval {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hA : PositiveTable A) (hX : PositiveCoordinates X) (p : NewParameter N) (c : State 2) :
    MvPolynomial.eval X (clearedReducedColumn A p c) =
      MvPolynomial.eval X (tailDenominator (N := N) A) * SourceHomogeneous.reducedColumn A X p c := by
  cases p with
  | inl p => exact clearedSingleBlockVector_eval hA hX p.1 p.2 c
  | inr p => exact clearedSingletonVector_eval hA hX p.1 p.2.1 p.2.2.2 p.2.2.1 c

end

end PanelMoments.SourcePolynomialKernels
