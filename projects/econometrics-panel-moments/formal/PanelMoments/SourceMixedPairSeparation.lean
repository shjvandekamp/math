import PanelMoments.SourceMixedPairDeterminant
import PanelMoments.SourcePolynomialCriterion
import Mathlib.Algebra.Polynomial.Coeff

set_option autoImplicit false

/-!
# Polynomial observations at a coalesced pair of source blocks

The observation is the coefficient of ε after the actual substitution
`X = P + ε e₀`.  It therefore applies to polynomial identities, even when
the pair point is outside the positive domain of the original kernels.

Two coalesced cleared-kernel factors make this observation vanish on every
existing cleared reduced source column.  The special-jet numerators use the
same polynomial kernel products; they are not independent surrogate columns.

The final theorem forces all six constant coefficients to vanish whenever a
combination of the actual off-diagonal special jets lies in the actual
coalesced reduced source span.  Its assumptions are explicit local geometric
units.  Independence of the leading family is not required, and independence
of the full equation (24) family is not asserted.
-/

namespace PanelMoments.SourceMixedPairSeparation

open scoped BigOperators
open SourceHomogeneous SourceRelativeTimeJet SourceLocalJetAlgebra SourceMixedPoleJet
open SourceMixedPairDeterminant SourcePolynomialKernels SourceTransferOrders SourceNewIndices

noncomputable section

/-- The exact polynomial substitution along the first coordinate direction. -/
def affineSubstitution (P : State 2 → ℝ) : Poly →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (P i) + if i = 0 then Polynomial.X else 0)

/-- A constant real linear observation, rather than pointwise rational scaling. -/
def firstCoeff (P : State 2 → ℝ) : Poly →ₗ[ℝ] ℝ :=
  (Polynomial.lcoeff ℝ 1).comp (affineSubstitution P).toLinearMap

private theorem affineSubstitution_coeff_zero (P : State 2 → ℝ) (p : Poly) :
    (affineSubstitution P p).coeff 0 = MvPolynomial.eval P p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [affineSubstitution]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.mul_coeff_zero, hp, MvPolynomial.eval_X]
      by_cases hi : i = 0 <;> simp [affineSubstitution, hi]

@[simp] theorem firstCoeff_C (P : State 2 → ℝ) (c : ℝ) :
    firstCoeff P (MvPolynomial.C c) = 0 := by
  simp [firstCoeff, affineSubstitution]

@[simp] theorem firstCoeff_X (P : State 2 → ℝ) (i : State 2) :
    firstCoeff P (MvPolynomial.X i) = if i = 0 then 1 else 0 := by
  by_cases hi : i = 0 <;> simp [firstCoeff, affineSubstitution, hi]

theorem firstCoeff_mul (P : State 2 → ℝ) (p q : Poly) :
    firstCoeff P (p * q) = MvPolynomial.eval P p * firstCoeff P q +
      firstCoeff P p * MvPolynomial.eval P q := by
  change (affineSubstitution P (p * q)).coeff 1 = _
  rw [map_mul, Polynomial.mul_coeff_one, affineSubstitution_coeff_zero,
    affineSubstitution_coeff_zero]
  rfl

/-- The coefficient observation is the actual derivative along `P + ε e₀`. -/
theorem firstCoeff_hasDerivAt (P : State 2 → ℝ) (p : Poly) :
    HasDerivAt (fun ε : ℝ => MvPolynomial.eval (affinePoint P ![1, 0, 0] ε) p)
      (firstCoeff P p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (0 : ℝ) c
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp =>
      have hi : HasDerivAt (fun ε : ℝ => affinePoint P ![1, 0, 0] ε i)
          (if i = 0 then 1 else 0) 0 := by
        have he : (![1, 0, 0] : State 2 → ℝ) i = if i = 0 then 1 else 0 := by
          fin_cases i <;> simp
        simpa [affinePoint, he] using
          ((hasDerivAt_id (0 : ℝ)).mul_const (![1, 0, 0] i)).const_add (P i)
      convert hp.fun_mul hi using 1
      · funext ε
        simp only [map_mul, MvPolynomial.eval_X]
      · simp only [firstCoeff_mul, firstCoeff_X, MvPolynomial.eval_X,
          affinePoint_zero]
        ring

private def ZeroJet (P : State 2 → ℝ) (p : Poly) : Prop :=
  MvPolynomial.eval P p = 0 ∧ firstCoeff P p = 0

private theorem zeroJet_sub {P : State 2 → ℝ} {p q : Poly}
    (hp : ZeroJet P p) (hq : ZeroJet P q) : ZeroJet P (p - q) := by
  simp [ZeroJet, map_sub, hp.1, hp.2, hq.1, hq.2]

private theorem zeroJet_mul_left {P : State 2 → ℝ} {p : Poly}
    (hp : ZeroJet P p) (q : Poly) : ZeroJet P (p * q) := by
  simp [ZeroJet, map_mul, firstCoeff_mul, hp.1, hp.2]

private theorem zeroJet_mul_right {P : State 2 → ℝ} {q : Poly}
    (hq : ZeroJet P q) (p : Poly) : ZeroJet P (p * q) := by
  rw [mul_comm]
  exact zeroJet_mul_left hq p

private theorem zeroJet_mul_of_values {P : State 2 → ℝ} {p q : Poly}
    (hp : MvPolynomial.eval P p = 0) (hq : MvPolynomial.eval P q = 0) :
    ZeroJet P (p * q) := by
  simp [ZeroJet, map_mul, firstCoeff_mul, hp, hq]

private theorem zeroJet_sum {ι : Type*} (s : Finset ι) (P : State 2 → ℝ)
    (f : ι → Poly) (h : ∀ i ∈ s, ZeroJet P (f i)) : ZeroJet P (∑ i ∈ s, f i) := by
  constructor
  · rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => (h i hi).1)
  · rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => (h i hi).2)

private theorem zeroJet_prod_of_mem {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : State 2 → ℝ) (f : ι → Poly) (i : ι)
    (hi : i ∈ s) (hf : ZeroJet P (f i)) : ZeroJet P (∏ j ∈ s, f j) := by
  rw [← Finset.mul_prod_erase s f hi]
  exact zeroJet_mul_left hf _

private theorem blockDenominator_zeroJet (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (a b : State 2) (hab : a ≠ b)
    (ha : rowForm A P t a = 0) (hb : rowForm A P t b = 0) :
    ZeroJet P (blockDenominator A t) := by
  have hbmem : b ∈ Finset.univ.erase a := by simp [Ne.symm hab]
  unfold blockDenominator
  rw [← Finset.mul_prod_erase Finset.univ (rowPolynomial A t) (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) (rowPolynomial A t) hbmem,
    ← mul_assoc]
  apply zeroJet_mul_left
  exact zeroJet_mul_of_values (by simpa only [rowPolynomial_eval] using ha)
    (by simpa only [rowPolynomial_eval] using hb)

/-- Every entry of the actual cleared kernel vanishes at a mixed pair point. -/
theorem clearedKernel_eval_eq_zero_of_pair (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (a b : State 2) (hab : a ≠ b)
    (ha : rowForm A P t a = 0) (hb : rowForm A P t b = 0) :
    evalMatrix P (clearedKernel A t) = 0 := by
  ext r c
  simp only [evalMatrix_apply, clearedKernel, Matrix.of_apply, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, rowPolynomial_eval, Matrix.zero_apply]
  suffices (∏ k ∈ Finset.univ.erase r, rowForm A P t k) = 0 by rw [this, mul_zero]
  by_cases hr : r = a
  · subst r
    exact Finset.prod_eq_zero (by simp [Ne.symm hab]) hb
  · exact Finset.prod_eq_zero (by simp [Ne.symm hr]) ha

private theorem matrix_zeroJet_mul_right (P : State 2 → ℝ)
    (M N : Matrix (State 2) (State 2) Poly)
    (hN : ∀ a b, ZeroJet P (N a b)) : ∀ a b, ZeroJet P ((M * N) a b) := by
  intro a b
  exact zeroJet_sum Finset.univ P _ (fun k _ => zeroJet_mul_right (hN k b) (M a k))

private theorem matrix_zeroJet_mul_of_values (P : State 2 → ℝ)
    (M N : Matrix (State 2) (State 2) Poly)
    (hM : evalMatrix P M = 0) (hN : evalMatrix P N = 0) :
    ∀ a b, ZeroJet P ((M * N) a b) := by
  intro a b
  exact zeroJet_sum Finset.univ P _ (fun k _ => zeroJet_mul_of_values
    (congrArg (fun B => B a k) hM) (congrArg (fun B => B k b) hN))

private theorem word_eval_zero_of_mem {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (w : List (Fin N)) (u : Fin N) (hu : u ∈ w)
    (hK : evalMatrix P (clearedKernel A (u.val + 2)) = 0) :
    evalMatrix P (clearedWordProduct A w) = 0 := by
  induction w with
  | nil => simp at hu
  | cons x w ih =>
      change evalMatrix P (clearedKernel A (x.val + 2) * clearedWordProduct A w) = 0
      rw [map_mul]
      rcases List.mem_cons.mp hu with h | h
      · subst x
        rw [hK, zero_mul]
      · rw [ih h, mul_zero]

private theorem word_zeroJet_of_two {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (w : List (Fin N)) (u v : Fin N) (huv : u ≠ v) (hu : u ∈ w) (hv : v ∈ w)
    (hKu : evalMatrix P (clearedKernel A (u.val + 2)) = 0)
    (hKv : evalMatrix P (clearedKernel A (v.val + 2)) = 0) :
    ∀ a b, ZeroJet P (clearedWordProduct A w a b) := by
  induction w with
  | nil => simp at hu
  | cons x w ih =>
      change ∀ a b, ZeroJet P ((clearedKernel A (x.val + 2) * clearedWordProduct A w) a b)
      by_cases hxu : x = u
      · subst x
        apply matrix_zeroJet_mul_of_values P _ _ hKu
        exact word_eval_zero_of_mem A P w v (by simpa [Ne.symm huv] using hv) hKv
      by_cases hxv : x = v
      · subst x
        apply matrix_zeroJet_mul_of_values P _ _ hKv
        exact word_eval_zero_of_mem A P w u (by simpa [huv] using hu) hKu
      apply matrix_zeroJet_mul_right P _ _
      exact ih (by simpa [Ne.symm hxu] using hu) (by simpa [Ne.symm hxv] using hv)

private theorem wordDenominator_zeroJet_of_mem {N : ℕ} (A : Table 2)
    (P : State 2 → ℝ) (w : List (Fin N)) (u : Fin N) (hu : u ∈ w)
    (hD : ZeroJet P (blockDenominator A (u.val + 2))) :
    ZeroJet P (wordDenominator A w) := by
  induction w with
  | nil => simp at hu
  | cons x w ih =>
      change ZeroJet P (blockDenominator A (x.val + 2) * wordDenominator A w)
      rcases List.mem_cons.mp hu with h | h
      · subst x
        exact zeroJet_mul_left hD _
      · exact zeroJet_mul_right (ih h) _

private theorem singleton_zeroJet_of_coalescence {N : ℕ} (A : Table 2)
    (P : State 2 → ℝ) (u v : Fin N) (huv : u ≠ v)
    (hKu : evalMatrix P (clearedKernel A (u.val + 2)) = 0)
    (hKv : evalMatrix P (clearedKernel A (v.val + 2)) = 0)
    (hDu : ZeroJet P (blockDenominator A (u.val + 2)))
    (hDv : ZeroJet P (blockDenominator A (v.val + 2)))
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b c : State 2) :
    ZeroJet P (clearedSingletonVector A t s a b c) := by
  let w := singletonWord t s.val
  have hmem (x : Fin N) (hx : x ≠ t) : x ∈ w :=
    (mem_singletonWord t s.val x s.property).mpr hx
  unfold clearedSingletonVector
  by_cases htu : t = u
  · subst t
    have hv : v ∈ w := hmem v (Ne.symm huv)
    apply zeroJet_mul_of_values
    · simp only [map_mul]
      rw [show MvPolynomial.eval P (clearedKernel A (u.val + 2) a b) = 0 from
        congrArg (fun M => M a b) hKu, mul_zero]
    · have hd := (wordDenominator_zeroJet_of_mem A P w v hv hDv).1
      have hw := congrArg (fun M => M b c) (word_eval_zero_of_mem A P w v hv hKv)
      change MvPolynomial.eval P (clearedWordProduct A w b c) = 0 at hw
      change MvPolynomial.eval P
        (wordDenominator A w * (if b = c then 1 else 0) - clearedWordProduct A w b c) = 0
      simp only [map_sub, map_mul, hd, zero_mul, sub_zero, hw]
  by_cases htv : t = v
  · subst t
    have hu : u ∈ w := hmem u huv
    apply zeroJet_mul_of_values
    · simp only [map_mul]
      rw [show MvPolynomial.eval P (clearedKernel A (v.val + 2) a b) = 0 from
        congrArg (fun M => M a b) hKv, mul_zero]
    · have hd := (wordDenominator_zeroJet_of_mem A P w u hu hDu).1
      have hw := congrArg (fun M => M b c) (word_eval_zero_of_mem A P w u hu hKu)
      change MvPolynomial.eval P (clearedWordProduct A w b c) = 0 at hw
      change MvPolynomial.eval P
        (wordDenominator A w * (if b = c then 1 else 0) - clearedWordProduct A w b c) = 0
      simp only [map_sub, map_mul, hd, zero_mul, sub_zero, hw]
  apply zeroJet_mul_right
  apply zeroJet_sub
  · exact zeroJet_mul_left
      (wordDenominator_zeroJet_of_mem A P w u (hmem u (Ne.symm htu)) hDu) _
  · exact word_zeroJet_of_two A P w u v huv
      (hmem u (Ne.symm htu)) (hmem v (Ne.symm htv)) hKu hKv b c

/-- Every existing reduced source numerator has zero first pair coefficient
when two distinct tail slots carry the same actual table block. This includes
the diagonal shared columns, whose rational functions can have double poles. -/
theorem clearedReducedColumn_firstCoeff_eq_zero {N : ℕ} (A : Table 2)
    (P : State 2 → ℝ) (u v : Fin N) (huv : u ≠ v)
    (hA : A (u.val + 2) = A (v.val + 2)) (a b : State 2) (hab : a ≠ b)
    (ha : rowForm A P (u.val + 2) a = 0)
    (hb : rowForm A P (u.val + 2) b = 0)
    (p : NewParameter N) (j : State 2) :
    firstCoeff P (clearedReducedColumn A p j) = 0 := by
  have hva : rowForm A P (v.val + 2) a = 0 := by simpa only [rowForm, ← hA] using ha
  have hvb : rowForm A P (v.val + 2) b = 0 := by simpa only [rowForm, ← hA] using hb
  have hKu := clearedKernel_eval_eq_zero_of_pair A P (u.val + 2) a b hab ha hb
  have hKv := clearedKernel_eval_eq_zero_of_pair A P (v.val + 2) a b hab hva hvb
  have hDu := blockDenominator_zeroJet A P (u.val + 2) a b hab ha hb
  have hDv := blockDenominator_zeroJet A P (v.val + 2) a b hab hva hvb
  cases p with
  | inl p =>
      apply And.right (a := MvPolynomial.eval P (clearedReducedColumn A (.inl p) j) = 0)
      change ZeroJet P (clearedSingleBlockVector A p.1 p.2 j)
      unfold clearedSingleBlockVector
      apply zeroJet_mul_left
      apply zeroJet_mul_right
      unfold tailDenominatorExcept
      by_cases h : u = p.1
      · exact zeroJet_prod_of_mem _ P _ v (by simp [← h, Ne.symm huv]) hDv
      · exact zeroJet_prod_of_mem _ P _ u (by simp [h]) hDu
  | inr p =>
      exact (singleton_zeroJet_of_coalescence A P u v huv hKu hKv hDu hDv
        p.1 p.2.1 p.2.2.2 p.2.2.1 j).2

private def prefixPolynomial (A : Table 2) (t : ℕ) (a b : State 2) : Poly :=
  MvPolynomial.C (A t a b) * MvPolynomial.X a * MvPolynomial.X b

private def directionPolynomial (A : Table 2) (t : ℕ) (d : State 2 → ℝ)
    (a : State 2) : Poly :=
  ∑ k, MvPolynomial.C (A t a k) * MvPolynomial.X k * MvPolynomial.C (d k)

private def tailPolynomial (A : Table 2) (t : ℕ)
    (M : Matrix (State 2) (State 2) Poly) (b j : State 2) : Poly :=
  ∑ k, MvPolynomial.C (A t b k) * MvPolynomial.X k * M k j

private def directionTailPolynomial (A : Table 2) (t : ℕ) (d : State 2 → ℝ)
    (M : Matrix (State 2) (State 2) Poly) (b j : State 2) : Poly :=
  ∑ k, MvPolynomial.C (A t b k) * MvPolynomial.X k *
    MvPolynomial.C (d k - d b) * M k j

private theorem prefixPolynomial_eval (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (a b : State 2) :
    MvPolynomial.eval P (prefixPolynomial A t a b) = prefixNumerator A P t a b := by
  simp [prefixPolynomial, prefixNumerator]

private theorem directionPolynomial_eval (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (a : State 2) :
    MvPolynomial.eval P (directionPolynomial A t d a) = rowFormJet A P t d a := by
  simp [directionPolynomial, rowFormJet]

private theorem tailPolynomial_eval (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (M : Matrix (State 2) (State 2) Poly) (b j : State 2) :
    MvPolynomial.eval P (tailPolynomial A t M b j) =
      rowTail A P t (evalMatrix P M) b j := by
  simp [tailPolynomial, rowTail]

private theorem directionTailPolynomial_eval (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (M : Matrix (State 2) (State 2) Poly) (b j : State 2) :
    MvPolynomial.eval P (directionTailPolynomial A t d M b j) =
      rowDirectionTail A P t d (evalMatrix P M) b j := by
  simp [directionTailPolynomial, rowDirectionTail]

private def pairNumerator {N : ℕ} (A : Table 2) (t : ℕ) (d : State 2 → ℝ)
    (w : List (Fin N)) (a b j : State 2) : Poly :=
  prefixPolynomial A t a b *
    (wordDenominator A w *
      (MvPolynomial.C (d b) * (if b = j then 1 else 0) * rowPolynomial A t a *
          rowPolynomial A t b ^ 2 -
        directionPolynomial A t d a * (if b = j then 1 else 0) * rowPolynomial A t b ^ 2) +
      directionTailPolynomial A t d (clearedWordProduct A w) b j *
        rowPolynomial A t a * rowPolynomial A t b +
      directionPolynomial A t d a * tailPolynomial A t (clearedWordProduct A w) b j *
        rowPolynomial A t b -
      directionPolynomial A t d b * tailPolynomial A t (clearedWordProduct A w) b j *
        rowPolynomial A t a)

/-- The nonsingular row-form factors left after clearing a selected pair. -/
def remainingSquare (A : Table 2) (t : ℕ) (a b : State 2) : Poly :=
  (∏ c ∈ (Finset.univ.erase a).erase b, rowPolynomial A t c) ^ 2

/-- The actual special jet cleared by the entire distinguished block squared
and the actual ordered tail denominator. -/
def jetNumerator {N : ℕ} (A : Table 2) (t : ℕ) (d : State 2 → ℝ)
    (w : List (Fin N)) (a b j : State 2) : Poly :=
  remainingSquare A t a b * pairNumerator A t d w a b j

private theorem rowTail_smul (A : Table 2) (P : State 2 → ℝ) (t : ℕ)
    (Q : Matrix (State 2) (State 2) ℝ) (r : ℝ) (b j : State 2) :
    rowTail A P t (r • Q) b j = r * rowTail A P t Q b j := by
  simp only [rowTail, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem rowDirectionTail_smul (A : Table 2) (P : State 2 → ℝ) (t : ℕ)
    (d : State 2 → ℝ) (Q : Matrix (State 2) (State 2) ℝ) (r : ℝ) (b j : State 2) :
    rowDirectionTail A P t d (r • Q) b j = r * rowDirectionTail A P t d Q b j := by
  simp only [rowDirectionTail, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem pairNumerator_eval {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N)) (a b j : State 2)
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0) :
    MvPolynomial.eval P (pairNumerator A t d w a b j) =
      MvPolynomial.eval P (wordDenominator A w) *
        clearedSpecial A P t d (homogeneousWordProduct A P w) a b j := by
  simp only [pairNumerator, map_mul, map_add, map_sub, map_pow, apply_ite, map_one,
    map_zero, MvPolynomial.eval_C, prefixPolynomial_eval, directionPolynomial_eval,
    rowPolynomial_eval, tailPolynomial_eval, directionTailPolynomial_eval,
    clearedWordProduct_eval_of_nonzero A P w hL, rowTail_smul, rowDirectionTail_smul,
    clearedSpecial]
  ring

private theorem remainingSquare_mul_pair (A : Table 2) (t : ℕ) (a b : State 2)
    (hab : a ≠ b) :
    remainingSquare A t a b * rowPolynomial A t a ^ 2 * rowPolynomial A t b ^ 2 =
      blockDenominator A t ^ 2 := by
  have hb : b ∈ Finset.univ.erase a := by simp [Ne.symm hab]
  unfold blockDenominator remainingSquare
  rw [← Finset.mul_prod_erase Finset.univ (rowPolynomial A t) (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) (rowPolynomial A t) hb]
  ring

/-- At ordinary points this polynomial is precisely the existing actual jet
times its stated common denominator, with the ordered tail unchanged. -/
theorem jetNumerator_eval {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N)) (a b j : State 2) (hab : a ≠ b)
    (hLa : rowForm A P t a ≠ 0) (hLb : rowForm A P t b ≠ 0)
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0) :
    MvPolynomial.eval P (jetNumerator A t d w a b j) =
      MvPolynomial.eval P (wordDenominator A w) *
        MvPolynomial.eval P (blockDenominator A t) ^ 2 *
        specialJet A P t d (homogeneousWordProduct A P w) a b j := by
  have hd := congrArg (MvPolynomial.eval P) (remainingSquare_mul_pair A t a b hab)
  simp only [map_mul, map_pow, rowPolynomial_eval] at hd
  rw [jetNumerator, map_mul, pairNumerator_eval A P t d w a b j hL,
    ← denominator_mul_specialJet A P t d (homogeneousWordProduct A P w) a b j hLa hLb]
  calc
    _ = MvPolynomial.eval P (wordDenominator A w) *
        (MvPolynomial.eval P (remainingSquare A t a b) * rowForm A P t a ^ 2 *
          rowForm A P t b ^ 2) * specialJet A P t d (homogeneousWordProduct A P w) a b j := by
      ring
    _ = _ := by rw [hd]

private theorem firstCoeff_rowPolynomial (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (a : State 2) : firstCoeff P (rowPolynomial A t a) = A t a 0 := by
  have h : HasDerivAt (fun ε : ℝ => rowForm A (affinePoint P ![1, 0, 0] ε) t a)
      (firstCoeff P (rowPolynomial A t a)) 0 := by
    simpa only [rowPolynomial_eval] using firstCoeff_hasDerivAt P (rowPolynomial A t a)
  simpa [rowForm, Fin.sum_univ_succ] using
    h.unique (rowForm_affine_hasDerivAt A P ![1, 0, 0] t a)

private theorem pairNumerator_pair_value {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N)) (a b j : State 2)
    (ha : rowForm A P t a = 0) (hb : rowForm A P t b = 0) :
    MvPolynomial.eval P (pairNumerator A t d w a b j) = 0 := by
  simp only [pairNumerator, map_mul, map_add, map_sub, map_pow, rowPolynomial_eval,
    ha, hb, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, sub_zero]

private theorem pairNumerator_firstCoeff {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N)) (a b j : State 2)
    (ha : rowForm A P t a = 0) (hb : rowForm A P t b = 0) :
    firstCoeff P (pairNumerator A t d w a b j) =
      prefixNumerator A P t a b * rowTail A P t (evalMatrix P (clearedWordProduct A w)) b j *
        (rowFormJet A P t d a * A t b 0 - rowFormJet A P t d b * A t a 0) := by
  simp only [pairNumerator, pow_two, firstCoeff_mul, map_add, map_sub, map_mul,
    rowPolynomial_eval, ha, hb, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    firstCoeff_rowPolynomial, prefixPolynomial_eval, directionPolynomial_eval,
    tailPolynomial_eval]
  ring

/-- At its own pair point the coefficient is the actual cleared derivative,
scaled by the regular tail denominator and the remaining row form squared. -/
theorem jetNumerator_firstCoeff {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N)) (a b j : State 2)
    (ha : rowForm A P t a = 0) (hb : rowForm A P t b = 0)
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0) :
    firstCoeff P (jetNumerator A t d w a b j) =
      (MvPolynomial.eval P (remainingSquare A t a b) *
        MvPolynomial.eval P (wordDenominator A w)) *
      clearedPairDerivative A P ![1, 0, 0] t d
        (fun ε => homogeneousWordProduct A (affinePoint P ![1, 0, 0] ε) w) a b j := by
  have hder := (clearedSpecial_word_affine_hasDerivAt A P ![1, 0, 0] t d w
    a b j ha hb hL).deriv
  change clearedPairDerivative A P ![1, 0, 0] t d
    (fun ε => homogeneousWordProduct A (affinePoint P ![1, 0, 0] ε) w) a b j = _ at hder
  rw [hder, jetNumerator, firstCoeff_mul, pairNumerator_pair_value A P t d w a b j ha hb,
    mul_zero, add_zero, pairNumerator_firstCoeff A P t d w a b j ha hb,
    clearedWordProduct_eval_of_nonzero A P w hL, rowTail_smul]
  simp [rowForm, Fin.sum_univ_succ]
  ring

/-- A vanishing row form absent from the ordered pair remains squared in the
global numerator and kills its value and first coefficient. -/
theorem jetNumerator_firstCoeff_eq_zero_of_other {N : ℕ} (A : Table 2)
    (P : State 2 → ℝ) (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N))
    (a b k j : State 2) (hka : k ≠ a) (hkb : k ≠ b)
    (hk : rowForm A P t k = 0) :
    firstCoeff P (jetNumerator A t d w a b j) = 0 := by
  have hprod : MvPolynomial.eval P
      (∏ c ∈ (Finset.univ.erase a).erase b, rowPolynomial A t c) = 0 := by
    simp only [map_prod, rowPolynomial_eval]
    exact Finset.prod_eq_zero (by simp [hka, hkb]) hk
  have hs : ZeroJet P (remainingSquare A t a b) := by
    unfold remainingSquare
    rw [pow_two]
    exact zeroJet_mul_of_values hprod hprod
  exact (zeroJet_mul_left hs (pairNumerator A t d w a b j)).2

private theorem wordDenominator_eval_ne_zero {N : ℕ} (A : Table 2)
    (P : State 2 → ℝ) (w : List (Fin N))
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0) :
    MvPolynomial.eval P (wordDenominator A w) ≠ 0 := by
  induction w with
  | nil => simp [wordDenominator]
  | cons u w ih =>
      change MvPolynomial.eval P
        (blockDenominator A (u.val + 2) * wordDenominator A w) ≠ 0
      rw [map_mul, blockDenominator_eval]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun c _ => hL u (by simp) c))
        (ih (fun v hv c => hL v (by simp [hv]) c))

private theorem remainingSquare_comm (A : Table 2) (t : ℕ) (a b : State 2) :
    remainingSquare A t a b = remainingSquare A t b a := by
  simp only [remainingSquare, Finset.erase_right_comm]

/-- The two polynomial numerator observations have a nonzero minor under
actual local coordinate, row-form, entry, and tail-determinant conditions. -/
theorem jetNumerator_pair_minor_ne_zero {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (τ ν : ℝ) (w : List (Fin N)) (a b : State 2)
    (ha : rowForm A P t a = 0) (hb : rowForm A P t b = 0)
    (hrest : ∀ c, c ≠ a → c ≠ b → rowForm A P t c ≠ 0)
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0)
    (hD : ∀ u ∈ w, (Matrix.of (A (u.val + 2))).det ≠ 0)
    (hP : ∀ c, P c ≠ 0) (hm : rowMinor01 A t a b ≠ 0)
    (hab : A t a b ≠ 0) (hba : A t b a ≠ 0) (hντ : ν - τ ≠ 0) :
    minor01 (fun j => firstCoeff P (jetNumerator A t (relativeDirection τ ν) w a b j))
      (fun j => firstCoeff P (jetNumerator A t (relativeDirection τ ν) w b a j)) ≠ 0 := by
  have hs : MvPolynomial.eval P (remainingSquare A t a b) ≠ 0 := by
    simp only [remainingSquare, map_pow, map_prod, rowPolynomial_eval]
    apply pow_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro c hc
    exact hrest c (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
      (Finset.mem_erase.mp hc).1
  have hα := mul_ne_zero hs (wordDenominator_eval_ne_zero A P w hL)
  have hminor := actualWord_pair_minor_ne_zero A P t τ ν w a b ha hb hL hD hP hm hab hba hντ
  have heq : minor01
      (fun j => firstCoeff P (jetNumerator A t (relativeDirection τ ν) w a b j))
      (fun j => firstCoeff P (jetNumerator A t (relativeDirection τ ν) w b a j)) =
      (MvPolynomial.eval P (remainingSquare A t a b) *
        MvPolynomial.eval P (wordDenominator A w)) ^ 2 *
      minor01
        (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν)
          (fun ε => homogeneousWordProduct A (affinePoint P ![1, 0, 0] ε) w) a b)
        (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν)
          (fun ε => homogeneousWordProduct A (affinePoint P ![1, 0, 0] ε) w) b a) := by
    simp only [minor01, jetNumerator_firstCoeff A P t (relativeDirection τ ν) w a b 0 ha hb hL,
      jetNumerator_firstCoeff A P t (relativeDirection τ ν) w a b 1 ha hb hL,
      jetNumerator_firstCoeff A P t (relativeDirection τ ν) w b a 0 hb ha hL,
      jetNumerator_firstCoeff A P t (relativeDirection τ ν) w b a 1 hb ha hL,
      remainingSquare_comm A t b a]
    ring
  rw [heq]
  exact mul_ne_zero (pow_ne_zero 2 hα) hminor

/-- The six ordered off-diagonal state pairs. -/
abbrev MixedPair := {p : State 2 × State 2 // p.1 ≠ p.2}

def reversePair (p : MixedPair) : MixedPair := ⟨(p.val.2, p.val.1), Ne.symm p.property⟩

private theorem pair_ne_reverse (p : MixedPair) : p ≠ reversePair p := by
  intro h
  exact p.property (congrArg (fun r : MixedPair => r.val.1) h)

/-- The actual ascending tail with the two coalesced slots removed. -/
def coalescedTail {N : ℕ} (u v : Fin N) : List (Fin N) :=
  ((Finset.univ.erase u).erase v).sort (· ≤ ·)

/-- The canonical tail and the doubled block give the same denominator as
the existing source columns, including the exact block multiplicity. -/
theorem tailDenominator_coalesced {N : ℕ} (A : Table 2) (u v : Fin N) (huv : u ≠ v)
    (hA : A (u.val + 2) = A (v.val + 2)) :
    tailDenominator (N := N) A =
      wordDenominator A (coalescedTail u v) * blockDenominator A (u.val + 2) ^ 2 := by
  have hw : wordDenominator A (coalescedTail u v) =
      ∏ x ∈ (Finset.univ.erase u).erase v, blockDenominator A (x.val + 2) := by
    unfold wordDenominator coalescedTail
    rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  have hd : blockDenominator A (v.val + 2) = blockDenominator A (u.val + 2) := by
    simp only [blockDenominator, rowPolynomial, ← hA]
  rw [hw]
  unfold tailDenominator
  rw [← Finset.mul_prod_erase Finset.univ (fun x : Fin N => blockDenominator A (x.val + 2))
    (Finset.mem_univ u),
    ← Finset.mul_prod_erase (Finset.univ.erase u)
      (fun x : Fin N => blockDenominator A (x.val + 2)) (by simp [Ne.symm huv] : v ∈ _), hd]
  ring

/-- On the model's positive domain, all six special numerators use precisely
the common clearing factor of the actual reduced source family. -/
theorem jetNumerator_eval_coalesced {N : ℕ} {A : Table 2} {X : State 2 → ℝ}
    (hpos : PositiveTable A) (hX : PositiveCoordinates X) (u v : Fin N) (huv : u ≠ v)
    (hA : A (u.val + 2) = A (v.val + 2)) (d : State 2 → ℝ)
    (a b j : State 2) (hab : a ≠ b) :
    MvPolynomial.eval X (jetNumerator A (u.val + 2) d (coalescedTail u v) a b j) =
      MvPolynomial.eval X (tailDenominator (N := N) A) *
        specialJet A X (u.val + 2) d (homogeneousWordProduct A X (coalescedTail u v)) a b j := by
  rw [jetNumerator_eval A X (u.val + 2) d (coalescedTail u v) a b j hab
    (ne_of_gt (rowForm_pos hpos hX _ a)) (ne_of_gt (rowForm_pos hpos hX _ b))
    (fun x _ c => ne_of_gt (rowForm_pos hpos hX _ c)),
    tailDenominator_coalesced A u v huv hA, map_mul, map_pow]

private theorem firstCoeff_other_pair {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N)) (p r : MixedPair)
    (ha : rowForm A P t p.val.1 = 0) (hb : rowForm A P t p.val.2 = 0)
    (hr : r ≠ p) (hrev : r ≠ reversePair p) (j : State 2) :
    firstCoeff P (jetNumerator A t d w r.val.1 r.val.2 j) = 0 := by
  by_cases hra : r.val.1 = p.val.1
  · have hsb : r.val.2 ≠ p.val.2 := by
      intro h
      exact hr (Subtype.ext (Prod.ext hra h))
    apply jetNumerator_firstCoeff_eq_zero_of_other A P t d w r.val.1 r.val.2 p.val.2 j
    · simpa only [hra] using Ne.symm p.property
    · exact Ne.symm hsb
    · exact hb
  by_cases hsa : r.val.2 = p.val.1
  · have hrb : r.val.1 ≠ p.val.2 := by
      intro h
      exact hrev (Subtype.ext (Prod.ext h hsa))
    apply jetNumerator_firstCoeff_eq_zero_of_other A P t d w r.val.1 r.val.2 p.val.2 j
    · exact Ne.symm hrb
    · simpa only [hsa] using Ne.symm p.property
    · exact hb
  exact jetNumerator_firstCoeff_eq_zero_of_other A P t d w r.val.1 r.val.2 p.val.1 j
    (Ne.symm hra) (Ne.symm hsa) ha

private theorem left_coefficient_eq_zero (r s : State 2 → ℝ) (c d : ℝ)
    (h0 : c * r 0 + d * s 0 = 0) (h1 : c * r 1 + d * s 1 = 0)
    (hm : minor01 r s ≠ 0) : c = 0 := by
  have hc : c * minor01 r s = 0 := by
    calc
      _ = (c * r 0 + d * s 0) * s 1 - (c * r 1 + d * s 1) * s 0 := by
        unfold minor01
        ring
      _ = 0 := by rw [h0, h1]; ring
  exact (mul_eq_zero.mp hc).resolve_right hm

/-- The six actual special-jet numerators are independent modulo the whole
actual coalesced reduced family. Only local geometric units are assumed;
neither old-source independence nor a rank premise is used. -/
theorem six_coefficients_eq_zero_of_relation {N : ℕ} (A : Table 2)
    (u v : Fin N) (huv : u ≠ v) (hA : A (u.val + 2) = A (v.val + 2))
    (τ ν : ℝ) (hντ : ν - τ ≠ 0) (P : MixedPair → State 2 → ℝ)
    (hzero : ∀ p, rowForm A (P p) (u.val + 2) p.val.1 = 0 ∧
      rowForm A (P p) (u.val + 2) p.val.2 = 0)
    (hrest : ∀ p c, c ≠ p.val.1 → c ≠ p.val.2 → rowForm A (P p) (u.val + 2) c ≠ 0)
    (hL : ∀ p x, x ∈ coalescedTail u v → ∀ c, rowForm A (P p) (x.val + 2) c ≠ 0)
    (hD : ∀ x ∈ coalescedTail u v, (Matrix.of (A (x.val + 2))).det ≠ 0)
    (hP : ∀ p c, P p c ≠ 0)
    (hm : ∀ p : MixedPair, rowMinor01 A (u.val + 2) p.val.1 p.val.2 ≠ 0)
    (hentry : ∀ a b, a ≠ b → A (u.val + 2) a b ≠ 0)
    (c : MixedPair → ℝ) (β : NewParameter N → ℝ)
    (hrel : ∀ j : State 2,
      ∑ p : MixedPair, c p • jetNumerator A (u.val + 2) (relativeDirection τ ν)
        (coalescedTail u v) p.val.1 p.val.2 j =
      ∑ i : NewParameter N, β i • clearedReducedColumn A i j) :
    ∀ p, c p = 0 := by
  intro p
  let r : State 2 → ℝ := fun j => firstCoeff (P p)
    (jetNumerator A (u.val + 2) (relativeDirection τ ν) (coalescedTail u v) p.val.1 p.val.2 j)
  let s : State 2 → ℝ := fun j => firstCoeff (P p)
    (jetNumerator A (u.val + 2) (relativeDirection τ ν) (coalescedTail u v) p.val.2 p.val.1 j)
  have hobs (j : State 2) : c p * r j + c (reversePair p) * s j = 0 := by
    have h := congrArg (firstCoeff (P p)) (hrel j)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    have hrhs : ∑ i : NewParameter N,
        β i * firstCoeff (P p) (clearedReducedColumn A i j) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [clearedReducedColumn_firstCoeff_eq_zero A (P p) u v huv hA
        p.val.1 p.val.2 p.property (hzero p).1 (hzero p).2 i j, mul_zero]
    rw [hrhs] at h
    have hsum := Finset.sum_eq_add_of_mem p (reversePair p)
      (Finset.mem_univ p) (Finset.mem_univ (reversePair p)) (pair_ne_reverse p)
      (f := fun x : MixedPair => c x * firstCoeff (P p)
        (jetNumerator A (u.val + 2) (relativeDirection τ ν)
          (coalescedTail u v) x.val.1 x.val.2 j))
      (fun x _ hx => by rw [firstCoeff_other_pair A (P p) (u.val + 2)
        (relativeDirection τ ν) (coalescedTail u v) p x (hzero p).1 (hzero p).2
        hx.1 hx.2 j, mul_zero])
    rw [hsum] at h
    exact h
  apply left_coefficient_eq_zero r s (c p) (c (reversePair p)) (hobs 0) (hobs 1)
  exact jetNumerator_pair_minor_ne_zero A (P p) (u.val + 2) τ ν (coalescedTail u v)
    p.val.1 p.val.2 (hzero p).1 (hzero p).2 (hrest p) (hL p) hD (hP p) (hm p)
    (hentry _ _ p.property) (hentry _ _ (Ne.symm p.property)) hντ

/-- The separation statement for the actual positive-coordinate functions.
Polynomial injectivity justifies observing the relation at the nonpositive
pair points; no analytic continuation or residue assumption is inserted. -/
theorem six_specialJets_separate_from_reduced {N : ℕ} {A : Table 2}
    (hpos : PositiveTable A) (u v : Fin N) (huv : u ≠ v)
    (hA : A (u.val + 2) = A (v.val + 2))
    (τ ν : ℝ) (hντ : ν - τ ≠ 0) (P : MixedPair → State 2 → ℝ)
    (hzero : ∀ p, rowForm A (P p) (u.val + 2) p.val.1 = 0 ∧
      rowForm A (P p) (u.val + 2) p.val.2 = 0)
    (hrest : ∀ p c, c ≠ p.val.1 → c ≠ p.val.2 → rowForm A (P p) (u.val + 2) c ≠ 0)
    (hL : ∀ p x, x ∈ coalescedTail u v → ∀ c, rowForm A (P p) (x.val + 2) c ≠ 0)
    (hD : ∀ x ∈ coalescedTail u v, (Matrix.of (A (x.val + 2))).det ≠ 0)
    (hP : ∀ p c, P p c ≠ 0)
    (hm : ∀ p : MixedPair, rowMinor01 A (u.val + 2) p.val.1 p.val.2 ≠ 0)
    (c : MixedPair → ℝ) (β : NewParameter N → ℝ)
    (hrel : ∀ X : State 2 → ℝ, PositiveCoordinates X → ∀ j : State 2,
      ∑ p : MixedPair, c p * specialJet A X (u.val + 2) (relativeDirection τ ν)
        (homogeneousWordProduct A X (coalescedTail u v)) p.val.1 p.val.2 j =
      ∑ i : NewParameter N, β i * SourceHomogeneous.reducedColumn A X i j) :
    ∀ p, c p = 0 := by
  apply six_coefficients_eq_zero_of_relation A u v huv hA τ ν hντ P hzero hrest hL hD hP hm
    (fun a b _ => ne_of_gt (hpos (u.val + 2) a b)) c β
  intro j
  apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0)
  intro X hXs
  have hX : PositiveCoordinates X := fun i => hXs i (Set.mem_univ i)
  change (MvPolynomial.aeval X : Poly →ₐ[ℝ] ℝ).toLinearMap _ =
    (MvPolynomial.aeval X : Poly →ₐ[ℝ] ℝ).toLinearMap _
  simp only [map_sum, map_smul, smul_eq_mul]
  change (∑ p : MixedPair, c p * MvPolynomial.eval X
      (jetNumerator A (u.val + 2) (relativeDirection τ ν) (coalescedTail u v) p.val.1 p.val.2 j)) =
    ∑ i : NewParameter N, β i * MvPolynomial.eval X (clearedReducedColumn A i j)
  calc
    _ = MvPolynomial.eval X (tailDenominator (N := N) A) *
        ∑ p : MixedPair, c p * specialJet A X (u.val + 2) (relativeDirection τ ν)
          (homogeneousWordProduct A X (coalescedTail u v)) p.val.1 p.val.2 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [jetNumerator_eval_coalesced hpos hX u v huv hA (relativeDirection τ ν)
        p.val.1 p.val.2 j p.property]
      ring
    _ = MvPolynomial.eval X (tailDenominator (N := N) A) *
        ∑ i : NewParameter N, β i * SourceHomogeneous.reducedColumn A X i j := by
      rw [hrel X hX j]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [clearedReducedColumn_eval hpos hX i j]
      ring

end

end PanelMoments.SourceMixedPairSeparation
