import PanelMoments.MomentLifts
import PanelMoments.PermutationMoments

set_option autoImplicit false

/-!
# Prepending a shared observation to a permutation moment

Fixing the first generation slot in both orders, and conditioning its outcome,
gives precisely an indicator lift of the shorter permutation moment. This is
the analytic part of the source-family recursion. The canonical index and
order transport are separate combinatorial statements.
-/

namespace PanelMoments.PermutationLifts

open scoped BigOperators
open PermutationMoments

noncomputable section

/-- Extend a generation order by placing a new common observation first. -/
def prependFirst {N : ℕ} (o : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N + 1)) where
  toFun := Fin.cases 0 (fun i => (o i).succ)
  invFun := Fin.cases 0 (fun i => (o.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem prependFirst_zero {N : ℕ} (o : Equiv.Perm (Fin N)) :
    prependFirst o 0 = 0 := by simp [prependFirst]

@[simp] theorem prependFirst_succ {N : ℕ} (o : Equiv.Perm (Fin N)) (i : Fin N) :
    prependFirst o i.succ = (o i).succ := by simp [prependFirst]

@[simp] theorem prependFirst_one {N : ℕ} (o : Equiv.Perm (Fin (N + 1))) :
    prependFirst o 1 = (o 0).succ := by
  change prependFirst o (0 : Fin (N + 1)).succ = _
  exact prependFirst_succ o 0

theorem comp_prependFirst {Q N : ℕ} (o : Equiv.Perm (Fin N))
    (a : State Q) (y : Path Q N) :
    (fun i => (Fin.cons a y : Path Q (N + 1)) (prependFirst o i)) =
      (Fin.cons a (fun i : Fin N => y (o i)) : Path Q (N + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem prefixIndicator_cons {Q k : ℕ} (a b : State Q) (q z : Path Q (k + 1)) :
    (prefixIndicator (Fin.cons a q) (Fin.cons b z) : ℝ) =
      if b = a then prefixIndicator q z else 0 := by
  by_cases hba : b = a
  · subst b
    simp [prefixIndicator, Fin.cons_inj]
  · simp [prefixIndicator, Fin.cons_inj, hba]

theorem originalScale_cons {Q N : ℕ} (A : Table Q) (r a : State Q)
    (y : Path Q (N + 1)) :
    PermutationMoments.originalScale A r (Fin.cons a y) =
      A 0 r a * PermutationMoments.originalScale (shift A) a y := by
  simp only [PermutationMoments.originalScale, Fin.cons_zero, Fin.prod_univ_succ]
  simp [shift]

theorem transformedScale_prepend {Q N : ℕ} (A : Table Q) (r a : State Q)
    (o : Equiv.Perm (Fin (N + 1))) (y : Path Q (N + 1)) :
    PermutationMoments.transformedScale A r (prependFirst o) (Fin.cons a y) =
      A 0 r a * PermutationMoments.transformedScale (shift A) a o y := by
  simp only [PermutationMoments.transformedScale, prependFirst_zero, Fin.cons_zero,
    Fin.prod_univ_succ]
  simp [shift]

theorem sourceNumerator_prepend {Q N k : ℕ} (A : Table Q) (r a b : State Q)
    (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (q : Path Q (k + 1)) (y : Path Q (N + 1)) :
    PermutationMoments.sourceNumerator A r (Nat.succ_le_succ hk) (prependFirst o₁) (prependFirst o₂)
        (Fin.cons a q) (Fin.cons b y) =
      if b = a then A 0 r b * PermutationMoments.sourceNumerator (shift A) b hk o₁ o₂ q y else 0 := by
  unfold PermutationMoments.sourceNumerator contrastNumerator
  rw [comp_prependFirst, comp_prependFirst, prefix_cons, prefix_cons,
    prefixIndicator_cons, prefixIndicator_cons,
    transformedScale_prepend, transformedScale_prepend]
  split_ifs <;> ring

/-- Equality of moment functions, not merely validity of both functions. -/
theorem sourceMoment_prepend {Q N k : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r a : State Q) (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (q : Path Q (k + 1)) :
    PermutationMoments.sourceMoment A r (Nat.succ_le_succ hk) (prependFirst o₁) (prependFirst o₂)
        (Fin.cons a q) =
      MomentLifts.firstStateLift a (PermutationMoments.sourceMoment (shift A) a hk o₁ o₂ q) := by
  funext y
  obtain ⟨b, z, rfl⟩ := Fin.exists_cons y
  rw [PermutationMoments.sourceMoment_eq_numerator_div, sourceNumerator_prepend, originalScale_cons,
    MomentLifts.firstStateLift_cons]
  split_ifs with hba
  · subst b
    rw [PermutationMoments.sourceMoment_eq_numerator_div]
    exact mul_div_mul_left _ _ (ne_of_gt (hA 0 r a))
  · simp

end

end PanelMoments.PermutationLifts
