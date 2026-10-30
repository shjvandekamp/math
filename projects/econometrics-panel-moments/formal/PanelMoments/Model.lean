import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

/-!
# Normalized finite dynamic multinomial-logit model

`Q + 1` is the number of alternatives; alternative zero has fixed-effect multiplier one.
The transition table is arbitrary and strictly positive. Time starts at zero; `T` counts
transitions after the fixed initial state. No rank or genericity assertion is made here.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

abbrev State (Q : ℕ) := Fin (Q + 1)
abbrev Path (Q T : ℕ) := Fin T → State Q
abbrev Table (Q : ℕ) := ℕ → State Q → State Q → ℝ

def PositiveTable {Q : ℕ} (A : Table Q) : Prop := ∀ t r q, 0 < A t r q

def PositiveEffects {Q : ℕ} (η : Fin Q → ℝ) : Prop := ∀ q, 0 < η q

def effect {Q : ℕ} (η : Fin Q → ℝ) : State Q → ℝ := Fin.cons 1 η

@[simp] theorem effect_zero {Q : ℕ} (η : Fin Q → ℝ) : effect η 0 = 1 := rfl

@[simp] theorem effect_succ {Q : ℕ} (η : Fin Q → ℝ) (q : Fin Q) :
    effect η q.succ = η q := rfl

theorem effect_pos {Q : ℕ} {η : Fin Q → ℝ} (hη : PositiveEffects η) (q : State Q) :
    0 < effect η q := by
  refine Fin.cases ?_ (fun i => ?_) q
  · exact zero_lt_one
  · exact hη i

def denominator {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ) (t : ℕ) (r : State Q) : ℝ :=
  ∑ q, A t r q * effect η q

def transition {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (t : ℕ) (r q : State Q) : ℝ :=
  A t r q * effect η q / denominator A η t r

theorem denominator_pos {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (t : ℕ) (r : State Q) :
    0 < denominator A η t r := by
  exact Finset.sum_pos (fun q _ => mul_pos (hA t r q) (effect_pos hη q))
    Finset.univ_nonempty

theorem transition_pos {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (t : ℕ) (r q : State Q) :
    0 < transition A η t r q :=
  div_pos (mul_pos (hA t r q) (effect_pos hη q)) (denominator_pos hA hη t r)

theorem transition_sum {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (t : ℕ) (r : State Q) :
    ∑ q, transition A η t r q = 1 := by
  simp only [transition, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (denominator_pos hA hη t r))

def shift {Q : ℕ} (A : Table Q) : Table Q := fun t => A (t + 1)

theorem shift_pos {Q : ℕ} {A : Table Q} (hA : PositiveTable A) :
    PositiveTable (shift A) := fun t r q => hA (t + 1) r q

/-- Product of successive transition probabilities, with initial state `r`. -/
def likelihood {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ) :
    (T : ℕ) → State Q → Path Q T → ℝ
  | 0, _, _ => 1
  | T + 1, r, y => transition A η 0 r (y 0) *
      likelihood (shift A) η T (y 0) (Fin.tail y)

theorem likelihood_pos {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ)
    (r : State Q) (y : Path Q T) : 0 < likelihood A η T r y := by
  induction T generalizing A r with
  | zero => exact zero_lt_one
  | succ T ih =>
    exact mul_pos (transition_pos hA hη 0 r (y 0))
      (ih (shift_pos hA) (y 0) (Fin.tail y))

/-- The path likelihood is a probability distribution on the finite path space. -/
theorem likelihood_sum {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (T : ℕ) (r : State Q) :
    ∑ y : Path Q T, likelihood A η T r y = 1 := by
  induction T generalizing A r with
  | zero => simp [likelihood]
  | succ T ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (T + 1) => State Q))]
    simp only [Fintype.sum_prod_type, likelihood, Fin.consEquiv, Equiv.coe_fn_mk,
      Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum]
    simp only [ih (shift_pos hA), mul_one]
    exact transition_sum hA hη 0 r

def IsMoment {Q : ℕ} (A : Table Q) (T : ℕ) (r : State Q)
    (m : Path Q T → ℝ) : Prop :=
  ∀ η : Fin Q → ℝ, PositiveEffects η → ∑ y, m y * likelihood A η T r y = 0

theorem three_choice_four_period_path_count : Fintype.card (Path 2 4) = 81 := by
  decide

end

end PanelMoments
