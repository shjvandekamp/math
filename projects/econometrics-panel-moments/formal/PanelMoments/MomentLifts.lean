import PanelMoments.SourceMoments
import PanelMoments.BasisCertificate

set_option autoImplicit false

/-!
# Lifting shorter-panel moments through the first observed state

The equation-(24) indices whose shared set contains time zero are three
disjoint indicator lifts of the shorter-panel family. This file proves the
model and linear-algebra facts for those lifts, without assuming independence
of the remaining source moments.
-/

namespace PanelMoments.MomentLifts

open scoped BigOperators

noncomputable section

def firstStateLift {Q T : ℕ} (a : State Q) (m : Path Q T → ℝ)
    (y : Path Q (T + 1)) : ℝ :=
  if y 0 = a then m (Fin.tail y) else 0

@[simp] theorem firstStateLift_cons {Q T : ℕ} (a b : State Q)
    (m : Path Q T → ℝ) (y : Path Q T) :
    firstStateLift a m (Fin.cons b y) = if b = a then m y else 0 := by
  simp [firstStateLift]

theorem firstStateLift_injective {Q T : ℕ} (a : State Q) :
    Function.Injective (firstStateLift (T := T) a) := by
  intro m n h
  funext y
  have hy := congrFun h (Fin.cons a y)
  simpa using hy

/-- Conditioning on the first outcome turns a shorter-panel moment into a
moment for any initial outcome in the longer panel. -/
theorem firstStateLift_isMoment {Q T : ℕ} {A : Table Q}
    (r a : State Q) {m : Path Q T → ℝ}
    (hm : IsMoment (shift A) T a m) :
    IsMoment A (T + 1) r (firstStateLift a m) := by
  intro η hη
  have htail := hm η hη
  calc
    _ = transition A η 0 r a *
        ∑ z : Path Q T, m z * likelihood (shift A) η T a z := by
      rw [sum_paths_succ]
      simp [firstStateLift, likelihood]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [htail, mul_zero]

/-- Independent shorter-panel families remain independent after placing each
one on the disjoint slice selected by its first outcome. -/
theorem linearIndependent_firstStateLift {Q T : ℕ} {ι : Type*} [Fintype ι]
    (v : State Q → ι → Path Q T → ℝ)
    (hv : ∀ a, LinearIndependent ℝ (v a)) :
    LinearIndependent ℝ (fun ai : State Q × ι => firstStateLift ai.1 (v ai.1 ai.2)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rintro ⟨a, i⟩
  have ha : ∑ j, c (a, j) • v a j = 0 := by
    funext y
    have hy := congrFun hc (Fin.cons a y)
    simpa [Fintype.sum_prod_type, firstStateLift, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum] using hy
  exact (Fintype.linearIndependent_iff.mp (hv a)) (fun j => c (a, j)) ha i

end

end PanelMoments.MomentLifts
