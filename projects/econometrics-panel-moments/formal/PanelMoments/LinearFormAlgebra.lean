import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Divisibility by normalized linear forms

The homogeneous denominator lines in three variables have coefficient one on
`X 0`. A triangular change of variables proves their primality. Evaluations at
two explicit points give exact divisibility criteria, without an assumption
about genericity. These results are algebraic ingredients for a later analysis
of the three cubic block generators; no spanning or dimension claim is made
here.
-/

namespace PanelMoments.LinearFormAlgebra

open scoped BigOperators
open MvPolynomial

noncomputable section

abbrev Poly := MvPolynomial (Fin 3) ℝ
abbrev Point := Fin 3 → ℝ

/-- A homogeneous line normalized by its first coefficient. -/
def normalizedLine (a b : ℝ) : Poly := X 0 + C a * X 1 + C b * X 2

theorem eval_normalizedLine (a b : ℝ) (p : Point) :
    eval p (normalizedLine a b) = p 0 + a * p 1 + b * p 2 := by
  simp [normalizedLine]

private def shearHom (a b : ℝ) : Poly →ₐ[ℝ] Poly :=
  aeval ![normalizedLine a b, X 1, X 2]

private theorem shearHom_comp_neg (a b : ℝ) :
    (shearHom a b).comp (shearHom (-a) (-b)) = AlgHom.id ℝ Poly := by
  ext i
  fin_cases i <;> simp [shearHom, normalizedLine] <;> ring

/-- The substitution `X 0 ↦ X 0 + a X 1 + b X 2`, fixing the other variables. -/
def shearEquiv (a b : ℝ) : Poly ≃ₐ[ℝ] Poly :=
  AlgEquiv.ofAlgHom (shearHom a b) (shearHom (-a) (-b))
    (shearHom_comp_neg a b) (by simpa using shearHom_comp_neg (-a) (-b))

@[simp]
theorem shearEquiv_X_zero (a b : ℝ) :
    shearEquiv a b (X 0) = normalizedLine a b := by
  change shearHom a b (X 0) = normalizedLine a b
  simp [shearHom]

theorem coordinate_prime (i : Fin 3) : Prime (X i : Poly) := MvPolynomial.X_prime

/-- No condition on the other two coefficients is needed for primality. -/
theorem normalizedLine_prime (a b : ℝ) : Prime (normalizedLine a b) := by
  rw [← shearEquiv_X_zero]
  exact (MulEquiv.prime_iff (shearEquiv a b)).2 (coordinate_prime 0)

theorem eval_eq_zero_of_dvd {f g : Poly} (hfg : f ∣ g) (p : Point)
    (hf : eval p f = 0) : eval p g = 0 := by
  rcases hfg with ⟨q, rfl⟩
  simp [hf]

/-- Two normalized lines divide one another precisely when their coefficients agree. -/
theorem normalizedLine_dvd_normalizedLine_iff (a b c d : ℝ) :
    normalizedLine a b ∣ normalizedLine c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h₁ := eval_eq_zero_of_dvd h (![-a, 1, 0]) (by simp [eval_normalizedLine])
    have h₂ := eval_eq_zero_of_dvd h (![-b, 0, 1]) (by simp [eval_normalizedLine])
    have hc : c - a = 0 := by
      simpa [eval_normalizedLine, sub_eq_add_neg, add_comm] using h₁
    have hd : d - b = 0 := by
      simpa [eval_normalizedLine, sub_eq_add_neg, add_comm] using h₂
    exact ⟨(sub_eq_zero.mp hc).symm, (sub_eq_zero.mp hd).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact dvd_rfl

theorem normalizedLine_not_dvd_normalizedLine {a b c d : ℝ}
    (h : a ≠ c ∨ b ≠ d) : ¬normalizedLine a b ∣ normalizedLine c d := by
  rw [normalizedLine_dvd_normalizedLine_iff]
  rintro ⟨ha, hb⟩
  exact h.elim (fun h => h ha) (fun h => h hb)

theorem normalizedLine_dvd_X_zero_iff (a b : ℝ) :
    normalizedLine a b ∣ (X 0 : Poly) ↔ a = 0 ∧ b = 0 := by
  simpa [normalizedLine] using normalizedLine_dvd_normalizedLine_iff a b 0 0

theorem normalizedLine_not_dvd_X_one (a b : ℝ) :
    ¬normalizedLine a b ∣ (X 1 : Poly) := by
  intro h
  have hz := eval_eq_zero_of_dvd h (![-a, 1, 0]) (by simp [eval_normalizedLine])
  simpa using hz

theorem normalizedLine_not_dvd_X_two (a b : ℝ) :
    ¬normalizedLine a b ∣ (X 2 : Poly) := by
  intro h
  have hz := eval_eq_zero_of_dvd h (![-b, 0, 1]) (by simp [eval_normalizedLine])
  simpa using hz

/-- The sole coordinate exception is the line `X 0` itself. -/
theorem normalizedLine_not_dvd_coordinate {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0) (i : Fin 3) : ¬normalizedLine a b ∣ (X i : Poly) := by
  fin_cases i
  · change ¬normalizedLine a b ∣ (X (0 : Fin 3) : Poly)
    rw [normalizedLine_dvd_X_zero_iff]
    rintro ⟨ha, hb⟩
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · exact normalizedLine_not_dvd_X_one a b
  · exact normalizedLine_not_dvd_X_two a b

theorem coordinate_not_dvd_coordinate {i j : Fin 3} (hij : i ≠ j) :
    ¬(X i : Poly) ∣ X j := by
  simpa using hij

theorem X_zero_dvd_normalizedLine_iff (a b : ℝ) :
    (X 0 : Poly) ∣ normalizedLine a b ↔ a = 0 ∧ b = 0 := by
  simpa [normalizedLine, eq_comm] using normalizedLine_dvd_normalizedLine_iff 0 0 a b

theorem X_one_not_dvd_normalizedLine (a b : ℝ) :
    ¬(X 1 : Poly) ∣ normalizedLine a b := by
  intro h
  have hz := eval_eq_zero_of_dvd h (![1, 0, 0]) (by simp)
  simpa [eval_normalizedLine] using hz

theorem X_two_not_dvd_normalizedLine (a b : ℝ) :
    ¬(X 2 : Poly) ∣ normalizedLine a b := by
  intro h
  have hz := eval_eq_zero_of_dvd h (![1, 0, 0]) (by simp)
  simpa [eval_normalizedLine] using hz

theorem coordinate_not_dvd_normalizedLine {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0) (i : Fin 3) : ¬(X i : Poly) ∣ normalizedLine a b := by
  fin_cases i
  · change ¬(X (0 : Fin 3) : Poly) ∣ normalizedLine a b
    rw [X_zero_dvd_normalizedLine_iff]
    rintro ⟨ha, hb⟩
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · exact X_one_not_dvd_normalizedLine a b
  · exact X_two_not_dvd_normalizedLine a b

/-- Primality removes every distinct normalized line from a finite product. -/
theorem normalizedLine_not_dvd_prod {ι : Type*} (s : Finset ι)
    (c d : ι → ℝ) {a b : ℝ} (h : ∀ j ∈ s, a ≠ c j ∨ b ≠ d j) :
    ¬normalizedLine a b ∣ ∏ j ∈ s, normalizedLine (c j) (d j) := by
  apply (normalizedLine_prime a b).not_dvd_finsetProd
  intro j hj
  exact normalizedLine_not_dvd_normalizedLine (h j hj)

/-- If a normalized line divides a coefficient times the remaining cubic
factors, it divides the coefficient. The hypotheses state the exact excluded
coincidences, rather than assuming a rank or dimension conclusion. -/
theorem normalizedLine_dvd_coefficient {ι : Type*} (s : Finset ι)
    (c d : ι → ℝ) {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (h : ∀ j ∈ s, a ≠ c j ∨ b ≠ d j) (i : Fin 3) (f : Poly)
    (hf : normalizedLine a b ∣ f * X i * ∏ j ∈ s, normalizedLine (c j) (d j)) :
    normalizedLine a b ∣ f := by
  have hp := normalizedLine_prime a b
  have hfx : normalizedLine a b ∣ f * X i :=
    hp.dvd_or_dvd hf |>.resolve_right (normalizedLine_not_dvd_prod s c d h)
  exact (hp.dvd_or_dvd hfx).resolve_right (normalizedLine_not_dvd_coordinate hab i)

end

end PanelMoments.LinearFormAlgebra
