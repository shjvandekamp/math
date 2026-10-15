import PanelMoments.Polynomial
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Universal validity of the four-period source moments

The six orders permute the first three generation slots and leave slot three last.
Two contrasts match first-state marginals; three contrasts match two-state marginals.
Their cardinality is 33 with three alternatives. No independence assertion is made.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

theorem sum_paths_succ {Q T : ℕ} (f : Path Q (T + 1) → ℝ) :
    ∑ y, f y = ∑ a, ∑ z : Path Q T, f (Fin.cons a z) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (T + 1) => State Q))]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk]

def chain4 {Q : ℕ} (p₀ : State Q → ℝ) (p₁ p₂ p₃ : State Q → State Q → ℝ)
    (y : Path Q 4) : ℝ :=
  p₀ (y 0) * p₁ (y 0) (y 1) * p₂ (y 1) (y 2) * p₃ (y 2) (y 3)

theorem chain4_first_marginal {Q : ℕ} (p₀ : State Q → ℝ)
    (p₁ p₂ p₃ : State Q → State Q → ℝ)
    (h₁ : ∀ a, ∑ b, p₁ a b = 1) (h₂ : ∀ a, ∑ b, p₂ a b = 1)
    (h₃ : ∀ a, ∑ b, p₃ a b = 1) (w : State Q → ℝ) :
    ∑ y : Path Q 4, w (y 0) * chain4 p₀ p₁ p₂ p₃ y = ∑ a, w a * p₀ a := by
  simp only [sum_paths_succ]
  change (∑ a, ∑ b, ∑ c, ∑ d, ∑ _z : Path Q 0,
    w a * (p₀ a * p₁ a b * p₂ b c * p₃ c d)) = _
  simp [mul_assoc, ← Finset.mul_sum, h₁, h₂, h₃]

theorem chain4_second_marginal {Q : ℕ} (p₀ : State Q → ℝ)
    (p₁ p₂ p₃ : State Q → State Q → ℝ)
    (h₂ : ∀ a, ∑ b, p₂ a b = 1) (h₃ : ∀ a, ∑ b, p₃ a b = 1)
    (w : State Q → State Q → ℝ) :
    ∑ y : Path Q 4, w (y 0) (y 1) * chain4 p₀ p₁ p₂ p₃ y =
      ∑ a, ∑ b, w a b * p₀ a * p₁ a b := by
  simp only [sum_paths_succ]
  change (∑ a, ∑ b, ∑ c, ∑ d, ∑ _z : Path Q 0,
    w a b * (p₀ a * p₁ a b * p₂ b c * p₃ c d)) = _
  simp [mul_assoc, ← Finset.mul_sum, h₂, h₃]

/-- Zero-based generation orders: 0123, 0213, 1023, 1203, 2013, 2103. -/
def orderPerm : Fin 6 → Equiv.Perm (Fin 4) :=
  ![Equiv.refl _, Equiv.swap 1 2, Equiv.swap 0 1,
    (Equiv.swap 0 1).trans (Equiv.swap 0 2),
    (Equiv.swap 0 2).trans (Equiv.swap 0 1), Equiv.swap 0 2]

def transformedChain {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ) (r : State Q)
    (o : Fin 6) (y : Path Q 4) : ℝ :=
  chain4 (transition A η 0 r)
    (transition A η ((orderPerm o 0).val + 1))
    (transition A η ((orderPerm o 1).val + 1))
    (transition A η ((orderPerm o 2).val + 1))
    (fun i => y (orderPerm o i))

theorem transformedChain_first_marginal {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State Q)
    (o : Fin 6) (w : State Q → ℝ) :
    ∑ y : Path Q 4, w (y (orderPerm o 0)) * transformedChain A η r o y =
      ∑ a, w a * transition A η 0 r a := by
  let e : Path Q 4 ≃ Path Q 4 :=
    Equiv.arrowCongr (orderPerm o).symm (Equiv.refl (State Q))
  calc
    _ = ∑ z : Path Q 4, w (z 0) * chain4 (transition A η 0 r)
        (transition A η ((orderPerm o 0).val + 1))
        (transition A η ((orderPerm o 1).val + 1))
        (transition A η ((orderPerm o 2).val + 1)) z := by
      simpa [e, Equiv.arrowCongr, transformedChain, Function.comp_def]
        using e.sum_comp (fun z => w (z 0) * chain4
          (transition A η 0 r) (transition A η ((orderPerm o 0).val + 1))
          (transition A η ((orderPerm o 1).val + 1))
          (transition A η ((orderPerm o 2).val + 1)) z)
    _ = _ := chain4_first_marginal _ _ _ _
      (transition_sum hA hη _) (transition_sum hA hη _) (transition_sum hA hη _) w

theorem transformedChain_second_marginal {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State Q)
    (o : Fin 6) (w : State Q → State Q → ℝ) :
    ∑ y : Path Q 4, w (y (orderPerm o 0)) (y (orderPerm o 1)) *
      transformedChain A η r o y =
      ∑ a, ∑ b, w a b * transition A η 0 r a *
        transition A η ((orderPerm o 0).val + 1) a b := by
  let e : Path Q 4 ≃ Path Q 4 :=
    Equiv.arrowCongr (orderPerm o).symm (Equiv.refl (State Q))
  calc
    _ = ∑ z : Path Q 4, w (z 0) (z 1) * chain4 (transition A η 0 r)
        (transition A η ((orderPerm o 0).val + 1))
        (transition A η ((orderPerm o 1).val + 1))
        (transition A η ((orderPerm o 2).val + 1)) z := by
      simpa [e, Equiv.arrowCongr, transformedChain, Function.comp_def]
        using e.sum_comp (fun z => w (z 0) (z 1) * chain4
          (transition A η 0 r) (transition A η ((orderPerm o 0).val + 1))
          (transition A η ((orderPerm o 1).val + 1))
          (transition A η ((orderPerm o 2).val + 1)) z)
    _ = _ := chain4_second_marginal _ _ _ _
      (transition_sum hA hη _) (transition_sum hA hη _) w

def originalScale {R : Type*} [CommRing R] {Q : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q) (y : Path Q 4) : R :=
  A 0 r (y 0) * A 1 (y 0) (y 1) * A 2 (y 1) (y 2) * A 3 (y 2) (y 3)

def transformedScale {R : Type*} [CommRing R] {Q : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q) (o : Fin 6)
    (y : Path Q 4) : R :=
  A 0 r (y (orderPerm o 0)) *
    A ((orderPerm o 0).val + 1) (y (orderPerm o 0)) (y (orderPerm o 1)) *
    A ((orderPerm o 1).val + 1) (y (orderPerm o 1)) (y (orderPerm o 2)) *
    A ((orderPerm o 2).val + 1) (y (orderPerm o 2)) (y (orderPerm o 3))

theorem originalScale_pos {Q : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (y : Path Q 4) : 0 < originalScale A r y := by
  exact mul_pos (mul_pos (mul_pos (hA 0 r (y 0)) (hA 1 (y 0) (y 1)))
    (hA 2 (y 1) (y 2))) (hA 3 (y 2) (y 3))

theorem likelihood_four {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (r : State Q) (y : Path Q 4) :
    likelihood A η 4 r y = chain4 (transition A η 0 r)
      (transition A η 1) (transition A η 2) (transition A η 3) y := by
  change transition A η 0 r (y 0) * (transition A η 1 (y 0) (y 1) *
    (transition A η 2 (y 1) (y 2) * (transition A η 3 (y 2) (y 3) * 1))) = _
  simp only [chain4]
  ring

/-- The likelihood ratio contains no fixed effects: the effect factors merely permute. -/
theorem scaleRatio_mul_likelihood {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State Q)
    (o : Fin 6) (y : Path Q 4) :
    (transformedScale A r o y / originalScale A r y) * likelihood A η 4 r y =
      transformedChain A η r o y := by
  have hd₀ := ne_of_gt (denominator_pos hA hη 0 r)
  have hd₁ := ne_of_gt (denominator_pos hA hη 1 (y 0))
  have hd₂ := ne_of_gt (denominator_pos hA hη 2 (y 1))
  have hd₃ := ne_of_gt (denominator_pos hA hη 3 (y 2))
  have ha₀ := ne_of_gt (hA 0 r (y 0))
  have ha₁ := ne_of_gt (hA 1 (y 0) (y 1))
  have ha₂ := ne_of_gt (hA 2 (y 1) (y 2))
  have ha₃ := ne_of_gt (hA 3 (y 2) (y 3))
  rw [likelihood_four]
  fin_cases o <;>
    simp [transformedScale, originalScale, transformedChain, chain4, orderPerm,
      Equiv.swap_apply_def, transition] <;>
    field_simp

/-- The two first-marginal contrasts and the three shared-prefix contrasts. In the
right summand, the coordinates are `(shared slot, second-state value, first-state value)`. -/
abbrev SourceIndex (Q : ℕ) := (Fin 2 × State Q) ⊕ (Fin 3 × State Q × State Q)

def sourceFirstOrder {Q : ℕ} : SourceIndex Q → Fin 6
  | .inl (i, _) => ![1, 0] i
  | .inr (s, _, _) => ![0, 2, 4] s

def sourceSecondOrder {Q : ℕ} : SourceIndex Q → Fin 6
  | .inl (i, _) => ![3, 5] i
  | .inr (s, _, _) => ![1, 3, 5] s

def sourceWeight {R : Type*} [Zero R] [One R] {Q : ℕ}
    (i : SourceIndex Q) (o : Fin 6) (y : Path Q 4) : R :=
  match i with
  | .inl (_, q) => if y (orderPerm o 0) = q then 1 else 0
  | .inr (_, q, a) => if y (orderPerm o 0) = a ∧ y (orderPerm o 1) = q then 1 else 0

def sourceMarginal {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ) (r : State Q)
    (i : SourceIndex Q) (o : Fin 6) : ℝ :=
  match i with
  | .inl (_, q) => transition A η 0 r q
  | .inr (_, q, a) => transition A η 0 r a *
      transition A η ((orderPerm o 0).val + 1) a q

theorem sourceWeightedChain_sum {Q : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State Q)
    (i : SourceIndex Q) (o : Fin 6) :
    ∑ y, sourceWeight i o y * transformedChain A η r o y =
      sourceMarginal A η r i o := by
  rcases i with ⟨j, q⟩ | ⟨s, q, a⟩
  · simpa [sourceWeight, sourceMarginal] using
      transformedChain_first_marginal hA hη r o (fun b => if b = q then 1 else 0)
  · simpa [sourceWeight, sourceMarginal, ite_and, mul_ite, ite_mul] using
      transformedChain_second_marginal hA hη r o
        (fun b c => if b = a ∧ c = q then 1 else 0)

theorem sourceMarginal_pair_eq {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (r : State Q) (i : SourceIndex Q) :
    sourceMarginal A η r i (sourceFirstOrder i) =
      sourceMarginal A η r i (sourceSecondOrder i) := by
  rcases i with ⟨j, q⟩ | ⟨s, q, a⟩
  · rfl
  · fin_cases s <;>
      simp [sourceMarginal, sourceFirstOrder, sourceSecondOrder, orderPerm,
        Equiv.swap_apply_def]

def sourceMoment {Q : ℕ} (A : Table Q) (r : State Q) (i : SourceIndex Q)
    (y : Path Q 4) : ℝ :=
  sourceWeight i (sourceFirstOrder i) y *
      (transformedScale A r (sourceFirstOrder i) y / originalScale A r y) -
    sourceWeight i (sourceSecondOrder i) y *
      (transformedScale A r (sourceSecondOrder i) y / originalScale A r y)

/-- The polynomial source-moment numerator. This definition is shared with exact
finite certificates; their row order is specified separately. -/
def sourceNumerator {R : Type*} [CommRing R] {Q : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q) (i : SourceIndex Q)
    (y : Path Q 4) : R :=
  sourceWeight i (sourceFirstOrder i) y * transformedScale A r (sourceFirstOrder i) y -
    sourceWeight i (sourceSecondOrder i) y * transformedScale A r (sourceSecondOrder i) y

theorem sourceMoment_eq_numerator_div {Q : ℕ} (A : Table Q) (r : State Q)
    (i : SourceIndex Q) (y : Path Q 4) :
    sourceMoment A r i y = sourceNumerator A r i y / originalScale A r y := by
  simp only [sourceMoment, sourceNumerator]
  ring

@[simp] theorem map_sourceWeight {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {Q : ℕ} (i : SourceIndex Q) (o : Fin 6) (y : Path Q 4) :
    f (sourceWeight i o y : R) = (sourceWeight i o y : S) := by
  cases i <;> simp only [sourceWeight] <;> split_ifs <;> simp

@[simp] theorem map_sourceNumerator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {Q : ℕ} (A : ℕ → State Q → State Q → R)
    (r : State Q) (i : SourceIndex Q) (y : Path Q 4) :
    f (sourceNumerator A r i y) = sourceNumerator (fun t s q => f (A t s q)) r i y := by
  simp [sourceNumerator, transformedScale]

/-- Every explicitly indexed source contrast is a fixed-effect-free moment. -/
theorem sourceMoment_isMoment {Q : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (i : SourceIndex Q) : IsMoment A 4 r (sourceMoment A r i) := by
  intro η hη
  simp only [sourceMoment, sub_mul, Finset.sum_sub_distrib, mul_assoc,
    scaleRatio_mul_likelihood hA hη]
  rw [sourceWeightedChain_sum hA hη, sourceWeightedChain_sum hA hη,
    sourceMarginal_pair_eq, sub_self]

theorem three_choice_source_count : Fintype.card (SourceIndex 2) = 33 := by
  decide

end

end PanelMoments
