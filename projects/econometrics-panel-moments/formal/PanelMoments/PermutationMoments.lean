import PanelMoments.SourceMoments

set_option autoImplicit false

/-!
# Validity of permutation moments at every horizon

An order permutes the `N + 1` observed outcome slots and fixes the final slot.
Its transformed Markov chain starts with transition table zero; after generating
slot `s`, it uses table `s + 1`. Consequently its likelihood ratio to the
original chain contains no fixed effects. Orders sharing their first `k` slots
have the same distribution of their first `k + 1` generated states.

The resulting indicator contrast is the construction in equations (16), (19),
(21), and (24). The canonical choice of orders and independence are separate
questions; neither is assumed by the validity theorem here.
-/

namespace PanelMoments.PermutationMoments

open scoped BigOperators

noncomputable section

/-- Restriction to the first `k` generation positions. -/
def pathPrefix {Q k T : ℕ} (h : k ≤ T) (y : Path Q T) : Path Q k :=
  fun i => y (Fin.castLE h i)

@[simp] theorem prefix_zero {Q T : ℕ} (h : 0 ≤ T) (y : Path Q T) :
    pathPrefix h y = (fun i => Fin.elim0 i) := by
  funext i
  exact Fin.elim0 i

@[simp] theorem prefix_cons {Q k T : ℕ} (h : k + 1 ≤ T + 1)
    (a : State Q) (y : Path Q T) :
    pathPrefix h (Fin.cons a y) =
      Fin.cons a (pathPrefix (Nat.succ_le_succ_iff.mp h) y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pathPrefix]
  · simp [pathPrefix]

/-- Summing out the tail leaves exactly the prefix likelihood. -/
theorem likelihood_prefix_sum {Q T k : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (h : k ≤ T)
    (r : State Q) (w : Path Q k → ℝ) :
    ∑ y : Path Q T, w (pathPrefix h y) * likelihood A η T r y =
      ∑ z : Path Q k, w z * likelihood A η k r z := by
  induction T generalizing k A r with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero h
      subst k
      simp [likelihood]
      exact congrArg w (Subsingleton.elim _ _)
  | succ T ih =>
      cases k with
      | zero =>
          simp only [prefix_zero, ← Finset.mul_sum, likelihood_sum hA hη]
          simp [likelihood]
          exact congrArg w (Subsingleton.elim _ _)
      | succ k =>
          have hk : k ≤ T := Nat.succ_le_succ_iff.mp h
          conv_lhs => rw [sum_paths_succ]
          conv_rhs => rw [sum_paths_succ]
          simp only [prefix_cons, likelihood, Fin.cons_zero, Fin.tail_cons]
          apply Finset.sum_congr rfl
          intro a _
          calc
            _ = transition A η 0 r a *
                ∑ y : Path Q T, w (Fin.cons a (pathPrefix hk y)) *
                  likelihood (shift A) η T a y := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
            _ = transition A η 0 r a *
                ∑ z : Path Q k, w (Fin.cons a z) *
                  likelihood (shift A) η k a z := by
              rw [ih (shift_pos hA) hk a (fun z => w (Fin.cons a z))]
            _ = _ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              ring

/-- Only the table entries inside the observed horizon affect a likelihood. -/
theorem likelihood_congr {Q T : ℕ} {A B : Table Q}
    (h : ∀ t, t < T → A t = B t) (η : Fin Q → ℝ)
    (r : State Q) (y : Path Q T) :
    likelihood A η T r y = likelihood B η T r y := by
  induction T generalizing A B r with
  | zero => rfl
  | succ T ih =>
      have hzero : transition A η 0 = transition B η 0 := by
        funext a b
        simp only [transition, denominator, h 0 (Nat.zero_lt_succ T)]
      have htail : ∀ t, t < T → shift A t = shift B t := by
        intro t ht
        exact h (t + 1) (Nat.succ_lt_succ ht)
      simp only [likelihood, hzero, ih htail]

/-- A finite product formula exposing the transitions after the first. -/
theorem likelihood_product {Q : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (N : ℕ) (r : State Q) (y : Path Q (N + 1)) :
    likelihood A η (N + 1) r y = transition A η 0 r (y 0) *
      ∏ i : Fin N, transition A η (i.val + 1) (y i.castSucc) (y i.succ) := by
  induction N generalizing A r with
  | zero => simp [likelihood]
  | succ N ih =>
      rw [likelihood, ih]
      rw [Fin.prod_univ_succ]
      change transition A η 0 r (y 0) *
          (transition A η 1 (y 0) (y 1) *
            ∏ i : Fin N, transition A η (i.val + 1 + 1)
              (y i.castSucc.succ) (y i.succ.succ)) =
        transition A η 0 r (y 0) *
          (transition A η 1 (y 0) (y 1) *
            ∏ i : Fin N, transition A η (i.val + 1 + 1)
              (y i.castSucc.succ) (y i.succ.succ))
      rfl

/-- The positive table used in generation order. Its values beyond the horizon
are irrelevant and are filled with the original table. -/
def generationTable {Q N : ℕ} (A : Table Q) (o : Equiv.Perm (Fin (N + 1))) :
    Table Q
  | 0 => A 0
  | t + 1 => if h : t < N then A ((o ⟨t, Nat.lt_succ_of_lt h⟩).val + 1)
      else A (t + 1)

@[simp] theorem generationTable_zero {Q N : ℕ} (A : Table Q)
    (o : Equiv.Perm (Fin (N + 1))) : generationTable A o 0 = A 0 := rfl

@[simp] theorem generationTable_succ {Q N : ℕ} (A : Table Q)
    (o : Equiv.Perm (Fin (N + 1))) (i : Fin N) :
    generationTable A o (i.val + 1) = A ((o i.castSucc).val + 1) := by
  simp only [generationTable, dite_eq_left i.isLt]
  rfl

theorem generationTable_pos {Q N : ℕ} {A : Table Q} (hA : PositiveTable A)
    (o : Equiv.Perm (Fin (N + 1))) : PositiveTable (generationTable A o) := by
  intro t r q
  cases t with
  | zero => exact hA 0 r q
  | succ t =>
      simp only [generationTable]
      split_ifs <;> exact hA _ r q

/-- The ordinary positive Markov chain, evaluated in the specified order. -/
def transformedChain {Q N : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (r : State Q) (o : Equiv.Perm (Fin (N + 1))) (y : Path Q (N + 1)) : ℝ :=
  likelihood (generationTable A o) η (N + 1) r (fun i => y (o i))

theorem transformedChain_product {Q N : ℕ} (A : Table Q) (η : Fin Q → ℝ)
    (r : State Q) (o : Equiv.Perm (Fin (N + 1))) (y : Path Q (N + 1)) :
    transformedChain A η r o y = transition A η 0 r (y (o 0)) *
      ∏ i : Fin N, transition A η ((o i.castSucc).val + 1)
        (y (o i.castSucc)) (y (o i.succ)) := by
  rw [transformedChain, likelihood_product]
  simp only [transition, denominator, generationTable_zero, generationTable_succ]

/-- The product of primitive table entries on the original path. -/
def originalScale {R : Type*} [CommRing R] {Q N : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q) (y : Path Q (N + 1)) : R :=
  A 0 r (y 0) * ∏ i : Fin N, A (i.val + 1) (y i.castSucc) (y i.succ)

/-- The numerator of the transformed likelihood ratio. Dividing this by
`originalScale` gives the exponential score in equation (16). -/
def transformedScale {R : Type*} [CommRing R] {Q N : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q)
    (o : Equiv.Perm (Fin (N + 1))) (y : Path Q (N + 1)) : R :=
  A 0 r (y (o 0)) * ∏ i : Fin N,
    A ((o i.castSucc).val + 1) (y (o i.castSucc)) (y (o i.succ))

theorem originalScale_pos {Q N : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (y : Path Q (N + 1)) : 0 < originalScale A r y := by
  exact mul_pos (hA 0 r (y 0)) (Finset.prod_pos (fun i _ => hA _ _ _))

/-- Reordering all positions except the last preserves their product. -/
theorem prod_castSucc_perm {N : ℕ} (o : Equiv.Perm (Fin (N + 1)))
    (hlast : o (Fin.last N) = Fin.last N) (f : Fin (N + 1) → ℝ)
    (hf : f (Fin.last N) ≠ 0) :
    ∏ i : Fin N, f (o i.castSucc) = ∏ i : Fin N, f i.castSucc := by
  have h := Equiv.prod_comp o f
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, hlast] at h
  exact mul_right_cancel₀ hf h

/-- Fixed effects cancel from the transformed-to-original likelihood ratio. -/
theorem scaleRatio_mul_likelihood {Q N : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (r : State Q)
    (o : Equiv.Perm (Fin (N + 1))) (hlast : o (Fin.last N) = Fin.last N)
    (y : Path Q (N + 1)) :
    (transformedScale A r o y / originalScale A r y) *
        likelihood A η (N + 1) r y = transformedChain A η r o y := by
  have heffect : effect η (y (o 0)) *
      (∏ i : Fin N, effect η (y (o i.succ))) =
      effect η (y 0) * ∏ i : Fin N, effect η (y i.succ) := by
    simpa only [Fin.prod_univ_succ] using
      Equiv.prod_comp o (fun i => effect η (y i))
  have hdenom :
      (∏ i : Fin N, denominator A η ((o i.castSucc).val + 1) (y (o i.castSucc))) =
        ∏ i : Fin N, denominator A η (i.val + 1) (y i.castSucc) :=
    prod_castSucc_perm o hlast (fun i => denominator A η (i.val + 1) (y i))
      (ne_of_gt (denominator_pos hA hη _ _))
  have hscale := ne_of_gt (originalScale_pos hA r y)
  have horiginal : likelihood A η (N + 1) r y =
      originalScale A r y *
        (effect η (y 0) * ∏ i : Fin N, effect η (y i.succ)) /
        (denominator A η 0 r *
          ∏ i : Fin N, denominator A η (i.val + 1) (y i.castSucc)) := by
    rw [likelihood_product]
    simp only [transition, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      originalScale]
    ring
  have htransformed : transformedChain A η r o y =
      transformedScale A r o y *
        (effect η (y (o 0)) * ∏ i : Fin N, effect η (y (o i.succ))) /
        (denominator A η 0 r *
          ∏ i : Fin N, denominator A η ((o i.castSucc).val + 1)
            (y (o i.castSucc))) := by
    rw [transformedChain_product]
    simp only [transition, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      transformedScale]
    ring
  rw [horiginal, htransformed, heffect, hdenom]
  calc
    _ = (transformedScale A r o y *
          ((originalScale A r y)⁻¹ * originalScale A r y)) *
        ((effect η (y 0) * ∏ i : Fin N, effect η (y i.succ)) /
          (denominator A η 0 r *
            ∏ i : Fin N, denominator A η (i.val + 1) (y i.castSucc))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hscale, mul_one]; ring

/-- Orders agree on the positions preceding the outcome being compared. -/
def SharedPrefix {N : ℕ} (k : ℕ) (o₁ o₂ : Equiv.Perm (Fin (N + 1))) : Prop :=
  ∀ i : Fin (N + 1), i.val < k → o₁ i = o₂ i

theorem generationTable_prefix_eq {Q N k : ℕ} (A : Table Q) (hk : k ≤ N)
    {o₁ o₂ : Equiv.Perm (Fin (N + 1))} (hprefix : SharedPrefix k o₁ o₂) :
    ∀ t, t < k + 1 → generationTable A o₁ t = generationTable A o₂ t := by
  intro t ht
  cases t with
  | zero => rfl
  | succ t =>
      have htk : t < k := Nat.succ_lt_succ_iff.mp ht
      have htN : t < N := Nat.lt_of_lt_of_le htk hk
      simp only [generationTable, dite_eq_left htN]
      rw [hprefix ⟨t, Nat.lt_succ_of_lt htN⟩ htk]

theorem transformedChain_prefix_sum {Q N k : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (hk : k ≤ N + 1)
    (r : State Q) (o : Equiv.Perm (Fin (N + 1))) (w : Path Q k → ℝ) :
    ∑ y : Path Q (N + 1), w (pathPrefix hk (fun i => y (o i))) *
        transformedChain A η r o y =
      ∑ z : Path Q k, w z * likelihood (generationTable A o) η k r z := by
  let e : Path Q (N + 1) ≃ Path Q (N + 1) :=
    Equiv.arrowCongr o.symm (Equiv.refl (State Q))
  calc
    _ = ∑ z : Path Q (N + 1), w (pathPrefix hk z) *
        likelihood (generationTable A o) η (N + 1) r z := by
      simpa [e, Equiv.arrowCongr, transformedChain, Function.comp_def] using
        e.sum_comp (fun z => w (pathPrefix hk z) *
          likelihood (generationTable A o) η (N + 1) r z)
    _ = _ := likelihood_prefix_sum (generationTable_pos hA o) hη hk r w

/-- The first `k + 1` generated states have the same distribution when the
preceding `k` generation positions agree. -/
theorem sharedPrefix_weightedChain_sum {Q N k : ℕ} {A : Table Q} {η : Fin Q → ℝ}
    (hA : PositiveTable A) (hη : PositiveEffects η) (hk : k ≤ N)
    (r : State Q) {o₁ o₂ : Equiv.Perm (Fin (N + 1))}
    (hprefix : SharedPrefix k o₁ o₂) (w : Path Q (k + 1) → ℝ) :
    ∑ y : Path Q (N + 1),
        w (pathPrefix (Nat.succ_le_succ hk) (fun i => y (o₁ i))) *
          transformedChain A η r o₁ y =
      ∑ y : Path Q (N + 1),
        w (pathPrefix (Nat.succ_le_succ hk) (fun i => y (o₂ i))) *
          transformedChain A η r o₂ y := by
  rw [transformedChain_prefix_sum hA hη, transformedChain_prefix_sum hA hη]
  apply Finset.sum_congr rfl
  intro z _
  rw [likelihood_congr (generationTable_prefix_eq A hk hprefix)]

/-- A shared-prefix contrast, expressed without fixed effects. -/
def contrast {Q N k : ℕ} (A : Table Q) (r : State Q) (hk : k ≤ N)
    (o₁ o₂ : Equiv.Perm (Fin (N + 1))) (w : Path Q (k + 1) → ℝ)
    (y : Path Q (N + 1)) : ℝ :=
  w (pathPrefix (Nat.succ_le_succ hk) (fun i => y (o₁ i))) *
      (transformedScale A r o₁ y / originalScale A r y) -
    w (pathPrefix (Nat.succ_le_succ hk) (fun i => y (o₂ i))) *
      (transformedScale A r o₂ y / originalScale A r y)

/-- A polynomial numerator shared by real moments and exact finite-field checks. -/
def contrastNumerator {R : Type*} [CommRing R] {Q N k : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q) (hk : k ≤ N)
    (o₁ o₂ : Equiv.Perm (Fin (N + 1))) (w : Path Q (k + 1) → R)
    (y : Path Q (N + 1)) : R :=
  w (pathPrefix (Nat.succ_le_succ hk) (fun i => y (o₁ i))) * transformedScale A r o₁ y -
    w (pathPrefix (Nat.succ_le_succ hk) (fun i => y (o₂ i))) * transformedScale A r o₂ y

theorem contrast_eq_numerator_div {Q N k : ℕ} (A : Table Q) (r : State Q)
    (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (w : Path Q (k + 1) → ℝ) (y : Path Q (N + 1)) :
    contrast A r hk o₁ o₂ w y =
      contrastNumerator A r hk o₁ o₂ w y / originalScale A r y := by
  simp only [contrast, contrastNumerator]
  ring

@[simp] theorem map_contrastNumerator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {Q N k : ℕ} (A : ℕ → State Q → State Q → R)
    (r : State Q) (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (w : Path Q (k + 1) → R) (y : Path Q (N + 1)) :
    f (contrastNumerator A r hk o₁ o₂ w y) =
      contrastNumerator (fun t a b => f (A t a b)) r hk o₁ o₂ (fun z => f (w z)) y := by
  simp [contrastNumerator, transformedScale]

/-- Universal validity, with no independence or rank premise. -/
theorem contrast_isMoment {Q N k : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (hlast₁ : o₁ (Fin.last N) = Fin.last N)
    (hlast₂ : o₂ (Fin.last N) = Fin.last N)
    (hprefix : SharedPrefix k o₁ o₂) (w : Path Q (k + 1) → ℝ) :
    IsMoment A (N + 1) r (contrast A r hk o₁ o₂ w) := by
  intro η hη
  simp only [contrast, sub_mul, Finset.sum_sub_distrib, mul_assoc,
    scaleRatio_mul_likelihood hA hη r o₁ hlast₁,
    scaleRatio_mul_likelihood hA hη r o₂ hlast₂]
  rw [sharedPrefix_weightedChain_sum hA hη hk r hprefix, sub_self]

/-- Fixing every outcome in the generated prefix gives the indicator weight
used by equation (24). The last coordinate is its `q₀`. -/
def prefixIndicator {R : Type*} [Zero R] [One R] {Q k : ℕ}
    (q z : Path Q (k + 1)) : R := if z = q then 1 else 0

def sourceNumerator {R : Type*} [CommRing R] {Q N k : ℕ}
    (A : ℕ → State Q → State Q → R) (r : State Q) (hk : k ≤ N)
    (o₁ o₂ : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1)) :
    Path Q (N + 1) → R :=
  contrastNumerator A r hk o₁ o₂ (prefixIndicator q)

def sourceMoment {Q N k : ℕ} (A : Table Q) (r : State Q) (hk : k ≤ N)
    (o₁ o₂ : Equiv.Perm (Fin (N + 1))) (q : Path Q (k + 1)) :
    Path Q (N + 1) → ℝ :=
  contrast A r hk o₁ o₂ (prefixIndicator q)

theorem sourceMoment_eq_numerator_div {Q N k : ℕ} (A : Table Q) (r : State Q)
    (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (q : Path Q (k + 1)) (y : Path Q (N + 1)) :
    sourceMoment A r hk o₁ o₂ q y =
      sourceNumerator A r hk o₁ o₂ q y / originalScale A r y :=
  contrast_eq_numerator_div A r hk o₁ o₂ (prefixIndicator q) y

@[simp] theorem map_sourceNumerator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {Q N k : ℕ} (A : ℕ → State Q → State Q → R)
    (r : State Q) (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (q : Path Q (k + 1)) (y : Path Q (N + 1)) :
    f (sourceNumerator A r hk o₁ o₂ q y) =
      sourceNumerator (fun t a b => f (A t a b)) r hk o₁ o₂ q y := by
  simp only [sourceNumerator, map_contrastNumerator]
  congr 1
  funext z
  simp [prefixIndicator]

theorem sourceMoment_isMoment {Q N k : ℕ} {A : Table Q} (hA : PositiveTable A)
    (r : State Q) (hk : k ≤ N) (o₁ o₂ : Equiv.Perm (Fin (N + 1)))
    (hlast₁ : o₁ (Fin.last N) = Fin.last N)
    (hlast₂ : o₂ (Fin.last N) = Fin.last N)
    (hprefix : SharedPrefix k o₁ o₂) (q : Path Q (k + 1)) :
    IsMoment A (N + 1) r (sourceMoment A r hk o₁ o₂ q) :=
  contrast_isMoment hA r hk o₁ o₂ hlast₁ hlast₂ hprefix (prefixIndicator q)

end

end PanelMoments.PermutationMoments
