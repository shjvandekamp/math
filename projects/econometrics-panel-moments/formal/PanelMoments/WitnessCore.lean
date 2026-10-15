import PanelMoments.WitnessData
import PanelMoments.WitnessRows

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# Model formulas for concrete rank witnesses

This module contains executable formulas, their exact model bridges, and fixed
minor definitions. The larger finite-field checks live in independently cached
row modules so each kernel computation can run within bounded memory.
-/

namespace PanelMoments.Witness

open scoped BigOperators

abbrev RingTable (R : Type*) := ℕ → State 2 → State 2 → R

/-- The normalized scalar-covariate witness: x_t = 3(t+1) log 2,
β_q = q and γ_qr = qr log 2. Arguments are time, lag state, outcome. -/
def table {R : Type*} [CommSemiring R] : RingTable R :=
  fun t r q => (2 : R) ^ ((3 * (t + 1) + r.val) * q.val)

def ringEffect {R : Type*} [One R] (η : Fin 2 → R) : State 2 → R := Fin.cons 1 η

def ringDenominator {R : Type*} [CommSemiring R]
    (A : RingTable R) (η : Fin 2 → R) (t : ℕ) (r : State 2) : R :=
  ∑ q, A t r q * ringEffect η q

def pathAmplitude {R : Type*} [CommSemiring R] (A : RingTable R) :
    (T : ℕ) → State 2 → Path 2 T → R
  | 0, _, _ => 1
  | T + 1, r, y => A 0 r (y 0) *
      pathAmplitude (fun t => A (t + 1)) T (y 0) (Fin.tail y)

def fullyReducedEval {R : Type*} [CommSemiring R]
    (A : RingTable R) (η : Fin 2 → R) : (T : ℕ) → State 2 → Path 2 T → R
  | 0, _, _ => 1
  | T + 1, r, y => ringEffect η (y 0) *
      (∏ s ∈ Finset.univ.erase r, ringDenominator A η 0 s) *
      fullyReducedEval (fun t => A (t + 1)) η T (y 0) (Fin.tail y)

/-- Evaluation of the normalized cleared numerator F_y/A_y. It is independent
of the initial state because the initial transition scale has been removed. -/
def reducedEval {R : Type*} [CommSemiring R]
    (A : RingTable R) (η : Fin 2 → R) : (T : ℕ) → Path 2 T → R
  | 0, _ => 1
  | T + 1, y => ringEffect η (y 0) *
      fullyReducedEval (fun t => A (t + 1)) η T (y 0) (Fin.tail y)

theorem map_table {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (t : ℕ) (r q : State 2) :
    f (table (R := R) t r q) = table (R := S) t r q := by
  simp [table, map_ofNat]

theorem map_ringEffect {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (η : Fin 2 → R) (q : State 2) :
    f (ringEffect η q) = ringEffect (fun k => f (η k)) q := by
  refine Fin.cases ?_ (fun k => ?_) q <;> simp [ringEffect]

theorem map_ringDenominator {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : RingTable R) (η : Fin 2 → R) (t : ℕ) (r : State 2) :
    f (ringDenominator A η t r) =
      ringDenominator (fun t r q => f (A t r q)) (fun k => f (η k)) t r := by
  simp [ringDenominator, map_ringEffect]

theorem map_fullyReducedEval {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : RingTable R) (η : Fin 2 → R)
    (T : ℕ) (r : State 2) (y : Path 2 T) :
    f (fullyReducedEval A η T r y) =
      fullyReducedEval (fun t r q => f (A t r q)) (fun k => f (η k)) T r y := by
  induction T generalizing A r with
  | zero => simp [fullyReducedEval]
  | succ T ih => simp [fullyReducedEval, map_ringEffect, map_ringDenominator, ih]

theorem map_reducedEval {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : RingTable R) (η : Fin 2 → R) (T : ℕ) (y : Path 2 T) :
    f (reducedEval A η T y) =
      reducedEval (fun t r q => f (A t r q)) (fun k => f (η k)) T y := by
  cases T <;> simp [reducedEval, map_ringEffect, map_fullyReducedEval]

theorem fullyReducedEval_congr {R : Type*} [CommSemiring R]
    (A B : RingTable R) (η : Fin 2 → R) (T : ℕ)
    (hAB : ∀ t < T, ∀ r q, A t r q = B t r q)
    (r : State 2) (y : Path 2 T) :
    fullyReducedEval A η T r y = fullyReducedEval B η T r y := by
  induction T generalizing A B r with
  | zero => rfl
  | succ T ih =>
    have h₀ : A 0 = B 0 := by
      funext r q
      exact hAB 0 (Nat.zero_lt_succ T) r q
    have hs : ∀ t < T, ∀ r q, A (t + 1) r q = B (t + 1) r q := by
      intro t ht r q
      exact hAB (t + 1) (Nat.succ_lt_succ ht) r q
    simp only [fullyReducedEval, ringDenominator]
    rw [h₀, ih _ _ hs]

theorem reducedEval_congr {R : Type*} [CommSemiring R]
    (A B : RingTable R) (η : Fin 2 → R) (T : ℕ)
    (hAB : ∀ t < T, ∀ r q, A t r q = B t r q) (y : Path 2 T) :
    reducedEval A η T y = reducedEval B η T y := by
  cases T with
  | zero => rfl
  | succ T =>
    simp only [reducedEval]
    congr 1
    apply fullyReducedEval_congr
    intro t ht r q
    exact hAB (t + 1) (Nat.succ_lt_succ ht) r q

noncomputable section

theorem table_pos : PositiveTable (table (R := ℝ)) := by
  intro t r q
  exact pow_pos zero_lt_two _

theorem pathAmplitude_pos {A : Table 2} (hA : PositiveTable A)
    (T : ℕ) (r : State 2) (y : Path 2 T) : 0 < pathAmplitude A T r y := by
  induction T generalizing A r with
  | zero => exact zero_lt_one
  | succ T ih =>
    exact mul_pos (hA 0 r (y 0)) (ih (fun t r q => hA (t + 1) r q) _ _)

/-- Algebraic bridge from the executable certificate formula to the model's
polynomial numerator. No value of a computed matrix is assumed here. -/
theorem eval_fullyClearedPathPoly (A : Table 2) (η : Fin 2 → ℝ)
    (T : ℕ) (r : State 2) (y : Path 2 T) :
    MvPolynomial.eval η (fullyClearedPathPoly A T r y) =
      pathAmplitude A T r y * fullyReducedEval A η T r y := by
  induction T generalizing A r with
  | zero => simp [fullyClearedPathPoly, pathAmplitude, fullyReducedEval]
  | succ T ih =>
    simp only [fullyClearedPathPoly, map_mul, map_prod, MvPolynomial.eval_C,
      eval_effectPoly, eval_denominatorPoly, ih, pathAmplitude, fullyReducedEval]
    change (A 0 r (y 0) * ringEffect η (y 0)) *
        (∏ s ∈ Finset.univ.erase r, ringDenominator A η 0 s) *
        (pathAmplitude (shift A) T (y 0) (Fin.tail y) *
          fullyReducedEval (shift A) η T (y 0) (Fin.tail y)) = _
    ring_nf <;> simp only [Nat.add_comm] <;> rfl

/-- The exact evaluation bridge, for every initial state and every effect vector. -/
theorem eval_clearedPathPoly (A : Table 2) (η : Fin 2 → ℝ)
    (T : ℕ) (r : State 2) (y : Path 2 T) :
    MvPolynomial.eval η (clearedPathPoly A T r y) =
      pathAmplitude A T r y * reducedEval A η T y := by
  cases T with
  | zero => simp [clearedPathPoly, pathAmplitude, reducedEval]
  | succ T =>
    simp only [clearedPathPoly, map_mul, MvPolynomial.eval_C, eval_effectPoly,
      eval_fullyClearedPathPoly, pathAmplitude, reducedEval]
    change (A 0 r (y 0) * ringEffect η (y 0)) *
      (pathAmplitude (shift A) T (y 0) (Fin.tail y) *
        fullyReducedEval (shift A) η T (y 0) (Fin.tail y)) = _
    ring_nf <;> simp only [Nat.add_comm] <;> rfl

end

/-- Fixed 48-by-48 evaluation minor; its entries are primitive path formulas. -/
def evaluationMinor {R : Type*} [CommSemiring R] (A : RingTable R) :
    Matrix (Fin 48) (Fin 48) R := fun i j =>
  reducedEval A (fun q => (evaluationPoints i q : R)) 4 (evaluationPaths j)

theorem map_evaluationMinor {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : RingTable R) :
    (evaluationMinor A).map f = evaluationMinor (fun t r q => f (A t r q)) := by
  ext i j
  simp [evaluationMinor, map_reducedEval]

theorem evaluationMinor_congr {R : Type*} [CommSemiring R]
    (A B : RingTable R) (hAB : ∀ t < 4, ∀ r q, A t r q = B t r q) :
    evaluationMinor A = evaluationMinor B := by
  ext i j
  exact reducedEval_congr A B _ 4 hAB _

/-- Each source contrast occurs exactly once in the explicit row enumeration. -/
theorem sourceRows_bijective : Function.Bijective sourceRows := by
  decide +kernel

/-- The source-moment minor may select different path columns for each initial state. -/
def sourcePaths : State 2 → Fin 33 → Path 2 4 :=
  ![sourcePaths0, sourcePaths1, sourcePaths2]

def sourceResidue : State 2 → Matrix (Fin 33) (Fin 33) (ZMod 11) :=
  ![sourceResidue0, sourceResidue1, sourceResidue2]

def sourceInverse : State 2 → Matrix (Fin 33) (Fin 33) (ZMod 11) :=
  ![sourceInverse0, sourceInverse1, sourceInverse2]

/-- A fixed minor of the actual source numerators, with all 33 rows included. -/
noncomputable def sourceMinor {R : Type*} [CommRing R] (A : RingTable R) (r : State 2) :
    Matrix (Fin 33) (Fin 33) R := fun i j =>
  sourceNumerator A r (sourceRows i) (sourcePaths r j)

theorem map_sourceMinor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : RingTable R) (r : State 2) :
    (sourceMinor A r).map f = sourceMinor (fun t s q => f (A t s q)) r := by
  ext i j
  simp [sourceMinor]

end PanelMoments.Witness
