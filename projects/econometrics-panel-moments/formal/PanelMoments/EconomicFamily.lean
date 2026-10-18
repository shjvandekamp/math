import PanelMoments.Genericity

/-!
# The normalized economic parameter family for any panel length

There are four state-dependence parameters, two scalar-covariate slopes, and
one covariate for each observed period. The baseline outcome column and the
baseline lag effects are normalized exactly as in the four-period family.
The explicit witness belongs to this economic family and yields pairwise
distinct positive conic parameters for every finite number of structural
blocks. This module makes no rank or generic-minor claim.
-/

namespace PanelMoments.EconomicFamily

open scoped BigOperators

noncomputable section

/-- Four normalized state-dependence coefficients, two slopes, then `T`
scalar covariates. -/
abbrev EconomicParameter (T : ℕ) := Fin (T + 6) → ℝ

def parameterGamma {T : ℕ} (θ : EconomicParameter T) (q : Fin 2) (r : State 2) : ℝ :=
  if r = 0 then 0 else θ ⟨q.val * 2 + (r.val - 1), by omega⟩

def parameterBeta {T : ℕ} (θ : EconomicParameter T) (q : Fin 2) (_ : Fin 1) : ℝ :=
  θ ⟨4 + q.val, by omega⟩

def parameterCovariate {T : ℕ} (θ : EconomicParameter T) (t : ℕ) (_ : Fin 1) : ℝ :=
  if ht : t < T then θ ⟨6 + t, by omega⟩ else 0

def parameterTable {T : ℕ} (θ : EconomicParameter T) : Table 2 :=
  economicTable (parameterGamma θ) (parameterBeta θ) (parameterCovariate θ)

@[simp]
theorem parameterGamma_baseline {T : ℕ} (θ : EconomicParameter T) (q : Fin 2) :
    parameterGamma θ q 0 = 0 := by
  simp [parameterGamma]

@[simp]
theorem parameterTable_baseline {T : ℕ} (θ : EconomicParameter T) (t : ℕ) (r : State 2) :
    parameterTable θ t r 0 = 1 := by
  simp [parameterTable]

theorem parameterTable_positive {T : ℕ} (θ : EconomicParameter T) :
    PositiveTable (parameterTable θ) :=
  economicTable_pos _ _ _

/-- Every table entry is real analytic on the full normalized economic domain. -/
theorem parameterTable_analytic (T t : ℕ) (r q : State 2) :
    AnalyticOnNhd ℝ (fun θ : EconomicParameter T => parameterTable θ t r q) Set.univ := by
  intro θ _
  have hp (i : Fin (T + 6)) :
      AnalyticAt ℝ (fun z : EconomicParameter T => z i) θ :=
    (ContinuousLinearMap.proj (R := ℝ) i).analyticAt θ
  have hg (i : Fin 2) : AnalyticAt ℝ (fun z => parameterGamma z i r) θ := by
    unfold parameterGamma
    split_ifs
    · exact analyticAt_const
    · exact hp _
  have hb (i : Fin 2) : AnalyticAt ℝ (fun z => parameterBeta z i 0) θ := hp _
  have hx : AnalyticAt ℝ (fun z => parameterCovariate z t 0) θ := by
    unfold parameterCovariate
    split_ifs
    · exact hp _
    · exact analyticAt_const
  refine Fin.cases ?_ (fun i => ?_) q
  · simpa [parameterTable] using (analyticAt_const :
      AnalyticAt ℝ (fun _ : EconomicParameter T => (1 : ℝ)) θ)
  · simpa [parameterTable, economicTable, economicIndex, Fin.sum_univ_one] using
      ((hg i).add (hx.mul (hb i))).rexp'

/-- The first four entries are `log 2`, `2 log 2`, `2 log 2`, `4 log 2`;
the next two entries are `1`, `2`. Entry `6 + t` is `3(t + 1) log 2`.
The index formula works for every `T`, including zero. -/
def parameterWitness (T : ℕ) : EconomicParameter T := fun i =>
  if i.val < 4 then
    (((i.val / 2 + 1) * (i.val % 2 + 1) : ℕ) : ℝ) * Real.log 2
  else if i.val < 6 then
    ((i.val - 3 : ℕ) : ℝ)
  else
    ((3 * (i.val - 5) : ℕ) : ℝ) * Real.log 2

theorem parameterWitness_gamma (T : ℕ) (q : Fin 2) (r : State 2) :
    parameterGamma (parameterWitness T) q r =
      (((q.val + 1) * r.val : ℕ) : ℝ) * Real.log 2 := by
  fin_cases q <;> fin_cases r <;>
    norm_num [parameterGamma, parameterWitness]

theorem parameterWitness_beta (T : ℕ) (q : Fin 2) (k : Fin 1) :
    parameterBeta (parameterWitness T) q k = ((q.val + 1 : ℕ) : ℝ) := by
  fin_cases q <;> norm_num [parameterBeta, parameterWitness]

theorem parameterWitness_covariate (T : ℕ) (t : Fin T) (k : Fin 1) :
    parameterCovariate (parameterWitness T) t.val k =
      ((3 * (t.val + 1) : ℕ) : ℝ) * Real.log 2 := by
  have h₄ : ¬6 + t.val < 4 := by omega
  have h₆ : ¬6 + t.val < 6 := by omega
  have hsub : 6 + t.val - 5 = t.val + 1 := by omega
  simp [parameterCovariate, t.isLt, parameterWitness, h₄, h₆, hsub]

theorem parameterWitness_index (T : ℕ) (t : Fin T) (r q : State 2) :
    economicIndex (parameterGamma (parameterWitness T))
        (parameterBeta (parameterWitness T)) (parameterCovariate (parameterWitness T))
        t.val r q =
      (((3 * (t.val + 1) + r.val) * q.val : ℕ) : ℝ) * Real.log 2 := by
  refine Fin.cases ?_ (fun q => ?_) q
  · simp [economicIndex]
  · simp only [economicIndex, Fin.cons_succ, Fin.sum_univ_one]
    rw [parameterWitness_gamma, parameterWitness_covariate, parameterWitness_beta]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    ring

/-- The economic witness realizes the same exact power table at every
observed period, with zero-based time and state indices. -/
theorem parameterWitness_table (T : ℕ) (t : Fin T) (r q : State 2) :
    parameterTable (parameterWitness T) t.val r q =
      (2 : ℝ) ^ ((3 * (t.val + 1) + r.val) * q.val) := by
  change Real.exp (economicIndex (parameterGamma (parameterWitness T))
    (parameterBeta (parameterWitness T)) (parameterCovariate (parameterWitness T))
    t.val r q) = _
  rw [parameterWitness_index, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Conic parameter for the block at observed time `t + 1`; the initial
period has already been separated from these `T - 1` blocks. -/
def structuralConicParameter {T : ℕ} (t : Fin (T - 1)) (r : State 2) : ℝ :=
  (2 : ℝ) ^ (3 * (t.val + 2) + r.val)

theorem structuralConicParameter_pos {T : ℕ} (t : Fin (T - 1)) (r : State 2) :
    0 < structuralConicParameter t r :=
  pow_pos (by norm_num) _

/-- Distinct block-state pairs have distinct exponents, since each block
occupies three consecutive integers. Powers of two preserve this distinction. -/
theorem structuralConicParameter_injective (T : ℕ) :
    Function.Injective (fun p : Fin (T - 1) × State 2 =>
      structuralConicParameter p.1 p.2) := by
  rintro ⟨t, r⟩ ⟨u, s⟩ h
  change (2 : ℝ) ^ (3 * (t.val + 2) + r.val) =
    (2 : ℝ) ^ (3 * (u.val + 2) + s.val) at h
  have hexp : 3 * (t.val + 2) + r.val = 3 * (u.val + 2) + s.val :=
    (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)) h
  have ht : t.val = u.val := by omega
  have hr : r.val = s.val := by omega
  exact Prod.ext (Fin.ext ht) (Fin.ext hr)

theorem structuralConicParameter_row_injective {T : ℕ} (t : Fin (T - 1)) :
    Function.Injective (structuralConicParameter t) := by
  intro r s h
  have hp : (t, r) = (t, s) := structuralConicParameter_injective T h
  exact congrArg Prod.snd hp

/-- The witness table at each structural block has the coefficients
`(1, w, w²)` of the conic line used in the geometric construction. -/
theorem parameterWitness_structural_table (T : ℕ) (t : Fin (T - 1)) (r q : State 2) :
    parameterTable (parameterWitness T) (t.val + 1) r q =
      structuralConicParameter t r ^ q.val := by
  have ht : t.val + 1 < T := by omega
  have h := parameterWitness_table T ⟨t.val + 1, ht⟩ r q
  simpa [structuralConicParameter, Nat.add_assoc, pow_mul] using h

end

end PanelMoments.EconomicFamily
