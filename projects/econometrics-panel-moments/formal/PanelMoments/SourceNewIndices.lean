import PanelMoments.SourceCounting

set_option autoImplicit false

/-!
# Explicit coordinates for the new canonical source indices

An admissible shared set omitting the initial slot is empty or a singleton.
For `N ≥ 2`, the complementary indices at horizon `N + 2` therefore have two
explicit forms: an empty shared set with one divergent outcome, or a shared
singleton with two outcome labels. The first divergent slot is always zero.
The equivalence below parameterizes these actual canonical indices; it makes
no claim about independence of their moments.
-/

namespace PanelMoments.SourceNewIndices

open scoped BigOperators
open SourceFamily

noncomputable section

abbrev NewIndex (N : ℕ) :=
  {i : SourceFamily.SourceIndex (N + 1) // (0 : Fin (N + 1)) ∉ i.1.val}

abbrev EmptyParameter (N : ℕ) := Fin N × State 2

abbrev SingletonParameter (N : ℕ) :=
  Σ t : Fin N, {s : Fin N // s ≠ t} × State 2 × State 2

abbrev NewParameter (N : ℕ) := EmptyParameter N ⊕ SingletonParameter N

theorem firstSlot_eq_zero {N : ℕ} (S : SharedSet (N + 1))
    (hzero : (0 : Fin (N + 1)) ∉ S.val) : firstSlot S = 0 :=
  le_antisymm (firstSlot_le S 0 hzero) (Fin.zero_le _)

theorem firstSlot_newIndex {N : ℕ} (i : NewIndex N) : firstSlot i.val.1 = 0 :=
  firstSlot_eq_zero i.val.1 i.property

theorem shared_card_le_one {N : ℕ} (i : NewIndex N) : i.val.1.val.card ≤ 1 := by
  apply SourceCounting.card_le_one_of_no_initial i.val.1
  intro j hj
  have hjzero : j = 0 := Fin.ext hj
  simpa only [hjzero] using i.property

def emptyShared {N : ℕ} (hN : 2 ≤ N) : SharedSet (N + 1) :=
  SourceCounting.emptyShared (by omega)

@[simp] theorem emptyShared_val {N : ℕ} (hN : 2 ≤ N) :
    (emptyShared hN).val = ∅ := rfl

def singletonShared {N : ℕ} (hN : 2 ≤ N) (t : Fin N) : SharedSet (N + 1) :=
  ⟨{t.succ}, by simpa using Nat.succ_le_succ hN, by simp⟩

@[simp] theorem singletonShared_val {N : ℕ} (hN : 2 ≤ N) (t : Fin N) :
    (singletonShared hN t).val = {t.succ} := rfl

theorem zero_not_mem_singletonShared {N : ℕ} (hN : 2 ≤ N) (t : Fin N) :
    (0 : Fin (N + 1)) ∉ (singletonShared hN t).val := by
  rw [singletonShared_val, Finset.mem_singleton]
  exact Ne.symm (Fin.succ_ne_zero t)

theorem sharedSlot_singleton {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (j : Fin (singletonShared hN t).val.card) :
    sharedSlot (singletonShared hN t) j = t.succ :=
  Finset.mem_singleton.mp (sharedSlot_mem (singletonShared hN t) j)

@[simp] theorem firstSlot_empty {N : ℕ} (hN : 2 ≤ N) :
    firstSlot (emptyShared hN) = 0 := firstSlot_eq_zero _ (by simp)

@[simp] theorem firstSlot_singleton {N : ℕ} (hN : 2 ≤ N) (t : Fin N) :
    firstSlot (singletonShared hN t) = 0 :=
  firstSlot_eq_zero _ (zero_not_mem_singletonShared hN t)

def emptySecond {N : ℕ} (hN : 2 ≤ N) (s : Fin N) : SecondSlot (emptyShared hN) :=
  ⟨s.succ, by simp⟩

def singletonSecond {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) : SecondSlot (singletonShared hN t) :=
  ⟨s.val.succ, by
    constructor
    · simpa only [singletonShared_val, Finset.mem_singleton, Fin.succ_inj] using s.property
    · rw [firstSlot_singleton]
      exact Fin.succ_ne_zero _⟩

/-- Empty shared-set columns: second divergent slot `s + 1`, outcome `q₀`. -/
def emptyIndex {N : ℕ} (hN : 2 ≤ N) (s : Fin N) (q₀ : State 2) : NewIndex N :=
  ⟨⟨emptyShared hN, emptySecond hN s, q₀, Fin.elim0⟩, by simp⟩

/-- Singleton columns: shared slot `t + 1`, second divergent slot `s + 1`,
divergent outcome `q₀`, and the shared outcome `q₁`. -/
def singletonIndex {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) : NewIndex N :=
  ⟨⟨singletonShared hN t, singletonSecond hN t s, q₀, fun _ => q₁⟩,
    zero_not_mem_singletonShared hN t⟩

@[simp] theorem emptyIndex_shared {N : ℕ} (hN : 2 ≤ N) (s : Fin N) (q₀ : State 2) :
    (emptyIndex hN s q₀).val.1.val = ∅ := rfl

@[simp] theorem singletonIndex_shared {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    (singletonIndex hN t s q₀ q₁).val.1.val = {t.succ} := rfl

@[simp] theorem emptyIndex_second {N : ℕ} (hN : 2 ≤ N) (s : Fin N) (q₀ : State 2) :
    (emptyIndex hN s q₀).val.2.1.val = s.succ := rfl

@[simp] theorem singletonIndex_second {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    (singletonIndex hN t s q₀ q₁).val.2.1.val = s.val.succ := rfl

theorem singletonShared_injective {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (singletonShared hN) := by
  intro t u h
  have hset : ({t.succ} : Finset (Fin (N + 1))) = {u.succ} :=
    congrArg Subtype.val h
  exact Fin.succ_inj.mp (Finset.singleton_inj.mp hset)

theorem emptyIndex_injective {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (fun p : EmptyParameter N => emptyIndex hN p.1 p.2) := by
  rintro ⟨s, b⟩ ⟨t, c⟩ h
  have hs : s = t := Fin.succ_inj.mp
    (congrArg (fun i : NewIndex N => i.val.2.1.val) h)
  have hb : b = c := congrArg (fun i : NewIndex N => i.val.2.2.1) h
  exact Prod.ext hs hb

theorem singletonIndex_injective {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (fun p : SingletonParameter N =>
      singletonIndex hN p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rintro ⟨t, s, b, c⟩ ⟨u, z, d, e⟩ h
  have htu : t = u := singletonShared_injective hN
    (congrArg (fun i : NewIndex N => i.val.1) h)
  subst u
  have hsz : s = z := Subtype.ext (Fin.succ_inj.mp
    (congrArg (fun i : NewIndex N => i.val.2.1.val) h))
  subst z
  have hbd : b = d := congrArg (fun i : NewIndex N => i.val.2.2.1) h
  subst d
  have hp : (singletonSecond hN t s, b, fun _ : Fin (singletonShared hN t).val.card => c) =
      (singletonSecond hN t s, b, fun _ : Fin (singletonShared hN t).val.card => e) :=
    eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
  have hlabels := congrArg Prod.snd (congrArg Prod.snd hp)
  have hce : c = e := congrFun hlabels ⟨0, by simp⟩
  subst e
  rfl

theorem emptyIndex_ne_singletonIndex {N : ℕ} (hN : 2 ≤ N)
    (s : Fin N) (q₀ : State 2) (t : Fin N) (z : {z : Fin N // z ≠ t})
    (r₀ r₁ : State 2) : emptyIndex hN s q₀ ≠ singletonIndex hN t z r₀ r₁ := by
  intro h
  have hset := congrArg (fun i : NewIndex N => i.val.1.val) h
  exact Finset.empty_ne_singleton _ hset

def parameterIndex {N : ℕ} (hN : 2 ≤ N) : NewParameter N → NewIndex N
  | Sum.inl p => emptyIndex hN p.1 p.2
  | Sum.inr p => singletonIndex hN p.1 p.2.1 p.2.2.1 p.2.2.2

theorem parameterIndex_injective {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (parameterIndex hN) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (emptyIndex_injective hN h)
    | inr q => exact (emptyIndex_ne_singletonIndex hN p.1 p.2
        q.1 q.2.1 q.2.2.1 q.2.2.2 h).elim
  | inr p =>
    cases q with
    | inl q => exact (emptyIndex_ne_singletonIndex hN q.1 q.2
        p.1 p.2.1 p.2.2.1 p.2.2.2 h.symm).elim
    | inr q => exact congrArg Sum.inr (singletonIndex_injective hN h)

/-- Every omitted-zero source index is one of the explicit empty or singleton
constructors. This proves coverage of indices, rather than just a count. -/
theorem parameterIndex_surjective {N : ℕ} (hN : 2 ≤ N) :
    Function.Surjective (parameterIndex hN) := by
  rintro ⟨⟨S, s, q₀, q⟩, hzero⟩
  have hcard : S.val.card ≤ 1 := shared_card_le_one ⟨⟨S, s, q₀, q⟩, hzero⟩
  by_cases hS : S.val.card = 0
  · have hshared : S = emptyShared hN := Subtype.ext (Finset.card_eq_zero.mp hS)
    subst S
    have hs0 : s.val ≠ 0 := by simpa only [firstSlot_empty] using s.property.2
    obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hs0
    have hs : s = emptySecond hN j := Subtype.ext hj
    subst s
    have hq : q = (Fin.elim0 : Fin (emptyShared hN).val.card → State 2) := by
      funext k
      exact Fin.elim0 k
    subst q
    exact ⟨Sum.inl (j, q₀), rfl⟩
  · have hSone : S.val.card = 1 := by omega
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hSone
    have ht0 : t ≠ 0 := by
      intro heq
      apply hzero
      rw [ht, heq]
      simp
    obtain ⟨u, hu⟩ := Fin.eq_succ_of_ne_zero ht0
    have hshared : S = singletonShared hN u := by
      apply Subtype.ext
      simpa only [singletonShared_val, hu] using ht
    subst S
    have hs0 : s.val ≠ 0 := by simpa only [firstSlot_singleton] using s.property.2
    obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hs0
    have hju : j ≠ u := by
      intro heq
      apply s.property.1
      simp only [singletonShared_val, Finset.mem_singleton, hj, heq]
    have hs : s = singletonSecond hN u ⟨j, hju⟩ := Subtype.ext hj
    subst s
    let c : State 2 := q ⟨0, by simp⟩
    have hq : q = (fun _ => c) := by
      funext k
      apply congrArg q
      apply Fin.ext
      have hk := k.isLt
      simp only [singletonShared_val, Finset.card_singleton] at hk
      change k.val = 0
      omega
    refine ⟨Sum.inr ⟨u, ⟨j, hju⟩, q₀, c⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun qs : Fin (singletonShared hN u).val.card → State 2 =>
      (⟨singletonShared hN u, singletonSecond hN u ⟨j, hju⟩, q₀, qs⟩ :
        SourceFamily.SourceIndex (N + 1))) hq.symm

def parameterEquiv {N : ℕ} (hN : 2 ≤ N) : NewParameter N ≃ NewIndex N :=
  Equiv.ofBijective (parameterIndex hN)
    ⟨parameterIndex_injective hN, parameterIndex_surjective hN⟩

/-- Actual coordinates for every new canonical index. The inverse is exactly
the displayed empty/singleton constructor map. -/
def newIndexEquiv {N : ℕ} (hN : 2 ≤ N) : NewIndex N ≃
    (Fin N × State 2) ⊕ (Σ t : Fin N, {s : Fin N // s ≠ t} × State 2 × State 2) :=
  (parameterEquiv hN).symm

@[simp] theorem newIndexEquiv_empty {N : ℕ} (hN : 2 ≤ N) (s : Fin N) (q₀ : State 2) :
    newIndexEquiv hN (emptyIndex hN s q₀) = Sum.inl (s, q₀) :=
  (parameterEquiv hN).symm_apply_apply (Sum.inl (s, q₀))

@[simp] theorem newIndexEquiv_singleton {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    newIndexEquiv hN (singletonIndex hN t s q₀ q₁) = Sum.inr ⟨t, s, q₀, q₁⟩ :=
  (parameterEquiv hN).symm_apply_apply (Sum.inr ⟨t, s, q₀, q₁⟩)

@[simp] theorem newIndexEquiv_symm_empty {N : ℕ} (hN : 2 ≤ N)
    (s : Fin N) (q₀ : State 2) :
    (newIndexEquiv hN).symm (Sum.inl (s, q₀)) = emptyIndex hN s q₀ := rfl

@[simp] theorem newIndexEquiv_symm_singleton {N : ℕ} (hN : 2 ≤ N) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (q₀ q₁ : State 2) :
    (newIndexEquiv hN).symm (Sum.inr ⟨t, s, q₀, q₁⟩) =
      singletonIndex hN t s q₀ q₁ := rfl

theorem newIndex_cases {N : ℕ} (hN : 2 ≤ N) (i : NewIndex N) :
    (∃ s q₀, i = emptyIndex hN s q₀) ∨
      (∃ t s q₀ q₁, i = singletonIndex hN t s q₀ q₁) := by
  obtain ⟨p, rfl⟩ := parameterIndex_surjective hN i
  cases p with
  | inl p => exact Or.inl ⟨p.1, p.2, rfl⟩
  | inr p => exact Or.inr ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, rfl⟩

theorem card_otherSlot {N : ℕ} (t : Fin N) :
    Fintype.card {s : Fin N // s ≠ t} = N - 1 := by
  rw [Fintype.card_subtype_compl (fun s : Fin N => s = t), Fintype.card_fin,
    Fintype.card_subtype_eq]

theorem card_newIndex {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (NewIndex N) = 3 * N + 9 * N * (N - 1) := by
  rw [Fintype.card_congr (newIndexEquiv hN)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
    card_otherSlot, State, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  ring

end

end PanelMoments.SourceNewIndices
