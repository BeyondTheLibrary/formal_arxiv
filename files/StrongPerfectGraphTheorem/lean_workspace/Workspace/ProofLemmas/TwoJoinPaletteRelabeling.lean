import Mathlib
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

namespace TwoJoinPaletteRelabelingAux

/-- The palette block of colours whose index lies in `[l, r)`. -/
def IV (n l r : ℕ) : Set (Fin n) := {i : Fin n | l ≤ i.val ∧ i.val < r}

theorem IV_inter (n l₁ r₁ l₂ r₂ : ℕ) :
    IV n l₁ r₁ ∩ IV n l₂ r₂ = IV n (max l₁ l₂) (min r₁ r₂) := by
  ext i
  simp only [IV, Set.mem_inter_iff, Set.mem_setOf_eq, max_le_iff, lt_min_iff]
  omega

theorem IV_ncard (n l r : ℕ) (hr : r ≤ n) : (IV n l r).ncard = r - l := by
  classical
  have hset : IV n l r
      = ((Finset.univ.filter (fun i : Fin n => l ≤ i.val ∧ i.val < r) : Finset (Fin n)) :
          Set (Fin n)) := by
    ext i
    simp [IV]
  rw [hset, Set.ncard_coe_finset]
  have himg : (Finset.univ.filter (fun i : Fin n => l ≤ i.val ∧ i.val < r)).image
      (fun i : Fin n => i.val) = Finset.Ico l r := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, by omega⟩, ⟨h1, h2⟩, rfl⟩
  have hinj : Function.Injective (fun i : Fin n => i.val) := Fin.val_injective
  rw [← Finset.card_image_of_injective _ hinj, himg, Nat.card_Ico]

theorem IV_disj (n l₁ r₁ l₂ r₂ : ℕ) (h : r₁ ≤ l₂ ∨ r₂ ≤ l₁) :
    Disjoint (IV n l₁ r₁) (IV n l₂ r₂) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [IV, Set.mem_setOf_eq] at hi hj
  omega

/-- If two pairs of colour sets have matching sizes and matching overlap, one
palette pair can be permuted onto the other. -/
theorem exists_perm_pair {n : ℕ} (A B A' B' : Set (Fin n))
    (h1 : A.ncard = A'.ncard) (h2 : B.ncard = B'.ncard)
    (h3 : (A ∩ B).ncard = (A' ∩ B').ncard) :
    ∃ σ : Equiv.Perm (Fin n), (∀ x ∈ A, σ x ∈ A') ∧ (∀ x ∈ B, σ x ∈ B') := by
  classical
  have conv : ∀ (P : Fin n → Prop) (S : Set (Fin n)), {x : Fin n | P x} = S →
      Nat.card {x : Fin n // P x} = S.ncard := by
    intro P S hPS
    rw [← hPS]
    exact Nat.card_coe_set_eq _
  have key : ∀ S T : Set (Fin n),
      Nat.card {x : Fin n // (decide (x ∈ S), decide (x ∈ T)) = (true, true)}
          = (S ∩ T).ncard ∧
      Nat.card {x : Fin n // (decide (x ∈ S), decide (x ∈ T)) = (true, false)}
          = S.ncard - (S ∩ T).ncard ∧
      Nat.card {x : Fin n // (decide (x ∈ S), decide (x ∈ T)) = (false, true)}
          = T.ncard - (S ∩ T).ncard ∧
      Nat.card {x : Fin n // (decide (x ∈ S), decide (x ∈ T)) = (false, false)}
          = n - (S.ncard + T.ncard - (S ∩ T).ncard) := by
    intro S T
    have e1 : (S ∩ T).ncard + (S \ T).ncard = S.ncard :=
      Set.ncard_inter_add_ncard_diff_eq_ncard S T (Set.toFinite _)
    have e2 : (T ∩ S).ncard + (T \ S).ncard = T.ncard :=
      Set.ncard_inter_add_ncard_diff_eq_ncard T S (Set.toFinite _)
    have e2' : (T ∩ S).ncard = (S ∩ T).ncard := by rw [Set.inter_comm]
    have e3 : (S ∪ T).ncard + (S ∩ T).ncard = S.ncard + T.ncard :=
      Set.ncard_union_add_ncard_inter S T (Set.toFinite _) (Set.toFinite _)
    have e4 : (S ∪ T).ncard + (S ∪ T)ᶜ.ncard = n := by
      have := Set.ncard_add_ncard_compl (S ∪ T) (Set.toFinite _) (Set.toFinite _)
      simpa [Nat.card_eq_fintype_card] using this
    refine ⟨conv _ (S ∩ T) (by ext x; simp), ?_, ?_, ?_⟩
    · rw [conv _ (S \ T) (by ext x; simp)]
      omega
    · rw [conv _ (T \ S) (by ext x; simp; tauto)]
      omega
    · rw [conv _ (S ∪ T)ᶜ (by ext x; simp)]
      omega
  have hcard : ∀ c : Bool × Bool,
      Nat.card {x : Fin n // (decide (x ∈ A), decide (x ∈ B)) = c}
        = Nat.card {x : Fin n // (decide (x ∈ A'), decide (x ∈ B')) = c} := by
    intro c
    obtain ⟨k1, k2, k3, k4⟩ := key A B
    obtain ⟨m1, m2, m3, m4⟩ := key A' B'
    obtain ⟨c1, c2⟩ := c
    cases c1 <;> cases c2
    · rw [k4, m4]; omega
    · rw [k3, m3]; omega
    · rw [k2, m2]; omega
    · rw [k1, m1]; omega
  have e : ∀ c : Bool × Bool,
      {x : Fin n // (decide (x ∈ A), decide (x ∈ B)) = c} ≃
        {x : Fin n // (decide (x ∈ A'), decide (x ∈ B')) = c} :=
    fun c => (Finite.card_eq.mp (hcard c)).some
  refine ⟨Equiv.ofFiberEquiv (f := fun x : Fin n => (decide (x ∈ A), decide (x ∈ B)))
      (g := fun x : Fin n => (decide (x ∈ A'), decide (x ∈ B'))) e, ?_, ?_⟩
  · intro x hx
    have hm := Equiv.ofFiberEquiv_map (f := fun x : Fin n => (decide (x ∈ A), decide (x ∈ B)))
      (g := fun x : Fin n => (decide (x ∈ A'), decide (x ∈ B'))) e x
    simp only [Prod.mk.injEq] at hm
    have h := hm.1
    simp only [hx, decide_true] at h
    simpa using h
  · intro x hx
    have hm := Equiv.ofFiberEquiv_map (f := fun x : Fin n => (decide (x ∈ A), decide (x ∈ B)))
      (g := fun x : Fin n => (decide (x ∈ A'), decide (x ∈ B'))) e x
    simp only [Prod.mk.injEq] at hm
    have h := hm.2
    simp only [hx, decide_true] at h
    simpa using h

theorem disj_of_images {n : ℕ} {S T S' T' : Set (Fin n)} {σ τ : Equiv.Perm (Fin n)}
    (hs : ∀ x ∈ S, σ x ∈ S') (ht : ∀ x ∈ T, τ x ∈ T') (h : Disjoint S' T') :
    Disjoint (Set.image σ S) (Set.image τ T) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzy⟩
  exact Set.disjoint_left.mp h (hs x hx) (hzy ▸ ht z hz)

end TwoJoinPaletteRelabelingAux

open TwoJoinPaletteRelabelingAux

/-- Simultaneously relabel two `Fin n` palettes.  The first two conjuncts are
the odd- and even-marker cases; the final conjunct contains the two instances
of the one-boundary case. -/
theorem TwoJoinPaletteRelabeling
    (n : ℕ)
    (A₁ B₁ A₂ B₂ : Set (Fin n))
    (a₁ b₁ a₂ b₂ : ℕ)
    (hA₁card : A₁.ncard = a₁) (hB₁card : B₁.ncard = b₁)
    (hA₂card : A₂.ncard = a₂) (hB₂card : B₂.ncard = b₂) :
    ((a₁ + a₂ ≤ n) →
      (b₁ + b₂ ≤ n) →
      (A₁ ∩ B₁).ncard = a₁ + b₁ - n →
      (A₂ ∩ B₂).ncard = a₂ + b₂ - n →
      ∃ σ₁ σ₂ : Equiv.Perm (Fin n),
        Disjoint (Set.image σ₁ A₁) (Set.image σ₂ A₂) ∧
          Disjoint (Set.image σ₁ B₁) (Set.image σ₂ B₂)) ∧
    ((a₁ + a₂ ≤ n) →
      (b₁ + b₂ ≤ n) →
      (A₁ ∩ B₁).ncard = min a₁ b₁ →
      (A₂ ∩ B₂).ncard = min a₂ b₂ →
      ∃ σ₁ σ₂ : Equiv.Perm (Fin n),
        Disjoint (Set.image σ₁ A₁) (Set.image σ₂ A₂) ∧
          Disjoint (Set.image σ₁ B₁) (Set.image σ₂ B₂)) ∧
    ((a₁ + a₂ ≤ n) →
      ∃ σ₁ σ₂ : Equiv.Perm (Fin n),
        Disjoint (Set.image σ₁ A₁) (Set.image σ₂ A₂)) ∧
    ((b₁ + b₂ ≤ n) →
      ∃ σ₁ σ₂ : Equiv.Perm (Fin n),
        Disjoint (Set.image σ₁ B₁) (Set.image σ₂ B₂)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- odd-marker case: `A₁ ↦ [0,a₁)`, `B₁ ↦ [n-b₁,n)`, `A₂ ↦ [n-a₂,n)`, `B₂ ↦ [0,b₂)`
    intro haa hbb hi1 hi2
    obtain ⟨σ₁, hσ₁A, hσ₁B⟩ :=
      exists_perm_pair A₁ B₁ (IV n 0 a₁) (IV n (n - b₁) n)
        (by rw [hA₁card, IV_ncard n 0 a₁ (by omega)]; omega)
        (by rw [hB₁card, IV_ncard n (n - b₁) n (by omega)]; omega)
        (by
          rw [hi1, IV_inter, IV_ncard n _ _ (by omega)]
          omega)
    obtain ⟨σ₂, hσ₂A, hσ₂B⟩ :=
      exists_perm_pair A₂ B₂ (IV n (n - a₂) n) (IV n 0 b₂)
        (by rw [hA₂card, IV_ncard n (n - a₂) n (by omega)]; omega)
        (by rw [hB₂card, IV_ncard n 0 b₂ (by omega)]; omega)
        (by
          rw [hi2, IV_inter, IV_ncard n _ _ (by omega)]
          omega)
    exact ⟨σ₁, σ₂, disj_of_images hσ₁A hσ₂A (IV_disj n 0 a₁ (n - a₂) n (Or.inl (by omega))),
      disj_of_images hσ₁B hσ₂B (IV_disj n (n - b₁) n 0 b₂ (Or.inr (by omega)))⟩
  · -- even-marker case: `A₁ ↦ [0,a₁)`, `B₁ ↦ [0,b₁)`, `A₂ ↦ [n-a₂,n)`, `B₂ ↦ [n-b₂,n)`
    intro haa hbb hi1 hi2
    obtain ⟨σ₁, hσ₁A, hσ₁B⟩ :=
      exists_perm_pair A₁ B₁ (IV n 0 a₁) (IV n 0 b₁)
        (by rw [hA₁card, IV_ncard n 0 a₁ (by omega)]; omega)
        (by rw [hB₁card, IV_ncard n 0 b₁ (by omega)]; omega)
        (by
          rw [hi1, IV_inter, IV_ncard n _ _ (by omega)]
          omega)
    obtain ⟨σ₂, hσ₂A, hσ₂B⟩ :=
      exists_perm_pair A₂ B₂ (IV n (n - a₂) n) (IV n (n - b₂) n)
        (by rw [hA₂card, IV_ncard n (n - a₂) n (by omega)]; omega)
        (by rw [hB₂card, IV_ncard n (n - b₂) n (by omega)]; omega)
        (by
          rw [hi2, IV_inter, IV_ncard n _ _ (by omega)]
          omega)
    exact ⟨σ₁, σ₂, disj_of_images hσ₁A hσ₂A (IV_disj n 0 a₁ (n - a₂) n (Or.inl (by omega))),
      disj_of_images hσ₁B hσ₂B (IV_disj n 0 b₁ (n - b₂) n (Or.inl (by omega)))⟩
  · -- only the `A` cross type is active
    intro haa
    obtain ⟨σ₁, hσ₁A, -⟩ :=
      exists_perm_pair A₁ (∅ : Set (Fin n)) (IV n 0 a₁) (∅ : Set (Fin n))
        (by rw [hA₁card, IV_ncard n 0 a₁ (by omega)]; omega)
        (by simp)
        (by simp)
    obtain ⟨σ₂, hσ₂A, -⟩ :=
      exists_perm_pair A₂ (∅ : Set (Fin n)) (IV n (n - a₂) n) (∅ : Set (Fin n))
        (by rw [hA₂card, IV_ncard n (n - a₂) n (by omega)]; omega)
        (by simp)
        (by simp)
    exact ⟨σ₁, σ₂, disj_of_images hσ₁A hσ₂A (IV_disj n 0 a₁ (n - a₂) n (Or.inl (by omega)))⟩
  · -- only the `B` cross type is active
    intro hbb
    obtain ⟨σ₁, hσ₁B, -⟩ :=
      exists_perm_pair B₁ (∅ : Set (Fin n)) (IV n 0 b₁) (∅ : Set (Fin n))
        (by rw [hB₁card, IV_ncard n 0 b₁ (by omega)]; omega)
        (by simp)
        (by simp)
    obtain ⟨σ₂, hσ₂B, -⟩ :=
      exists_perm_pair B₂ (∅ : Set (Fin n)) (IV n (n - b₂) n) (∅ : Set (Fin n))
        (by rw [hB₂card, IV_ncard n (n - b₂) n (by omega)]; omega)
        (by simp)
        (by simp)
    exact ⟨σ₁, σ₂, disj_of_images hσ₁B hσ₂B (IV_disj n 0 b₁ (n - b₂) n (Or.inl (by omega)))⟩

end Workspace.ProofLemmas
