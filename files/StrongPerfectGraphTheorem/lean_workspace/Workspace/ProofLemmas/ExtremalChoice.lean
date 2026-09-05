import Mathlib

/-!
# Choosing an extremal object

The paper says *"choose an optimal pseudowheel"*, *"suppose `(C,Y)` is an odd wheel with `Y`
maximal, and subject to that, such that the number of `Y`-complete edges in `C` is minimum"*,
*"there is a minimal connected set `F` such that …"* dozens of times.  Every one of those is an
instance of one of the two lemmas below: minimise, or maximise, a `ℕ`-valued measure over a
nonempty family.

For a family indexed by several objects, instantiate `α` at a product type — e.g.
`α := Set V × Set V × List V` — and destructure with `obtain ⟨⟨X, Y, P⟩, hp, hmin⟩`; a
`simp only []` afterwards β-reduces the measure so that `omega` can see it.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.ExtremalChoice

/-- Minimise a `ℕ`-valued measure over a nonempty family. -/
theorem exists_min_nat {α : Type*} (p : α → Prop) (f : α → ℕ) (h : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → f a ≤ f b := by
  classical
  have hne : {n : ℕ | ∃ a, p a ∧ f a = n}.Nonempty := by
    obtain ⟨a, ha⟩ := h
    exact ⟨f a, a, ha, rfl⟩
  obtain ⟨a, ha, hfa⟩ := Nat.sInf_mem hne
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hfa]
  exact Nat.sInf_le ⟨b, hb, rfl⟩

/-- Maximise a bounded `ℕ`-valued measure over a nonempty family. -/
theorem exists_max_nat {α : Type*} (p : α → Prop) (f : α → ℕ) (N : ℕ)
    (hbd : ∀ a, p a → f a ≤ N) (h : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → f b ≤ f a := by
  classical
  have hne : {n : ℕ | ∃ a, p a ∧ f a = n}.Nonempty := by
    obtain ⟨a, ha⟩ := h
    exact ⟨f a, a, ha, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ a, p a ∧ f a = n} := by
    refine ⟨N, ?_⟩
    rintro n ⟨a, ha, rfl⟩
    exact hbd a ha
  obtain ⟨a, ha, hfa⟩ := Nat.sSup_mem hne hbdd
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hfa]
  exact le_csSup hbdd ⟨b, hb, rfl⟩

/-- Every subset of a finite type has at most `Fintype.card` elements — the bound that makes
`exists_max_nat` applicable to a family of vertex sets. -/
theorem ncard_le_card {V : Type*} [Fintype V] (S : Set V) : S.ncard ≤ Fintype.card V := by
  calc S.ncard ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = Fintype.card V := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]

end Workspace.ProofLemmas.ExtremalChoice
