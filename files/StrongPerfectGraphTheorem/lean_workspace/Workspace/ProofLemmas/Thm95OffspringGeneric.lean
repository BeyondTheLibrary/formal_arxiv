import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Knots

/-!
# Striations indexed by an arbitrary finite type

`Types.Knots.SPGT.IsStriation` fixes the index types to be `Fin m` and `Fin n`, and states the
anticompleteness, completeness and twist conditions for `i < i'` only.  The construction of
9.5(1) produces its strips and antistrips indexed by other finite types (the offspring of an
antistrip are indexed by a subtype of `Fin n × Bool`, and the new strip family by
`Option (Fin m)`), and produces the conditions symmetrically, for `i ≠ i'`.

This file bridges the two.  `mk_striation` takes a striation in the symmetric, arbitrarily
indexed form and re-indexes it along `Finite.equivFin`, producing exactly the existential
statement that 9.5(1) has to prove.  Nothing here is mathematics from the paper: the two
directions of each symmetric condition are the same statement because
`SPGT.Anticomplete`, `SPGT.Complete` and `IsTwist` are symmetric.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringGeneric

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- `SPGT.Anticomplete` is symmetric. -/
theorem anticomplete_symm {A B : Set V} (h : Anticomplete G A B) : Anticomplete G B A :=
  fun x hx y hy hadj => h y hy x hx hadj.symm

/-- `SPGT.Complete` is symmetric. -/
theorem complete_symm {A B : Set V} (h : Complete G A B) : Complete G B A :=
  fun x hx y hy => (h y hy x hx).symm

/-- Swapping the two antistrips of a twist gives a twist. -/
theorem isTwist_swap_T {S₁ S₂ T₁ T₂ : Set V × Set V × Set V}
    (h : IsTwist G S₁ S₂ T₁ T₂) : IsTwist G S₁ S₂ T₂ T₁ := h.symm

/-- Swapping the two strips of a twist gives a twist. -/
theorem isTwist_swap_S {S₁ S₂ T₁ T₂ : Set V × Set V × Set V}
    (h : IsTwist G S₁ S₂ T₁ T₂) : IsTwist G S₂ S₁ T₁ T₂ := by
  have hag : ∀ T, AgreeOn G S₁ S₂ T → AgreeOn G S₂ S₁ T :=
    fun _ h => h.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
  rcases h with ⟨hag', hd⟩ | ⟨hag', hd⟩
  · exact Or.inl ⟨hag _ hag', hd.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩
  · exact Or.inr ⟨hag _ hag', hd.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩

/-- Two distinct elements force `2 ≤ Nat.card`. -/
theorem two_le_card {ι : Type*} [Finite ι] {i i' : ι} (h : i ≠ i') : 2 ≤ Nat.card ι := by
  classical
  have : Function.Injective (fun b : Bool => if b then i else i') := by
    intro b b' hbb'
    cases b <;> cases b' <;> simp_all
  simpa using Nat.card_le_card_of_injective _ this

/-- **Re-indexing a striation.**  A family of strips and a family of antistrips indexed by
arbitrary finite types, satisfying the conditions of `IsStriation` in their symmetric (`i ≠ i'`)
form, give a striation in the sense of `Types.Knots.SPGT.IsStriation`, on the same vertex set. -/
theorem mk_striation {ι κ : Type*} [Finite ι] [Finite κ]
    (S : ι → Set V × Set V × Set V) (T : κ → Set V × Set V × Set V)
    (hS : ∀ i, IsStrip G (S i)) (hT : ∀ j, IsAntistrip G (T j))
    (hSS : ∀ i i', i ≠ i' → Disjoint (stripVertices (S i)) (stripVertices (S i')))
    (hTT : ∀ j j', j ≠ j' → Disjoint (stripVertices (T j)) (stripVertices (T j')))
    (hST : ∀ i j, Disjoint (stripVertices (S i)) (stripVertices (T j)))
    (hSo : ∀ i p, IsSRung G (S i) p → Odd (pathLength p))
    (hTo : ∀ j p, IsSRung Gᶜ (T j) p → Odd (pathLength p))
    (hi : ∃ i i' : ι, i ≠ i') (hj : ∃ j j' : κ, j ≠ j')
    (hSa : ∀ i i', i ≠ i' → Anticomplete G (stripVertices (S i)) (stripVertices (S i')))
    (hTc : ∀ j j', j ≠ j' → Complete G (stripVertices (T j)) (stripVertices (T j')))
    (hpc : ∀ i j, ParallelStripAntistrip G (S i) (T j) ∨ CoParallel G (S i) (T j))
    (htwS : ∀ i i', i ≠ i' → ∃ j j', j ≠ j' ∧ IsTwist G (S i) (S i') (T j) (T j'))
    (htwT : ∀ j j', j ≠ j' → ∃ i i', i ≠ i' ∧ IsTwist G (S i) (S i') (T j) (T j')) :
    ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V), IsStriation G S' T' ∧
      striationVertices S' T' =
        (⋃ i : ι, stripVertices (S i)) ∪ (⋃ j : κ, stripVertices (T j)) := by
  classical
  obtain ⟨i₀, i₁, hi₀₁⟩ := hi
  obtain ⟨j₀, j₁, hj₀₁⟩ := hj
  let e := Finite.equivFin ι
  let f := Finite.equivFin κ
  refine ⟨Nat.card ι, Nat.card κ, fun a => S (e.symm a), fun b => T (f.symm b), ?_, ?_⟩
  · refine ⟨fun a => hS _, fun b => hT _, ?_, ?_, fun a b => hST _ _, fun a p h => hSo _ p h,
      fun b p h => hTo _ p h, two_le_card hi₀₁, two_le_card hj₀₁, ?_, ?_,
      fun a b => hpc _ _, ?_, ?_⟩
    · exact fun a a' h => hSS _ _ (fun hc => h (e.symm.injective hc))
    · exact fun b b' h => hTT _ _ (fun hc => h (f.symm.injective hc))
    · exact fun a a' h => hSa _ _ (fun hc => (ne_of_lt h) (e.symm.injective hc))
    · exact fun b b' h => hTc _ _ (fun hc => (ne_of_lt h) (f.symm.injective hc))
    · intro a a' h
      obtain ⟨b, b', hbb', ht⟩ := htwS _ _ (fun hc => (ne_of_lt h) (e.symm.injective hc))
      exact ⟨f b, f b', fun hc => hbb' (f.injective hc), by simpa using ht⟩
    · intro b b' h
      obtain ⟨a, a', haa', ht⟩ := htwT _ _ (fun hc => (ne_of_lt h) (f.symm.injective hc))
      exact ⟨e a, e a', fun hc => haa' (e.injective hc), by simpa using ht⟩
  · unfold striationVertices
    congr 1
    · refine Set.ext (fun v => ⟨?_, ?_⟩)
      · rintro hv
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
        exact Set.mem_iUnion_of_mem _ ha
      · rintro hv
        obtain ⟨i, hii⟩ := Set.mem_iUnion.mp hv
        exact Set.mem_iUnion_of_mem (e i) (by simpa using hii)
    · refine Set.ext (fun v => ⟨?_, ?_⟩)
      · rintro hv
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hv
        exact Set.mem_iUnion_of_mem _ hb
      · rintro hv
        obtain ⟨j, hjj⟩ := Set.mem_iUnion.mp hv
        exact Set.mem_iUnion_of_mem (f j) (by simpa using hjj)

end Workspace.ProofLemmas.Thm95OffspringGeneric
