import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# The components of a set of vertices

Infrastructure for the proof of 1.5 (item P5 of the natural-language proof).
`IsComponent G A C` says that `C` is a *maximal* connected subset of `A`
(`C ⊆ A`, `ConnectedSet G C`, and `C ⊆ D ⊆ A` with `D` connected forces `D = C`);
the paper introduces this and then uses the following five facts without comment:

* every vertex of `A` lies in a component of `A`;
* a component of a nonempty `A` is nonempty;
* two distinct components are disjoint and mutually anticomplete;
* `A` is the union of its components;
* if `A` is nonempty and not connected, it has two distinct components.

All five share the "choose a connected subset of maximum cardinality" construction,
which is why they live in one module.  Clause `exists_isComponent_mem` applied in
`Gᶜ` is also what supplies the anticomponent `B₁` of `B` in §1 of the proof, so no
separate existence lemma is emitted.

Clause `exists_two_isComponent` is stated as "two distinct components exist" rather
than `|𝒜| ≥ 2` so as to avoid a `Finset`-of-`Set`-of-`Set` encoding; that is all any
call site needs.

None of these lemmas has a counterpart in the paper; they are bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.ComponentsOfSetBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-- A singleton is connected. -/
private theorem connectedSet_singleton {V : Type*} (G : SimpleGraph V) (v : V) :
    ConnectedSet G ({v} : Set V) := by
  intro a b
  exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)

/-- Two components that are *linked* (they meet, or there is an edge between them)
coincide: their union is a connected subset of `A` containing each of them, so
maximality collapses it onto both. -/
private theorem union_eq_of_isComponent {V : Type*} (G : SimpleGraph V)
    {A P Q : Set V} (hP : IsComponent G A P) (hQ : IsComponent G A Q)
    (hlink : (P ∩ Q).Nonempty ∨ ∃ p ∈ P, ∃ q ∈ Q, G.Adj p q) : P = Q := by
  have hcon : ConnectedSet G (P ∪ Q) :=
    Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hP.2.1 hQ.2.1 hlink
  have h1 : P ∪ Q = P :=
    hP.2.2 (P ∪ Q) Set.subset_union_left (Set.union_subset hP.1 hQ.1) hcon
  have h2 : P ∪ Q = Q :=
    hQ.2.2 (P ∪ Q) Set.subset_union_right (Set.union_subset hP.1 hQ.1) hcon
  exact h1.symm.trans h2

/-- **(i)** Every vertex of `A` lies in a component of `A`.

Applied in `Gᶜ` this is the existence of an anticomponent of a nonempty set. -/
theorem exists_isComponent_mem {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A : Set V) {v : V} (hv : v ∈ A) :
    ∃ C : Set V, IsComponent G A C ∧ v ∈ C := by
  classical
  -- `Set V` is finite, so the family of connected subsets of `A` has a maximal
  -- member above the connected set `{v}`.
  have hmem : ({v} : Set V) ∈ {C : Set V | ConnectedSet G C ∧ C ⊆ A} :=
    ⟨connectedSet_singleton G v, by simpa using hv⟩
  obtain ⟨C, hsub, hmax⟩ :=
    Set.Finite.exists_le_maximal (Set.toFinite {C : Set V | ConnectedSet G C ∧ C ⊆ A}) hmem
  refine ⟨C, ⟨hmax.1.2, hmax.1.1, ?_⟩, hsub rfl⟩
  intro D hCD hDA hDcon
  exact Set.Subset.antisymm (hmax.2 ⟨hDcon, hDA⟩ hCD) hCD

/-- **(ii)** A component of a nonempty set is nonempty. -/
theorem nonempty_of_isComponent {V : Type*} [Fintype V] (G : SimpleGraph V)
    {A C : Set V} (hA : A.Nonempty) (hC : IsComponent G A C) :
    C.Nonempty := by
  obtain ⟨v, hv⟩ := hA
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  -- `{v}` is a connected subset of `A` containing `∅`, so maximality forces `{v} = ∅`
  have := hC.2.2 {v} (Set.empty_subset _) (Set.singleton_subset_iff.mpr hv)
    (connectedSet_singleton G v)
  exact absurd (this ▸ (rfl : v ∈ ({v} : Set V))) (Set.notMem_empty v)

/-- **(iii), first half** Two distinct components of `A` are disjoint. -/
theorem disjoint_of_isComponent {V : Type*} [Fintype V] (G : SimpleGraph V)
    {A P Q : Set V} (hP : IsComponent G A P) (hQ : IsComponent G A Q) (hPQ : P ≠ Q) :
    Disjoint P Q := by
  by_contra hd
  rw [Set.not_disjoint_iff] at hd
  obtain ⟨x, hxP, hxQ⟩ := hd
  exact hPQ (union_eq_of_isComponent G hP hQ (Or.inl ⟨x, hxP, hxQ⟩))

/-- **(iii), second half** There is no edge between two distinct components of `A`. -/
theorem anticomplete_of_isComponent {V : Type*} [Fintype V] (G : SimpleGraph V)
    {A P Q : Set V} (hP : IsComponent G A P) (hQ : IsComponent G A Q) (hPQ : P ≠ Q) :
    Anticomplete G P Q := by
  intro x hx y hy hadj
  exact hPQ (union_eq_of_isComponent G hP hQ (Or.inr ⟨x, hx, y, hy, hadj⟩))

/-- **(iv)** `A` is the union of its components. -/
theorem eq_iUnion_isComponent {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Set V) :
    A = ⋃ C ∈ {D : Set V | IsComponent G A D}, C := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · intro hv
    obtain ⟨C, hC, hvC⟩ := exists_isComponent_mem G A hv
    exact ⟨C, hC, hvC⟩
  · rintro ⟨C, hC, hvC⟩
    exact hC.1 hvC

/-- **(v)** A nonempty set that is not connected has two distinct components. -/
theorem exists_two_isComponent {V : Type*} [Fintype V] (G : SimpleGraph V) {A : Set V}
    (hA : A.Nonempty) (hcon : ¬ ConnectedSet G A) :
    ∃ P Q : Set V, IsComponent G A P ∧ IsComponent G A Q ∧ P ≠ Q := by
  -- `A` not connected gives two vertices of `A` not joined inside `A`
  simp only [ConnectedSet, SimpleGraph.Preconnected] at hcon
  push Not at hcon
  obtain ⟨u, v, huv⟩ := hcon
  obtain ⟨P, hP, huP⟩ := exists_isComponent_mem G A u.2
  obtain ⟨Q, hQ, hvQ⟩ := exists_isComponent_mem G A v.2
  refine ⟨P, Q, hP, hQ, ?_⟩
  rintro rfl
  -- if the two components coincided, the walk inside them would lift to `A`
  refine huv ?_
  obtain ⟨w⟩ := hP.2.1 ⟨(u : V), huP⟩ ⟨(v : V), hvQ⟩
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hP.1 z.2⟩, fun {_ _} hab => hab⟩ : (G.induce P) →g (G.induce A)) w⟩

end Workspace.ProofLemmas.ComponentsOfSetBasics
