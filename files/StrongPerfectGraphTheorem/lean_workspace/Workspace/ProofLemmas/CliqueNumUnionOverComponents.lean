import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.CliqueNumOfInducedSet

/-!
# A clique meets only one component, so `ω` over a union of components is bounded

§6 of the proof of 1.5 compresses two applications of the same argument into one
sentence:

> *"Since there are no edges between different `Aᵢ`'s, it follows from (2) that
> `ω(C) = s`, and similarly `ω(D) ≤ t − s`."*

Factored out here so that §6 does not run the argument twice.  Take a maximum clique
`K` of `G` inside the union (`CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum`);
distinct components are anticomplete
(`ComponentsOfSetBasics.anticomplete_of_isComponent`) and `f P ⊆ P`, so all vertices
of `K` outside `R` lie in a single `f P₀`; if there are none, take any component `P₀`,
which exists by `ComponentsOfSetBasics.exists_isComponent_mem` and `A ≠ ∅`.  Then
`K ⊆ R ∪ f P₀` and `CliqueNumOfInducedSet.card_le_cliqueNum_induce` finishes.

Used twice in §6: with `R = B₁`, `f P = C_P`, `k = s` to get `ω(C) ≤ s`; and with
`R = B \ B₁`, `f P = P \ C_P`, `k = t − s` to get `ω(D) ≤ t − s`.  The matching lower
bound `ω(C) ≥ ω(B₁) = s` is plain monotonicity and is left to the root.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.CliqueNumUnionOverComponents

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

/-- If, for every component `P` of the nonempty set `A`, the set `f P` is contained
in `P` and `ω(R ∪ f P) ≤ k`, then `ω` of `R` together with **all** the `f P` at once
is still at most `k`. -/
theorem cliqueNum_union_iUnion_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A R : Set V} {f : Set V → Set V} {k : ℕ}
    (hA : A.Nonempty)
    (hsub : ∀ P : Set V, IsComponent G A P → f P ⊆ P)
    (hbound : ∀ P : Set V, IsComponent G A P → (G.induce (R ∪ f P)).cliqueNum ≤ k) :
    (G.induce (R ∪ ⋃ P ∈ {Q : Set V | IsComponent G A Q}, f P)).cliqueNum ≤ k := by
  classical
  obtain ⟨K, hKU, hK, hcard⟩ :=
    CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G
      (R ∪ ⋃ P ∈ {Q : Set V | IsComponent G A Q}, f P)
  -- a single component `P₀` absorbs every vertex of `K` that is not in `R`
  obtain ⟨P₀, hP₀, hKsub⟩ : ∃ P₀ : Set V, IsComponent G A P₀ ∧ (↑K : Set V) ⊆ R ∪ f P₀ := by
    by_cases hall : (↑K : Set V) ⊆ R
    · -- no such vertex: any component will do, and `A ≠ ∅` supplies one
      obtain ⟨v, hv⟩ := hA
      obtain ⟨P₀, hP₀, -⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A hv
      exact ⟨P₀, hP₀, hall.trans Set.subset_union_left⟩
    · obtain ⟨x, hxK, hxR⟩ : ∃ x ∈ (↑K : Set V), x ∉ R := by
        by_contra hc
        push Not at hc
        exact hall hc
      obtain ⟨P₀, hP₀, hxP₀⟩ : ∃ P₀ : Set V, IsComponent G A P₀ ∧ x ∈ f P₀ := by
        rcases hKU hxK with h | h
        · exact absurd h hxR
        · simpa only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using h
      refine ⟨P₀, hP₀, ?_⟩
      intro y hyK
      rcases hKU hyK with hyR | hyU
      · exact Set.mem_union_left _ hyR
      · obtain ⟨P₁, hP₁, hyP₁⟩ : ∃ P₁ : Set V, IsComponent G A P₁ ∧ y ∈ f P₁ := by
          simpa only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hyU
        rcases eq_or_ne P₀ P₁ with rfl | hne
        · exact Set.mem_union_right _ hyP₁
        · -- there are no edges between distinct components, but `K` is a clique
          rcases eq_or_ne x y with rfl | hxy
          · exact Set.mem_union_right _ hxP₀
          · exact absurd (hK hxK hyK hxy)
              (ComponentsOfSetBasics.anticomplete_of_isComponent G hP₀ hP₁ hne
                x (hsub P₀ hP₀ hxP₀) y (hsub P₁ hP₁ hyP₁))
  calc (G.induce (R ∪ ⋃ P ∈ {Q : Set V | IsComponent G A Q}, f P)).cliqueNum
      = K.card := hcard.symm
    _ ≤ (G.induce (R ∪ f P₀)).cliqueNum :=
        CliqueNumOfInducedSet.card_le_cliqueNum_induce G hKsub hK
    _ ≤ k := hbound P₀ hP₀

end Workspace.ProofLemmas.CliqueNumUnionOverComponents
