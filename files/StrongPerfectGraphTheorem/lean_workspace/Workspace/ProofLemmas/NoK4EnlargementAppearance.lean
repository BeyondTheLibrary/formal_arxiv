import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Statements.S05.Thm_5_3
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# No `K₄`-enlargement appears

This module discharges the **first paragraph** of the proof of 9.6 (printed p. 54):

> *"If there is an appearance in `G` of some `K₄`-enlargement, say `L(H₀)`, then by 5.3, either
> `H₀ = K₃,₃`, which is impossible by hypothesis, or there is a subgraph `H''` of `H₀` which is
> a bipartite subdivision of `K₄`, such that `L(H'')` is nondegenerate, and again this is
> impossible by hypothesis.  So there is no appearance in `G` of a `K₄`-enlargement, and
> similarly there is none in `Ḡ`."*

The result produced here is exactly the `hnoenl` hypothesis that `thm_9_4` and `thm_9_5`
demand, so it is the bridge from 9.6's own hypotheses into §9's main machinery.

The argument is the `K₄` analogue of the `hnoenl` block already proved inside
`Workspace.Statements.S05.Thm_5_2` (which does the same for `K₃,₃`-enlargements).  Given a
`K₄`-enlargement `J'` with an appearance `L(H')` in `Gx`, the subdivision `H'` is bipartite and
cyclically 3-connected, so 5.3 applies and leaves three cases:

* **`H' = K₃,₃`.**  Then `L(K₃,₃) ≃ Gx|K'`, contradicting `hnoL33`.  (This is where 9.6 uses
  its *"no induced subgraph isomorphic to `L(K₃,₃)`"* hypothesis; the corresponding case of
  5.2 was an edge count instead, which does **not** work for `K₄`: `|E(K₄)| = 6 ≤ |E(D)| <
  |E(J')| ≤ |E(H')| = |E(K₃,₃)| = 9` is perfectly consistent.)
* **`H'` is a subdivision of `K₄`.**  Then the branch-vertices of `H'` are simultaneously the
  image of `V(J')` and the image of `V(K₄)`, so `|V(J')| ≤ 4`; three-connectivity forces
  `|V(J')| = 4`, and then `|E(K₄)| ≤ |E(D)| < |E(J')| ≤ |E(K₄)|`, absurd.  (No arithmetic on
  the literal `6` is needed — the two bounds are literally the same quantity.)
* **`H'` has a subgraph `H''` which is a `K₄`-subdivision with `L(H'')` nondegenerate.**  Since
  `L(H'')` is an *induced* subgraph of `L(H')`, hence of `Gx`, it is an appearance of `K₄` in
  `Gx`, so `hdeg` makes it degenerate — contradiction.

**Caller's obligation for the complement.**  The statement is parameterised by an arbitrary
`Gx : SimpleGraph V`, so 9.6 applies it once to `G` and once to `Gᶜ`.  For the `Gᶜ` call the
hypothesis needed is *"no induced subgraph of `Gᶜ` is isomorphic to `L(K₃,₃)`"*, which does not
appear literally among 9.6's hypotheses; it follows from the one that does, because `L(K₃,₃)`
(the `3 × 3` rook's graph, the unique `SRG(9,4,1,2)`) is **self-complementary**.  That fact is
not yet in the development.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.NoK4EnlargementAppearance

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {V : Type*}

/-- **No `K₄`-enlargement appears in `Gx`** — the first paragraph of the proof of 9.6.

`hdeg` is 9.6's *"every appearance of `K₄` in `Gx` is degenerate"* and `hnoL33` is its
*"there is no induced subgraph of `Gx` isomorphic to `L(K₃,₃)`"*.  The conclusion is the
`hnoenl` hypothesis of `thm_9_4` / `thm_9_5`, restricted to `Gx` (those statements ask for the
disjunction over `G` and `Gᶜ`, which is this lemma applied twice). -/
theorem no_k4_enlargement_appears (Gx : SimpleGraph V)
    (hdeg : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hnoL33 : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g Gx.induce K)) :
    ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ Appears Gx J' := by
  classical
  rintro ⟨m', J', ⟨hJ'3, S, hSne, nD, Dg, hDsub, ⟨φD⟩⟩, n', H', K', hsub', φ'⟩
  obtain ⟨hsubJ', hbip'⟩ := hsub'
  obtain ⟨φ'⟩ := φ'
  have hc3 : CyclicallyThreeConnected H' := ⟨m', J', hJ'3, hsubJ'⟩
  rcases _root_.Workspace.Statements.S05.SPGT.thm_5_3 H' hbip' hc3 with
    heH | hsub4 | ⟨Ssub, hsubK4, hnondeg⟩
  · -- (a) `H' = K₃,₃`: then `L(K₃,₃)` is an induced subgraph of `Gx`.
    obtain ⟨eH⟩ := heH
    exact hnoL33 ⟨K', ⟨(eH.lineGraph).symm.trans φ'⟩⟩
  · -- (b) `H'` is a subdivision of `K₄`: the branch-vertices pin `|V(J')|` to `4`.
    obtain ⟨ι', T', hι', htrack', hlen', hrev', hdisj', hnew', hcover', hedges'⟩ := hsubJ'
    obtain ⟨ι4, T4, hι4, htrack4, hlen4, hrev4, hdisj4, hnew4, hcover4, hedges4⟩ := hsub4
    have hdeg' : ∀ u : Fin m', 3 ≤ (J'.neighborSet u).ncard :=
      three_le_degree_of_three_connected J' hJ'3
    have hA : Set.range ι' ⊆ branchVertices H' :=
      range_subset_branchVertices hι' htrack' hlen' hdisj' hnew' hdeg'
    have hB : branchVertices H' ⊆ Set.range ι4 :=
      branchVertices_subset_range htrack4 hrev4 hdisj4 hcover4 hedges4
    have hcardA : (Set.range ι').ncard = m' := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hι', Set.ncard_univ]
      simp
    have hcardB : (Set.range ι4).ncard = 4 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hι4, Set.ncard_univ]
      simp
    have hle : m' ≤ 4 := by
      have := Set.ncard_le_ncard (hA.trans hB) (Set.toFinite _)
      omega
    have hgt : 3 < m' := by simpa using hJ'3.1
    obtain rfl : m' = 4 := by omega
    -- `|E(K₄)| ≤ |E(D)| < |E(J')| ≤ |E(K₄)|`.
    have h1 : (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard ≤ Dg.edgeSet.ncard :=
      edgeSet_ncard_le_of_isSubdivision (⊤ : SimpleGraph (Fin 4)) Dg hDsub
    have h2 : Dg.edgeSet.ncard < J'.edgeSet.ncard :=
      edgeSet_ncard_lt_of_ne_top J' hJ'3 S hSne Dg φD
    have h3 : J'.edgeSet.ncard ≤ (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard :=
      Set.ncard_le_ncard (SimpleGraph.edgeSet_mono le_top) (Set.toFinite _)
    omega
  · -- (c) a nondegenerate `K₄`-subdivision inside `H'`, hence an appearance of `K₄` in `Gx`.
    haveI : Fintype ↥Ssub.verts := Fintype.ofFinite _
    obtain ⟨K'', -, θ⟩ := exists_lineGraph_iso_induce_of_subgraph φ' Ssub
    obtain ⟨θ⟩ := θ
    obtain ⟨H'', ψ⟩ : ∃ H'' : SimpleGraph (Fin (Fintype.card ↥Ssub.verts)),
        Nonempty (Ssub.coe ≃g H'') := ⟨_, ⟨Ssub.coe.overFinIso rfl⟩⟩
    obtain ⟨ψ⟩ := ψ
    have happ : IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H'' K'' :=
      ⟨⟨isSubdivision_of_iso ψ hsubK4,
        SimpleGraph.Colorable.of_hom ψ.symm.toHom
          (SimpleGraph.Colorable.of_hom (subgraphCopy Ssub).toHom hbip')⟩,
       ⟨ψ.lineGraph.symm.trans θ⟩⟩
    rcases hdeg _ H'' K'' happ with ⟨-, hdk⟩ | ⟨hnk, -, -⟩
    · exact hnondeg (Or.inl ⟨⟨SimpleGraph.Iso.refl⟩,
        degenerateK4Appearance_of_iso ψ.symm hdk⟩)
    · exact hnk ⟨SimpleGraph.Iso.refl⟩

end Workspace.ProofLemmas.NoK4EnlargementAppearance
