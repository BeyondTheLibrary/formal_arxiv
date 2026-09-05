/-  Proof attempt for statement 5.2 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.

    THE PAPER'S PROOF (printed p. 23, "Proof of 5.2, assuming 5.4"):

      "Let G be Berge, and let L(H0) be an appearance of K3,3 in G, where H0 = K3,3.
       We may assume that both G, Gbar contain no nondegenerate L(H) where H is a bipartite
       subdivision of K4.  By 5.3, no K3,3-enlargement appears in either G, Gbar.
       By 5.4, either G = L(K3,3), or G admits a balanced skew partition.
       This proves 5.2."

    Step by step:

    * "We may assume that both G, Gbar contain no nondegenerate L(H) ..." is the `by_cases`
      on the middle disjunct of the conclusion.
    * "By 5.3, no K3,3-enlargement appears in either G, Gbar."  Let `J'` be a
      K3,3-enlargement with an appearance in `Gx`, through a bipartite subdivision `H'` of
      `J'`.  `H'` is bipartite and cyclically 3-connected, so 5.3 applies to it and gives
      three cases:
        (a) H' = K3,3.  Then |E(K3,3)| < |E(J')| <= |E(H')| = |E(K3,3)|, absurd.
        (b) H' is a subdivision of K4.  Then the branch-vertices of H' are both the vertex
            set of J' and the vertex set of K4, so |V(J')| <= 4; but a K3,3-enlargement has
            at least 6 vertices, absurd.
        (c) H' has a subgraph H'' which is a subdivision of K4 with L(H'') nondegenerate.
            L(H'') is an *induced* subgraph of L(H'), hence of `Gx`, contradicting the
            standing assumption.
    * "By 5.4 ..." is the application of `thm_5_4` with `J = H0 = K3,3` (transported onto
      `Fin 6`, which is the shape 5.4's statement quantifies over).  Its 2-join outcome
      carries the side condition `H0 != K3,3`, which is false here, so it drops out --
      exactly the point of the published form of 5.4.

    The counting and branch-vertex machinery lives in
    `Workspace.ProofLemmas.SubdivisionCounting`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Statements.S05.Thm_5_3
import Workspace.Statements.S05.Thm_5_4
import Workspace.ProofLemmas.SubdivisionCounting

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S05

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **5.2** (printed pp. 18–19) -/
theorem thm_5_2 (G : SimpleGraph V) (hG : Berge G) (K : Set V)
    (hK : Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)) :
    Nonempty (G ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph) ∨
    (∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∧
      ((∃ K' : Set V, Nonempty (H.lineGraph ≃g G.induce K')) ∨
       (∃ K' : Set V, Nonempty (H.lineGraph ≃g Gᶜ.induce K')))) ∨
    AdmitsBalancedSkewPartition G := by
  classical
  -- "We may assume that both `G`, `Ḡ` contain no nondegenerate `L(H)` where `H` is a
  -- bipartite subdivision of `K₄`."
  by_cases hmid : (∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∧
      ((∃ K' : Set V, Nonempty (H.lineGraph ≃g G.induce K')) ∨
       (∃ K' : Set V, Nonempty (H.lineGraph ≃g Gᶜ.induce K'))))
  · exact Or.inr (Or.inl hmid)
  have hnoG : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∧
      ∃ K' : Set V, Nonempty (H.lineGraph ≃g G.induce K') := by
    rintro ⟨n, H, h1, h2, h3⟩
    exact hmid ⟨n, H, h1, h2, Or.inl h3⟩
  have hnoGc : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∧
      ∃ K' : Set V, Nonempty (H.lineGraph ≃g Gᶜ.induce K') := by
    rintro ⟨n, H, h1, h2, h3⟩
    exact hmid ⟨n, H, h1, h2, Or.inr h3⟩
  -- `K₃,₃` transported onto `Fin 6`, which is the shape 5.4 quantifies over.
  have hc6 : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  obtain ⟨J₆, e6⟩ : ∃ J : SimpleGraph (Fin 6),
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)) ≃g J) :=
    ⟨_, ⟨(completeBipartiteGraph (Fin 3) (Fin 3)).overFinIso hc6⟩⟩
  obtain ⟨e6⟩ := e6
  -- "By 5.3, no `K₃,₃`-enlargement appears in either `G, Ḡ`."
  have hnoenl : ∀ Gx : SimpleGraph V,
      (¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
          IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H ∧
          NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∧
          ∃ K' : Set V, Nonempty (H.lineGraph ≃g Gx.induce K')) →
      ¬ ∃ (m' : ℕ) (J' : SimpleGraph (Fin m')), IsJEnlargement J₆ J' ∧ Appears Gx J' := by
    rintro Gx hno ⟨m', J', ⟨hJ'3, S, hSne, nD, Dg, hDsub, ⟨φD⟩⟩, n', H', K', hsub', φ'⟩
    obtain ⟨hsubJ', hbip'⟩ := hsub'
    obtain ⟨φ'⟩ := φ'
    have hc3 : CyclicallyThreeConnected H' := ⟨m', J', hJ'3, hsubJ'⟩
    rcases thm_5_3 H' hbip' hc3 with heH | hsub4 | ⟨Ssub, hsubK4, hnondeg⟩
    · -- (a) `H' = K₃,₃`: an edge count.
      obtain ⟨eH⟩ := heH
      have h1 : J'.edgeSet.ncard ≤ H'.edgeSet.ncard :=
        edgeSet_ncard_le_of_isSubdivision J' H' hsubJ'
      have h2 : H'.edgeSet.ncard = (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard := by
        simpa only [Nat.card_coe_set_eq] using Nat.card_congr eH.mapEdgeSet
      have h3 : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard = J₆.edgeSet.ncard := by
        simpa only [Nat.card_coe_set_eq] using Nat.card_congr e6.mapEdgeSet
      have h4 : J₆.edgeSet.ncard ≤ Dg.edgeSet.ncard :=
        edgeSet_ncard_le_of_isSubdivision J₆ Dg hDsub
      have h5 : Dg.edgeSet.ncard < J'.edgeSet.ncard :=
        edgeSet_ncard_lt_of_ne_top J' hJ'3 S hSne Dg φD
      omega
    · -- (b) `H'` is a subdivision of `K₄`: the branch-vertices pin `|V(J')|` to `≤ 4`.
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
      -- but a `K₃,₃`-enlargement has at least six vertices
      obtain ⟨ιD, TD, hιD, -, -, -, -, -, -, -⟩ := hDsub
      have h6 : 6 ≤ nD := by
        have := Fintype.card_le_of_injective ιD hιD
        simpa using this
      have hSD : Nat.card ↥S.verts = nD := by
        simpa using Nat.card_congr φD.toEquiv
      have hSle : S.verts.ncard ≤ m' := by
        have h1 := Set.ncard_le_ncard (Set.subset_univ S.verts) (Set.toFinite _)
        rw [Set.ncard_univ] at h1
        simpa using h1
      rw [Nat.card_coe_set_eq] at hSD
      omega
    · -- (c) a nondegenerate `K₄`-subdivision inside `H'`, hence inside `Gx`.
      haveI : Fintype ↥Ssub.verts := Fintype.ofFinite _
      obtain ⟨K'', -, θ⟩ := exists_lineGraph_iso_induce_of_subgraph φ' Ssub
      obtain ⟨θ⟩ := θ
      obtain ⟨H'', ψ⟩ : ∃ H'' : SimpleGraph (Fin (Fintype.card ↥Ssub.verts)),
          Nonempty (Ssub.coe ≃g H'') := ⟨_, ⟨Ssub.coe.overFinIso rfl⟩⟩
      obtain ⟨ψ⟩ := ψ
      refine hno ⟨_, H'', ⟨isSubdivision_of_iso ψ hsubK4, ?_⟩, ?_, K'', ⟨ψ.lineGraph.symm.trans θ⟩⟩
      · exact SimpleGraph.Colorable.of_hom ψ.symm.toHom
          (SimpleGraph.Colorable.of_hom (subgraphCopy Ssub).toHom hbip')
      · intro hd
        rcases hd with ⟨-, hdk⟩ | ⟨hnk, -, -⟩
        · exact hnondeg (Or.inl ⟨⟨SimpleGraph.Iso.refl⟩,
            degenerateK4Appearance_of_iso ψ.symm hdk⟩)
        · exact hnk ⟨SimpleGraph.Iso.refl⟩
  -- "By 5.4, either `G = L(K₃,₃)`, or `G` admits a balanced skew partition."
  have hJ₆3 : IsKConnected J₆ 3 := isKConnected_of_iso e6 k33_three_connected
  have hbip6 : J₆.IsBipartite := SimpleGraph.Colorable.of_hom e6.symm.toHom k33_bipartite
  have happ6 : IsAppearance G J₆ J₆ K :=
    ⟨⟨isSubdivision_self J₆, hbip6⟩, ⟨(e6.lineGraph).symm.trans hK.some⟩⟩
  have h54 := thm_5_4 G hG 6 J₆ hJ₆3
    (by
      rintro ⟨m', J', henl, n', H', K', happ', -⟩
      exact hnoenl G hnoG ⟨m', J', henl, n', H', K', happ'⟩)
    6 J₆ K happ6
    (fun _ => ⟨⟨e6.symm⟩, ⟨e6.symm⟩, hnoenl Gᶜ hnoGc⟩)
  rcases h54 with heG | ⟨hne, -⟩ | hskew
  · obtain ⟨eG⟩ := heG
    exact Or.inl ⟨eG.trans (e6.lineGraph).symm⟩
  · exact absurd ⟨e6.symm⟩ hne
  · exact Or.inr (Or.inr hskew)


end SPGT

end Workspace.Statements.S05
