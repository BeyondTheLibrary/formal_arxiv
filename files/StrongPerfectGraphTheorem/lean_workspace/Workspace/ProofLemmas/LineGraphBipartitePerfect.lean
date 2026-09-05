import Workspace.ProofLemmas.ColoringCliqueSandwich
import Workspace.ProofLemmas.RetainedEdgeLineGraphIso
import Workspace.ProofLemmas.FiniteBipartiteEdgeColoringMaxDegree
import Workspace.ProofLemmas.IsoTransport

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- The line graph of every finite bipartite simple graph is perfect. -/
theorem LineGraphBipartitePerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : H.IsBipartite) :
    SPGT.IsPerfect H.lineGraph := by
  classical
  intro X
  obtain ⟨_hle, φ, _hφval, hφbip⟩ := RetainedEdgeLineGraphIso H X
  let K : SimpleGraph W := retainedEdgeGraph H X
  have hKbip : K.IsBipartite := hφbip hH
  letI : DecidableRel K.Adj := Classical.decRel _
  have hcolor : K.lineGraph.Colorable K.maxDegree :=
    FiniteBipartiteEdgeColoringMaxDegree K hKbip
  have hclique : ∃ Q : Finset K.edgeSet,
      K.lineGraph.IsClique (↑Q : Set K.edgeSet) ∧ Q.card = K.maxDegree := by
    cases isEmpty_or_nonempty W with
    | inl hW =>
        letI : IsEmpty W := hW
        refine ⟨∅, ?_, ?_⟩
        · simp
        · rw [Finset.card_empty, K.maxDegree_of_isEmpty]
    | inr hW =>
        letI : Nonempty W := hW
        obtain ⟨v, hv⟩ := K.exists_maximal_degree_vertex
        have hmem : ∀ e : {e : Sym2 W // e ∈ K.incidenceFinset v},
            (e : Sym2 W) ∈ K.edgeSet ∧ v ∈ (e : Sym2 W) := by
          intro e
          have h2 := e.2
          rw [K.mem_incidenceFinset] at h2
          exact ⟨h2.1, h2.2⟩
        let inc : {e : Sym2 W // e ∈ K.incidenceFinset v} ↪ K.edgeSet :=
          ⟨fun e => ⟨(e : Sym2 W), (hmem e).1⟩, by
            intro e f hef
            exact Subtype.ext (congrArg (fun z : K.edgeSet => (z : Sym2 W)) hef)⟩
        refine ⟨(K.incidenceFinset v).attach.map inc, ?_, ?_⟩
        · intro e he f hf hef
          rw [SimpleGraph.lineGraph_adj_iff_exists]
          refine ⟨hef, v, ?_, ?_⟩
          · obtain ⟨e', -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp he)
            exact (hmem e').2
          · obtain ⟨f', -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hf)
            exact (hmem f').2
        · rw [Finset.card_map, Finset.card_attach,
            K.card_incidenceFinset_eq_degree, hv]
  rw [IsoTransport.chromaticNumber_iso φ, IsoTransport.cliqueNum_iso φ]
  exact ColoringCliqueSandwich K.lineGraph K.maxDegree hcolor hclique

end Workspace.ProofLemmas
