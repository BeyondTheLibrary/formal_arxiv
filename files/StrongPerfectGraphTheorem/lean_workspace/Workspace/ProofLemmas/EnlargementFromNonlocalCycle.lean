import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.PathGlue

/-! The cycle formed by the old and new tracks becomes an induced hole in the line graph. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.EnlargementFromNonlocalCycle

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism

/-- PAPER (printed p. 19): "the edge-set of a track becomes the vertex-set of a path".
Two tracks with common ends, disjoint edges, and no other common vertices therefore
form a hole in the line graph. If that line graph appears in a Berge graph, their
lengths have an even sum. -/
theorem even_sum {V W : Type*} {G : SimpleGraph V} (hG : Berge G)
    {H : SimpleGraph W} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    {p q : List W} {a b : W} (hp : IsTrackFrom H p a b) (hq : IsTrackFrom H q a b)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hdisj : Disjoint (trackEdges p) (trackEdges q))
    (hmeet : ∀ z ∈ p, z ∈ q → z = a ∨ z = b)
    (hlen : 4 ≤ trackLength p + trackLength q) :
    Even (trackLength p + trackLength q) := by
  have edge_vertex : ∀ {r : List W} {e : Sym2 W}, e ∈ trackEdges r →
      ∀ z ∈ e, z ∈ r := by
    rintro r e ⟨i, hi, rfl⟩ z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> exact List.getElem_mem _
  have hdisjR : ∀ x ∈ trackRung φ p hp.1, x ∉ trackRung φ q hq.1 := by
    intro x hx hy
    obtain ⟨e, he, hep, heq⟩ := (mem_trackRung_iff φ hp.1).mp hx
    obtain ⟨f, hf, hfq, hfeq⟩ := (mem_trackRung_iff φ hq.1).mp hy
    have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext (heq.symm.trans hfeq)))
    exact Set.disjoint_left.mp hdisj hep (hef.symm ▸ hfq)
  have hcross : ∀ x ∈ trackRung φ p hp.1, ∀ y ∈ trackRung φ q hq.1,
      G.Adj x y ↔
        (x = firstRungVertex φ p hp.1 hp2 ∧ y = firstRungVertex φ q hq.1 hq2) ∨
        (x = lastRungVertex φ p hp.1 hp2 ∧ y = lastRungVertex φ q hq.1 hq2) := by
    intro x hx y hy
    obtain ⟨e, he, hep, rfl⟩ := (mem_trackRung_iff φ hp.1).mp hx
    obtain ⟨f, hf, hfq, rfl⟩ := (mem_trackRung_iff φ hq.1).mp hy
    have hmap : G.Adj (φ ⟨e, he⟩ : V) (φ ⟨f, hf⟩ : V) ↔
        H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff
    rw [hmap, SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨_, z, hze, hzf⟩
      rcases hmeet z (edge_vertex hep z hze) (edge_vertex hfq z hzf) with rfl | rfl
      · left
        constructor
        · exact congrArg (fun t : H.edgeSet => (φ t : V))
            (Subtype.ext (edge_eq_firstTrackEdge hp hp2 hep hze))
        · exact congrArg (fun t : H.edgeSet => (φ t : V))
            (Subtype.ext (edge_eq_firstTrackEdge hq hq2 hfq hzf))
      · right
        constructor
        · exact congrArg (fun t : H.edgeSet => (φ t : V))
            (Subtype.ext (edge_eq_lastTrackEdge hp hp2 hep hze))
        · exact congrArg (fun t : H.edgeSet => (φ t : V))
            (Subtype.ext (edge_eq_lastTrackEdge hq hq2 hfq hzf))
    · intro h
      have hne : (⟨e, he⟩ : H.edgeSet) ≠ ⟨f, hf⟩ := by
        intro hh
        have hv : e = f := congrArg Subtype.val hh
        exact Set.disjoint_left.mp hdisj hep (hv.symm ▸ hfq)
      refine ⟨hne, ?_⟩
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have heq : e = firstTrackEdge p hp2 :=
          congrArg Subtype.val (φ.injective (Subtype.ext hx))
        have hfq : f = firstTrackEdge q hq2 :=
          congrArg Subtype.val (φ.injective (Subtype.ext hy))
        exact ⟨a, heq.symm ▸ firstTrackEdge_contains hp hp2,
          hfq.symm ▸ firstTrackEdge_contains hq hq2⟩
      · have heq : e = lastTrackEdge p hp2 :=
          congrArg Subtype.val (φ.injective (Subtype.ext hx))
        have hfq : f = lastTrackEdge q hq2 :=
          congrArg Subtype.val (φ.injective (Subtype.ext hy))
        exact ⟨b, heq.symm ▸ lastTrackEdge_contains hp hp2,
          hfq.symm ▸ lastTrackEdge_contains hq hq2⟩
  have hh := PathGlue.glue_hole (trackRung_isPathFrom_ends φ hp hp2)
    (PathBasics.isPathFrom_reverse (trackRung_isPathFrom_ends φ hq hq2))
    (by intro x hx; simpa only [List.mem_reverse] using hdisjR x hx)
    (by
      intro x hx y hy
      have h := hcross x hx y (List.mem_reverse.mp hy)
      simpa only [or_comm] using h)
    (by simpa only [List.length_reverse, trackRung_length] using hlen)
  simpa only [holeLength, List.length_append, List.length_reverse, trackRung_length]
    using hG.1 _ hh

end Workspace.ProofLemmas.EnlargementFromNonlocalCycle
