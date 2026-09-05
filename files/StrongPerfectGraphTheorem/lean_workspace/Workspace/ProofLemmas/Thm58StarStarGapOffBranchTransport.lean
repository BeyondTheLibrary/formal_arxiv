import Workspace.ProofLemmas.Thm58StarStarGapOffBranchConn

/-!
# Passing between `H` and the graph with the branch deleted

PAPER, proof of 5.8 (4), printed p. 27: *"we can apply 5.6 to the graph obtained from `H` by
deleting the edges and internal vertices of the branch between `v₁` and `v₂`"*.

That graph is `(H.deleteEdges (trackEdges q)).induce S`, where `S` is the set of vertices of
`H` that are not internal vertices of the branch `q`.  This file collects the translations
between the two graphs that the application of 5.6 needs: connected sets, incident edges, and
tracks.  Nothing here is a mathematical step of the paper; it is the bookkeeping the paper
leaves implicit when it says *"the graph obtained from `H` by deleting ..."*.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapOffBranchTransport

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT

variable {W : Type*}

/-- The graph obtained from `H` by deleting the edges in `E` and the vertices outside `S`. -/
abbrev del (H : SimpleGraph W) (E : Set (Sym2 W)) (S : Set W) : SimpleGraph ↥S :=
  (H.deleteEdges E).induce S

variable {H : SimpleGraph W} {E : Set (Sym2 W)} {S : Set W}

theorem del_adj {x y : ↥S} :
    (del H E S).Adj x y ↔ H.Adj (x : W) (y : W) ∧ s((x : W), (y : W)) ∉ E := by
  simp [del, SimpleGraph.deleteEdges_adj]

/-! ## Connected sets -/

/-- A connected set of `H` all of whose vertices survive, and no two of whose vertices are
joined by a deleted edge, is a connected set of the deleted graph. -/
theorem connectedSet_del {T : Set ↥S} {Y : Set W}
    (hYT : ∀ x : W, x ∈ Y ↔ ∃ hx : x ∈ S, (⟨x, hx⟩ : ↥S) ∈ T)
    (hE : ∀ x ∈ Y, ∀ y ∈ Y, s(x, y) ∉ E)
    (hconn : ConnectedSet H Y) :
    ConnectedSet (del H E S) T := by
  classical
  intro u v
  set GB := (del H E S).induce T with hGB
  have hmemY : ∀ w : ↥T, ((w : ↥S) : W) ∈ Y := fun w => (hYT _).mpr ⟨(w : ↥S).2, w.2⟩
  let f : ↥Y → ↥T := fun x =>
    ⟨⟨(x : W), ((hYT (x : W)).mp x.2).choose⟩, ((hYT (x : W)).mp x.2).choose_spec⟩
  have hf : ∀ {x y : ↥Y}, (H.induce Y).Adj x y → GB.Adj (f x) (f y) := by
    intro x y hxy
    have hadj : H.Adj (x : W) (y : W) := hxy
    refine del_adj.mpr ⟨hadj, hE _ x.2 _ y.2⟩
  have hmap : GB.Reachable (f ⟨((u : ↥S) : W), hmemY u⟩) (f ⟨((v : ↥S) : W), hmemY v⟩) :=
    (hconn ⟨((u : ↥S) : W), hmemY u⟩ ⟨((v : ↥S) : W), hmemY v⟩).map
      (⟨f, hf⟩ : (H.induce Y) →g GB)
  have hu : f ⟨((u : ↥S) : W), hmemY u⟩ = u := Subtype.ext (Subtype.ext rfl)
  have hv : f ⟨((v : ↥S) : W), hmemY v⟩ = v := Subtype.ext (Subtype.ext rfl)
  rwa [hu, hv] at hmap

/-! ## Incident edges -/

theorem incidentEdges_del {c : W} (hc : c ∈ S) :
    incidentEdges (del H E S) ⟨c, hc⟩
      = Sym2.map Subtype.val ⁻¹' (incidentEdges H c \ E) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [incidentEdges, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_diff,
      Sym2.map_mk, SimpleGraph.mem_edgeSet]
    constructor
    · rintro ⟨hadj, hmem⟩
      rw [del_adj] at hadj
      refine ⟨⟨hadj.1, ?_⟩, hadj.2⟩
      rcases Sym2.mem_iff.mp hmem with h | h
      · exact h ▸ Sym2.mem_mk_left _ _
      · exact h ▸ Sym2.mem_mk_right _ _
    · rintro ⟨⟨hadj, hmem⟩, hE⟩
      refine ⟨del_adj.mpr ⟨hadj, hE⟩, ?_⟩
      rcases Sym2.mem_iff.mp hmem with h | h
      · exact (Subtype.ext h : (⟨c, hc⟩ : ↥S) = x) ▸ Sym2.mem_mk_left _ _
      · exact (Subtype.ext h : (⟨c, hc⟩ : ↥S) = y) ▸ Sym2.mem_mk_right _ _

/-! ## Tracks -/

theorem isTrackList_map {t : List ↥S} (ht : IsTrackList (del H E S) t) :
    IsTrackList H (t.map Subtype.val) := by
  refine ⟨fun hcon => ht.1 (List.map_eq_nil_iff.mp hcon), ht.2.1.map Subtype.val_injective, ?_⟩
  intro i hi
  rw [List.length_map] at hi
  have hadj := ht.2.2 i hi
  rw [del_adj] at hadj
  simpa [List.getElem_map] using hadj.1

theorem trackEdges_map_notMem {t : List ↥S} (ht : IsTrackList (del H E S) t) :
    ∀ e ∈ trackEdges (t.map Subtype.val), e ∉ E := by
  rintro e ⟨i, hi, rfl⟩
  rw [List.length_map] at hi
  have hadj := ht.2.2 i hi
  rw [del_adj] at hadj
  simpa [List.getElem_map] using hadj.2

end Workspace.ProofLemmas.Thm58StarStarGapOffBranchTransport
