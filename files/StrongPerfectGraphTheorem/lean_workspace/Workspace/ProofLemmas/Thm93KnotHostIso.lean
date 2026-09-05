import Workspace.ProofLemmas.Thm93KnotHost

/-!
# `L(H) = K` for the canonical knot appearance

PAPER (9.3, printed p. 48): *"Then `K` is a degenerate appearance of `K₄` in `G`, say
`K = L(H)`."*

The map `edgeOf` of `Thm93KnotHost` is a bijection from the vertices of `graph m n` to the
edges of `host m n` which turns adjacency in `graph m n` into "distinct edges with a common
end", so it is an isomorphism from `graph m n` to the line graph of `host m n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93KnotHostIso

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93KnotModel
open Workspace.ProofLemmas.Thm93KnotHost

variable {m n : ℕ}

/-- The vertices of `graph m n`, read as edges of the host graph. -/
def toEdge (hm : 2 ≤ m) (hn : 2 ≤ n) (u : (Set.univ : Set (Vertex m n))) :
    (host m n).edgeSet :=
  ⟨edgeOf m n u.1, edgeOf_mem_edgeSet (by omega) (by omega) u.1⟩

theorem toEdge_bijective (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Function.Bijective (toEdge hm hn) := by
  constructor
  · intro a b h
    exact Subtype.ext (edgeOf_injective hm hn (congrArg Subtype.val h))
  · rintro ⟨e, he⟩
    obtain ⟨u, rfl⟩ := edgeOf_surjective e he
    exact ⟨⟨u, Set.mem_univ u⟩, rfl⟩

/-- `graph m n` is the line graph of the host graph. -/
noncomputable def psi (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (graph m n).induce (Set.univ : Set (Vertex m n)) ≃g (host m n).lineGraph :=
  { Equiv.ofBijective (toEdge hm hn) (toEdge_bijective hm hn) with
    map_rel_iff' := by
      intro a b
      show (host m n).lineGraph.Adj (toEdge hm hn a) (toEdge hm hn b) ↔ (graph m n).Adj a.1 b.1
      rw [SimpleGraph.lineGraph_adj_iff_exists, ← edgeOf_meet_iff hm hn]
      constructor
      · rintro ⟨hne, hw⟩
        exact ⟨fun h => hne (Subtype.ext (congrArg (edgeOf m n) h)), hw⟩
      · rintro ⟨hne, hw⟩
        exact ⟨fun h => hne (edgeOf_injective hm hn (congrArg Subtype.val h)), hw⟩ }

/-- The appearance isomorphism: the line graph of the host graph is `graph m n`. -/
noncomputable def phi (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (host m n).lineGraph ≃g (graph m n).induce (Set.univ : Set (Vertex m n)) :=
  (psi hm hn).symm

theorem phi_edgeOf (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n)
    (he : edgeOf m n u ∈ (host m n).edgeSet) :
    (↑(phi hm hn ⟨edgeOf m n u, he⟩) : Vertex m n) = u := by
  have hrw : (⟨edgeOf m n u, he⟩ : (host m n).edgeSet)
      = psi hm hn ⟨u, Set.mem_univ u⟩ := rfl
  rw [phi, hrw, RelIso.symm_apply_apply]

/-- Reading a set of edges of the host graph back as a set of vertices of `graph m n`. -/
theorem phiSet_eq (hm : 2 ≤ m) (hn : 2 ≤ n) (S : Set (Sym2 (Host m n))) :
    {v : Vertex m n | ∃ (e : Sym2 (Host m n)) (he : e ∈ (host m n).edgeSet),
        e ∈ S ∧ v = (↑(phi hm hn ⟨e, he⟩) : Vertex m n)}
      = {u : Vertex m n | edgeOf m n u ∈ S} := by
  ext v
  constructor
  · rintro ⟨e, he, hS, rfl⟩
    obtain ⟨u, rfl⟩ := edgeOf_surjective e he
    show edgeOf m n _ ∈ S
    rw [phi_edgeOf hm hn u he]
    exact hS
  · intro hv
    exact ⟨edgeOf m n v, edgeOf_mem_edgeSet (by omega) (by omega) v, hv,
      (phi_edgeOf hm hn v _).symm⟩

end Workspace.ProofLemmas.Thm93KnotHostIso
