import Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance
import Workspace.ProofLemmas.Thm61Claim12RookTheta

/-!
# Reading off the labels of `lineGraphIsoInduceOfEdgeIndex`

`Thm61EvenEndgameComplementAppearance.lineGraphIsoInduceOfEdgeIndex` builds an appearance out
of an indexing of the host edges and a matching indexing of the vertices of the induced
subgraph.  The `K₃,₃` endgame of 6.1(12) has to inspect the stars at the two ends of the new
branch, so it needs the labels themselves, not merely the existence of the isomorphism; that is
`apply_edge` below.  `Thm61EvenEndgameComplementAppearance` proves exactly these two statements
for its own fixed indexing.

Also recorded here are the two incidence facts of `Thm61Claim12RookTheta` in the form the
endgame uses them.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Claim12RookIso

open Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance
open Workspace.ProofLemmas.Thm61Claim12RookTheta

variable {V W I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- The vertex labelled by the `i`-th host edge is `w i`. -/
theorem apply_edge (G : SimpleGraph V) (H : SimpleGraph W) (edge : I ≃ H.edgeSet) (w : I → V)
    (hwinj : Function.Injective w)
    (hrel : ∀ i j : I, H.lineGraph.Adj (edge i) (edge j) ↔ G.Adj (w i) (w j)) (i : I) :
    (↑(lineGraphIsoInduceOfEdgeIndex G H edge w hwinj hrel (edge i)) : V) = w i := by
  simp only [lineGraphIsoInduceOfEdgeIndex]
  change w (edge.symm (edge i)) = w i
  rw [edge.symm_apply_apply]

/-! ### The two stars of `rookTheta` at the ends of the deleted edge -/

theorem edge_incident_three (e : rookTheta.edgeSet) (h : (3 : Fin 6) ∈ (e : Sym2 (Fin 6))) :
    e = rookEdge 0 ∨ e = rookEdge 4 := by
  obtain ⟨k, rfl⟩ := rookEdge_bijective.2 e
  rcases (rookEdge_mem_three k).1 h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem edge_incident_one (e : rookTheta.edgeSet) (h : (1 : Fin 6) ∈ (e : Sym2 (Fin 6))) :
    e = rookEdge 1 ∨ e = rookEdge 3 := by
  obtain ⟨k, rfl⟩ := rookEdge_bijective.2 e
  rcases (rookEdge_mem_one k).1 h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Workspace.ProofLemmas.Thm61Claim12RookIso
