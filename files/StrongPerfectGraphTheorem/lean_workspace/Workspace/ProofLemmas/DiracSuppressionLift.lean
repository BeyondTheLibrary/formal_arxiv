import Workspace.ProofLemmas.K4DatumComposeWitness

/-!
# Lifting a `K₄` datum through suppression of a degree-two vertex

Delete `u` and, when its two neighbours `a,b` are nonadjacent, insert the edge `ab`.  The
inserted edge is represented in the old graph by the track `[a,u,b]`; every old edge is
represented by its two endpoints.  The local subdivision-composition theorem then lifts a
`K₄` datum from the suppressed graph.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.DiracSuppressionLift

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.SubdivisionCompose
open Workspace.ProofLemmas.K4DatumComposeWitness

variable {U : Type*} [DecidableEq U]

abbrev Without (u : U) := {x : U // x ≠ u}

def suppressVertexGraph (G : SimpleGraph U) (u a b : U)
    (ha : a ≠ u) (hb : b ≠ u) : SimpleGraph (Without u) :=
  G.induce ({u} : Set U)ᶜ ⊔ SimpleGraph.edge (⟨a, ha⟩ : Without u) (⟨b, hb⟩ : Without u)

private def suppressTrack (u a b : U) (x y : Without u) : List U :=
  if s((x : U), (y : U)) = s(a, b) then [(x : U), u, (y : U)] else [(x : U), (y : U)]

private theorem suppressTrack_reverse (u a b : U) (x y : Without u) :
    suppressTrack u a b y x = (suppressTrack u a b x y).reverse := by
  simp only [suppressTrack, Sym2.eq_swap]
  split_ifs <;> simp_all

private theorem inserted_pair_ends {u a b : U} {x y : Without u}
    (hpair : s((x : U), (y : U)) = s(a, b)) :
    ((x : U) = a ∧ (y : U) = b) ∨ ((x : U) = b ∧ (y : U) = a) :=
  Sym2.eq_iff.mp hpair

private theorem old_adj_of_suppressed_adj {G : SimpleGraph U} {u a b : U}
    {ha : a ≠ u} {hb : b ≠ u} {x y : Without u}
    (hxy : (suppressVertexGraph G u a b ha hb).Adj x y)
    (hne : s((x : U), (y : U)) ≠ s(a, b)) : G.Adj (x : U) (y : U) := by
  rw [suppressVertexGraph, SimpleGraph.sup_adj] at hxy
  rcases hxy with hxy | hxy
  · exact hxy
  · rw [SimpleGraph.adj_edge] at hxy
    have hp : s((x : U), (y : U)) = s(a, b) := by
      simpa [Sym2.map_mk] using
        congrArg (Sym2.map (fun z : Without u ↦ (z : U))) hxy.1.symm
    exact (hne hp).elim

private theorem suppressionWitness {G : SimpleGraph U} {u a b : U}
    (hau : G.Adj a u) (hub : G.Adj u b) (hab : ¬ G.Adj a b) :
    SubdivWitness
      (suppressVertexGraph G u a b hau.ne hub.ne.symm) G
      (fun x : Without u ↦ (x : U)) (suppressTrack u a b) := by
  let K := suppressVertexGraph G u a b hau.ne hub.ne.symm
  refine ⟨Subtype.val_injective, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hxyne : x ≠ y := hxy.ne
    by_cases hp : s((x : U), (y : U)) = s(a, b)
    · have hxu : G.Adj (x : U) u := by
        rcases inserted_pair_ends hp with ⟨hx, -⟩ | ⟨hx, -⟩
        · simpa [hx] using hau
        · simpa [hx] using hub.symm
      have huy : G.Adj u (y : U) := by
        rcases inserted_pair_ends hp with ⟨-, hy⟩ | ⟨-, hy⟩
        · simpa [hy] using hub
        · simpa [hy] using hau.symm
      have hvalne : (x : U) ≠ (y : U) := fun h ↦ hxyne (Subtype.ext h)
      rw [suppressTrack, if_pos hp]
      refine ⟨⟨by simp, ?_, ?_⟩, by simp, by simp⟩
      · have huyne : u ≠ (y : U) := y.property.symm
        simp [x.property, huyne, hvalne]
      · intro i hi
        have hi' : i = 0 ∨ i = 1 := by simp at hi; omega
        rcases hi' with rfl | rfl
        · simpa using hxu
        · simpa using huy
    · have hold : G.Adj (x : U) (y : U) := old_adj_of_suppressed_adj hxy hp
      have hvalne : (x : U) ≠ (y : U) := fun h ↦ hxyne (Subtype.ext h)
      rw [suppressTrack, if_neg hp]
      refine ⟨⟨by simp, by simpa using hvalne, ?_⟩, by simp, by simp⟩
      · intro i hi
        have : i = 0 := by simp at hi; omega
        subst i
        simpa using hold
  · intro x y hxy
    have hxyne : x ≠ y := hxy.ne
    by_cases hp : s((x : U), (y : U)) = s(a, b) <;>
      simp [suppressTrack, hp, trackLength]
  · intro x y _
    exact suppressTrack_reverse u a b x y
  · intro x y x' y' hxy hxy' hedge w hw hmem
    by_cases hp : s((x : U), (y : U)) = s(a, b)
    · have hw' : w = u := by simpa [suppressTrack, hp, trackInterior] using hw
      subst w
      have hp' : s((x' : U), (y' : U)) ≠ s(a, b) := by
        intro h
        apply hedge
        apply Sym2.map.injective Subtype.val_injective
        simpa [Sym2.map_mk] using hp.trans h.symm
      rw [suppressTrack, if_neg hp'] at hmem
      simp at hmem
      rcases hmem with h | h
      · exact x'.property h.symm
      · exact y'.property h.symm
    · simpa [suppressTrack, hp, trackInterior] using hw
  · intro x y hxy w hw hrange
    by_cases hp : s((x : U), (y : U)) = s(a, b)
    · have hw' : w = u := by simpa [suppressTrack, hp, trackInterior] using hw
      subst w
      rcases hrange with ⟨z, hz⟩
      exact z.property hz
    · simpa [suppressTrack, hp, trackInterior] using hw

/-- A datum in the graph obtained by suppressing `u` lifts to the original graph. -/
theorem hasK4Datum_of_suppress_vertex {G : SimpleGraph U} {u a b : U}
    (hau : G.Adj a u) (hub : G.Adj u b) (hab : ¬ G.Adj a b)
    (hdat : HasK4Datum (suppressVertexGraph G u a b hau.ne hub.ne.symm)) : HasK4Datum G :=
  hasK4Datum_of_subdivWitness hdat (suppressionWitness hau hub hab)

end Workspace.ProofLemmas.DiracSuppressionLift
