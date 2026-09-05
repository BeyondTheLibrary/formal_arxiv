import Workspace.ProofLemmas.DiracSuppressionLift

/-! Elementary finite-degree and datum lemmas used by the Dirac induction. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.DiracInductionBasics

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.DiracSuppressionLift

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem ncard_neighborSet_lt_card (G : SimpleGraph U) (x : U) :
    (G.neighborSet x).ncard < Fintype.card U := by
  have hs : G.neighborSet x ⊂ (Set.univ : Set U) := Set.ssubset_iff_exists.mpr
    ⟨Set.subset_univ _, x, Set.mem_univ x, by simp⟩
  have h := Set.ncard_lt_ncard hs (Set.toFinite _)
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

@[simp] theorem card_without (u : U) :
    Fintype.card (Without u) = Fintype.card U - 1 := by
  simp [Without, Fintype.card_subtype_compl]

theorem two_le_card_without (u : U) (h : 3 ≤ Fintype.card U) :
    2 ≤ Fintype.card (Without u) := by
  rw [card_without]
  omega

theorem ncard_neighborSet_induce_compl_singleton_of_adj (G : SimpleGraph U) (u : U)
    (x : Without u) (hxu : G.Adj x u) :
    ((G.induce ({u} : Set U)ᶜ).neighborSet x).ncard =
      (G.neighborSet (x : U)).ncard - 1 := by
  let S : Set (Without u) := (G.induce ({u} : Set U)ᶜ).neighborSet x
  let f : Without u → U := fun y ↦ (y : U)
  have himage : Set.image f S = G.neighborSet (x : U) \ {u} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, by simpa using y.property⟩
    · rintro ⟨hz, hzu⟩
      have hzu' : z ≠ u := by simpa using hzu
      exact ⟨⟨z, hzu'⟩, hz, rfl⟩
  change S.ncard = _
  rw [← Set.ncard_image_of_injective S Subtype.val_injective, himage]
  exact Set.ncard_diff_singleton_of_mem hxu

theorem ncard_neighborSet_induce_compl_singleton_of_not_adj (G : SimpleGraph U) (u : U)
    (x : Without u) (hxu : ¬ G.Adj x u) :
    ((G.induce ({u} : Set U)ᶜ).neighborSet x).ncard =
      (G.neighborSet (x : U)).ncard := by
  let S : Set (Without u) := (G.induce ({u} : Set U)ᶜ).neighborSet x
  let f : Without u → U := fun y ↦ (y : U)
  have himage : Set.image f S = G.neighborSet (x : U) \ {u} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, by simpa using y.property⟩
    · rintro ⟨hz, hzu⟩
      have hzu' : z ≠ u := by simpa using hzu
      exact ⟨⟨z, hzu'⟩, hz, rfl⟩
  change S.ncard = _
  rw [← Set.ncard_image_of_injective S Subtype.val_injective, himage]
  have heq : G.neighborSet (x : U) \ {u} = G.neighborSet (x : U) := by
    ext z
    simp [hxu]
  rw [heq]

theorem ncard_neighborSet_sup_edge_left (G : SimpleGraph U) {a b : U}
    (hab : ¬ G.Adj a b) (hne : a ≠ b) :
    ((G ⊔ SimpleGraph.edge a b).neighborSet a).ncard =
      (G.neighborSet a).ncard + 1 := by
  have hs : (G ⊔ SimpleGraph.edge a b).neighborSet a = insert b (G.neighborSet a) := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
      Set.mem_insert_iff]
    aesop
  rw [hs, Set.ncard_insert_of_notMem]
  exact fun h ↦ hab ((G.mem_neighborSet a b).1 h)

theorem ncard_neighborSet_sup_edge_right (G : SimpleGraph U) {a b : U}
    (hab : ¬ G.Adj a b) (hne : a ≠ b) :
    ((G ⊔ SimpleGraph.edge a b).neighborSet b).ncard =
      (G.neighborSet b).ncard + 1 := by
  rw [SimpleGraph.edge_comm]
  exact ncard_neighborSet_sup_edge_left G (fun h ↦ hab h.symm) hne.symm

theorem ncard_neighborSet_sup_edge_other (G : SimpleGraph U) {a b x : U}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    ((G ⊔ SimpleGraph.edge a b).neighborSet x).ncard = (G.neighborSet x).ncard := by
  have hs : (G ⊔ SimpleGraph.edge a b).neighborSet x = G.neighborSet x := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    aesop
  rw [hs]

theorem three_le_neighborSet_induce_compl_singleton_of_not_adj
    (G : SimpleGraph U) (u : U) (x : Without u) (hxu : ¬ G.Adj x u)
    (hdeg : 3 ≤ (G.neighborSet (x : U)).ncard) :
    3 ≤ ((G.induce ({u} : Set U)ᶜ).neighborSet x).ncard := by
  rw [ncard_neighborSet_induce_compl_singleton_of_not_adj G u x hxu]
  exact hdeg

theorem two_le_neighborSet_induce_compl_singleton_of_adj
    (G : SimpleGraph U) (u : U) (x : Without u) (hxu : G.Adj x u)
    (hdeg : 3 ≤ (G.neighborSet (x : U)).ncard) :
    2 ≤ ((G.induce ({u} : Set U)ᶜ).neighborSet x).ncard := by
  rw [ncard_neighborSet_induce_compl_singleton_of_adj G u x hxu]
  omega

theorem three_le_neighborSet_sup_edge_left_after_induce
    (G : SimpleGraph U) (u : U) {a b : Without u}
    (hab : ¬ (G.induce ({u} : Set U)ᶜ).Adj a b) (hne : a ≠ b)
    (hau : G.Adj a u) (hdeg : 3 ≤ (G.neighborSet (a : U)).ncard) :
    3 ≤ ((G.induce ({u} : Set U)ᶜ ⊔ SimpleGraph.edge a b).neighborSet a).ncard := by
  rw [ncard_neighborSet_sup_edge_left _ hab hne,
    ncard_neighborSet_induce_compl_singleton_of_adj G u a hau]
  omega

theorem three_le_neighborSet_sup_edge_right_after_induce
    (G : SimpleGraph U) (u : U) {a b : Without u}
    (hab : ¬ (G.induce ({u} : Set U)ᶜ).Adj a b) (hne : a ≠ b)
    (hbu : G.Adj b u) (hdeg : 3 ≤ (G.neighborSet (b : U)).ncard) :
    3 ≤ ((G.induce ({u} : Set U)ᶜ ⊔ SimpleGraph.edge a b).neighborSet b).ncard := by
  rw [ncard_neighborSet_sup_edge_right _ hab hne,
    ncard_neighborSet_induce_compl_singleton_of_adj G u b hbu]
  omega

theorem three_le_neighborSet_sup_edge_other_after_induce
    (G : SimpleGraph U) (u : U) {a b x : Without u}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxu : ¬ G.Adj x u)
    (hdeg : 3 ≤ (G.neighborSet (x : U)).ncard) :
    3 ≤ ((G.induce ({u} : Set U)ᶜ ⊔ SimpleGraph.edge a b).neighborSet x).ncard := by
  rw [ncard_neighborSet_sup_edge_other (G.induce ({u} : Set U)ᶜ)
      (a := a) (b := b) (x := x) hxa hxb,
    ncard_neighborSet_induce_compl_singleton_of_not_adj G u x hxu]
  exact hdeg

def deleteEdge (G : SimpleGraph U) (a b : U) : SimpleGraph U :=
  G.deleteEdges {s(a, b)}

theorem ncard_neighborSet_deleteEdge_left (G : SimpleGraph U) {a b : U}
    (hab : G.Adj a b) :
    ((deleteEdge G a b).neighborSet a).ncard = (G.neighborSet a).ncard - 1 := by
  have hs : (deleteEdge G a b).neighborSet a = G.neighborSet a \ {b} := by
    ext z
    simp [deleteEdge, hab.ne]
  rw [hs, Set.ncard_diff_singleton_of_mem]
  exact hab

theorem ncard_neighborSet_deleteEdge_right (G : SimpleGraph U) {a b : U}
    (hab : G.Adj a b) :
    ((deleteEdge G a b).neighborSet b).ncard = (G.neighborSet b).ncard - 1 := by
  rw [show deleteEdge G a b = deleteEdge G b a by simp [deleteEdge, Sym2.eq_swap]]
  exact ncard_neighborSet_deleteEdge_left G hab.symm

theorem ncard_neighborSet_deleteEdge_other (G : SimpleGraph U) {a b x : U}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    ((deleteEdge G a b).neighborSet x).ncard = (G.neighborSet x).ncard := by
  have hs : (deleteEdge G a b).neighborSet x = G.neighborSet x := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, deleteEdge, SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · exact And.left
    · intro hxz
      refine ⟨hxz, ?_⟩
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hxa h1
      · exact hxb h1
  rw [hs]

theorem hasK4Datum_mono {G H : SimpleGraph U} (hGH : G ≤ H) (h : HasK4Datum G) :
    HasK4Datum H :=
  hasK4Datum_of_injHom id Function.injective_id (fun _ _ hxy ↦ hGH hxy) h

theorem hasK4Datum_of_induce_compl_singleton {G : SimpleGraph U} {u : U}
    (h : HasK4Datum (G.induce ({u} : Set U)ᶜ)) : HasK4Datum G :=
  hasK4Datum_of_injHom Subtype.val Subtype.val_injective (fun _ _ hxy ↦ hxy) h

theorem hasK4Datum_of_suppress_vertex_of_adj {G : SimpleGraph U} {u a b : U}
    (hau : G.Adj a u) (hub : G.Adj u b) (hab : G.Adj a b)
    (h : HasK4Datum (suppressVertexGraph G u a b hau.ne hub.ne.symm)) : HasK4Datum G := by
  apply hasK4Datum_of_injHom Subtype.val Subtype.val_injective _ h
  intro x y hxy
  rw [suppressVertexGraph, SimpleGraph.sup_adj] at hxy
  rcases hxy with hxy | hxy
  · exact hxy
  · rw [SimpleGraph.edge_adj] at hxy
    rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm

private def topTrack (a b : Fin 4) : List (Fin 4) := [a, b]

theorem hasK4Datum_top : HasK4Datum (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨id, topTrack, Function.injective_id, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    refine ⟨⟨by simp [topTrack], by simp [topTrack, hab], ?_⟩, by simp [topTrack], by simp [topTrack]⟩
    intro i hi
    have hi0 : i = 0 := by simp [topTrack] at hi; omega
    subst i
    simpa [topTrack, SimpleGraph.top_adj] using hab
  · intro a b hab
    simp [topTrack, trackLength]
  · intro a b hab
    simp [topTrack]
  · intro a b a' b' hab hab' hs w hw
    simpa [topTrack, trackInterior] using hw
  · intro a b hab w hw
    simpa [topTrack, trackInterior] using hw

theorem hasK4Datum_of_four_clique {G : SimpleGraph U} (kappa : Fin 4 → U)
    (hinj : Function.Injective kappa)
    (hadj : ∀ a b : Fin 4, a ≠ b → G.Adj (kappa a) (kappa b)) : HasK4Datum G :=
  hasK4Datum_of_injHom kappa hinj
    (fun a b h ↦ hadj a b (by simpa [SimpleGraph.top_adj] using h)) hasK4Datum_top

end Workspace.ProofLemmas.DiracInductionBasics
