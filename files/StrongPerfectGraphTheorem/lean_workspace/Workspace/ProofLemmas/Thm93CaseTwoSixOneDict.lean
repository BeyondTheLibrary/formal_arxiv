import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.ProofLemmas.K4AppearanceEightVertices

/-!
# Reading edges of `H` through the knot dictionary

Small facts about the isomorphism `φ : L(H) ≃g G|K` of an appearance: it is injective and
onto `K`, an edge incident with a branch-vertex `c` has its image in `N c`, and the four
branch-vertices of the knot dictionary form a four-cycle whose two diagonals are not edges.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoSixOneDict

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

variable {V : Type*} {n : ℕ} {D : SimpleGraph V} {H : SimpleGraph (Fin n)} {K : Set V}

/-- The vertices of `L(H)` are the edges of `H`, so `φ` is injective on edges. -/
theorem img_inj (phi : H.lineGraph ≃g D.induce K) {e e' : Sym2 (Fin n)}
    (he : e ∈ H.edgeSet) (he' : e' ∈ H.edgeSet)
    (h : (↑(phi ⟨e, he⟩) : V) = ↑(phi ⟨e', he'⟩)) : e = e' := by
  have h1 : phi ⟨e, he⟩ = phi ⟨e', he'⟩ := Subtype.ext h
  have h2 : (⟨e, he⟩ : ↥H.edgeSet) = ⟨e', he'⟩ := phi.injective h1
  exact congrArg Subtype.val h2

/-- Every vertex of `K` is the image of an edge of `H`. -/
theorem exists_preimage (phi : H.lineGraph ≃g D.induce K) {w : V} (hw : w ∈ K) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), w = (↑(phi ⟨e, he⟩) : V) := by
  refine ⟨(phi.symm ⟨w, hw⟩).1, (phi.symm ⟨w, hw⟩).2, ?_⟩
  have : phi (phi.symm ⟨w, hw⟩) = ⟨w, hw⟩ := phi.apply_symm_apply _
  rw [show ((⟨(phi.symm ⟨w, hw⟩).1, (phi.symm ⟨w, hw⟩).2⟩ : ↥H.edgeSet)) = phi.symm ⟨w, hw⟩ from
    Subtype.ext rfl, this]

/-- Images of edges lie in `K`. -/
theorem img_mem (phi : H.lineGraph ≃g D.induce K) {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) :
    (↑(phi ⟨e, he⟩) : V) ∈ K := (phi ⟨e, he⟩).2

/-- An edge incident with `c` has its image in `N c`. -/
theorem img_mem_N (phi : H.lineGraph ≃g D.induce K) (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (c : Fin n) {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) (hinc : e ∈ incidentEdges H c) :
    (↑(phi ⟨e, he⟩) : V) ∈ N c := by
  rw [hN c]; exact ⟨e, he, hinc, rfl⟩

/-- The edge joining two adjacent vertices is incident with both. -/
theorem mem_incidentEdges_left {u v : Fin n} (h : H.Adj u v) :
    s(u, v) ∈ incidentEdges H u := ⟨h, by simp⟩

/-- The edge joining two adjacent vertices is incident with both. -/
theorem mem_incidentEdges_right {u v : Fin n} (h : H.Adj u v) :
    s(u, v) ∈ incidentEdges H v := ⟨h, by simp⟩

/-- Two branch-vertices whose triangles are disjoint are nonadjacent. -/
theorem not_adj_of_N_disjoint (phi : H.lineGraph ≃g D.induce K) (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    {c c' : Fin n} (hdisj : ∀ v : V, v ∈ N c → v ∈ N c' → False) : ¬ H.Adj c c' := by
  intro h
  have he : s(c, c') ∈ H.edgeSet := h
  exact hdisj _ (img_mem_N phi N hN c he (mem_incidentEdges_left h))
    (img_mem_N phi N hN c' he (mem_incidentEdges_right h))

/-- **The eight labellings of the four-cycle.**  A four-cycle on the four branch-vertices,
whose two diagonals are not edges, is the given four-cycle up to rotation and reflection. -/
theorem cycle_labels {c₁ c₂ c₃ c₄ v₁ v₂ v₃ v₄ : Fin n}
    (hvnd : [v₁, v₂, v₃, v₄].Nodup)
    (hmem : ∀ v : Fin n, v ∈ ({v₁, v₂, v₃, v₄} : Set (Fin n)) →
      v ∈ ({c₁, c₂, c₃, c₄} : Set (Fin n)))
    (h13 : ¬ H.Adj c₁ c₃) (h24 : ¬ H.Adj c₂ c₄)
    (a12 : H.Adj v₁ v₂) (a23 : H.Adj v₂ v₃) (a34 : H.Adj v₃ v₄) (a41 : H.Adj v₄ v₁) :
    ((v₁, v₂, v₃, v₄) = (c₁, c₂, c₃, c₄) ∨ (v₁, v₂, v₃, v₄) = (c₂, c₃, c₄, c₁)) ∨
    ((v₁, v₂, v₃, v₄) = (c₃, c₄, c₁, c₂) ∨ (v₁, v₂, v₃, v₄) = (c₄, c₁, c₂, c₃)) ∨
    ((v₁, v₂, v₃, v₄) = (c₂, c₁, c₄, c₃) ∨ (v₁, v₂, v₃, v₄) = (c₁, c₄, c₃, c₂)) ∨
    ((v₁, v₂, v₃, v₄) = (c₄, c₃, c₂, c₁) ∨ (v₁, v₂, v₃, v₄) = (c₃, c₂, c₁, c₄)) := by
  have h31 : ¬ H.Adj c₃ c₁ := fun h => h13 h.symm
  have h42 : ¬ H.Adj c₄ c₂ := fun h => h24 h.symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or] at hvnd
  obtain ⟨⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩ := hvnd
  have m1 := hmem v₁ (by simp)
  have m2 := hmem v₂ (by simp)
  have m3 := hmem v₃ (by simp)
  have m4 := hmem v₄ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m1 m2 m3 m4
  rcases m1 with rfl | rfl | rfl | rfl <;> rcases m2 with rfl | rfl | rfl | rfl <;>
    rcases m3 with rfl | rfl | rfl | rfl <;> rcases m4 with rfl | rfl | rfl | rfl <;>
    simp_all

/-- The path of `K` carried by a track has at most as many vertices as the track has edges. -/
theorem length_le_trackLength (phi : H.lineGraph ≃g D.induce K) {q : List (Fin n)} {Q : List V}
    (hQnd : Q.Nodup) (hqnd : q.Nodup)
    (hset : {v : V | v ∈ Q} = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : V)}) :
    Q.length ≤ trackLength q := by
  classical
  set S : Set ↥H.edgeSet := {E : ↥H.edgeSet | (↑E : Sym2 (Fin n)) ∈ trackEdges q} with hS
  have h1 : {v : V | v ∈ Q} = (fun E : ↥H.edgeSet => (↑(phi E) : V)) '' S := by
    rw [hset]
    ext v
    constructor
    · rintro ⟨e, he, hmem, rfl⟩; exact ⟨⟨e, he⟩, hmem, rfl⟩
    · rintro ⟨⟨e, he⟩, hmem, rfl⟩; exact ⟨e, he, hmem, rfl⟩
  have h2 : ({v : V | v ∈ Q}).ncard = Q.length := by
    rw [show {v : V | v ∈ Q} = (↑Q.toFinset : Set V) by ext v; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hQnd]
  have h3 : ((fun E : ↥H.edgeSet => (↑(phi E) : V)) '' S).ncard ≤ S.ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have h4 : S.ncard ≤ (trackEdges q).ncard :=
    Set.ncard_le_ncard_of_injOn (fun E => (↑E : Sym2 (Fin n))) (fun E hE => hE)
      (fun a _ b _ h => Subtype.ext h) (Set.toFinite _)
  have h5 : (trackEdges q).ncard = trackLength q :=
    Workspace.ProofLemmas.K4AppearanceEightVertices.trackEdges_ncard q hqnd
  rw [h1] at h2
  omega

/-- With only six vertices, a branch joining two of the four branch-vertices has length at
most three. -/
theorem trackLength_le_three [DecidableEq (Fin n)] {q : List (Fin n)} {c₁ c₂ c₃ c₄ : Fin n}
    (hq : IsBranch H q) (hnd : [c₁, c₂, c₃, c₄].Nodup)
    (hbv : branchVertices H = ({c₁, c₂, c₃, c₄} : Set (Fin n)))
    (hcard : Fintype.card (Fin n) = 6) : trackLength q ≤ 3 := by
  classical
  have hqnd : q.Nodup := hq.1.2.1
  have hInd : (trackInterior q).Nodup :=
    ((q.tail.dropLast_sublist).trans q.tail_sublist).nodup hqnd
  have hsub : (trackInterior q).toFinset ⊆ Finset.univ \ ({c₁, c₂, c₃, c₄} : Finset (Fin n)) := by
    intro v hv
    have hv' : v ∈ trackInterior q := List.mem_toFinset.mp hv
    have := hq.2.1 v hv'
    rw [hbv] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact this
  have hcards : ({c₁, c₂, c₃, c₄} : Finset (Fin n)).card = 4 := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true, not_or] at hnd
    obtain ⟨⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩ := hnd
    rw [Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
      Finset.card_insert_of_notMem (by simp [n23, n24]),
      Finset.card_insert_of_notMem (by simp [n34])]
    simp
  have hle : (trackInterior q).length ≤ 2 := by
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hInd,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, hcards] at this
    exact this
  have hlen : (trackInterior q).length = q.length - 2 := by
    simp only [trackInterior, List.length_dropLast, List.length_tail]
    omega
  simp only [trackLength]
  omega

/-- An edge in the prescribed lower bound of a vertex's neighbour set really is a neighbour. -/
theorem adj_of_edge_mem (phi : H.lineGraph ≃g D.induce K) {f : V} {E : Set (Sym2 (Fin n))}
    (hsup : E ⊆ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, D.Adj f (↑(phi ⟨e, he⟩) : V)})
    {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) (hmem : e ∈ E) :
    D.Adj f (↑(phi ⟨e, he⟩) : V) := (hsup hmem).2

/-- A neighbour of `f` in `K` is the image of an edge in the prescribed upper bound. -/
theorem mem_image_of_adj (phi : H.lineGraph ≃g D.induce K) {f : V} {E : Set (Sym2 (Fin n))}
    (hsub : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, D.Adj f (↑(phi ⟨e, he⟩) : V)} ⊆ E)
    {w : V} (hw : w ∈ K) (hadj : D.Adj f w) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ E ∧ w = (↑(phi ⟨e, he⟩) : V) := by
  obtain ⟨e, he, rfl⟩ := exists_preimage phi hw
  exact ⟨e, he, hsub ⟨he, hadj⟩, rfl⟩

end Workspace.ProofLemmas.Thm93CaseTwoSixOneDict
