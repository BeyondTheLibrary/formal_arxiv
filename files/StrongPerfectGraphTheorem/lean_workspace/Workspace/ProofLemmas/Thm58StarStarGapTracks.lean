import Workspace.ProofLemmas.Thm58StarStarTracks
import Workspace.ProofLemmas.Thm58StarStarGapLocal
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
import Workspace.ProofLemmas.Thm56Basics

/-!
# Building the two tracks of 5.8 (3) and (4)

The paper produces two tracks of `H`.  The first one, *"a track in `H` from `v₁` to `v₂` with
end-edges in `A₁` and `A₂` respectively"*, is a track of `H \ {v₁, v₂}` between the far ends of
one edge of `A₁` and one edge of `A₂`, with `v₁` hung on the front and `v₂` on the back; that
is `exists_track_hung` below.  The second one is the output of 5.6, and `partition` records
that splitting the edges at a vertex according to whether their vertex of `L(H)` is adjacent to
a given vertex of `G` is a partition of `δ_H(v)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapTracks

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics
open ThreeTracksLineGraphPrism TrackToRungPath

/-! ## Hanging two vertices on a track of a connected set -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Hang `c` on the front and `d` on the back of a track of `D` inside `S`.  The two end-edges
of the result are the prescribed ones, and every internal vertex stays in `S`. -/
theorem exists_track_hung {D : SimpleGraph W} {S : Set W} (hS : ConnectedSet D S)
    {c d a b : W} (hcd : c ≠ d) (hca : D.Adj c a) (hbd : D.Adj b d)
    (ha : a ∈ S) (hb : b ∈ S) (hcS : c ∉ S) (hdS : d ∉ S) :
    ∃ (Q : List W) (h2 : 2 ≤ Q.length), IsTrackFrom D Q c d ∧
      firstTrackEdge Q h2 = s(c, a) ∧ lastTrackEdge Q h2 = s(b, d) ∧
      3 ≤ Q.length ∧ (a ≠ b → 4 ≤ Q.length) ∧
      ∀ z ∈ Q, z = c ∨ z = d ∨ z ∈ S := by
  classical
  obtain ⟨a', ha', b', hb', P, hP, hPS, -, -⟩ :=
    ConnectedSetHasEndpointCleanTrack D S {a} {b} hS ⟨a, rfl⟩ ⟨b, rfl⟩
      (by simpa using ha) (by simpa using hb)
  have haa : a' = a := by simpa using ha'
  have hbb : b' = b := by simpa using hb'
  rw [haa, hbb] at hP
  have hPpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  have hcP : c ∉ P := fun hc => hcS (hPS c hc)
  have hdP : d ∉ P := fun hc => hdS (hPS d hc)
  have hcat : IsTrackFrom D (P ++ [d]) a d := TrackSlice.isTrackFrom_concat hP hbd hdP
  have hcP' : c ∉ P ++ [d] := by
    intro hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcP hc
    · exact hcd (List.eq_of_mem_singleton hc)
  have hab : a ≠ b → 2 ≤ P.length := by
    intro hne
    by_contra hcon
    have h1 : P.length = 1 := by omega
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp h1
    rw [hz] at hP
    exact hne ((by simpa using hP.2.1 : z = a).symm.trans (by simpa using hP.2.2 : z = b))
  refine ⟨c :: (P ++ [d]), by simp,
    Thm61Claim1Helpers.isTrackFrom_cons hcat hca hcP', ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (c :: (P ++ [d]))[1]'(by simp) = a := by
      rw [List.getElem_cons_succ, List.getElem_append_left hPpos]
      exact Thm61Claim1Helpers.head_getElem hP.2.1 hPpos
    simp only [firstTrackEdge]
    rw [h1]
    rfl
  · have hlen : (c :: (P ++ [d])).length = P.length + 2 := by simp
    have hb2 : (c :: (P ++ [d]))[(c :: (P ++ [d])).length - 2]'(by omega) = b := by
      rw [SubdivisionCounting.getElem_eq_of_index_eq (c :: (P ++ [d]))
        (show (c :: (P ++ [d])).length - 2 = P.length - 1 + 1 by omega) (by omega) (by omega),
        List.getElem_cons_succ, List.getElem_append_left (show P.length - 1 < P.length by omega)]
      exact Thm61Claim1Helpers.last_getElem hP.2.2 hPpos
    have hd2 : (c :: (P ++ [d]))[(c :: (P ++ [d])).length - 1]'(by omega) = d := by
      rw [SubdivisionCounting.getElem_eq_of_index_eq (c :: (P ++ [d]))
        (show (c :: (P ++ [d])).length - 1 = P.length + 1 by omega) (by omega) (by omega),
        List.getElem_cons_succ, List.getElem_append_right (by omega)]
      simp
    simp only [lastTrackEdge]
    rw [hb2, hd2]
  · simp only [List.length_cons, List.length_append]
    omega
  · intro hne
    have := hab hne
    simp only [List.length_cons, List.length_append]
    omega
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact Or.inl hz
    · rcases List.mem_append.mp hz with hz | hz
      · exact Or.inr (Or.inr (hPS z hz))
      · exact Or.inr (Or.inl (List.eq_of_mem_singleton hz))

/-- A track on at least three vertices has no edge joining its two ends. -/
theorem ends_edge_not_mem {D : SimpleGraph W} {Q : List W} {a b : W}
    (hQ : IsTrackFrom D Q a b) (h3 : 3 ≤ Q.length) : s(a, b) ∉ trackEdges Q := by
  rintro ⟨i, hi, hEq⟩
  have h0 : Q[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hl : Q[Q.length - 1]'(by omega) = b :=
    Thm61Claim1Helpers.last_getElem hQ.2.2 (by omega)
  have hnd := hQ.1.2.1
  rcases Sym2.eq_iff.mp hEq with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hi0 : (0 : ℕ) = i := hnd.getElem_inj_iff.mp (h0.trans e1)
    have hi1 : Q.length - 1 = i + 1 := hnd.getElem_inj_iff.mp (hl.trans e2)
    omega
  · have hi0 : Q.length - 1 = i := hnd.getElem_inj_iff.mp (hl.trans e2)
    omega

/-- PAPER, 5.6, printed p. 21: *"first edge in `A₁`, second edge in `B₁` (and hence second
vertex `c₁`)"*.  A vertex lying on both the first and the second edge of a track is its second
vertex. -/
theorem second_vertex_eq {D : SimpleGraph W} {t : List W} (ht : IsTrackList D t)
    (h3 : 3 ≤ t.length) {c : W}
    (h1 : c ∈ s(t[0]'(by omega), t[1]'(by omega)))
    (h2 : c ∈ s(t[1]'(by omega), t[2]'(by omega))) :
    t[1]'(by omega) = c := by
  have hnd := ht.2.1
  rcases Sym2.mem_iff.mp h1 with hc0 | hc1
  · rcases Sym2.mem_iff.mp h2 with hc1 | hc2
    · exact hc1.symm
    · exact absurd (hnd.getElem_inj_iff.mp (hc0.symm.trans hc2)) (by omega)
  · exact hc1.symm

/-! ## Splitting the edges at a vertex by adjacency to an outside vertex -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
  {φ : H.lineGraph ≃g G.induce K}

/-- PAPER, proof of 5.8 (3), printed p. 26: *"Let `A₁` be the set of vertices in `N_{v₁}`
adjacent to `p₁`"*. -/
def adjPart (G : SimpleGraph V) {H : SimpleGraph (Fin n)} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (p : V) (c : Fin n) : Set (Sym2 (Fin n)) :=
  {e | ∃ he : e ∈ H.edgeSet, c ∈ e ∧ G.Adj p (φ ⟨e, he⟩ : V)}

/-- PAPER, proof of 5.8 (3), printed p. 26: *"and `B₁ = N_{v₁} \ A₁`"*. -/
def nonAdjPart (G : SimpleGraph V) {H : SimpleGraph (Fin n)} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (p : V) (c : Fin n) : Set (Sym2 (Fin n)) :=
  {e | ∃ he : e ∈ H.edgeSet, c ∈ e ∧ ¬ G.Adj p (φ ⟨e, he⟩ : V)}

theorem mem_adjPart_iff {p : V} {c : Fin n} {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) :
    e ∈ adjPart G φ p c ↔ (c ∈ e ∧ G.Adj p (φ ⟨e, he⟩ : V)) := by
  constructor
  · rintro ⟨he', hce, hadj⟩; exact ⟨hce, hadj⟩
  · rintro ⟨hce, hadj⟩; exact ⟨he, hce, hadj⟩

theorem mem_nonAdjPart_iff {p : V} {c : Fin n} {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) :
    e ∈ nonAdjPart G φ p c ↔ (c ∈ e ∧ ¬ G.Adj p (φ ⟨e, he⟩ : V)) := by
  constructor
  · rintro ⟨he', hce, hadj⟩; exact ⟨hce, hadj⟩
  · rintro ⟨hce, hadj⟩; exact ⟨he, hce, hadj⟩

theorem mem_incident_of_adjPart {p : V} {c : Fin n} {e : Sym2 (Fin n)}
    (he : e ∈ adjPart G φ p c) : c ∈ e := he.choose_spec.1

theorem mem_incident_of_nonAdjPart {p : V} {c : Fin n} {e : Sym2 (Fin n)}
    (he : e ∈ nonAdjPart G φ p c) : c ∈ e := he.choose_spec.1

theorem part_union (p : V) (c : Fin n) :
    adjPart G φ p c ∪ nonAdjPart G φ p c = incidentEdges H c := by
  classical
  ext e
  constructor
  · rintro (⟨he, hce, -⟩ | ⟨he, hce, -⟩) <;> exact ⟨he, hce⟩
  · rintro ⟨he, hce⟩
    by_cases hadj : G.Adj p (φ ⟨e, he⟩ : V)
    · exact Or.inl ⟨he, hce, hadj⟩
    · exact Or.inr ⟨he, hce, hadj⟩

theorem part_disjoint (p : V) (c : Fin n) :
    Disjoint (adjPart G φ p c) (nonAdjPart G φ p c) := by
  rw [Set.disjoint_left]
  rintro e ⟨he, -, hadj⟩ hne
  exact ((mem_nonAdjPart_iff he).mp hne).2 hadj

/-- A vertex of `L(H)` lies in the star of `c` exactly when its edge is incident with `c`. -/
theorem mem_star_iff {N : Fin n → Set V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {c : Fin n} {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) :
    (φ ⟨e, he⟩ : V) ∈ N c ↔ c ∈ e := by
  rw [hstar c, image_mem_iff he]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- A vertex of the star of `c` that is adjacent to `p` comes from an edge of `adjPart`. -/
theorem exists_adjPart_edge {N : Fin n → Set V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {p : V} {c : Fin n} {x : V} (hx : x ∈ N c) (hadj : G.Adj p x) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ adjPart G φ p c ∧ x = (φ ⟨e, he⟩ : V) := by
  rw [hstar c] at hx
  obtain ⟨e, he, hce, rfl⟩ := hx
  exact ⟨e, he, ⟨he, hce.2, hadj⟩, rfl⟩

/-- A vertex of the star of `c` that is not adjacent to `p` comes from an edge of
`nonAdjPart`. -/
theorem exists_nonAdjPart_edge {N : Fin n → Set V}
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {p : V} {c : Fin n} {x : V} (hx : x ∈ N c) (hadj : ¬ G.Adj p x) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ nonAdjPart G φ p c ∧ x = (φ ⟨e, he⟩ : V) := by
  rw [hstar c] at hx
  obtain ⟨e, he, hce, rfl⟩ := hx
  exact ⟨e, he, ⟨he, hce.2, hadj⟩, rfl⟩

end Workspace.ProofLemmas.Thm58StarStarGapTracks
