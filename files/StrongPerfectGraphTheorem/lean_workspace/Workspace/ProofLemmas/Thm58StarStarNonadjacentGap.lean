import Workspace.ProofLemmas.Thm58StarStarTracks
import Workspace.ProofLemmas.Thm58StarStarGapTracks
import Workspace.ProofLemmas.Thm58StarStarGapLocal
import Workspace.Statements.S05.Thm_5_6

/-!
# The two paths of 5.8 (3)

PAPER (proof of 5.8 (3), printed p. 26): *"Certainly `A₁` and `A₂` are both nonempty, so there
is a track in `H` from `v₁` to `v₂` with end-edges in `A₁` and `A₂` respectively.  Hence there
is a path `S₁` in `L(H)` from `A₁` to `A₂`, vertex-disjoint from `N_{v₁} ∪ N_{v₂}` except for
its ends.  Since `X = A₁ ∪ A₂` is not local, there is no `w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`.
Hence we can apply 5.6, and we deduce (possibly after exchanging `v₁` and `v₂`) that there is a
path `S₂` in `L(H)` with first vertex in `A₁`, second vertex in `B₁`, last vertex in `A₂`, and
otherwise disjoint from `N_{v₁} ∪ N_{v₂}`.  Since `H` is bipartite, `S₁` and `S₂` have opposite
parity; but they can both be completed via `F`, a contradiction."*

Only the two *tracks* of `H` are left open (`exists_tracks`).  Everything the paper does with
them is proved here: the two paths of `L(H)` are their rungs, the sentences *"vertex-disjoint
from `N_{v₁} ∪ N_{v₂}` except for its ends"* and *"first vertex in `A₁`, second vertex in `B₁`"*
are the star dictionary of `Thm58StarStarTracks`, *"opposite parity"* is bipartiteness of `H`,
and *"they can both be completed via `F`"* is `Thm58StarStarHoles.holes_of_completions`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarNonadjacentGap

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles Thm58StarStarTracks
open ThreeTracksLineGraphPrism TrackToRungPath Thm58StarStarGapTracks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-- In claim (3) the two stars are disjoint: a common vertex would be the edge `c₁c₂` of `H`,
which is a branch containing both star vertices. -/
theorem stars_disjoint (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) :
    N c₁ ∩ N c₂ = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx₁ hx₂
  exact hnb ⟨[c₁, c₂], isBranch_pair h (star_inter_adj h ⟨hx₁, hx₂⟩), by simp, by simp⟩

/-- GAP — PAPER, proof of 5.8 (3), printed p. 26: *"Certainly `A₁` and `A₂` are both nonempty,
so there is a track in `H` from `v₁` to `v₂` with end-edges in `A₁` and `A₂` respectively. ...
Since `X = A₁ ∪ A₂` is not local, there is no `w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`.  Hence we can
apply 5.6, and we deduce (possibly after exchanging `v₁` and `v₂`) that there is a path `S₂` in
`L(H)` with first vertex in `A₁`, second vertex in `B₁`, last vertex in `A₂`."*

`A₁` is the set of vertices of `N_{v₁}` adjacent to `p₁` and `B₁ = N_{v₁} \ A₁`, and `A₂` is
the set of vertices of `N_{v₂}` adjacent to `p₂`, so *"end-edges in `A₁` and `A₂`"* is the pair
of adjacencies asked of the first track, and the three conditions on the first three vertices
of the path `S₂` of 5.6 are the conditions on the first two edges and the last edge of the
second track (the path given by 5.6 has second vertex in `B₁`, hence second vertex `c₁`, which
is why the second track passes through `c₁` at its second vertex).  The two tracks avoid no
edges here, so the edge set to be avoided is empty.  The disjunction is the paper's *"possibly
after exchanging `v₁` and `v₂`"*: 5.6 gives its track at either of the two stars. -/
theorem exists_tracks
    (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (hB : (∃ x ∈ N c₁, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂, ¬ G.Adj p₂ x)) :
    TracksFound G H K φ p₁ p₂ c₁ c₂ ∅ ∨ TracksFound G H K φ p₂ p₁ c₂ c₁ ∅ := by
  classical
  have hc3 : CyclicallyThreeConnected H := ⟨m, J, h.ready.2.1, h.ready.2.2.1.1⟩
  have hnadj : ¬ H.Adj c₁ c₂ := by
    intro hadj
    exact hnb ⟨[c₁, c₂], isBranch_pair h hadj, by simp, by simp⟩
  have hconn : ConnectedSet H (({c₁, c₂} : Set (Fin n))ᶜ) :=
    Thm57EndgameConnectivity.connected_compl_pair_of_no_common_branch H hc3 c₁ c₂ hnb
  set A₁ := adjPart G φ p₁ c₁ with hA₁def
  set B₁ := nonAdjPart G φ p₁ c₁ with hB₁def
  set A₂ := adjPart G φ p₂ c₂ with hA₂def
  set B₂ := nonAdjPart G φ p₂ c₂ with hB₂def
  -- `A₁` and `A₂` are nonempty: each end of the outside path sees the star of its own vertex.
  obtain ⟨x₁, hx₁, hx₁adj⟩ := first_outside h
  obtain ⟨e₁, he₁, he₁A, -⟩ := exists_adjPart_edge (star_eq h) hx₁.1 hx₁adj
  obtain ⟨x₂, hx₂, hx₂adj⟩ := last_outside h
  obtain ⟨e₂, he₂, he₂A, -⟩ := exists_adjPart_edge (star_eq h) hx₂.1 hx₂adj
  have hAne₁ : A₁.Nonempty := ⟨e₁, he₁A⟩
  have hAne₂ : A₂.Nonempty := ⟨e₂, he₂A⟩
  -- at least one of `B₁`, `B₂` is nonempty
  have hBne : B₁.Nonempty ∨ B₂.Nonempty := by
    rcases hB with ⟨y, hy, hny⟩ | ⟨y, hy, hny⟩
    · obtain ⟨f, hf, hfB, -⟩ := exists_nonAdjPart_edge (star_eq h) hy hny
      exact Or.inl ⟨f, hfB⟩
    · obtain ⟨f, hf, hfB, -⟩ := exists_nonAdjPart_edge (star_eq h) hy hny
      exact Or.inr ⟨f, hfB⟩
  -- every edge of `A₁ ∪ A₂` is an edge of `H`, so deleting its ends leaves `H` connected
  have hAedge : ∀ e ∈ A₁ ∪ A₂, e ∈ H.edgeSet := by
    rintro e (⟨he, -, -⟩ | ⟨he, -, -⟩) <;> exact he
  have hAconn : ∀ e ∈ A₁ ∪ A₂, ∀ u v : Fin n, e = s(u, v) →
      ConnectedSet H (({u, v} : Set (Fin n))ᶜ) := by
    intro e he u v huv
    exact Thm57EndgameConnectivity.edgeEndDeletionConnected_gap H hc3 e (hAedge e he) u v huv
  -- the paper's *"since `X = A₁ ∪ A₂` is not local"*
  have hdisjstars : N c₁ ∩ N c₂ = ∅ := stars_disjoint h hnb
  have hXsub : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      (φ ⟨e, he⟩ : V) ∈ attachments G F K} ⊆ A₁ ∪ A₂ := by
    rintro e ⟨he, hxK, f, hfF, hadj⟩
    have hfP : f ∈ P := mem_path h hfF
    by_cases hf₁ : f = p₁
    · exact Or.inl ⟨he, ((mem_star_iff (star_eq h) he).mp
        (first_adj_mem h hxK (hf₁ ▸ hadj.symm))), hf₁ ▸ hadj.symm⟩
    by_cases hf₂ : f = p₂
    · exact Or.inr ⟨he, ((mem_star_iff (star_eq h) he).mp
        (last_adj_mem h hxK (hf₂ ▸ hadj.symm))), hf₂ ▸ hadj.symm⟩
    · have := mid_adj_mem h hfP hf₁ hf₂ hxK hadj.symm
      rw [hdisjstars] at this
      exact absurd this (Set.notMem_empty _)
  have hnocover : ¬ ∃ w : Fin n, ∀ e ∈ A₁ ∪ A₂, w ∈ e := by
    rintro ⟨w, hw⟩
    refine h.ready.2.2.2.2.2.1 ?_
    have hloc : LocalForLineGraph H (A₁ ∪ A₂) :=
      Thm58StarStarGapLocal.local_of_common_vertex h.ready.2.1 h.ready.2.2.1.1
        (fun e he => ⟨hAedge e he, hw e he⟩)
    rcases hloc with ⟨v, hv, hsub⟩ | ⟨q, hq, hsub⟩
    · exact Or.inl ⟨v, hv, hXsub.trans hsub⟩
    · exact Or.inr ⟨q, hq, hXsub.trans hsub⟩
  -- the track of `H` from `c₁` to `c₂` with end-edges in `A₁` and `A₂`
  obtain ⟨a, haE, hea⟩ := Thm56Basics.exists_endpoint_of_mem (part_union p₁ c₁) he₁A
  obtain ⟨b, hbE, heb⟩ := Thm56Basics.exists_endpoint_of_mem (part_union p₂ c₂) he₂A
  have hca : H.Adj c₁ a := Thm56Basics.adj_of_mem_endpoints (part_union p₁ c₁) haE
  have hcb : H.Adj c₂ b := Thm56Basics.adj_of_mem_endpoints (part_union p₂ c₂) hbE
  have haS : a ∈ (({c₁, c₂} : Set (Fin n))ᶜ) := by
    rintro (h' | h')
    · exact hca.ne' h'
    · exact hnadj (h' ▸ hca)
  have hbS : b ∈ (({c₁, c₂} : Set (Fin n))ᶜ) := by
    rintro (h' | h')
    · exact hnadj (h' ▸ hcb).symm
    · exact hcb.ne' h'
  have hc₁S : c₁ ∉ (({c₁, c₂} : Set (Fin n))ᶜ) := by simp
  have hc₂S : c₂ ∉ (({c₁, c₂} : Set (Fin n))ᶜ) := by simp
  obtain ⟨Q, hQ2, hQ, hQfirst, hQlast, -⟩ :=
    exists_track_hung hconn (stars_ne h) hca hcb.symm haS hbS hc₁S hc₂S
  obtain ⟨Q', hQ'2, hQ', hQ'first, hQ'last, -⟩ :=
    exists_track_hung hconn (stars_ne h).symm hcb hca.symm hbS haS hc₂S hc₁S
  have hQadj₁ : G.Adj p₁ (firstRungVertex φ Q hQ.1 hQ2) := by
    have : firstTrackEdge Q hQ2 ∈ A₁ := by rw [hQfirst, ← hea]; exact he₁A
    exact this.choose_spec.2
  have hQadj₂ : G.Adj p₂ (lastRungVertex φ Q hQ.1 hQ2) := by
    have : lastTrackEdge Q hQ2 ∈ A₂ := by
      rw [hQlast, Sym2.eq_swap, ← heb]; exact he₂A
    exact this.choose_spec.2
  have hQ'adj₂ : G.Adj p₂ (firstRungVertex φ Q' hQ'.1 hQ'2) := by
    have : firstTrackEdge Q' hQ'2 ∈ A₂ := by rw [hQ'first, ← heb]; exact he₂A
    exact this.choose_spec.2
  have hQ'adj₁ : G.Adj p₁ (lastRungVertex φ Q' hQ'.1 hQ'2) := by
    have : lastTrackEdge Q' hQ'2 ∈ A₁ := by
      rw [hQ'last, Sym2.eq_swap, ← hea]; exact he₁A
    exact this.choose_spec.2
  -- 5.6 supplies the second track, at one of the two stars
  rcases Workspace.Statements.S05.SPGT.thm_5_6 H c₁ c₂ hnadj hconn A₁ B₁ A₂ B₂
      (part_union p₁ c₁) (part_disjoint p₁ c₁) (part_union p₂ c₂) (part_disjoint p₂ c₂)
      hAne₁ hAne₂ hBne hAconn hnocover with
    ⟨t, ht3, htrack, htA, htB, htlast, htA'⟩ | ⟨t, ht3, htrack, htA, htB, htlast, htA'⟩
  · refine Or.inl ⟨Q, t, t[0]'(by omega), hQ2, ht3, hQ, ⟨htrack, ?_, htlast⟩, ?_, ?_, ?_,
      hQadj₁, hQadj₂, ?_, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    · exact second_vertex_eq htrack ht3 (mem_incident_of_adjPart htA)
        (mem_incident_of_nonAdjPart htB)
    · intro e _; exact Set.notMem_empty e
    · intro e _; exact Set.notMem_empty e
    · exact htA.choose_spec.2
    · exact fun hcon => htB.choose_spec.2 hcon
    · exact htA'.choose_spec.2
  · refine Or.inr ⟨Q', t, t[0]'(by omega), hQ'2, ht3, hQ', ⟨htrack, ?_, htlast⟩, ?_, ?_, ?_,
      hQ'adj₂, hQ'adj₁, ?_, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    · exact second_vertex_eq htrack ht3 (mem_incident_of_adjPart htA)
        (mem_incident_of_nonAdjPart htB)
    · intro e _; exact Set.notMem_empty e
    · intro e _; exact Set.notMem_empty e
    · exact htA.choose_spec.2
    · exact fun hcon => htB.choose_spec.2 hcon
    · exact htA'.choose_spec.2

/-- PAPER, proof of 5.8 (3), printed p. 26, last sentence: the two paths of `L(H)` are the rungs
of the two tracks, they have opposite parity, and both are completed via `F`. -/
theorem holes
    (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (hB : (∃ x ∈ N c₁, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂, ¬ G.Adj p₂ x)) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  refine holes_of_tracks h ?_ (exists_tracks h hnb hB)
  rw [stars_disjoint h hnb]
  exact Set.empty_subset _

end Workspace.ProofLemmas.Thm58StarStarNonadjacentGap
