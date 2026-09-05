import Workspace.ProofLemmas.Thm58StarStarTracks
import Workspace.ProofLemmas.Thm58StarStarGapTracks
import Workspace.ProofLemmas.Thm58StarStarGapCross
import Workspace.ProofLemmas.Thm58StarStarGapLocal
import Workspace.ProofLemmas.Thm58StarStarGapOffBranch
import Workspace.ProofLemmas.Thm58StarStarGapCovered

/-!
# The paths of 5.8 (4)

The two star vertices are joined by a branch, whose rung is the path `R` of `L(H)` from `r₁` to
`r₂`.  The paper's proof of claim (4) splits into two halves.

* *"Suppose that both `B₁` and `B₂` are empty.  There is a cycle in `J` of length `≥ 4` using
  the edge `v₁v₂`, and so there is a path in `L(H)` of length `≥ 2` from `A₁` to `A₂` with no
  internal vertex in `N_{v₁} ∪ V(R_{v₁v₂}) ∪ N_{v₂}`.  The union of this path with `R_{v₁v₂}`
  induces a hole, and so does its union with `F`, and therefore these two paths have lengths of
  the same parity."*  The existence of the crossing track of `H` is the gap `exists_crossTrack`;
  its rung, the two holes and the parity conclusion are proved (here and in
  `Thm58StarStarGaps`).

* *"So we may assume that at least one of `B₁`, `B₂` is nonempty."*  This half splits again,
  according to whether some star of `H` contains `A₁ ∪ A₂`.  If not, 5.6 gives two paths of
  opposite parity that are both completed via `F` (the gap `exists_tracks`, the exact
  analogue of claim (3)).  If so, the paper's final paragraph builds two completions of one
  path `T` that have different parity; that paragraph is the gap `covered_holes`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarAdjacentGap

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles Thm58StarStarTracks
open ThreeTracksLineGraphPrism TrackToRungPath Thm58StarStarGapTracks
open Thm58StarStarGapOffBranch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}
  {q : List (Fin n)} {R : List V} {r₁ r₂ : V}

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-! ## Bookkeeping around the rung -/

/-- The two stars meet only on the rung. -/
theorem inter_subset_rung (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂)
    (hq2 : 2 ≤ q.length) (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q)) :
    N c₁ ∩ N c₂ ⊆ {x : V | x ∈ R} := by
  rw [hRset]
  exact Thm58StarStarGeometry.stars_inter_subset_rung h hq hfrom hq2

/-- A vertex of the first star other than `r₁` is off the rung. -/
theorem not_mem_rung₁ (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) {x : V}
    (hx : x ∈ N c₁) (hne : x ≠ r₁) : x ∉ R := by
  intro hmem
  have : x ∈ N c₁ ∩ {y : V | y ∈ R} := ⟨hx, hmem⟩
  rw [hi₁] at this
  exact hne this

/-- A vertex of the second star other than `r₂` is off the rung. -/
theorem not_mem_rung₂ (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂}) {x : V}
    (hx : x ∈ N c₂) (hne : x ≠ r₂) : x ∉ R := by
  intro hmem
  have : x ∈ N c₂ ∩ {y : V | y ∈ R} := ⟨hx, hmem⟩
  rw [hi₂] at this
  exact hne this

theorem mem_rung₁ (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) : r₁ ∈ N c₁ ∧ r₁ ∈ R := by
  have : r₁ ∈ N c₁ ∩ {y : V | y ∈ R} := by rw [hi₁]; rfl
  exact ⟨this.1, this.2⟩

theorem mem_rung₂ (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂}) : r₂ ∈ N c₂ ∧ r₂ ∈ R := by
  have : r₂ ∈ N c₂ ∩ {y : V | y ∈ R} := by rw [hi₂]; rfl
  exact ⟨this.1, this.2⟩

/-! ## The crossing path of the first half -/

/-- A rung whose track shares no edge with the branch is disjoint from the branch rung. -/
theorem rung_disjoint (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    {Q : List (Fin n)} (hQ : IsTrackList H Q)
    (hdisj : ∀ e ∈ trackEdges Q, e ∉ trackEdges q) :
    ∀ x ∈ trackRung φ Q hQ, x ∉ R := by
  intro x hx hmem
  obtain ⟨f, hf, hfQ, rfl⟩ := (mem_trackRung_iff φ hQ).mp hx
  have hmem' : (φ ⟨f, hf⟩ : V) ∈ edgeImage φ (trackEdges q) := by
    rw [← hRset]; exact hmem
  exact hdisj f hfQ ((image_mem_iff hf).mp hmem')

/-- GAP — PAPER, proof of 5.8 (4), printed p. 27: *"There is a cycle in `J` of length `≥ 4`
using the edge `v₁v₂`, and so there is a path in `L(H)` of length `≥ 2` from `A₁` to `A₂` with
no internal vertex in `N_{v₁} ∪ V(R_{v₁v₂}) ∪ N_{v₂}`."*

The path of `L(H)` is the rung of a track `Q` of `H` from `v₁` to `v₂` that shares no edge with
the branch: the cycle of `J` of length `≥ 4` through `v₁v₂` is a cycle of `H` through the
branch, and `Q` is the rest of that cycle.  *"Length `≥ 2"`* is `4 ≤ Q.length`, and
*"from `A₁` to `A₂`"* is the two adjacencies, `A₁` being the set of vertices of
`N_{v₁} \ {r₁}` adjacent to `p₁` and `A₂` the set of vertices of `N_{v₂} \ {r₂}` adjacent to
`p₂`.  Both `B₁` and `B₂` are empty here (`hB₁`, `hB₂`), so the first edge of any such track
is automatically a neighbour of `p₁` and its last edge one of `p₂`. -/
theorem exists_crossTrack
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB₁ : ∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hB₂ : ∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x) :
    ∃ (Q : List (Fin n)) (h4 : 4 ≤ Q.length) (hQ : IsTrackFrom H Q c₁ c₂),
      (∀ e ∈ trackEdges Q, e ∉ trackEdges q) ∧
      G.Adj p₁ (firstRungVertex φ Q hQ.1 (by omega)) ∧
      G.Adj p₂ (lastRungVertex φ Q hQ.1 (by omega)) := by
  classical
  obtain ⟨Q, h4, hQ, hd⟩ :=
    Thm58StarStarGapCross.exists_cross_track h.ready.2.1 h.ready.2.2.1.1 hq hfrom hq2
      h.star₁ h.star₂
  have h2 : 2 ≤ Q.length := by omega
  have hnotR : ∀ x ∈ trackRung φ Q hQ.1, x ∉ R := by
    intro x hx hmem
    obtain ⟨f, hf, hfQ, rfl⟩ := (mem_trackRung_iff φ hQ.1).mp hx
    have : (φ ⟨f, hf⟩ : V) ∈ edgeImage φ (trackEdges q) := by rw [← hRset]; exact hmem
    exact hd f hfQ ((image_mem_iff hf).mp this)
  have hne₁ : firstRungVertex φ Q hQ.1 h2 ≠ r₁ := by
    intro hc
    exact hnotR _ (firstRungVertex_mem φ hQ.1 h2) (hc ▸ (mem_rung₁ h hi₁).2)
  have hne₂ : lastRungVertex φ Q hQ.1 h2 ≠ r₂ := by
    intro hc
    exact hnotR _ (lastRungVertex_mem φ hQ.1 h2) (hc ▸ (mem_rung₂ h hi₂).2)
  exact ⟨Q, h4, hQ, hd,
    hB₁ _ ⟨firstRungVertex_mem_star (star_eq h) hQ h2, by simpa using hne₁⟩,
    hB₂ _ ⟨lastRungVertex_mem_star (star_eq h) hQ h2, by simpa using hne₂⟩⟩

/-- PAPER, proof of 5.8 (4), printed p. 27: the path of `L(H)` of length `≥ 2` from `A₁` to
`A₂` with no internal vertex in `N_{v₁} ∪ V(R_{v₁v₂}) ∪ N_{v₂}`, read in `G`. -/
theorem exists_crossPath
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB₁ : ∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hB₂ : ∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x) :
    ∃ (T : List V) (a₁ a₂ : V),
      IsPathFrom G T a₁ a₂ ∧ (∀ x ∈ T, x ∈ K) ∧ 3 ≤ T.length ∧
      a₁ ∈ N c₁ \ {r₁} ∧ G.Adj p₁ a₁ ∧ a₂ ∈ N c₂ \ {r₂} ∧ G.Adj p₂ a₂ ∧
      (∀ x ∈ T, x ≠ a₁ → x ≠ a₂ → x ∉ N c₁ ∧ x ∉ N c₂ ∧ x ∉ R) := by
  classical
  obtain ⟨Q, h4, hQ, hd, hp₁, hp₂⟩ :=
    exists_crossTrack h hq hfrom hq2 hR hRset hi₁ hi₂ hA₁ hA₂ hB₁ hB₂
  have h2 : 2 ≤ Q.length := by omega
  have hoff := rung_disjoint h hRset hQ.1 hd
  have hlen : (trackRung φ Q hQ.1).length = Q.length - 1 := by
    rw [trackRung_length]; rfl
  refine ⟨trackRung φ Q hQ.1, firstRungVertex φ Q hQ.1 h2, lastRungVertex φ Q hQ.1 h2,
    trackRung_isPathFrom_ends φ hQ h2, trackRung_subset_K φ Q hQ.1, by omega, ?_, hp₁, ?_, hp₂,
    ?_⟩
  · refine ⟨firstRungVertex_mem_star (star_eq h) hQ h2, ?_⟩
    intro hcon
    exact hoff _ (firstRungVertex_mem φ hQ.1 h2) (hcon ▸ (mem_rung₁ h hi₁).2)
  · refine ⟨lastRungVertex_mem_star (star_eq h) hQ h2, ?_⟩
    intro hcon
    exact hoff _ (lastRungVertex_mem φ hQ.1 h2) (hcon ▸ (mem_rung₂ h hi₂).2)
  · intro x hx hx₁ hx₂
    refine ⟨fun hcon => hx₁ (eq_firstRungVertex (star_eq h) hQ h2 hcon hx),
      fun hcon => hx₂ (eq_lastRungVertex (star_eq h) hQ h2 hcon hx), hoff x hx⟩

/-! ## The two halves of the second case -/

/-- GAP — PAPER, proof of 5.8 (4), printed p. 27: *"There is a path `S₁` from `A₁` to `A₂` with
no vertex in `N_{v₁} ∪ N_{v₂} ∪ V(R_{v₁v₂})` except for its ends.  Suppose that there is no
vertex `w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`.  Then we can apply 5.6 to the graph obtained from `H`
by deleting the edges and internal vertices of the branch between `v₁` and `v₂`.  We deduce
(possibly after exchanging `v₁` and `v₂`) that there is a path `S₂` of `L(H)` with first vertex
in `A₁`, second vertex in `B₁`, last vertex in `A₂`, and otherwise disjoint from
`N_{v₁} ∪ N_{v₂} ∪ V(R_{v₁v₂})`."*

The two paths are the rungs of two tracks of `H`, exactly as in claim (3), and *"no vertex in
`V(R_{v₁v₂})`"* is the disjointness of the two tracks from the edges of the branch.  The
disjunction is the paper's *"possibly after exchanging `v₁` and `v₂`"*. -/
theorem exists_tracks
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB : (∃ x ∈ N c₁ \ {r₁}, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂ \ {r₂}, ¬ G.Adj p₂ x))
    (hnw : ¬ ∃ w : Fin n, (∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x ∈ N w) ∧
      (∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x ∈ N w)) :
    TracksFound G H K φ p₁ p₂ c₁ c₂ (trackEdges q) ∨
      TracksFound G H K φ p₂ p₁ c₂ c₁ (trackEdges q) := by
  classical
  have hc3 : CyclicallyThreeConnected H := ⟨m, J, h.ready.2.1, h.ready.2.2.1.1⟩
  -- the only edge of `H` joining the two star vertices is an edge of the branch
  have hchord : ∀ f ∈ H.edgeSet, c₁ ∈ f → c₂ ∈ f → f ∈ trackEdges q := by
    intro f hf h1 h2
    have hmem : (φ ⟨f, hf⟩ : V) ∈ N c₁ ∩ N c₂ := by
      refine ⟨?_, ?_⟩
      · rw [star_eq h c₁]; exact ⟨f, hf, ⟨hf, h1⟩, rfl⟩
      · rw [star_eq h c₂]; exact ⟨f, hf, ⟨hf, h2⟩, rfl⟩
    exact (image_mem_iff hf).mp
      (Thm58StarStarGeometry.stars_inter_subset_rung h hq hfrom hq2 hmem)
  set A₁ := adjPartOff G φ p₁ c₁ (trackEdges q) with hA₁d
  set B₁ := nonAdjPartOff G φ p₁ c₁ (trackEdges q) with hB₁d
  set A₂ := adjPartOff G φ p₂ c₂ (trackEdges q) with hA₂d
  set B₂ := nonAdjPartOff G φ p₂ c₂ (trackEdges q) with hB₂d
  obtain ⟨x₁, hx₁, hx₁a⟩ := hA₁
  obtain ⟨e₁, he₁, he₁A, -⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₁ hx₁ hx₁a
  obtain ⟨x₂, hx₂, hx₂a⟩ := hA₂
  obtain ⟨e₂, he₂, he₂A, -⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₂ hx₂ hx₂a
  have hAne₁ : A₁.Nonempty := ⟨e₁, he₁A⟩
  have hAne₂ : A₂.Nonempty := ⟨e₂, he₂A⟩
  have hBne : B₁.Nonempty ∨ B₂.Nonempty := by
    rcases hB with ⟨y, hy, hny⟩ | ⟨y, hy, hny⟩
    · obtain ⟨f, hf, hfB, -⟩ := exists_nonAdjPartOff_edge (star_eq h) hRset hi₁ hy hny
      exact Or.inl ⟨f, hfB⟩
    · obtain ⟨f, hf, hfB, -⟩ := exists_nonAdjPartOff_edge (star_eq h) hRset hi₂ hy hny
      exact Or.inr ⟨f, hfB⟩
  have hnocover : ¬ ∃ w : Fin n, ∀ e ∈ A₁ ∪ A₂, w ∈ e := by
    rintro ⟨w, hw⟩
    refine hnw ⟨w, ?_, ?_⟩
    · intro x hx hadj
      obtain ⟨e, he, heA, rfl⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₁ hx hadj
      exact (Thm58StarStarGapTracks.mem_star_iff (star_eq h) he).mpr (hw e (Or.inl heA))
    · intro x hx hadj
      obtain ⟨e, he, heA, rfl⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₂ hx hadj
      exact (Thm58StarStarGapTracks.mem_star_iff (star_eq h) he).mpr (hw e (Or.inr heA))
  -- the far ends of the two prescribed edges lie off the branch
  obtain ⟨a, hea, hcaAdj, haq⟩ := far_end_off_branch hq hfrom hq2 hchord (Or.inl rfl) he₁
    (mem_incident_of_adjPartOff he₁A) (notMem_of_adjPartOff he₁A)
  obtain ⟨b, heb, hcbAdj, hbq⟩ := far_end_off_branch hq hfrom hq2 hchord (Or.inr rfl) he₂
    (mem_incident_of_adjPartOff he₂A) (notMem_of_adjPartOff he₂A)
  have hc₁q : c₁ ∈ q := List.mem_of_head? hfrom.2.1
  have hc₂q : c₂ ∈ q := List.mem_of_getLast? hfrom.2.2
  have hconn := branch_complement_connected hc3 hq hq2
  -- a track from `c₁` to `c₂` off the branch with the two prescribed end-edges
  have hbuild : ∀ (d₁ d₂ z₁ z₂ : Fin n), d₁ ≠ d₂ → H.Adj d₁ z₁ → H.Adj z₂ d₂ →
      z₁ ∉ q → z₂ ∉ q → d₁ ∈ q → d₂ ∈ q →
      ∃ (Q : List (Fin n)) (h2 : 2 ≤ Q.length) (hQ : IsTrackFrom H Q d₁ d₂),
        firstTrackEdge Q h2 = s(d₁, z₁) ∧ lastTrackEdge Q h2 = s(z₂, d₂) ∧
        ∀ e ∈ trackEdges Q, e ∉ trackEdges q := by
    intro d₁ d₂ z₁ z₂ hne hadj₁ hadj₂ hz₁ hz₂ hd₁ hd₂
    obtain ⟨Q, hQ2, hQ, hQf, hQl, hQ3, -, hQmem⟩ :=
      exists_track_hung hconn hne hadj₁ hadj₂ hz₁ hz₂ (by simpa using hd₁) (by simpa using hd₂)
    refine ⟨Q, hQ2, hQ, hQf, hQl, ?_⟩
    intro e heQ heq'
    obtain ⟨i, hi, rfl⟩ := heq'
    have hmemQ := BranchClassification.mem_of_mem_trackEdges heQ
    have hcase : ∀ j : ℕ, ∀ hj : j < q.length, q[j]'hj ∈ Q → q[j]'hj = d₁ ∨ q[j]'hj = d₂ := by
      intro j hj hjQ
      rcases hQmem _ hjQ with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd (List.getElem_mem hj) h'
    have hne' : q[i]'(by omega) ≠ q[i + 1]'hi := by
      intro hc
      have := hq.1.2.1.getElem_inj_iff.mp hc
      omega
    have h1 := hcase i (by omega) hmemQ.1
    have h2 := hcase (i + 1) hi hmemQ.2
    have habs : s(q[i]'(by omega), q[i + 1]'hi) = s(d₁, d₂) := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne'
      · rw [h1, h2]
      · rw [h1, h2, Sym2.eq_swap]
      · exact absurd (h1.trans h2.symm) hne'
    exact ends_edge_not_mem hQ (by omega) (habs ▸ heQ)
  -- 5.6, applied off the branch, supplies the second track at one of the two stars
  rcases five_six_off_branch hc3 hq hfrom hq2 hchord A₁ B₁ A₂ B₂ (partOff_union p₁ c₁ _)
      (partOff_disjoint p₁ c₁ _) (partOff_union p₂ c₂ _) (partOff_disjoint p₂ c₂ _)
      hAne₁ hAne₂ hBne hnocover with
    ⟨t, ht3, htrack, htE, htA, htB, htlast, htA'⟩ | ⟨t, ht3, htrack, htE, htA, htB, htlast, htA'⟩
  · obtain ⟨Q, hQ2, hQ, hQf, hQl, hQE⟩ :=
      hbuild c₁ c₂ a b (stars_ne h) hcaAdj hcbAdj.symm haq hbq hc₁q hc₂q
    have hadj₁ : G.Adj p₁ (firstRungVertex φ Q hQ.1 hQ2) := by
      have hmem : firstTrackEdge Q hQ2 ∈ A₁ := by rw [hQf, ← hea]; exact he₁A
      exact hmem.choose_spec.2.2
    have hadj₂ : G.Adj p₂ (lastRungVertex φ Q hQ.1 hQ2) := by
      have hmem : lastTrackEdge Q hQ2 ∈ A₂ := by
        rw [hQl, Sym2.eq_swap, ← heb]; exact he₂A
      exact hmem.choose_spec.2.2
    refine Or.inl ⟨Q, t, t[0]'(by omega), hQ2, ht3, hQ, ⟨htrack, ?_, htlast⟩, ?_, hQE, htE,
      hadj₁, hadj₂, ?_, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    · exact second_vertex_eq htrack ht3 (mem_incident_of_adjPartOff htA)
        (mem_incident_of_nonAdjPartOff htB)
    · exact htA.choose_spec.2.2
    · exact fun hcon => htB.choose_spec.2.2 hcon
    · exact htA'.choose_spec.2.2
  · obtain ⟨Q, hQ2, hQ, hQf, hQl, hQE⟩ :=
      hbuild c₂ c₁ b a (stars_ne h).symm hcbAdj hcaAdj.symm hbq haq hc₂q hc₁q
    have hadj₂ : G.Adj p₂ (firstRungVertex φ Q hQ.1 hQ2) := by
      have hmem : firstTrackEdge Q hQ2 ∈ A₂ := by rw [hQf, ← heb]; exact he₂A
      exact hmem.choose_spec.2.2
    have hadj₁ : G.Adj p₁ (lastRungVertex φ Q hQ.1 hQ2) := by
      have hmem : lastTrackEdge Q hQ2 ∈ A₁ := by
        rw [hQl, Sym2.eq_swap, ← hea]; exact he₁A
      exact hmem.choose_spec.2.2
    refine Or.inr ⟨Q, t, t[0]'(by omega), hQ2, ht3, hQ, ⟨htrack, ?_, htlast⟩, ?_, hQE, htE,
      hadj₂, hadj₁, ?_, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    · exact second_vertex_eq htrack ht3 (mem_incident_of_adjPartOff htA)
        (mem_incident_of_nonAdjPartOff htB)
    · exact htA.choose_spec.2.2
    · exact fun hcon => htB.choose_spec.2.2 hcon
    · exact htA'.choose_spec.2.2

/-- PAPER, proof of 5.8 (4), printed p. 27: *"Since `H` is bipartite, `S₁` and `S₂` have
opposite parity; but they can both be completed via `F`, a contradiction."* -/
theorem holes_of_not_covered
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB : (∃ x ∈ N c₁ \ {r₁}, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂ \ {r₂}, ¬ G.Adj p₂ x))
    (hnw : ¬ ∃ w : Fin n, (∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x ∈ N w) ∧
      (∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x ∈ N w)) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 :=
  holes_of_tracks h (Thm58StarStarGeometry.stars_inter_subset_rung h hq hfrom hq2)
    (exists_tracks h hq hfrom hq2 hR hRset hi₁ hi₂ hA₁ hA₂ hB hnw)

/-- GAP — PAPER, proof of 5.8 (4), printed p. 27, the final paragraph: *"Consequently there is
a vertex `w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`.  Since `H` is bipartite, and there is a 2-edge track
of `H` between `v₁, v₂` (via `w`), it follows that the branch of `H` with ends `v₁, v₂` has
even length, and therefore `R_{v₁v₂}` has odd length, and in particular `r₁ ≠ r₂`.  Since
`|N_{vᵢ} ∩ N_w| ≤ 1` (since `J` is simple) it follows that `|Aᵢ| = 1`, `Aᵢ = {aᵢ}` say, for
`i = 1, 2`.  Since `X` is not local it is not a subset of `N_w` and so there is a vertex of
`R_{v₁v₂}` in `X`.  Since `Xᵢ ⊆ N_{vᵢ}` for `i = 1, 2`, no internal vertex of `R_{v₁v₂}` is in
`X`, so we may assume that `r₁ ∈ X`.  Since `r₁ ∉ N_{v₂}` it follows that `r₁ ∉ X₂`, and hence
`p₁` is the only vertex in `F` adjacent to `r₁`.  Now the hole `p₁-⋯-pₙ-a₂-a₁-p₁` is even, and
so `n` is even.  If we delete the vertex `v₂` and the edge `a₁` from `H`, what remains is still
connected, and so contains a track from `w` to `v₁`.  Hence there is a path `T` in `L(H)` from
some `a₃ ∈ N(w)` to `r₁`, disjoint from `N_{v₂} ∪ a₁`.  But `T` can be completed to a hole via
`r₁-R_{v₁v₂}-r₂-a₂-a₃` and via `r₁-p₁-⋯-pₙ-a₂-a₃`, and these two completions have different
parity, a contradiction."*

The two completions of the last sentence are the two holes of different parity below. -/
theorem covered_holes
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB : (∃ x ∈ N c₁ \ {r₁}, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂ \ {r₂}, ¬ G.Adj p₂ x))
    (hw : ∃ w : Fin n, (∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x ∈ N w) ∧
      (∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x ∈ N w)) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  classical
  obtain ⟨w, hw1, hw2⟩ := hw
  have hchord : ∀ f ∈ H.edgeSet, c₁ ∈ f → c₂ ∈ f → f ∈ trackEdges q := by
    intro f hf h1 h2
    have hmem : (φ ⟨f, hf⟩ : V) ∈ N c₁ ∩ N c₂ := by
      refine ⟨?_, ?_⟩
      · rw [star_eq h c₁]; exact ⟨f, hf, ⟨hf, h1⟩, rfl⟩
      · rw [star_eq h c₂]; exact ⟨f, hf, ⟨hf, h2⟩, rfl⟩
    exact (image_mem_iff hf).mp
      (Thm58StarStarGeometry.stars_inter_subset_rung h hq hfrom hq2 hmem)
  obtain ⟨x₁, hx₁, hx₁a⟩ := hA₁
  obtain ⟨e₁, he₁, he₁A, hx₁eq⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₁ hx₁ hx₁a
  obtain ⟨x₂, hx₂, hx₂a⟩ := hA₂
  obtain ⟨e₂, he₂, he₂A, hx₂eq⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₂ hx₂ hx₂a
  have hwe₁ : w ∈ e₁ := by
    have := hw1 x₁ hx₁ hx₁a
    rw [hx₁eq] at this
    exact (Thm58StarStarGapTracks.mem_star_iff (star_eq h) he₁).mp this
  have hwe₂ : w ∈ e₂ := by
    have := hw2 x₂ hx₂ hx₂a
    rw [hx₂eq] at this
    exact (Thm58StarStarGapTracks.mem_star_iff (star_eq h) he₂).mp this
  have hc₁e₁ : c₁ ∈ e₁ := mem_incident_of_adjPartOff he₁A
  have hc₂e₂ : c₂ ∈ e₂ := mem_incident_of_adjPartOff he₂A
  have hE₁ : e₁ ∉ trackEdges q := notMem_of_adjPartOff he₁A
  have hE₂ : e₂ ∉ trackEdges q := notMem_of_adjPartOff he₂A
  have hwne₁ : w ≠ c₁ := by
    rintro rfl
    exact hE₂ (hchord e₂ he₂ hwe₂ hc₂e₂)
  have hwne₂ : w ≠ c₂ := by
    rintro rfl
    exact hE₁ (hchord e₁ he₁ hc₁e₁ hwe₁)
  have he₁' : e₁ = s(c₁, w) :=
    (Sym2.mem_and_mem_iff (Ne.symm hwne₁)).mp ⟨hc₁e₁, hwe₁⟩
  have he₂' : e₂ = s(c₂, w) :=
    (Sym2.mem_and_mem_iff (Ne.symm hwne₂)).mp ⟨hc₂e₂, hwe₂⟩
  have hw₁ : H.Adj c₁ w := by
    have : s(c₁, w) ∈ H.edgeSet := he₁' ▸ he₁
    exact this
  have hw₂ : H.Adj c₂ w := by
    have : s(c₂, w) ∈ H.edgeSet := he₂' ▸ he₂
    exact this
  have hs₁ : s(c₁, w) ∉ trackEdges q := he₁' ▸ hE₁
  have hs₂ : s(c₂, w) ∉ trackEdges q := he₂' ▸ hE₂
  have hsing₁ : ∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x = (φ ⟨s(c₁, w), hw₁⟩ : V) := by
    intro x hx hadj
    obtain ⟨f, hf, hfA, rfl⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₁ hx hadj
    have hwf : w ∈ f :=
      (Thm58StarStarGapTracks.mem_star_iff (star_eq h) hf).mp (hw1 _ hx hadj)
    have hcf : c₁ ∈ f := mem_incident_of_adjPartOff hfA
    have hfe : f = s(c₁, w) := (Sym2.mem_and_mem_iff (Ne.symm hwne₁)).mp ⟨hcf, hwf⟩
    exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext hfe)
  have hsing₂ : ∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x = (φ ⟨s(c₂, w), hw₂⟩ : V) := by
    intro x hx hadj
    obtain ⟨f, hf, hfA, rfl⟩ := exists_adjPartOff_edge (star_eq h) hRset hi₂ hx hadj
    have hwf : w ∈ f :=
      (Thm58StarStarGapTracks.mem_star_iff (star_eq h) hf).mp (hw2 _ hx hadj)
    have hcf : c₂ ∈ f := mem_incident_of_adjPartOff hfA
    have hfe : f = s(c₂, w) := (Sym2.mem_and_mem_iff (Ne.symm hwne₂)).mp ⟨hcf, hwf⟩
    exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext hfe)
  exact Thm58StarStarGapCovered.covered_endgame h hq hfrom hq2 hR hRset hi₁ hi₂ hw₁ hw₂
    hs₁ hs₂ hsing₁ hsing₂ ⟨x₁, hx₁, hx₁a⟩ ⟨x₂, hx₂, hx₂a⟩ hB

end Workspace.ProofLemmas.Thm58StarStarAdjacentGap
