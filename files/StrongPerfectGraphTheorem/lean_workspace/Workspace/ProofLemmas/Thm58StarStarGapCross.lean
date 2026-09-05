import Workspace.ProofLemmas.Thm58StarStarGapTracks
import Workspace.ProofLemmas.SubdivisionTrackExpansion
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# The cycle of `J` through an edge, read in `H`

PAPER, proof of 5.8 (4), printed p. 27: *"There is a cycle in `J` of length `≥ 4` using the
edge `v₁v₂`, and so there is a path in `L(H)` of length `≥ 2` from `A₁` to `A₂` with no
internal vertex in `N_{v₁} ∪ V(R_{v₁v₂}) ∪ N_{v₂}`."*

The cycle is the edge `v₁v₂` together with a track of `J` from `v₁` to `v₂` that does not use
that edge; `exists_long_track_off_edge` builds that track, and *"length `≥ 4`"* is the fact
that the track can be taken with at least three edges.  Expanding the track through the
subdivision turns it into a track of `H` from `v₁` to `v₂` sharing no edge with the branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapCross

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCompose
open Thm58StarStarGapTracks

/-! ## A long track of `J` between the ends of an edge -/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- PAPER, proof of 5.8 (4), printed p. 27: *"There is a cycle in `J` of length `≥ 4` using the
edge `v₁v₂`"*.  The cycle is this track together with the edge `uv`. -/
theorem exists_long_track_off_edge {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {u v : U} (huv : J.Adj u v) :
    ∃ p : List U, 4 ≤ p.length ∧ IsTrackFrom J p u v ∧ s(u, v) ∉ trackEdges p := by
  classical
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hcard : ({u, v} : Set U).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hconn : ConnectedSet J (({u, v} : Set U)ᶜ) :=
    (hJ.2 ({u, v} : Set U) (by omega)).preconnected
  -- a neighbour of `u` other than `v`
  have hx : ∃ x ∈ J.neighborSet u, x ≠ v := by
    by_contra hc
    push_neg at hc
    have hsub : J.neighborSet u ⊆ {v} := fun z hz => hc z hz
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h1 : ({v} : Set U).ncard = 1 := Set.ncard_singleton v
    have := hdeg u
    omega
  obtain ⟨x, hxu, hxv⟩ := hx
  -- a neighbour of `v` other than `u` and `x`
  have hy : ∃ y ∈ J.neighborSet v, y ≠ u ∧ y ≠ x := by
    by_contra hc
    push_neg at hc
    have hsub : J.neighborSet v ⊆ {u, x} := by
      intro z hz
      by_cases hzu : z = u
      · exact Or.inl hzu
      · exact Or.inr (hc z hz hzu)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h1 : ({u, x} : Set U).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    have := hdeg v
    omega
  obtain ⟨y, hyv, hyu, hyx⟩ := hy
  have hxS : x ∈ (({u, v} : Set U)ᶜ) := by
    rintro (h | h)
    · exact (SimpleGraph.mem_neighborSet _ _ _ |>.mp hxu).ne' h
    · exact hxv h
  have hyS : y ∈ (({u, v} : Set U)ᶜ) := by
    rintro (h | h)
    · exact hyu h
    · exact (SimpleGraph.mem_neighborSet _ _ _ |>.mp hyv).ne' h
  obtain ⟨Q, hQ2, hQ, -, -, -, hlen4, -⟩ :=
    exists_track_hung hconn huv.ne hxu ((SimpleGraph.mem_neighborSet _ _ _ |>.mp hyv).symm)
      hxS hyS (by simp) (by simp)
  have h4 : 4 ≤ Q.length := hlen4 (Ne.symm hyx)
  exact ⟨Q, h4, hQ, ends_edge_not_mem hQ (by omega)⟩

/-! ## Expansion through the subdivision -/

variable {W : Type*} {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

/-- The expansion of a track of `J` has at least as many vertices as the track. -/
theorem length_le_expandTracks (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → p.length ≤ (expandTracks ι T p).length := by
  intro p
  induction p with
  | nil => intro _; simp
  | cons a t ih =>
    cases t with
    | nil => intro _; simp
    | cons b rest =>
      intro hch
      have hab : J.Adj a b := hch.rel_head
      have htail : List.IsChain J.Adj (b :: rest) := hch.tail
      have h1 : 1 ≤ ((T a b).dropLast).length := by
        rw [List.length_dropLast]
        have := two_le_track_length hS hab
        omega
      have := ih htail
      rw [expandTracks_cons_cons, List.length_append]
      simp only [List.length_cons] at this ⊢
      omega

/-- A vertex of the expansion is either an image of a vertex of the track, or an internal
vertex of the subdividing track of an *edge* of the track.  (This is the strengthening of
`SubdivisionCompose.mem_expandTracks` that names the edge.) -/
theorem mem_expandTracks_edge (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → ∀ w : W, w ∈ expandTracks ι T p →
      (∃ x ∈ p, w = ι x) ∨
      (∃ x y : U, s(x, y) ∈ trackEdges p ∧ J.Adj x y ∧ w ∈ trackInterior (T x y)) := by
  intro p
  induction p with
  | nil => intro _ w hw; simp at hw
  | cons x tail ih =>
    cases tail with
    | nil =>
      intro _ w hw
      rw [expandTracks_singleton] at hw
      exact Or.inl ⟨x, by simp, by simpa using hw⟩
    | cons y rest =>
      intro hch w hw
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      rw [expandTracks_cons_cons] at hw
      rcases List.mem_append.mp hw with hw | hw
      · have hwT : w ∈ T x y := List.dropLast_subset _ hw
        by_cases hint : w ∈ trackInterior (T x y)
        · exact Or.inr ⟨x, y, ⟨0, by simp, rfl⟩, hxy, hint⟩
        · rcases mem_ends_of_mem (track_head? hS hxy) (track_getLast? hS hxy) hwT hint with
            h | h
          · exact Or.inl ⟨x, by simp, h⟩
          · exact Or.inl ⟨y, by simp, h⟩
      · rcases ih htail w hw with ⟨z, hz, heq⟩ | ⟨z, z', he, hzz', hint⟩
        · exact Or.inl ⟨z, by simp [hz], heq⟩
        · refine Or.inr ⟨z, z', ?_, hzz', hint⟩
          obtain ⟨i, hi, hEq⟩ := he
          refine ⟨i + 1, by simp only [List.length_cons] at hi ⊢; omega, ?_⟩
          simp only [List.getElem_cons_succ]
          exact hEq

/-! ## The track of `H` from `v₁` to `v₂` off the branch -/

/-- PAPER, proof of 5.8 (4), printed p. 27: *"There is a cycle in `J` of length `≥ 4` using the
edge `v₁v₂`, and so there is a path in `L(H)` of length `≥ 2` from `A₁` to `A₂` with no
internal vertex in `N_{v₁} ∪ V(R_{v₁v₂}) ∪ N_{v₂}`."*

The path of `L(H)` is the rung of the track `Q` produced here: the rest of the cycle, expanded
through the subdivision.  *"Length `≥ 2`"* is `4 ≤ Q.length`, and *"no internal vertex in
`V(R_{v₁v₂})`"* is the disjointness of the edges of `Q` from the edges of the branch. -/
theorem exists_cross_track [Fintype W] [DecidableEq W] {J : SimpleGraph U} {H : SimpleGraph W}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {c₁ c₂ : W} {q : List W} (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂)
    (hq2 : 2 ≤ q.length) (hb₁ : c₁ ∈ branchVertices H) (hb₂ : c₂ ∈ branchVertices H) :
    ∃ Q : List W, 4 ≤ Q.length ∧ IsTrackFrom H Q c₁ c₂ ∧
      ∀ e ∈ trackEdges Q, e ∉ trackEdges q := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  obtain ⟨u₀, v₀, hu₀v₀, hEq0, hcase⟩ :=
    BranchClassification.exists_trackEdges_eq_and_ends hι htrack hlen hrev hdisj hnew hcover
      hedges hdeg hq hq2 hfrom hb₁ hb₂
  have hnorm : ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (T u v) ∧
      c₁ = ι u ∧ c₂ = ι v := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨u₀, v₀, hu₀v₀, hEq0, h1, h2⟩
    · refine ⟨v₀, u₀, hu₀v₀.symm, ?_, h1, h2⟩
      rw [hrev u₀ v₀ hu₀v₀, SubdivisionCounting.trackEdges_reverse]
      exact hEq0
  obtain ⟨u, v, huv, hEq, hc1, hc2⟩ := hnorm
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlen, hrev, hdisj, hnew⟩
  obtain ⟨p, hp4, hpfrom, hpedge⟩ := exists_long_track_off_edge hJ huv
  have hpch : List.IsChain J.Adj p := List.isChain_iff_getElem.mpr hpfrom.1.2.2
  have hQfrom : IsTrackFrom H (expandTracks ι T p) (ι u) (ι v) :=
    SubdivisionTrackExpansion.expandTracks_isTrackFrom hS hpfrom
  have hQ4 : 4 ≤ (expandTracks ι T p).length :=
    le_trans hp4 (length_le_expandTracks hS p hpch)
  have hQfrom' : IsTrackFrom H (expandTracks ι T p) c₁ c₂ := by rw [hc1, hc2]; exact hQfrom
  refine ⟨expandTracks ι T p, hQ4, hQfrom', ?_⟩
  -- no vertex of the expansion is internal to the branch
  have key : ∀ z ∈ expandTracks ι T p, z ∉ trackInterior (T u v) := by
    intro z hz hint
    rcases mem_expandTracks_edge hS p hpch z hz with ⟨x, hx, rfl⟩ | ⟨x, y, hxy, hadj, hzint⟩
    · exact hnew u v huv (ι x) hint ⟨x, rfl⟩
    · have hne : s(x, y) ≠ s(u, v) := fun hc => hpedge (hc ▸ hxy)
      exact hdisj x y u v hadj huv hne z hzint (mem_of_mem_trackInterior hint)
  have hTlen : 0 < (T u v).length := by
    have := hlen u v huv
    simp only [trackLength] at this
    omega
  have hhead : (T u v)[0]'hTlen = ι u :=
    SubdivisionCounting.track_head (htrack u v huv) hTlen
  have hlast : (T u v)[(T u v).length - 1]'(by omega) = ι v :=
    DegenerateK4Tracks.track_getLast (htrack u v huv) hTlen
  intro e heQ heq'
  rw [hEq] at heq'
  obtain ⟨i, hi, rfl⟩ := heq'
  have hmemQ := BranchClassification.mem_of_mem_trackEdges heQ
  have hends : ∀ j : ℕ, ∀ hj : j < (T u v).length,
      (T u v)[j]'hj ∈ expandTracks ι T p → (T u v)[j]'hj = ι u ∨ (T u v)[j]'hj = ι v := by
    intro j hj hjQ
    rcases DegenerateK4Tracks.mem_ends_of_notMem_interior (List.getElem_mem hj)
      (key _ hjQ) hTlen with h | h
    · exact Or.inl (h.trans hhead)
    · exact Or.inr (h.trans hlast)
  have hne : (T u v)[i]'(by omega) ≠ (T u v)[i + 1]'hi := by
    intro hc
    have := (htrack u v huv).1.2.1.getElem_inj_iff.mp hc
    omega
  have hi1 := hends i (by omega) hmemQ.1
  have hi2 := hends (i + 1) hi hmemQ.2
  have habs : s((T u v)[i]'(by omega), (T u v)[i + 1]'hi) = s(c₁, c₂) := by
    rw [hc1, hc2]
    rcases hi1 with h1 | h1 <;> rcases hi2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]
    · exact absurd (h1.trans h2.symm) hne
  exact ends_edge_not_mem hQfrom' (by omega) (habs ▸ heQ)

end Workspace.ProofLemmas.Thm58StarStarGapCross
