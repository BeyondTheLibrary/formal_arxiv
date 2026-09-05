import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism

/-!
# Splitting the rung of a track at an interior branch vertex

PAPER (proof of 7.5, claim (2), printed p. 37): *"There also correspond three tracks in `H′`,
yielding a prism in `L(H′)`."*

When the replaced branch shares the end `c₁` with the distinguished branch, the track of `H`
through the replaced branch begins with that whole branch and then continues.  Its rung is
therefore the rung of the branch followed by the rung of the continuation, and only the first
half changes under the rung replacement.  This module proves that splitting, and the small
list fact that the tail of a track is a track.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndSplit

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.Thm75Setup

variable {V W : Type*}

/-- The tail of a track is a track: dropping the first vertex keeps the second as the new
first end and leaves the other end where it was. -/
theorem isTrackFrom_tail {H : SimpleGraph W} {a b c : W} {rest : List W}
    (h : IsTrackFrom H (a :: c :: rest) a b) : IsTrackFrom H (c :: rest) c b := by
  refine ⟨⟨by simp, h.1.2.1.of_cons, ?_⟩, rfl, ?_⟩
  · intro i hi
    have h2 := h.1.2.2 (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
    simpa using h2
  · have := h.2.2
    rwa [List.getLast?_cons_cons] at this

/-- **The rung of a concatenated track splits.**

If the track `L` is the track `t` followed by the rest of a track `M` that starts where `t`
ends, then the rung of `L` is the rung of `t` followed by the rung of `M`. -/
theorem trackRung_append {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {t M' : List W} {c : W}
    (ht : IsTrackList H t) (hM : IsTrackList H (c :: M'))
    (hL : IsTrackList H (t ++ M')) (hjoin : t.getLast? = some c) :
    trackRung φ (t ++ M') hL = trackRung φ t ht ++ trackRung φ (c :: M') hM := by
  have hnpos : 0 < t.length := by
    rcases List.eq_nil_or_concat t with rfl | ⟨l, x, rfl⟩
    · simp at hjoin
    · simp
  have hlast : t[t.length - 1]'(by omega) = c := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hjoin
    exact Option.some_injective _ hjoin
  set n := t.length with hn
  have hlenL : (t ++ M').length = n + M'.length := by simp [hn]
  have hlenLHS : (trackRung φ (t ++ M') hL).length = n + M'.length - 1 := by
    rw [trackRung_length]; simp [trackLength, hlenL]
  have hlenRHS : (trackRung φ t ht ++ trackRung φ (c :: M') hM).length
      = (n - 1) + M'.length := by
    simp [trackLength, hn]
  refine List.ext_getElem (by rw [hlenLHS, hlenRHS]; omega) ?_
  intro i hi hi'
  rw [hlenLHS] at hi
  have hi1 : i + 1 < (t ++ M').length := by rw [hlenL]; omega
  have he : s((t ++ M')[i]'(by omega), (t ++ M')[i + 1]'hi1) ∈ H.edgeSet :=
    trackEdge_mem_edgeSet hL i hi1
  rw [trackRung_getElem φ (t ++ M') hL i (by rw [hlenLHS]; omega) hi1 he]
  rcases Nat.lt_or_ge i (n - 1) with hlt | hge
  · -- inside `t`
    have hL1 : (t ++ M')[i]'(by omega) = t[i]'(by omega) :=
      List.getElem_append_left (by omega)
    have hL2 : (t ++ M')[i + 1]'hi1 = t[i + 1]'(by omega) :=
      List.getElem_append_left (by omega)
    have hidx : i < (trackRung φ t ht).length := by
      rw [trackRung_length]
      simp only [trackLength]
      omega
    have he' : s(t[i]'(by omega), t[i + 1]'(by omega)) ∈ H.edgeSet :=
      trackEdge_mem_edgeSet ht i (by omega)
    have hRHS : (trackRung φ t ht ++ trackRung φ (c :: M') hM)[i]'hi'
        = (trackRung φ t ht)[i]'hidx := List.getElem_append_left hidx
    rw [hRHS, trackRung_getElem φ t ht i hidx (by omega) he']
    apply congrArg (fun y : H.edgeSet => (φ y : V))
    apply Subtype.ext
    simp only [hL1, hL2]
  · -- inside `M`
    obtain ⟨j, hij⟩ : ∃ j : ℕ, i = (n - 1) + j := ⟨i - (n - 1), by omega⟩
    have hlent : (trackRung φ t ht).length = n - 1 := by
      rw [trackRung_length]
      simp only [trackLength]
      omega
    have hjlt : j < M'.length := by omega
    have hidx : (trackRung φ t ht).length ≤ i := by rw [hlent]; omega
    have hMidx : j < (trackRung φ (c :: M') hM).length := by
      rw [trackRung_length]
      simp only [trackLength, List.length_cons]
      omega
    have hjM : j + 1 < (c :: M').length := by simp only [List.length_cons]; omega
    have he' : s((c :: M')[j]'(by omega), (c :: M')[j + 1]'hjM)
        ∈ H.edgeSet := trackEdge_mem_edgeSet hM j hjM
    have hRHS : (trackRung φ t ht ++ trackRung φ (c :: M') hM)[i]'hi'
        = (trackRung φ (c :: M') hM)[j]'hMidx := by
      rw [List.getElem_append_right hidx]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _
        (by omega) _ _
    rw [hRHS, trackRung_getElem φ (c :: M') hM j hMidx hjM he']
    have hA : (t ++ M')[i]'(by omega) = (c :: M')[j]'(by omega) := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hin : i = n - 1 := by omega
        have h1 : (t ++ M')[i]'(by omega) = t[i]'(by omega) :=
          List.getElem_append_left (by omega)
        rw [h1]
        have h2 : t[i]'(by omega) = t[t.length - 1]'(by omega) :=
          Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _
            (by omega) _ _
        rw [h2, hlast]
        exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
          (c :: M') (show 0 = j by omega) (by simp) (by omega)).symm ▸ rfl
      · have h1 : (t ++ M')[i]'(by omega) = M'[i - t.length]'(by omega) :=
          List.getElem_append_right (by omega)
        rw [h1]
        have h2 : (c :: M')[j]'(by omega) = M'[j - 1]'(by omega) := by
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
          simp
        rw [h2]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _
          (by omega) _ _
    have hB : (t ++ M')[i + 1]'hi1 = (c :: M')[j + 1]'hjM := by
      have h1 : (t ++ M')[i + 1]'hi1 = M'[i + 1 - t.length]'(by omega) :=
        List.getElem_append_right (by omega)
      rw [h1]
      have h2 : (c :: M')[j + 1]'hjM = M'[j]'(by omega) := by simp
      rw [h2]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _
        (by omega) _ _
    have hEq : s((t ++ M')[i]'(by omega), (t ++ M')[i + 1]'hi1)
        = s((c :: M')[j]'(by omega), (c :: M')[j + 1]'hjM) := by rw [hA, hB]
    exact congrArg (fun y : H.edgeSet => (φ y : V)) (Subtype.ext hEq)


/-- Rewriting a rung along an equality of the underlying tracks. -/
theorem trackRung_congr {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {l l' : List W}
    (h : IsTrackList H l) (h' : IsTrackList H l') (heq : l = l') :
    trackRung φ l h = trackRung φ l' h' := by
  subst heq; rfl

/-- **A rung meets the clique at one end of its track in exactly the first rung vertex.** -/
theorem mem_nset_trackRung_iff {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h2 : 2 ≤ q.length) :
    ∀ w ∈ trackRung φ q hq.1,
      (w ∈ NSet G H K φ a ↔ w = firstRungVertex φ q hq.1 h2) := by
  intro w hw
  obtain ⟨e, he, heq, hwe⟩ := (mem_trackRung_iff φ hq.1).mp hw
  constructor
  · rintro ⟨g, hg, hga, hwg⟩
    have hef : e = g := Thm75EndgameHelpers.phi_inj φ he hg (hwe ▸ hwg)
    have hae : a ∈ e := hef ▸ hga.2
    have hfst := edge_eq_firstTrackEdge hq h2 heq hae
    rw [hwe]
    simp only [firstRungVertex]
    exact congrArg (fun y : H.edgeSet => (φ y : V)) (Subtype.ext hfst)
  · rintro rfl
    exact ⟨firstTrackEdge q h2, firstTrackEdge_mem hq.1 h2,
      ⟨firstTrackEdge_mem hq.1 h2, firstTrackEdge_contains hq h2⟩, rfl⟩

/-- The mirror of `mem_nset_trackRung_iff` at the other end of the track. -/
theorem mem_nset_trackRung_iff_last {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h2 : 2 ≤ q.length) :
    ∀ w ∈ trackRung φ q hq.1,
      (w ∈ NSet G H K φ b ↔ w = lastRungVertex φ q hq.1 h2) := by
  intro w hw
  obtain ⟨e, he, heq, hwe⟩ := (mem_trackRung_iff φ hq.1).mp hw
  constructor
  · rintro ⟨g, hg, hgb, hwg⟩
    have hef : e = g := Thm75EndgameHelpers.phi_inj φ he hg (hwe ▸ hwg)
    have hbe : b ∈ e := hef ▸ hgb.2
    have hlst := edge_eq_lastTrackEdge hq h2 heq hbe
    rw [hwe]
    simp only [lastRungVertex]
    exact congrArg (fun y : H.edgeSet => (φ y : V)) (Subtype.ext hlst)
  · rintro rfl
    exact ⟨lastTrackEdge q h2, lastTrackEdge_mem hq.1 h2,
      ⟨lastTrackEdge_mem hq.1 h2, lastTrackEdge_contains hq h2⟩, rfl⟩

/-- If a vertex of `H` is off the track `q`, then the clique it names misses the rung of `q`. -/
theorem notMem_nset_of_notMem_track {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} (hq : IsTrackList H q) {a : W}
    (ha : a ∉ q) : ∀ w ∈ trackRung φ q hq, w ∉ NSet G H K φ a := by
  intro w hw hwN
  obtain ⟨e, he, heq, hwe⟩ := (mem_trackRung_iff φ hq).mp hw
  obtain ⟨g, hg, hga, hwg⟩ := hwN
  have hef : e = g := Thm75EndgameHelpers.phi_inj φ he hg (hwe ▸ hwg)
  have hae : a ∈ e := hef ▸ hga.2
  obtain ⟨i, hi, rfl⟩ := heq
  rcases Sym2.mem_iff.mp hae with h | h <;> rw [h] at ha <;> exact ha (List.getElem_mem _)

/-- Two tracks with no common edge have disjoint rungs. -/
theorem trackRung_disjoint {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q q' : List W}
    (hq : IsTrackList H q) (hq' : IsTrackList H q')
    (hdisj : ∀ e ∈ trackEdges q, e ∉ trackEdges q') :
    ∀ w ∈ trackRung φ q hq, w ∉ trackRung φ q' hq' := by
  intro w hw hw'
  obtain ⟨e, he, heq, hwe⟩ := (mem_trackRung_iff φ hq).mp hw
  obtain ⟨f, hf, hfq, hwf⟩ := (mem_trackRung_iff φ hq').mp hw'
  have hef : e = f := Thm75EndgameHelpers.phi_inj φ he hf (hwe ▸ hwf)
  exact hdisj e heq (hef ▸ hfq)

end Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndSplit
