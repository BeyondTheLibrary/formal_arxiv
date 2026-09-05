import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.NaturalAppearanceStripSystemCore

open Workspace.Types.Core
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.TrackToRungPath

variable {U W : Type*}

/-- Both ends of an edge belonging to a track occur on the track. -/
theorem endpoints_mem_of_mem_trackEdges {q : List W} {e : Sym2 W}
    (he : e ∈ trackEdges q) {z : W} (hz : z ∈ e) : z ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hz with h | h
  · rw [h]
    exact List.getElem_mem _
  · rw [h]
    exact List.getElem_mem _

/-- An edge at position `i` of a track is incident with the named first end exactly at
position zero. -/
theorem left_endpoint_mem_edge_iff {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (hlen : 1 ≤ trackLength q)
    (i : ℕ) (hi : i + 1 < q.length) :
    a ∈ s(q[i]'(by omega), q[i + 1]'hi) ↔ i = 0 := by
  have hpos : 0 < q.length := by
    simpa only [trackLength] using (show 0 < q.length from by omega)
  have hzero : q[0]'hpos = a := track_head hq hpos
  constructor
  · intro hmem
    rcases Sym2.mem_iff.mp hmem with h | h
    · have heq : q[i]'(by omega) = q[0]'hpos := h.symm.trans hzero.symm
      exact (hq.1.2.1.getElem_inj_iff).mp heq
    · have heq : q[i + 1]'hi = q[0]'hpos := h.symm.trans hzero.symm
      have : i + 1 = 0 := (hq.1.2.1.getElem_inj_iff).mp heq
      omega
  · rintro rfl
    rw [← hzero]
    exact Sym2.mem_mk_left _ _

/-- An edge at position `i` of a track is incident with the named last end exactly when it is
the final edge. -/
theorem right_endpoint_mem_edge_iff {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (hlen : 1 ≤ trackLength q)
    (i : ℕ) (hi : i + 1 < q.length) :
    b ∈ s(q[i]'(by omega), q[i + 1]'hi) ↔ i + 2 = q.length := by
  have hpos : 0 < q.length := by omega
  have hlast : q[q.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hq hpos
  constructor
  · intro hmem
    rcases Sym2.mem_iff.mp hmem with h | h
    · have heq : q[i]'(by omega) = q[q.length - 1]'(by omega) := h.symm.trans hlast.symm
      have hind : i = q.length - 1 := (hq.1.2.1.getElem_inj_iff).mp heq
      omega
    · have heq : q[i + 1]'hi = q[q.length - 1]'(by omega) := h.symm.trans hlast.symm
      have hind : i + 1 = q.length - 1 := (hq.1.2.1.getElem_inj_iff).mp heq
      omega
  · intro hind
    have heq : q[i + 1]'hi = q[q.length - 1]'(by omega) :=
      getElem_eq_of_index_eq q (by omega) _ _
    rw [← hlast, ← heq]
    exact Sym2.mem_mk_right _ _

/-- A branch vertex `ι u` which lies on one subdivision track is one of that track's named
ends. -/
theorem range_mem_track_iff_end
    {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hnew : ∀ u v : U, J.Adj u v → ∀ z ∈ trackInterior (T u v), z ∉ Set.range ι)
    {u p q : U} (hpq : J.Adj p q) (hmem : ι u ∈ T p q) : u = p ∨ u = q := by
  have hpos : 0 < (T p q).length := (htrack p q hpq).1.1 |> List.length_pos_of_ne_nil
  have hnint : ι u ∉ trackInterior (T p q) := fun hint =>
    hnew p q hpq (ι u) hint ⟨u, rfl⟩
  rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
      hmem hnint hpos with hleft | hright
  · left
    apply hι
    rw [hleft, track_head (htrack p q hpq) hpos]
  · right
    apply hι
    rw [hright, Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast
      (htrack p q hpq) hpos]

/-- Distinct subdividing tracks can meet only at the image of a common end of their original
edges. -/
theorem common_vertex_of_distinct_tracks
    {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hdisj : ∀ u v p q : U, J.Adj u v → J.Adj p q → s(u, v) ≠ s(p, q) →
      ∀ z ∈ trackInterior (T u v), z ∉ T p q)
    {u v p q : U} (huv : J.Adj u v) (hpq : J.Adj p q)
    (hne : s(u, v) ≠ s(p, q)) {z : W} (hzuv : z ∈ T u v) (hzpq : z ∈ T p q) :
    (u = p ∧ z = ι u) ∨ (u = q ∧ z = ι u) ∨
      (v = p ∧ z = ι v) ∨ (v = q ∧ z = ι v) := by
  have hposuv : 0 < (T u v).length :=
    List.length_pos_of_ne_nil (htrack u v huv).1.1
  have hpospq : 0 < (T p q).length :=
    List.length_pos_of_ne_nil (htrack p q hpq).1.1
  have hnintuv : z ∉ trackInterior (T u v) := fun hz =>
    hdisj u v p q huv hpq hne z hz hzpq
  have hnintpq : z ∉ trackInterior (T p q) := fun hz =>
    hdisj p q u v hpq huv (Ne.symm hne) z hz hzuv
  rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
      hzuv hnintuv hposuv with hzU | hzV <;>
    rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
      hzpq hnintpq hpospq with hzP | hzQ
  · left
    have hzu : z = ι u := hzU.trans (track_head (htrack u v huv) hposuv)
    have hzp : z = ι p := hzP.trans (track_head (htrack p q hpq) hpospq)
    exact ⟨hι (hzu.symm.trans hzp), hzu⟩
  · right; left
    have hzu : z = ι u := hzU.trans (track_head (htrack u v huv) hposuv)
    have hzq : z = ι q := hzQ.trans
      (Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (htrack p q hpq) hpospq)
    exact ⟨hι (hzu.symm.trans hzq), hzu⟩
  · right; right; left
    have hzv : z = ι v := hzV.trans
      (Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (htrack u v huv) hposuv)
    have hzp : z = ι p := hzP.trans (track_head (htrack p q hpq) hpospq)
    exact ⟨hι (hzv.symm.trans hzp), hzv⟩
  · right; right; right
    have hzv : z = ι v := hzV.trans
      (Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (htrack u v huv) hposuv)
    have hzq : z = ι q := hzQ.trans
      (Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (htrack p q hpq) hpospq)
    exact ⟨hι (hzv.symm.trans hzq), hzv⟩

/-- The consecutive edges of one subdivision track, transported through a line-graph
appearance, form the natural rung.  Its only vertices in the two incident-edge sets are its
first and last vertices. -/
theorem trackRung_isUVRung
    {V : Type*} {G : SimpleGraph V} {J : SimpleGraph U} {H : SimpleGraph W} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K) (iota : U → W) (T : U → U → List W)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (iota u) (iota v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (S : U → U → Set V) (N : U → Set V) {u v : U} (huv : J.Adj u v)
    (hS : ∀ z : V,
      z ∈ S u v ↔ z ∈ trackRung phi (T u v) (htrack u v huv).1)
    (hN : ∀ (r : U) (z : V),
      z ∈ N r ↔ ∃ e : H.edgeSet, iota r ∈ e.1 ∧ z = (phi e : V)) :
    IsUVRung G J S N u v (trackRung phi (T u v) (htrack u v huv).1) := by
  obtain ⟨s, t, hpath⟩ :=
    trackRung_exists_isPathFrom phi (T u v) (htrack u v huv).1 (hlen u v huv)
  refine ⟨huv, s, t, hpath, ?_, ?_, ?_⟩
  · intro x hx
    exact (hS x).2 hx
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have hjT : j + 1 < (T u v).length := by
      rw [trackRung_length] at hj
      simp only [trackLength] at hj
      omega
    have hedge : s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) ∈ H.edgeSet :=
      trackEdge_mem_edgeSet (htrack u v huv).1 j hjT
    have hvalue :
        (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
          (phi ⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : V) :=
      trackRung_getElem phi (T u v) (htrack u v huv).1 j hj hjT hedge
    have hRpos : 0 < (trackRung phi (T u v) (htrack u v huv).1).length := by
      rw [trackRung_length]
      exact hlen u v huv
    have hRzero :
        (trackRung phi (T u v) (htrack u v huv).1)[0]'hRpos = s :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hpath.2.1 hRpos
    constructor
    · intro hxN
      rw [hN] at hxN
      obtain ⟨e, heu, heval⟩ := hxN
      have heq : e =
          (⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : H.edgeSet) := by
        apply phi.injective
        apply Subtype.ext
        exact heval.symm.trans hvalue
      have hinc : iota u ∈
          s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) := by
        change iota u ∈ e.1 at heu
        rw [heq] at heu
        exact heu
      have hjzero : j = 0 :=
        (left_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mp hinc
      have hget :
          (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
            (trackRung phi (T u v) (htrack u v huv).1)[0]'hRpos :=
        getElem_eq_of_index_eq _ hjzero _ _
      exact hget.trans hRzero
    · intro hxs
      rw [hN]
      have hget :
          (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
            (trackRung phi (T u v) (htrack u v huv).1)[0]'hRpos :=
        hxs.trans hRzero.symm
      have hjzero : j = 0 := (hpath.1.2.1.getElem_inj_iff).mp hget
      exact ⟨⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩,
        (left_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mpr hjzero,
        hvalue⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have hjT : j + 1 < (T u v).length := by
      rw [trackRung_length] at hj
      simp only [trackLength] at hj
      omega
    have hedge : s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) ∈ H.edgeSet :=
      trackEdge_mem_edgeSet (htrack u v huv).1 j hjT
    have hvalue :
        (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
          (phi ⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : V) :=
      trackRung_getElem phi (T u v) (htrack u v huv).1 j hj hjT hedge
    have hRpos : 0 < (trackRung phi (T u v) (htrack u v huv).1).length := by
      rw [trackRung_length]
      exact hlen u v huv
    have hRlast :
        (trackRung phi (T u v) (htrack u v huv).1)[
          (trackRung phi (T u v) (htrack u v huv).1).length - 1]'(by omega) = t :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hpath.2.2 hRpos
    constructor
    · intro hxN
      rw [hN] at hxN
      obtain ⟨e, hev, heval⟩ := hxN
      have heq : e =
          (⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : H.edgeSet) := by
        apply phi.injective
        apply Subtype.ext
        exact heval.symm.trans hvalue
      have hinc : iota v ∈
          s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) := by
        change iota v ∈ e.1 at hev
        rw [heq] at hev
        exact hev
      have hjlastT : j + 2 = (T u v).length :=
        (right_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mp hinc
      have hjlastR : j =
          (trackRung phi (T u v) (htrack u v huv).1).length - 1 := by
        rw [trackRung_length]
        simp only [trackLength]
        omega
      have hget :
          (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
            (trackRung phi (T u v) (htrack u v huv).1)[
              (trackRung phi (T u v) (htrack u v huv).1).length - 1]'(by omega) :=
        getElem_eq_of_index_eq _ hjlastR _ _
      exact hget.trans hRlast
    · intro hxt
      rw [hN]
      have hget :
          (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
            (trackRung phi (T u v) (htrack u v huv).1)[
              (trackRung phi (T u v) (htrack u v huv).1).length - 1]'(by omega) :=
        hxt.trans hRlast.symm
      have hjlastR : j =
          (trackRung phi (T u v) (htrack u v huv).1).length - 1 :=
        (hpath.1.2.1.getElem_inj_iff).mp hget
      have hjlastT : j + 2 = (T u v).length := by
        rw [trackRung_length, trackLength] at hjlastR
        omega
      exact ⟨⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩,
        (right_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mpr hjlastT,
        hvalue⟩

end Workspace.ProofLemmas.NaturalAppearanceStripSystemCore
