import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61EvenClaims
-- extra imports needed by the proof only
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.Statements.S02.Thm_2_2

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim9

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61EvenClaims
set_option maxHeartbeats 1600000
open Workspace.ProofLemmas


private theorem geq {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i]'hi = l[j]'hj := by subst h; rfl

private theorem edge_subtype_congr {W : Type*} {H : SimpleGraph W} {e f : Sym2 W}
    (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) (h : e = f) :
    (⟨e, he⟩ : ↥H.edgeSet) = ⟨f, hf⟩ := Subtype.ext h

/-- **2.2, applied to the path `L(T)` of a track `T` of `H`.**

PAPER (proof of 6.1(9), printed p. 32): *"The path `L(P)` of `G` is odd and has length `≥ 3`;
its ends are `Y'`-complete, and its internal vertices are not.  By 2.2, `f` is adjacent (in `G`)
to vertices in the interior of `L(P)`; that is, `f` is incident in `H` with an internal vertex
of `P`."* -/
private theorem two_two_track
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    (Y' : Set V) (hY'anti : AnticonnectedSet G Y')
    (hY'K : ∀ y ∈ Y', y ∉ K)
    (T : List (Fin n)) (hT : IsTrackList H T) (h5 : 5 ≤ T.length)
    (hpar : T.length % 2 = 1)
    (h0 : s(T[0]'(by omega), T[1]'(by omega)) ∈ completeEdges G H K φ Y')
    (hlast : s(T[T.length - 2]'(by omega), T[T.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y')
    (hint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < T.length,
      s(T[i]'(by omega), T[i + 1]'(by omega)) ∉ completeEdges G H K φ Y')
    (g : Sym2 (Fin n)) (hg : g ∈ completeEdges G H K φ Y') :
    ∃ i : ℕ, 1 ≤ i ∧ ∃ _hi : i + 2 < T.length,
      MeetEdges g s(T[i]'(by omega), T[i + 1]'(by omega)) := by
  classical
  set p : List V := TrackToRungPath.trackRung φ T hT with hpdef
  have hlen : p.length = T.length - 1 := by
    simp [hpdef, TrackToRungPath.trackRung_length, trackLength]
  have hplen : 4 ≤ p.length := by omega
  have hval : ∀ (i : ℕ) (hi : i < p.length) (hi' : i + 1 < T.length)
      (he : s(T[i]'(by omega), T[i + 1]'hi') ∈ H.edgeSet),
      p[i]'hi = (φ ⟨s(T[i]'(by omega), T[i + 1]'hi'), he⟩ : V) := by
    intro i hi hi' he
    exact TrackToRungPath.trackRung_getElem φ T hT i hi hi' he
  have hpath : IsPathList G p := TrackToRungPath.trackRung_isPathList φ T hT (by
    simp only [trackLength]; omega)
  have hpfrom : IsPathFrom G p (p[0]'(by omega)) (p[p.length - 1]'(by omega)) := by
    refine ⟨hpath, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < p.length by omega)]
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (show p.length - 1 < p.length by
        omega)]
  -- membership of `p` in `K`
  have hpK : ∀ x ∈ p, x ∈ K := TrackToRungPath.trackRung_subset_K φ T hT
  -- the ends of `p` are `Y'`-complete
  have hend0 : VertexComplete G (p[0]'(by omega)) Y' := by
    obtain ⟨he, hc⟩ := h0
    rw [hval 0 (by omega) (by omega) he]
    exact hc
  have hendl : VertexComplete G (p[p.length - 1]'(by omega)) Y' := by
    obtain ⟨he, hc⟩ := hlast
    have hek : s(T[p.length - 1]'(show p.length - 1 < T.length by omega),
        T[p.length - 1 + 1]'(show p.length - 1 + 1 < T.length by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hT (p.length - 1) (by omega)
    have hEq : s(T[p.length - 1]'(show p.length - 1 < T.length by omega),
        T[p.length - 1 + 1]'(show p.length - 1 + 1 < T.length by omega))
        = s(T[T.length - 2]'(show T.length - 2 < T.length by omega),
            T[T.length - 1]'(show T.length - 1 < T.length by omega)) := by
      rw [geq T (show p.length - 1 = T.length - 2 by omega)
        (show p.length - 1 < T.length by omega) (show T.length - 2 < T.length by omega),
        geq T (show p.length - 1 + 1 = T.length - 1 by omega)
        (show p.length - 1 + 1 < T.length by omega) (show T.length - 1 < T.length by omega)]
    rw [hval (p.length - 1) (by omega) (by omega) hek, edge_subtype_congr hek he hEq]
    exact hc
  -- internal vertices of `p` are not `Y'`-complete
  have hnotc : ∀ (i : ℕ) (hi : i < p.length), 1 ≤ i → i + 1 < p.length →
      ¬ VertexComplete G (p[i]'hi) Y' := by
    intro i hi hi1 hi2 hcon
    refine hint i hi1 (by omega) ⟨TrackToRungPath.trackEdge_mem_edgeSet hT i (by omega), ?_⟩
    rw [hval i hi (by omega) (TrackToRungPath.trackEdge_mem_edgeSet hT i (by omega))] at hcon
    exact hcon
  -- no vertex of `p` lies in `Y'`
  have hpY : ∀ w ∈ p, w ∉ Y' := by
    intro w hw hwY
    exact hY'K w hwY (hpK w hw)
  -- no edge of `p` is `Y'`-complete
  have hnoedge : ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G Y' u v := by
    rintro ⟨u, hu, v, hv, hadj, hcu, hcv⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    have hcons := (PathBasics.path_adj_iff hpath hi hj).mp hadj
    rcases hcons with h | h
    · -- j = i + 1
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact hnotc j hj (by omega) (by omega) hcv
      · exact hnotc i hi hipos (by omega) hcu
    · -- i = j + 1
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact hnotc i hi (by omega) (by omega) hcu
      · exact hnotc j hj hjpos (by omega) hcv
  -- `L(T)` is odd
  have hoddp : Odd (pathLength p) := by
    rw [pathLength, hlen]
    exact Nat.odd_iff.mpr (by omega)
  -- the vertex of `g`
  obtain ⟨hge, hgc⟩ := hg
  have hgK : (φ ⟨g, hge⟩ : V) ∈ K := (φ ⟨g, hge⟩).2
  obtain ⟨w, hwint, hwadj⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hG Y' hY'anti p (p[0]'(by omega))
      (p[p.length - 1]'(by omega)) hpfrom hpY hoddp hend0 hendl hnoedge
      (↑(φ ⟨g, hge⟩) : V) hgc
  -- `w` is an internal vertex of `p`: extract its index
  rw [PathBasics.mem_interior_iff_of_pathFrom hpfrom] at hwint
  obtain ⟨hwp, hw0, hwl⟩ := hwint
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hwp
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hw0 rfl
  have hkl : k ≠ p.length - 1 := by
    rintro rfl; exact hwl rfl
  refine ⟨k, by omega, by omega, ?_⟩
  -- adjacency in `G` transfers to adjacency in `L(H)`, i.e. the two edges meet
  intro hdisj
  have hek : s(T[k]'(show k < T.length by omega), T[k + 1]'(show k + 1 < T.length by omega))
      ∈ H.edgeSet := TrackToRungPath.trackEdge_mem_edgeSet hT k (by omega)
  rw [hval k hk (by omega) hek] at hwadj
  have hlg : H.lineGraph.Adj ⟨g, hge⟩ ⟨_, hek⟩ := φ.map_adj_iff.mp hwadj
  obtain ⟨-, z, hz₁, hz₂⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
  exact hdisj z ⟨hz₁, hz₂⟩

/-! ### The two shapes of contradiction the printed proof uses -/

section Shapes

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}

/-- Indices of a `Nodup` list are determined by their entries. -/
private theorem idx_eq {P : List (Fin n)} (hnd : P.Nodup) {i j : ℕ} (hi : i < P.length)
    (hj : j < P.length) (h : P[i]'hi = P[j]'hj) : i = j := hnd.getElem_inj_iff.mp h

/-- Two edges of a track meet only when their indices are within one of each other. -/
private theorem meet_indices {P : List (Fin n)} (hnd : P.Nodup) {i j : ℕ}
    (hi : i + 1 < P.length) (hj : j + 1 < P.length)
    (hmeet : MeetEdges (s(P[i]'(by omega), P[i + 1]'hi)) (s(P[j]'(by omega), P[j + 1]'hj))) :
    j ≤ i + 1 ∧ i ≤ j + 1 := by
  by_contra hcon
  refine hmeet ?_
  intro w ⟨hw1, hw2⟩
  have h1 : w = P[i]'(by omega) ∨ w = P[i + 1]'hi := by simpa using hw1
  have h2 : w = P[j]'(by omega) ∨ w = P[j + 1]'hj := by simpa using hw2
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · have := idx_eq hnd (by omega) (by omega) h2; omega
  · have := idx_eq hnd (by omega) (by omega) h2; omega
  · have := idx_eq hnd (by omega) (by omega) h2; omega
  · have := idx_eq hnd (by omega) (by omega) h2; omega

/-- **The contradiction 2.2 delivers**: a `Y''`-complete edge with no neighbour in the interior
of the odd path `L(T)`. -/
private theorem far_edge_contra (hG : Berge G)
    (Y'' : Set V) (hanti : AnticonnectedSet G Y'') (hYK : ∀ y ∈ Y'', y ∉ K)
    (T : List (Fin n)) (hT : IsTrackList H T) (h5 : 5 ≤ T.length)
    (hpar : T.length % 2 = 1)
    (h0 : s(T[0]'(by omega), T[1]'(by omega)) ∈ completeEdges G H K φ Y'')
    (hl : s(T[T.length - 2]'(by omega), T[T.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y'')
    (hint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < T.length,
      s(T[i]'(by omega), T[i + 1]'(by omega)) ∉ completeEdges G H K φ Y'')
    (g : Sym2 (Fin n)) (hg : g ∈ completeEdges G H K φ Y'')
    (hfar : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < T.length,
      ¬ MeetEdges g (s(T[i]'(by omega), T[i + 1]'(by omega)))) : False := by
  obtain ⟨i, hi1, hi2, hmeet⟩ :=
    two_two_track G hG φ Y'' hanti hYK T hT h5 hpar h0 hl hint g hg
  exact hfar i hi1 hi2 hmeet

/-- **The prefix-jump contradiction.**

PAPER (proof of 6.1(9), printed p. 32): *"Hence the track `T` with edge-set
`{h₁, …, h_{i-1}, f}` has even length, at least 4 …; and yet in `G` the `Y'`-complete vertex
`h_{n-1}` has no neighbour in the interior of the odd path `L(T)`, contrary to 2.2."*

Used twice: once with `z = pⱼ` (both ends of `f` on `P`), and once with `z` the end of `f` off
`P` (the paragraph *"In `G`, `h₁-⋯-h_{i-1}-f` is a path; … so by 2.2, this path is even"*). -/
private theorem prefix_jump_contra (hG : Berge G)
    (Y2 : Set V) (hanti : AnticonnectedSet G Y2) (hYK : ∀ y ∈ Y2, y ∉ K)
    (P : List (Fin n)) (hP : IsTrackList H P) (hPlen : 5 ≤ P.length)
    (he0 : s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y2)
    (hel : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y2)
    (hint : ∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 < P.length,
      s(P[m]'(by omega), P[m + 1]'(by omega)) ∉ completeEdges G H K φ Y2)
    (a : ℕ) (ha3 : 3 ≤ a) (haodd : a % 2 = 1) (haP : a + 3 ≤ P.length)
    (z : Fin n) (hadj : H.Adj (P[a]'(by omega)) z)
    (hz : ∀ k : ℕ, ∀ _hk : k < P.length, k ≤ a → P[k]'(by omega) ≠ z)
    (hfz : s(P[a]'(by omega), z) ∈ completeEdges G H K φ Y2) : False := by
  classical
  have hnd : P.Nodup := hP.2.1
  have hslen : (TrackSlice.slice P 0 a).length = a + 1 := by
    have := TrackSlice.length_slice P (show a < P.length by omega) (Nat.zero_le a)
    omega
  have hsget : ∀ (k : ℕ) (hk : k < (TrackSlice.slice P 0 a).length) (hk' : k < P.length),
      (TrackSlice.slice P 0 a)[k]'hk = P[k]'hk' := by
    intro k hk hk'
    rw [TrackSlice.getElem_slice P hk (show 0 + k < P.length by omega)]
    exact geq P (by omega) _ _
  have hsfrom : IsTrackFrom H (TrackSlice.slice P 0 a) (P[0]'(by omega)) (P[a]'(by omega)) :=
    TrackSlice.isTrackFrom_slice hP (show a < P.length by omega) (Nat.zero_le a)
  have hznot : z ∉ TrackSlice.slice P 0 a := by
    intro hzs
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hzs
    exact hz k (by omega) (by omega) ((hsget k hk (by omega)).symm.trans hkz)
  have hTfrom : IsTrackFrom H (TrackSlice.slice P 0 a ++ [z]) (P[0]'(by omega)) z :=
    TrackSlice.isTrackFrom_concat hsfrom hadj hznot
  have hTlen : (TrackSlice.slice P 0 a ++ [z]).length = a + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hslen]
  have hTget : ∀ (k : ℕ) (hk : k < (TrackSlice.slice P 0 a ++ [z]).length)
      (hk' : k < P.length), k ≤ a → (TrackSlice.slice P 0 a ++ [z])[k]'hk = P[k]'hk' := by
    intro k hk hk' hka
    rw [List.getElem_append_left (show k < (TrackSlice.slice P 0 a).length by omega)]
    exact hsget k (by omega) hk'
  have hTlast : (TrackSlice.slice P 0 a ++ [z])[a + 1]'(by omega) = z := by
    rw [List.getElem_append_right (show (TrackSlice.slice P 0 a).length ≤ a + 1 by omega)]
    simp only [hslen]
    norm_num
  refine far_edge_contra hG Y2 hanti hYK (TrackSlice.slice P 0 a ++ [z]) hTfrom.1
    (by omega) (by omega) ?_ ?_ ?_
    (s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))) hel ?_
  · rw [hTget 0 (by omega) (by omega) (by omega), hTget 1 (by omega) (by omega) (by omega)]
    exact he0
  · rw [geq (TrackSlice.slice P 0 a ++ [z])
        (show (TrackSlice.slice P 0 a ++ [z]).length - 2 = a by omega) (by omega) (by omega),
      geq (TrackSlice.slice P 0 a ++ [z])
        (show (TrackSlice.slice P 0 a ++ [z]).length - 1 = a + 1 by omega) (by omega) (by omega),
      hTget a (by omega) (by omega) (by omega), hTlast]
    exact hfz
  · intro m hm1 hm2
    rw [hTget m (by omega) (by omega) (by omega),
      hTget (m + 1) (by omega) (by omega) (by omega)]
    exact hint m hm1 (by omega)
  · intro m hm1 hm2 hmeet
    rw [hTget m (by omega) (by omega) (by omega),
      hTget (m + 1) (by omega) (by omega) (by omega)] at hmeet
    have hmeet' : MeetEdges (s(P[P.length - 2]'(by omega), P[(P.length - 2) + 1]'(by omega)))
        (s(P[m]'(by omega), P[m + 1]'(by omega))) := by
      rw [geq P (show (P.length - 2) + 1 = P.length - 1 by omega)
        (show (P.length - 2) + 1 < P.length by omega) (show P.length - 1 < P.length by omega)]
      exact hmeet
    have := meet_indices hnd (show P.length - 2 + 1 < P.length by omega)
      (show m + 1 < P.length by omega) hmeet'
    omega

/-! ### *"from the symmetry we may assume …"*: reversing the track -/

private theorem rev_get (P : List (Fin n)) {k : ℕ} (h : k < P.reverse.length)
    (h' : P.length - 1 - k < P.length) : P.reverse[k]'h = P[P.length - 1 - k]'h' := by
  simp [List.getElem_reverse]

/-- Reversing a track preserves the whole hypothesis package of (9). -/
private theorem rev_pkg (Y2 : Set V)
    (P : List (Fin n)) (hP : IsTrackList H P) (hPlen : 5 ≤ P.length)
    (he0 : s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y2)
    (hel : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y2)
    (hint : ∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 < P.length,
      s(P[m]'(by omega), P[m + 1]'(by omega)) ∉ completeEdges G H K φ Y2) :
    IsTrackList H P.reverse ∧ 5 ≤ P.reverse.length ∧
      s(P.reverse[0]'(by simp only [List.length_reverse]; omega),
        P.reverse[1]'(by simp only [List.length_reverse]; omega))
        ∈ completeEdges G H K φ Y2 ∧
      s(P.reverse[P.reverse.length - 2]'(by simp only [List.length_reverse]; omega),
        P.reverse[P.reverse.length - 1]'(by simp only [List.length_reverse]; omega))
        ∈ completeEdges G H K φ Y2 ∧
      (∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 < P.reverse.length,
        s(P.reverse[m]'(by omega), P.reverse[m + 1]'(by omega))
          ∉ completeEdges G H K φ Y2) := by
  have hrlen : P.reverse.length = P.length := by simp
  refine ⟨TrackSlice.isTrackList_reverse hP, by omega, ?_, ?_, ?_⟩
  · rw [rev_get P (by simp only [List.length_reverse]; omega) (show P.length - 1 - 0 < P.length by
      omega), rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - 1 < P.length by omega),
      geq P (show P.length - 1 - 0 = P.length - 1 by omega) (by omega) (by omega),
      geq P (show P.length - 1 - 1 = P.length - 2 by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact hel
  · rw [rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (P.reverse.length - 2) < P.length by omega),
      rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (P.reverse.length - 1) < P.length by omega),
      geq P (show P.length - 1 - (P.reverse.length - 2) = 1 by omega) (by omega) (by omega),
      geq P (show P.length - 1 - (P.reverse.length - 1) = 0 by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact he0
  · intro m hm1 hm2
    rw [rev_get P (by omega) (show P.length - 1 - m < P.length by omega),
      rev_get P (by omega) (show P.length - 1 - (m + 1) < P.length by omega),
      geq P (show P.length - 1 - (m + 1) = P.length - 2 - m by omega) (by omega) (by omega),
      geq P (show P.length - 1 - m = (P.length - 2 - m) + 1 by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact hint (P.length - 2 - m) (by omega) (by omega)

/-- **The suffix-jump contradiction** — `prefix_jump_contra` read on the reversed track. -/
private theorem suffix_jump_contra (hG : Berge G)
    (Y2 : Set V) (hanti : AnticonnectedSet G Y2) (hYK : ∀ y ∈ Y2, y ∉ K)
    (P : List (Fin n)) (hP : IsTrackList H P) (hPlen : 5 ≤ P.length)
    (he0 : s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y2)
    (hel : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y2)
    (hint : ∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 < P.length,
      s(P[m]'(by omega), P[m + 1]'(by omega)) ∉ completeEdges G H K φ Y2)
    (b : ℕ) (hb : b + 4 ≤ P.length) (hb2 : 2 ≤ b)
    (hbodd : (P.length - 1 - b) % 2 = 1)
    (z : Fin n) (hadj : H.Adj (P[b]'(by omega)) z)
    (hz : ∀ k : ℕ, ∀ _hk : k < P.length, b ≤ k → P[k]'(by omega) ≠ z)
    (hfz : s(P[b]'(by omega), z) ∈ completeEdges G H K φ Y2) : False := by
  have hrlen : P.reverse.length = P.length := by simp
  obtain ⟨hRT, hRlen, hRe0, hRel, hRint⟩ := rev_pkg Y2 P hP hPlen he0 hel hint
  have hRb : P.reverse[P.length - 1 - b]'(by simp only [List.length_reverse]; omega)
      = P[b]'(by omega) := by
    rw [rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (P.length - 1 - b) < P.length by omega)]
    exact geq P (by omega) _ _
  refine prefix_jump_contra hG Y2 hanti hYK P.reverse hRT hRlen hRe0 hRel hRint
    (P.length - 1 - b) (by omega) hbodd (by omega) z ?_ ?_ ?_
  · rw [hRb]; exact hadj
  · intro k hk hka
    rw [rev_get P hk (show P.length - 1 - k < P.length by omega)]
    exact hz (P.length - 1 - k) (by omega) (by simp only [List.length_reverse] at hk; omega)
  · rw [hRb]; exact hfz

/-! ### The sub-track contradiction

PAPER (proof of 6.1(9), printed p. 32): *"In `G`, the path `h₁-⋯-h_{i-1}` is odd; its ends are
`Y`-complete, its internal vertices are not, and the `Y`-complete vertex `h_{n-1}` has no
neighbour in its interior, so it has length 1, that is, `i = 3`.  Similarly `n - i = 2`."*
(Read with `Y' = Y \ {y₁}` resp. `Y \ {y₂}`, since the far end of the path lies in `X₁` resp.
`X₂`.) -/

private theorem prefix_sub_contra (hG : Berge G)
    (Y2 : Set V) (hanti : AnticonnectedSet G Y2) (hYK : ∀ y ∈ Y2, y ∉ K)
    (P : List (Fin n)) (hP : IsTrackList H P)
    (a : ℕ) (ha4 : 4 ≤ a) (haeven : a % 2 = 0) (haP : a + 1 ≤ P.length)
    (he0 : s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y2)
    (hea : s(P[a - 1]'(by omega), P[a]'(by omega)) ∈ completeEdges G H K φ Y2)
    (hint : ∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 ≤ a,
      s(P[m]'(by omega), P[m + 1]'(by omega)) ∉ completeEdges G H K φ Y2)
    (g : Sym2 (Fin n)) (hg : g ∈ completeEdges G H K φ Y2)
    (hfar : ∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 ≤ a,
      ¬ MeetEdges g (s(P[m]'(by omega), P[m + 1]'(by omega)))) : False := by
  have hslen : (TrackSlice.slice P 0 a).length = a + 1 := by
    have := TrackSlice.length_slice P (show a < P.length by omega) (Nat.zero_le a)
    omega
  have hsget : ∀ (k : ℕ) (hk : k < (TrackSlice.slice P 0 a).length) (hk' : k < P.length),
      (TrackSlice.slice P 0 a)[k]'hk = P[k]'hk' := by
    intro k hk hk'
    rw [TrackSlice.getElem_slice P hk (show 0 + k < P.length by omega)]
    exact geq P (by omega) _ _
  have hsfrom : IsTrackFrom H (TrackSlice.slice P 0 a) (P[0]'(by omega)) (P[a]'(by omega)) :=
    TrackSlice.isTrackFrom_slice hP (show a < P.length by omega) (Nat.zero_le a)
  refine far_edge_contra hG Y2 hanti hYK (TrackSlice.slice P 0 a) hsfrom.1
    (by omega) (by omega) ?_ ?_ ?_ g hg ?_
  · rw [hsget 0 (by omega) (by omega), hsget 1 (by omega) (by omega)]
    exact he0
  · rw [geq (TrackSlice.slice P 0 a) (show (TrackSlice.slice P 0 a).length - 2 = a - 1 by omega)
      (by omega) (by omega),
      geq (TrackSlice.slice P 0 a) (show (TrackSlice.slice P 0 a).length - 1 = a by omega)
      (by omega) (by omega),
      hsget (a - 1) (by omega) (by omega), hsget a (by omega) (by omega)]
    exact hea
  · intro m hm1 hm2
    rw [hsget m (by omega) (by omega), hsget (m + 1) (by omega) (by omega)]
    exact hint m hm1 (by omega)
  · intro m hm1 hm2
    rw [hsget m (by omega) (by omega), hsget (m + 1) (by omega) (by omega)]
    exact hfar m hm1 (by omega)

private theorem suffix_sub_contra (hG : Berge G)
    (Y2 : Set V) (hanti : AnticonnectedSet G Y2) (hYK : ∀ y ∈ Y2, y ∉ K)
    (P : List (Fin n)) (hP : IsTrackList H P)
    (b : ℕ) (hb4 : b + 5 ≤ P.length) (hbeven : (P.length - 1 - b) % 2 = 0)
    (hel : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y2)
    (heb : s(P[b]'(by omega), P[b + 1]'(by omega)) ∈ completeEdges G H K φ Y2)
    (hint : ∀ m : ℕ, b + 1 ≤ m → ∀ _hm : m + 2 < P.length,
      s(P[m]'(by omega), P[m + 1]'(by omega)) ∉ completeEdges G H K φ Y2)
    (g : Sym2 (Fin n)) (hg : g ∈ completeEdges G H K φ Y2)
    (hfar : ∀ m : ℕ, b + 1 ≤ m → ∀ _hm : m + 2 < P.length,
      ¬ MeetEdges g (s(P[m]'(by omega), P[m + 1]'(by omega)))) : False := by
  have hrlen : P.reverse.length = P.length := by simp
  refine prefix_sub_contra hG Y2 hanti hYK P.reverse (TrackSlice.isTrackList_reverse hP)
    (P.length - 1 - b) (by omega) hbeven (by omega) ?_ ?_ ?_ g hg ?_
  · rw [rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - 0 < P.length by omega),
      rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - 1 < P.length by omega),
      geq P (show P.length - 1 - 0 = P.length - 1 by omega) (by omega) (by omega),
      geq P (show P.length - 1 - 1 = P.length - 2 by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact hel
  · rw [rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (P.length - 1 - b - 1) < P.length by omega),
      rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (P.length - 1 - b) < P.length by omega),
      geq P (show P.length - 1 - (P.length - 1 - b - 1) = b + 1 by omega) (by omega) (by omega),
      geq P (show P.length - 1 - (P.length - 1 - b) = b by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact heb
  · intro m hm1 hm2
    rw [rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - m < P.length by omega),
      rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (m + 1) < P.length by omega),
      geq P (show P.length - 1 - (m + 1) = P.length - 2 - m by omega) (by omega) (by omega),
      geq P (show P.length - 1 - m = (P.length - 2 - m) + 1 by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact hint (P.length - 2 - m) (by omega) (by omega)
  · intro m hm1 hm2
    rw [rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - m < P.length by omega),
      rev_get P (by simp only [List.length_reverse]; omega)
      (show P.length - 1 - (m + 1) < P.length by omega),
      geq P (show P.length - 1 - (m + 1) = P.length - 2 - m by omega) (by omega) (by omega),
      geq P (show P.length - 1 - m = (P.length - 2 - m) + 1 by omega) (by omega) (by omega),
      Sym2.eq_swap]
    exact hfar (P.length - 2 - m) (by omega) (by omega)

/-! ### Bookkeeping around `X`, `X₁`, `X₂` -/

/-- `Z ⊆ Y` makes every `Y`-complete edge `Z`-complete. -/
private theorem CE_mono (Z Y : Set V) (hZ : Z ⊆ Y) :
    completeEdges G H K φ Y ⊆ completeEdges G H K φ Z := by
  rintro e ⟨he, hc⟩
  exact ⟨he, fun x hx => hc x (hZ hx)⟩

/-- *"So `X ∪ Xᵢ` is the set of all `Y \ {yᵢ}`-complete vertices in `L(H)`"* (printed p. 29). -/
private theorem CE_diff_eq (Y : Set V) (y : V) :
    completeEdges G H K φ (Y \ {y})
      = completeEdges G H K φ Y ∪ extraEdges G H K φ Y y := by
  rw [extraEdges, Set.union_diff_self]
  exact (Set.union_eq_self_of_subset_left (CE_mono (Y \ {y}) Y Set.diff_subset)).symm

/-- Deleting an *end* of an antipath leaves an antipath (printed p. 29, *"`Y \ {yᵢ}` is
anticonnected"*). -/
private theorem anticonnected_diff_head {Y : Set V} {Q : List V} {u : V}
    (hp : IsPathList Gᶜ Q) (hhead : Q.head? = some u) (hlen : 1 < Q.length)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) : AnticonnectedSet G (Y \ {u}) := by
  have hset : {z : V | z ∈ Q.drop 1} = Y \ {u} := by
    obtain ⟨t, rfl⟩ : ∃ t : List V, Q = u :: t := by
      cases Q with
      | nil => simp at hhead
      | cons a t => exact ⟨t, by simp at hhead; rw [hhead]⟩
    have hnd := hp.2.1
    have hut : u ∉ t := by simpa using (List.nodup_cons.mp hnd).1
    ext z
    simp only [List.drop_succ_cons, List.drop_zero, Set.mem_setOf_eq, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨(hQY z).mp (List.mem_cons_of_mem _ hz), fun h => hut (h ▸ hz)⟩
    · rintro ⟨hzY, hzu⟩
      rcases List.mem_cons.mp ((hQY z).mpr hzY) with h | h
      · exact absurd h hzu
      · exact h
  have := InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (G := Gᶜ) (PathBasics.isPathList_drop hp (k := 1) hlen)
  rw [hset] at this
  exact this

/-- Three distinct neighbours make a branch-vertex. -/
private theorem branchVertex_of_three {v a b c : Fin n} (ha : H.Adj v a) (hb : H.Adj v b)
    (hc : H.Adj v c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : v ∈ branchVertices H := by
  have hsub : ({a, b, c} : Set (Fin n)) ⊆ H.neighborSet v := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard : ({a, b, c} : Set (Fin n)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]),
      Set.ncard_insert_of_notMem (by simp [hbc]), Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  simpa [branchVertices, hcard] using hcard ▸ this

/-- A four-vertex induced path, from its six adjacency facts. -/
private theorem isPathList_quad {W : Type*} {D : SimpleGraph W} {a b c d : W}
    (hab : D.Adj a b) (hbc : D.Adj b c) (hcd : D.Adj c d)
    (hac : ¬ D.Adj a c) (had : ¬ D.Adj a d) (hbd : ¬ D.Adj b d)
    (hnd : [a, b, c, d].Nodup) : IsPathList D [a, b, c, d] := by
  refine ⟨by simp, hnd, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  have hca : ¬ D.Adj c a := fun h => hac h.symm
  have hda : ¬ D.Adj d a := fun h => had h.symm
  have hdb : ¬ D.Adj d b := fun h => hbd h.symm
  interval_cases i <;> interval_cases j <;>
    simp [hab, hbc, hcd, hac, had, hbd, hca, hda, hdb, hab.symm, hbc.symm, hcd.symm]

/-! ### *"so it has length 1, that is, `i = 3`.  Similarly `n - i = 2`"* -/

/-- **The endgame of the printed proof of (9)**, in the labelling `h_{i-1} ∈ X₁`, `hᵢ ∈ X₂`. -/
private theorem endgame_contra (hG : Berge G)
    (Y : Set V) (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : ∀ h₁ h₂ : Sym2 (Fin n), h₁ ∈ extraEdges G H K φ Y y₁ →
      h₂ ∈ extraEdges G H K φ Y y₂ → MeetEdges h₁ h₂)
    (P : List (Fin n)) (hP : IsTrackList H P) (hPlen : 5 ≤ P.length)
    (hpar : P.length % 2 = 1)
    (he0 : s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y)
    (hel : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))
      ∈ completeEdges G H K φ Y)
    (hint : ∀ m : ℕ, 1 ≤ m → ∀ _hm : m + 2 < P.length,
      s(P[m]'(by omega), P[m + 1]'(by omega)) ∉ completeEdges G H K φ Y)
    (c : ℕ) (hc2 : 2 ≤ c) (hcP : c + 3 ≤ P.length) (hceven : c % 2 = 0)
    (hem : s(P[c - 1]'(by omega), P[c]'(by omega)) ∈ extraEdges G H K φ Y y₁)
    (hep : s(P[c]'(by omega), P[c + 1]'(by omega)) ∈ extraEdges G H K φ Y y₂) : False := by
  classical
  have hnd : P.Nodup := hP.2.1
  -- `y₁, y₂ ∈ Y`, and `Y \ {yᵢ}` is anticonnected
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp (List.mem_of_mem_getLast? hQ.2.2)
  have hQlen : 1 < Q.length := by
    by_contra hcon
    have h1 : Q.length = 1 := by
      rcases Nat.eq_zero_or_pos Q.length with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hQ.1.1
      · omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    have h₁ : y₁ ∈ Q := List.mem_of_mem_head? hQ.2.1
    have h₂ : y₂ ∈ Q := List.mem_of_mem_getLast? hQ.2.2
    rw [ha] at h₁ h₂
    exact hy ((List.eq_of_mem_singleton h₁).trans (List.eq_of_mem_singleton h₂).symm)
  have hanti₁ : AnticonnectedSet G (Y \ {y₁}) :=
    anticonnected_diff_head hQ.1 hQ.2.1 hQlen hQY
  have hanti₂ : AnticonnectedSet G (Y \ {y₂}) := by
    refine anticonnected_diff_head (Q := Q.reverse) (PathBasics.isPathList_reverse hQ.1) ?_ ?_ ?_
    · rw [List.head?_reverse]; exact hQ.2.2
    · simpa using hQlen
    · intro v; rw [List.mem_reverse]; exact hQY v
  have hYK : ∀ y ∈ Y, y ∉ K := fun y hy => (hYmajor y hy).1
  have hYK₁ : ∀ y ∈ Y \ {y₁}, y ∉ K := fun y hy => hYK y hy.1
  have hYK₂ : ∀ y ∈ Y \ {y₂}, y ∉ K := fun y hy => hYK y hy.1
  -- *"so it has length 1, that is, `i = 3`"*
  have hc : c = 2 := by
    by_contra hne
    have hc4 : 4 ≤ c := by omega
    refine prefix_sub_contra hG (Y \ {y₁}) hanti₁ hYK₁ P hP c hc4 hceven (by omega)
      (CE_mono _ _ Set.diff_subset he0) ?_ ?_
      (s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega)))
      (CE_mono _ _ Set.diff_subset hel) ?_
    · rw [CE_diff_eq]; exact Or.inr hem
    · intro m hm1 hm2
      rw [CE_diff_eq]
      rintro (h | h)
      · exact hint m hm1 (by omega) h
      · have hmeet := h8 _ _ h hep
        have := meet_indices hnd (show m + 1 < P.length by omega)
          (show c + 1 < P.length by omega) hmeet
        omega
    · intro m hm1 hm2 hmeet
      have hmeet' : MeetEdges (s(P[P.length - 2]'(by omega), P[(P.length - 2) + 1]'(by omega)))
          (s(P[m]'(by omega), P[m + 1]'(by omega))) := by
        rw [geq P (show (P.length - 2) + 1 = P.length - 1 by omega)
          (show (P.length - 2) + 1 < P.length by omega) (show P.length - 1 < P.length by omega)]
        exact hmeet
      have := meet_indices hnd (show P.length - 2 + 1 < P.length by omega)
        (show m + 1 < P.length by omega) hmeet'
      omega
  -- *"Similarly `n - i = 2`, that is, `n = 5`"*
  have hlen5 : P.length = 5 := by
    by_contra hne
    have hbig : c + 5 ≤ P.length := by omega
    refine suffix_sub_contra hG (Y \ {y₂}) hanti₂ hYK₂ P hP c hbig (by omega)
      (CE_mono _ _ Set.diff_subset hel) ?_ ?_
      (s(P[0]'(by omega), P[1]'(by omega))) (CE_mono _ _ Set.diff_subset he0) ?_
    · rw [CE_diff_eq]; exact Or.inr hep
    · intro m hm1 hm2
      rw [CE_diff_eq]
      rintro (h | h)
      · exact hint m (by omega) (by omega) h
      · have hmeet := h8 _ _ hem h
        have hmeet' : MeetEdges (s(P[c - 1]'(by omega), P[(c - 1) + 1]'(by omega)))
            (s(P[m]'(by omega), P[m + 1]'(by omega))) := by
          rw [geq P (show (c - 1) + 1 = c by omega) (show (c - 1) + 1 < P.length by omega)
            (show c < P.length by omega)]
          exact hmeet
        have := meet_indices hnd (show c - 1 + 1 < P.length by omega)
          (show m + 1 < P.length by omega) hmeet'
        omega
    · intro m hm1 hm2 hmeet
      have hmeet' : MeetEdges (s(P[0]'(by omega), P[0 + 1]'(by omega)))
          (s(P[m]'(by omega), P[m + 1]'(by omega))) := hmeet
      have := meet_indices hnd (show 0 + 1 < P.length by omega)
        (show m + 1 < P.length by omega) hmeet'
      omega
  -- *"But then `Q` can be completed to an odd antihole via `y₂-h₃-h₁-h₄-h₂-y₁`, a
  -- contradiction."*  With `n = 5` and `i = 3` the four edges of `P` are
  -- `h₁ = p₁p₂ ∈ X`, `h₂ = p₂p₃ ∈ X₁`, `h₃ = p₃p₄ ∈ X₂`, `h₄ = p₄p₅ ∈ X`.
  have E0 : s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y := he0
  have E1 : s(P[1]'(by omega), P[2]'(by omega)) ∈ extraEdges G H K φ Y y₁ := by
    rw [geq P (show (1 : ℕ) = c - 1 by omega) (by omega) (by omega),
      geq P (show (2 : ℕ) = c by omega) (by omega) (by omega)]
    exact hem
  have E2 : s(P[2]'(by omega), P[3]'(by omega)) ∈ extraEdges G H K φ Y y₂ := by
    rw [geq P (show (2 : ℕ) = c by omega) (by omega) (by omega),
      geq P (show (3 : ℕ) = c + 1 by omega) (by omega) (by omega)]
    exact hep
  have E3 : s(P[3]'(by omega), P[4]'(by omega)) ∈ completeEdges G H K φ Y := by
    rw [geq P (show (3 : ℕ) = P.length - 2 by omega) (by omega) (by omega),
      geq P (show (4 : ℕ) = P.length - 1 by omega) (by omega) (by omega)]
    exact hel
  obtain ⟨he0e, hcp0⟩ := E0
  obtain ⟨⟨he1e, hcp1⟩, hn1⟩ := E1
  obtain ⟨⟨he2e, hcp2⟩, hn2⟩ := E2
  obtain ⟨he3e, hcp3⟩ := E3
  -- generic transfer facts between `H` and `L(H) ⊆ G`
  have hzK : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), (↑(φ ⟨e, he⟩) : V) ∈ K :=
    fun e he => (φ ⟨e, he⟩).2
  have hdisjE : ∀ (i j : ℕ) (hi : i + 1 < P.length) (hj : j + 1 < P.length), i + 1 < j →
      DisjointEdges (s(P[i]'(by omega), P[i + 1]'hi)) (s(P[j]'(by omega), P[j + 1]'hj)) := by
    intro i j hi hj hij w hw
    obtain ⟨hw1, hw2⟩ := hw
    have h1 : w = P[i]'(by omega) ∨ w = P[i + 1]'hi := by simpa using hw1
    have h2 : w = P[j]'(by omega) ∨ w = P[j + 1]'hj := by simpa using hw2
    rcases h1 with rfl | rfl <;> rcases h2 with h | h <;>
      (have := idx_eq hnd (by omega) (by omega) h; omega)
  have hneE : ∀ (i j : ℕ) (hi : i + 1 < P.length) (hj : j + 1 < P.length), i ≠ j →
      s(P[i]'(by omega), P[i + 1]'hi) ≠ s(P[j]'(by omega), P[j + 1]'hj) := by
    intro i j hi hj hij hcon
    rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hij (idx_eq hnd (by omega) (by omega) h1)
    · have k1 := idx_eq hnd (show i < P.length by omega) (show j + 1 < P.length by omega) h1
      have k2 := idx_eq hnd (show i + 1 < P.length by omega) (show j < P.length by omega) h2
      omega
  have hGadj : ∀ (e f : Sym2 (Fin n)) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) (w : Fin n),
      e ≠ f → w ∈ e → w ∈ f →
      G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) := by
    intro e f he hf w hne hwe hwf
    refine φ.map_adj_iff.mpr ?_
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨fun hcon => hne (congrArg Subtype.val hcon), w, hwe, hwf⟩
  have hGnadj : ∀ (e f : Sym2 (Fin n)) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet),
      DisjointEdges e f → ¬ G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) := by
    intro e f he hf hdisj hcon
    obtain ⟨-, w, hw1, hw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_adj_iff.mp hcon)
    exact hdisj w ⟨hw1, hw2⟩
  have hzneq : ∀ (e f : Sym2 (Fin n)) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet), e ≠ f →
      (↑(φ ⟨e, he⟩) : V) ≠ (↑(φ ⟨f, hf⟩) : V) := by
    intro e f he hf hne hcon
    exact hne (congrArg Subtype.val (φ.toEquiv.injective (Subtype.ext hcon)))
  -- the four vertices of `L(H)`
  set z0 : V := (↑(φ ⟨s(P[0]'(by omega), P[1]'(by omega)), he0e⟩) : V) with hz0def
  set z1 : V := (↑(φ ⟨s(P[1]'(by omega), P[2]'(by omega)), he1e⟩) : V) with hz1def
  set z2 : V := (↑(φ ⟨s(P[2]'(by omega), P[3]'(by omega)), he2e⟩) : V) with hz2def
  set z3 : V := (↑(φ ⟨s(P[3]'(by omega), P[4]'(by omega)), he3e⟩) : V) with hz3def
  have hz0K : z0 ∈ K := hzK _ he0e
  have hz1K : z1 ∈ K := hzK _ he1e
  have hz2K : z2 ∈ K := hzK _ he2e
  have hz3K : z3 ∈ K := hzK _ he3e
  -- the three `G`-edges among them
  have hA23 : G.Adj z2 z3 :=
    hGadj _ _ he2e he3e (P[3]'(by omega)) (hneE 2 3 (by omega) (by omega) (by omega))
      (by simp) (by simp)
  have hA21 : G.Adj z2 z1 :=
    hGadj _ _ he2e he1e (P[2]'(by omega)) (hneE 2 1 (by omega) (by omega) (by omega))
      (by simp) (by simp)
  have hA01 : G.Adj z0 z1 :=
    hGadj _ _ he0e he1e (P[1]'(by omega)) (hneE 0 1 (by omega) (by omega) (by omega))
      (by simp) (by simp)
  -- and the three non-edges
  have hN20 : ¬ G.Adj z2 z0 :=
    hGnadj _ _ he2e he0e (fun w hw => hdisjE 0 2 (by omega) (by omega) (by omega) w ⟨hw.2, hw.1⟩)
  have hN03 : ¬ G.Adj z0 z3 :=
    hGnadj _ _ he0e he3e (hdisjE 0 3 (by omega) (by omega) (by omega))
  have hN31 : ¬ G.Adj z3 z1 :=
    hGnadj _ _ he3e he1e (fun w hw => hdisjE 1 3 (by omega) (by omega) (by omega) w ⟨hw.2, hw.1⟩)
  have hD20 : z2 ≠ z0 := hzneq _ _ he2e he0e (hneE 2 0 (by omega) (by omega) (by omega))
  have hD23 : z2 ≠ z3 := hzneq _ _ he2e he3e (hneE 2 3 (by omega) (by omega) (by omega))
  have hD21 : z2 ≠ z1 := hzneq _ _ he2e he1e (hneE 2 1 (by omega) (by omega) (by omega))
  have hD03 : z0 ≠ z3 := hzneq _ _ he0e he3e (hneE 0 3 (by omega) (by omega) (by omega))
  have hD01 : z0 ≠ z1 := hzneq _ _ he0e he1e (hneE 0 1 (by omega) (by omega) (by omega))
  have hD31 : z3 ≠ z1 := hzneq _ _ he3e he1e (hneE 3 1 (by omega) (by omega) (by omega))
  -- `y₂-h₃-h₁-h₄-h₂-y₁`: the four-vertex antipath `h₃-h₁-h₄-h₂`
  have hRpath : IsPathFrom Gᶜ [z2, z0, z3, z1] z2 z1 := by
    refine ⟨isPathList_quad ((G.compl_adj _ _).mpr ⟨hD20, hN20⟩)
      ((G.compl_adj _ _).mpr ⟨hD03, hN03⟩) ((G.compl_adj _ _).mpr ⟨hD31, hN31⟩)
      (fun h => ((G.compl_adj _ _).mp h).2 hA23)
      (fun h => ((G.compl_adj _ _).mp h).2 hA21)
      (fun h => ((G.compl_adj _ _).mp h).2 hA01) ?_, rfl, rfl⟩
    simp [hD20, hD23, hD21, hD03, hD01, hD31]
  -- `h₂ ∈ X₁` misses exactly `y₁`, and `h₃ ∈ X₂` misses exactly `y₂`
  have hn1' : ¬ G.Adj z1 y₁ := by
    intro hcon
    refine hn1 ⟨he1e, ?_⟩
    intro x hx
    by_cases hxy : x = y₁
    · exact hxy ▸ hcon
    · exact hcp1 x ⟨hx, by simpa using hxy⟩
  have hn2' : ¬ G.Adj z2 y₂ := by
    intro hcon
    refine hn2 ⟨he2e, ?_⟩
    intro x hx
    by_cases hxy : x = y₂
    · exact hxy ▸ hcon
    · exact hcp2 x ⟨hx, by simpa using hxy⟩
  -- `Q` misses the four vertices, which lie in `K`
  have hdisjQ : ∀ x ∈ Q, x ∉ [z2, z0, z3, z1] := by
    intro x hx hmem
    have hxK : x ∉ K := hYK x ((hQY x).mp hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hxK hz2K
    · exact hxK hz0K
    · exact hxK hz3K
    · exact hxK hz1K
  have hcross : ∀ x ∈ Q, ∀ y ∈ [z2, z0, z3, z1],
      (Gᶜ.Adj x y ↔ (x = y₂ ∧ y = z2) ∨ (x = y₁ ∧ y = z1)) := by
    intro x hx y hy
    have hxY : x ∈ Y := (hQY x).mp hx
    have hxK : x ∉ K := hYK x hxY
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · by_cases hxy : x = y₂
      · subst hxy
        exact iff_of_true ((G.compl_adj _ _).mpr ⟨fun h => hxK (h ▸ hz2K), fun h => hn2' h.symm⟩)
          (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon => hcon.2 (hcp2 x ⟨hxY, by simpa using hxy⟩).symm) ?_
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hxy h
        · exact hD21 h
    · refine iff_of_false (fun hcon => hcon.2 (hcp0 x hxY).symm) ?_
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact hD20 h.symm
      · exact hD01 h
    · refine iff_of_false (fun hcon => hcon.2 (hcp3 x hxY).symm) ?_
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact hD23 h.symm
      · exact hD31 h
    · by_cases hxy : x = y₁
      · subst hxy
        exact iff_of_true ((G.compl_adj _ _).mpr ⟨fun h => hxK (h ▸ hz1K), fun h => hn1' h.symm⟩)
          (Or.inr ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon => hcon.2 (hcp1 x ⟨hxY, by simpa using hxy⟩).symm) ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hD21 h.symm
        · exact hxy h
  have hhole : IsHoleList Gᶜ (Q ++ [z2, z0, z3, z1]) :=
    PathGlue.glue_hole hQ hRpath hdisjQ hcross (by simp)
  have heven := hG.2 _ hhole
  simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at heven
  rw [Nat.even_iff] at heven
  have hple : Even (pathLength Q) := hQeven
  rw [pathLength, Nat.even_iff] at hple
  omega

private theorem sym2_mem_split {W : Type*} (a : W) (e : Sym2 W) : a ∈ e → ∃ b, e = s(a, b) := by
  induction e using Sym2.ind with
  | _ u v =>
    intro h
    rcases Sym2.mem_iff.mp h with rfl | rfl
    · exact ⟨v, rfl⟩
    · exact ⟨u, Sym2.eq_swap⟩

end Shapes

/-- **6.1(9)** *"For all `W ∈ {X, X ∪ X₁, X ∪ X₂}` and for every even track `P` in `H` of
length `≥ 4` and with both end-edges and no internal edges in `W`, every edge in `W` is
incident with a penultimate vertex of `P`."* -/
theorem thm_6_1_claim9
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) :
    Claim9 G H K φ Y y₁ y₂ := by
  classical
  intro Y' hY'cases P hP hlen heven he0 hel hint f hf
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hb1, hbl⟩ := hcon
  have hnd : P.Nodup := hP.2.1
  have hpar : P.length % 2 = 1 := by
    rw [trackLength, Nat.even_iff] at heven
    omega
  -- the standing facts about `Y`
  have hYK : ∀ y ∈ Y, y ∉ K := fun y hy' => (hYmajor y hy').1
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp (List.mem_of_mem_getLast? hQ.2.2)
  have hQlen : 1 < Q.length := by
    by_contra hcon'
    have h1 : Q.length = 1 := by
      rcases Nat.eq_zero_or_pos Q.length with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hQ.1.1
      · omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    have k₁ : y₁ ∈ Q := List.mem_of_mem_head? hQ.2.1
    have k₂ : y₂ ∈ Q := List.mem_of_mem_getLast? hQ.2.2
    rw [ha] at k₁ k₂
    exact hy ((List.eq_of_mem_singleton k₁).trans (List.eq_of_mem_singleton k₂).symm)
  have hanti₁ : AnticonnectedSet G (Y \ {y₁}) :=
    anticonnected_diff_head hQ.1 hQ.2.1 hQlen hQY
  have hanti₂ : AnticonnectedSet G (Y \ {y₂}) := by
    refine anticonnected_diff_head (Q := Q.reverse) (PathBasics.isPathList_reverse hQ.1) ?_ ?_ ?_
    · rw [List.head?_reverse]; exact hQ.2.2
    · simpa using hQlen
    · intro v; rw [List.mem_reverse]; exact hQY v
  have hY'sub : Y' ⊆ Y := by
    rcases hY'cases with rfl | rfl | rfl
    · exact subset_rfl
    · exact Set.diff_subset
    · exact Set.diff_subset
  have hY'anti : AnticonnectedSet G Y' := by
    rcases hY'cases with rfl | rfl | rfl
    · exact hYanti
    · exact hanti₁
    · exact hanti₂
  have hY'K : ∀ y ∈ Y', y ∉ K := fun y hy' => hYK y (hY'sub hy')
  -- *"By 2.2, `f` is adjacent (in `G`) to vertices in the interior of `L(P)`; that is, `f` is
  -- incident in `H` with an internal vertex of `P`."*
  obtain ⟨k, hk1, hk2, hmeet⟩ :=
    two_two_track G hG φ Y' hY'anti hY'K P hP hlen hpar he0 hel hint f hf
  obtain ⟨w, hwf, hwe⟩ : ∃ w : Fin n, w ∈ f ∧
      w ∈ s(P[k]'(by omega), P[k + 1]'(by omega)) := by
    by_contra hcon'
    exact hmeet (fun w hw => hcon' ⟨w, hw⟩)
  obtain ⟨c, hclt, hc1, hc2, hcf⟩ : ∃ c : ℕ, ∃ hclt : c < P.length,
      1 ≤ c ∧ c + 2 ≤ P.length ∧ P[c]'hclt ∈ f := by
    have h2 : w = P[k]'(by omega) ∨ w = P[k + 1]'(by omega) := by simpa using hwe
    rcases h2 with rfl | rfl
    · exact ⟨k, by omega, hk1, by omega, hwf⟩
    · exact ⟨k + 1, by omega, by omega, by omega, hwf⟩
  -- the two forbidden indices
  have hcne1 : c ≠ 1 := by
    rintro rfl
    exact hb1 hcf
  have hcnel : c ≠ P.length - 2 := by
    rintro rfl
    exact hbl hcf
  have hcrange : 2 ≤ c ∧ c + 3 ≤ P.length := by omega
  -- *"`f` is incident with a (unique, unless both ends lie on `P`) vertex `pᵢ`"*
  obtain ⟨z, hfz⟩ := sym2_mem_split (P[c]'hclt) f hcf
  have hfcopy := hf
  obtain ⟨hfe, -⟩ := hfcopy
  have hfe' : s(P[c]'hclt, z) ∈ H.edgeSet := by rw [← hfz]; exact hfe
  have hadjz : H.Adj (P[c]'hclt) z := (SimpleGraph.mem_edgeSet H).mp hfe'
  have hfCE : s(P[c]'hclt, z) ∈ completeEdges G H K φ Y' := by rw [← hfz]; exact hf
  -- the bipartite 2-colouring of `H`
  obtain ⟨col⟩ := hsub.2
  have hcol : ∀ (i : ℕ) (hi : i < P.length) (h0 : 0 < P.length),
      ((col (P[i]'hi) : ℕ) + i) % 2 = ((col (P[0]'h0) : ℕ)) % 2 :=
    DegenerateK4Tracks.track_color col hP
  -- *"Suppose first that both ends of `f` belong to `P`."*
  have keyA : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length), i < j →
      i ≠ 1 → j ≠ 1 → i ≠ P.length - 2 → j ≠ P.length - 2 →
      f = s(P[i]'hi, P[j]'hj) → False := by
    intro i j hi hj hij hi1 hj1 hi2 hj2 hfij
    have hadjij : H.Adj (P[i]'hi) (P[j]'hj) := by
      refine (SimpleGraph.mem_edgeSet H).mp ?_
      rw [← hfij]; exact hfe
    -- *"Since `H` is bipartite, `j - i` is odd"*
    have hcolne : (col (P[i]'hi) : ℕ) ≠ (col (P[j]'hj) : ℕ) := fun h =>
      col.valid hadjij (Fin.val_injective h)
    have hci := hcol i hi (by omega)
    have hcj := hcol j hj (by omega)
    have hi2' := (col (P[i]'hi)).isLt
    have hj2' := (col (P[j]'hj)).isLt
    have hparij : (j - i) % 2 = 1 := by omega
    -- exactly one of `i` and `P.length - 1 - j` is odd
    have hsplit : i % 2 = 1 ∨ (P.length - 1 - j) % 2 = 1 := by omega
    rcases hsplit with hodd | hodd
    · -- *"the track `T` with edge-set `{h₁, …, h_{i-1}, f}`"*
      refine prefix_jump_contra hG Y' hY'anti hY'K P hP hlen he0 hel hint i (by omega) hodd
        (by omega) (P[j]'hj) hadjij ?_ ?_
      · intro k' hk' hk'i hcon'
        have := idx_eq hnd hk' hj hcon'
        omega
      · rw [← hfij]; exact hf
    · -- the mirror image of the same track
      refine suffix_jump_contra hG Y' hY'anti hY'K P hP hlen he0 hel hint j (by omega)
        (by omega) hodd (P[i]'hi) hadjij.symm ?_ ?_
      · intro k' hk' hk'j hcon'
        have := idx_eq hnd hk' hi hcon'
        omega
      · rw [Sym2.eq_swap, ← hfij]; exact hf
  by_cases hzP : z ∈ P
  · -- both ends of `f` lie on `P`
    obtain ⟨d, hd, hdz⟩ := List.mem_iff_getElem.mp hzP
    have hdc : d ≠ c := by
      rintro rfl
      exact H.irrefl (hdz ▸ hadjz)
    have hd1 : d ≠ 1 := by
      rintro rfl
      refine hb1 ?_
      rw [hfz, hdz]
      simp
    have hd2 : d ≠ P.length - 2 := by
      rintro rfl
      refine hbl ?_
      rw [hfz, hdz]
      simp
    rcases Nat.lt_or_ge c d with hlt | hge
    · exact keyA c d hclt hd hlt hcne1 hd1 hcnel hd2 (by rw [hfz, hdz])
    · exact keyA d c hd hclt (by omega) hd1 hcne1 hd2 hcnel
        (by rw [hfz, hdz, Sym2.eq_swap])
  · -- *"So not both ends of `f` belong to `P`.  Hence `f` is incident with a unique vertex
    -- `pᵢ` of `P`."*
    have hzne : ∀ (k' : ℕ) (hk' : k' < P.length), P[k']'hk' ≠ z := by
      intro k' hk' hcon'
      exact hzP (hcon' ▸ List.getElem_mem hk')
    -- *"so by 2.2, this path is even, that is, `i` is odd"* — in `0`-indexing, `c` is even
    have hceven : c % 2 = 0 := by
      by_contra hodd
      refine prefix_jump_contra hG Y' hY'anti hY'K P hP hlen he0 hel hint c (by omega)
        (by omega) (by omega) z hadjz (fun k' hk' _ => hzne k' hk') hfCE
    -- *"Since `pᵢ` is a branch-vertex of `H`, and at least two of the edges incident with it
    -- do not belong to `W`, it follows that `W = X` and `Y' = Y`."*
    have hem0 : s(P[c - 1]'(by omega), P[(c - 1) + 1]'(by omega))
        ∉ completeEdges G H K φ Y' := hint (c - 1) (by omega) (by omega)
    have hep0 : s(P[c]'hclt, P[c + 1]'(by omega)) ∉ completeEdges G H K φ Y' :=
      hint c (by omega) (by omega)
    have hem1 : s(P[c - 1]'(by omega), P[c]'hclt) ∉ completeEdges G H K φ Y' := by
      rw [geq P (show c = (c - 1) + 1 by omega) hclt (show (c - 1) + 1 < P.length by omega)]
      exact hem0
    have hadjm : H.Adj (P[c - 1]'(by omega)) (P[c]'hclt) := by
      have := hP.2.2 (c - 1) (show (c - 1) + 1 < P.length by omega)
      rwa [geq P (show (c - 1) + 1 = c by omega) (show (c - 1) + 1 < P.length by omega) hclt]
        at this
    have hadjp : H.Adj (P[c]'hclt) (P[c + 1]'(by omega)) := hP.2.2 c (by omega)
    have hbranch : (P[c]'hclt) ∈ branchVertices H :=
      branchVertex_of_three hadjm.symm hadjp hadjz
        (fun h => by have := idx_eq hnd (show c - 1 < P.length by omega)
                       (show c + 1 < P.length by omega) h; omega)
        (fun h => hzne (c - 1) (by omega) h)
        (fun h => hzne (c + 1) (by omega) h)
    have hIm : s(P[c - 1]'(by omega), P[c]'hclt) ∈ incidentEdges H (P[c]'hclt) :=
      ⟨(SimpleGraph.mem_edgeSet H).mpr hadjm, by simp⟩
    have hIp : s(P[c]'hclt, P[c + 1]'(by omega)) ∈ incidentEdges H (P[c]'hclt) :=
      ⟨(SimpleGraph.mem_edgeSet H).mpr hadjp, by simp⟩
    have hEne : s(P[c - 1]'(by omega), P[c]'hclt) ≠ s(P[c]'hclt, P[c + 1]'(by omega)) := by
      intro hcon'
      rcases Sym2.eq_iff.mp hcon' with ⟨h1, -⟩ | ⟨h1, -⟩
      · have := idx_eq hnd (show c - 1 < P.length by omega) hclt h1; omega
      · have := idx_eq hnd (show c - 1 < P.length by omega)
          (show c + 1 < P.length by omega) h1
        omega
    have hY'eq : Y' = Y := by
      have hsat : ∀ y : V, y ∈ Y → Y' = Y \ {y} → False := by
        intro y hyY hY'y
        have hss : Y \ {y} ⊂ Y := Set.diff_singleton_ssubset.mpr hyY
        have hantiy : AnticonnectedSet G (Y \ {y}) := by rw [← hY'y]; exact hY'anti
        have hsatY' : SaturatesLineGraph H (completeEdges G H K φ Y') := by
          rw [hY'y]; exact hmin _ hss hantiy
        exact hEne (hsatY' _ hbranch ⟨hIm, hem1⟩ ⟨hIp, hep0⟩)
      rcases hY'cases with h | h | h
      · exact h
      · exact absurd h (fun hh => hsat y₁ hy₁Y hh)
      · exact absurd h (fun hh => hsat y₂ hy₂Y hh)
    rw [hY'eq] at he0 hel hint hem1 hep0 hfCE hY'anti hY'K
    -- *"we may assume that `h_{i-1} ∈ X₁` and `hᵢ ∈ X₂`"*
    have hgetX : ∀ y : V, y ∈ Y → AnticonnectedSet G (Y \ {y}) →
        s(P[c - 1]'(by omega), P[c]'hclt) ∈ extraEdges G H K φ Y y ∨
        s(P[c]'hclt, P[c + 1]'(by omega)) ∈ extraEdges G H K φ Y y := by
      intro y hyY hantiy
      have hss : Y \ {y} ⊂ Y := Set.diff_singleton_ssubset.mpr hyY
      by_contra hcon'
      rw [not_or] at hcon'
      obtain ⟨hm', hp'⟩ := hcon'
      have hsat := hmin _ hss hantiy
      refine hEne (hsat _ hbranch ⟨hIm, ?_⟩ ⟨hIp, ?_⟩)
      · intro hmem; exact hm' ⟨hmem, hem1⟩
      · intro hmem; exact hp' ⟨hmem, hep0⟩
    have hdisj₁₂ : Disjoint (extraEdges G H K φ Y y₁) (extraEdges G H K φ Y y₂) := by
      obtain ⟨-, -, -, -, -, hd, -, -⟩ :=
        Thm61Setup.X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
      exact hd
    have hsplit :
        (s(P[c - 1]'(by omega), P[c]'hclt) ∈ extraEdges G H K φ Y y₁ ∧
          s(P[c]'hclt, P[c + 1]'(by omega)) ∈ extraEdges G H K φ Y y₂) ∨
        (s(P[c - 1]'(by omega), P[c]'hclt) ∈ extraEdges G H K φ Y y₂ ∧
          s(P[c]'hclt, P[c + 1]'(by omega)) ∈ extraEdges G H K φ Y y₁) := by
      rcases hgetX y₁ hy₁Y hanti₁ with h₁ | h₁
      · rcases hgetX y₂ hy₂Y hanti₂ with h₂ | h₂
        · exact absurd h₂ (Set.disjoint_left.mp hdisj₁₂ h₁)
        · exact Or.inl ⟨h₁, h₂⟩
      · rcases hgetX y₂ hy₂Y hanti₂ with h₂ | h₂
        · exact Or.inr ⟨h₂, h₁⟩
        · exact absurd h₂ (Set.disjoint_left.mp hdisj₁₂ h₁)
    rcases hsplit with ⟨hm', hp'⟩ | ⟨hm', hp'⟩
    · exact endgame_contra hG Y hYmajor y₁ y₂ Q hQ hQY hy hQeven h8 P hP hlen hpar
        he0 hel hint c (by omega) (by omega) hceven hm' hp'
    · -- *"from the symmetry"*: exchange `y₁, y₂` (reverse the antipath `Q`)
      refine endgame_contra hG Y hYmajor y₂ y₁ Q.reverse
        (PathBasics.isPathFrom_reverse hQ) ?_ hy.symm ?_ ?_ P hP hlen hpar
        he0 hel hint c (by omega) (by omega) hceven hm' hp'
      · intro v; rw [List.mem_reverse]; exact hQY v
      · rwa [PathBasics.pathLength_reverse]
      · intro a b ha hb hd
        exact h8 b a hb ha (fun w hw => hd w ⟨hw.2, hw.1⟩)

end Workspace.ProofLemmas.Thm61Claim9
