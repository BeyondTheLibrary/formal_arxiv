import Workspace.ProofLemmas.Thm57Claim2TrackParity
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint

/-! # Joining the clean tracks in the same-biparity case of 5.7 (2) -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2Join

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup
open Workspace.ProofLemmas.TrackSlice Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The final vertex, with a bound proof suitable for calculations on track edges. -/
theorem last_vertex {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) : q[q.length - 1]'(by have := List.length_pos_of_ne_nil hq.1.1; omega) = b := by
  have h := hq.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil hq.1.1; omega)] at h
  exact Option.some_injective _ h

/-- Appending a new end creates the edge from the old end to the new one. -/
theorem concat_last_edge {q : List W} {b : W} (hq : q ≠ [])
    (hb : q.getLast? = some b) (z : W) :
    s((q ++ [z])[(q ++ [z]).length - 2]'(by have := List.length_pos_of_ne_nil hq; simp only [List.length_append, List.length_singleton]; omega),
      (q ++ [z])[(q ++ [z]).length - 1]'(by simp)) = s(b, z) := by
  have hpos := List.length_pos_of_ne_nil hq
  have hl : q[q.length - 1]'(by omega) = b := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hb
    exact Option.some_injective _ hb
  simp only [List.length_append, List.length_singleton]
  rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega),
    getElem_eq_of_index_eq q (show q.length + 1 - 2 = q.length - 1 by omega) (by omega) (by omega), hl]
  simp <;> omega

/-- The first edge is unchanged when a vertex is appended to a nontrivial track. -/
theorem concat_first_edge {q : List W} (hq : 2 ≤ q.length) (z : W) :
    s((q ++ [z])[0]'(by simp only [List.length_append, List.length_tail, List.length_singleton]; omega), (q ++ [z])[1]'(by simp only [List.length_append, List.length_tail, List.length_singleton]; omega)) = s(q[0], q[1]) := by
  rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
  rfl

/-- Every edge after appending one vertex is old or is the new last edge. -/
theorem concat_edges {q : List W} {b : W} (hq : q ≠ [])
    (hb : q.getLast? = some b) (z : W) :
    trackEdges (q ++ [z]) ⊆ trackEdges q ∪ {s(b, z)} := by
  rintro e ⟨k, hk, rfl⟩
  have hlen : (q ++ [z]).length = q.length + 1 := by simp
  by_cases hkq : k + 1 < q.length
  · left
    refine ⟨k, hkq, ?_⟩
    rw [List.getElem_append_left (by omega), List.getElem_append_left hkq]
  · right
    change s((q ++ [z])[k]'(by omega), (q ++ [z])[k + 1]'hk) = s(b, z)
    rw [getElem_eq_of_index_eq (q ++ [z]) (show k = (q ++ [z]).length - 2 by omega),
      getElem_eq_of_index_eq (q ++ [z]) (show k + 1 = (q ++ [z]).length - 1 by omega)]
    exact concat_last_edge hq hb z

/-- Gluing at a common end uses only edges of the two tracks. -/
theorem glue_edges {H : SimpleGraph W} {P R : List W} {a r b : W}
    (hP : IsTrackFrom H P a r) (hR : IsTrackFrom H R r b) :
    trackEdges (P ++ R.tail) ⊆ trackEdges P ∪ trackEdges R := by
  have hPpos := List.length_pos_of_ne_nil hP.1.1
  have hRpos := List.length_pos_of_ne_nil hR.1.1
  rintro e ⟨k, hk, rfl⟩
  have hlen : (P ++ R.tail).length = P.length + (R.length - 1) := by simp
  by_cases hkP : k + 1 < P.length
  · left
    refine ⟨k, hkP, ?_⟩
    rw [List.getElem_append_left (by omega), List.getElem_append_left hkP]
  · right
    by_cases hkP' : k < P.length
    · refine ⟨0, by omega, ?_⟩
      rw [List.getElem_append_left hkP', List.getElem_append_right (by omega),
        List.getElem_tail, getElem_eq_of_index_eq P (show k = P.length - 1 by omega),
        last_vertex hP, track_head hR,
        getElem_eq_of_index_eq R (show k + 1 - P.length + 1 = 0 + 1 by omega)] <;> omega
    · refine ⟨k - P.length + 1, by omega, ?_⟩
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
        List.getElem_tail, List.getElem_tail,
        getElem_eq_of_index_eq R
          (show k + 1 - P.length + 1 = k - P.length + 1 + 1 by omega)]

/-- PAPER: *"From the track `Q₁-c₁-P₁-b-P₂-c₂-a` and the hypothesis ..."*

More generally, a track carrying just its first `X`-edge, followed by a clean track and
one final `X`-edge, has odd total length. Both tracks have an edge, so an even total length
would be at least four. -/
theorem clean_join_odd {H : SimpleGraph W} {X : Set (Sym2 W)}
    (hnotrack : NoEvenTrack57 H X) {P R : List W} {a r b z : W}
    (hP : IsTrackFrom H P a r) (hR : IsTrackFrom H R r b)
    (hPlen : 2 ≤ P.length) (hRlen : 2 ≤ R.length)
    (hcommon : ∀ w ∈ P, w ∈ R → w = r)
    (hzP : z ∉ P) (hzR : z ∉ R) (hclose : H.Adj b z)
    (hfirst : s(P[0], P[1]) ∈ X) (hlast : s(b, z) ∈ X)
    (hPclean : ∀ e ∈ trackEdges P, e ∈ X → e = s(P[0], P[1]))
    (hRclean : ∀ e ∈ trackEdges R, e ∉ X) :
    Odd (trackLength P + trackLength R + 1) := by
  obtain ⟨hglue, hmem⟩ := Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
    H P R a r b hP hR hcommon
  have hz : z ∉ P ++ R.tail := by
    intro h
    rcases hmem z h with h | h
    · exact hzP h
    · exact hzR h
  have hq := isTrackFrom_concat hglue hclose hz
  have hlen : (P ++ R.tail ++ [z]).length = P.length + R.length := by
    simp only [List.length_append, List.length_tail, List.length_singleton]
    omega
  have hlength : trackLength (P ++ R.tail ++ [z]) = trackLength P + trackLength R + 1 := by
    unfold trackLength
    rw [hlen]
    omega
  have hfirsteq :
      s((P ++ R.tail ++ [z])[0]'(by rw [hlen]; omega),
        (P ++ R.tail ++ [z])[1]'(by rw [hlen]; omega)) = s(P[0], P[1]) := by
    rw [concat_first_edge (by simp only [List.length_append, List.length_tail, List.length_singleton]; omega), List.getElem_append_left (by omega),
      List.getElem_append_left (by omega)]
    rfl
  have hlasteq := concat_last_edge hglue.1.1 hglue.2.2 z
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hlong : 5 ≤ (P ++ R.tail ++ [z]).length := by
    rw [Nat.even_iff, ← hlength, trackLength, hlen] at heven
    rw [hlen]
    omega
  apply hnotrack
  refine ⟨P ++ R.tail ++ [z], hlong, hq.1, hlength.symm ▸ heven,
    hfirsteq.symm ▸ hfirst, hlasteq.symm ▸ hlast, ?_⟩
  intro e he hnef hnel heX
  rcases concat_edges hglue.1.1 hglue.2.2 z he with he | he
  · rcases glue_edges hP hR he with he | he
    · exact hnef ((hPclean e he heX).trans hfirsteq.symm)
    · exact hRclean e he heX
  · exact hnel ((show e = s(b, z) from he).trans hlasteq.symm)

end Workspace.ProofLemmas.Thm57Claim2Join
