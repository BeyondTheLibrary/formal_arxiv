import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm61Claim1Helpers

/-!
# 5.6 — endpoint sets and track assembly

The paper replaces each part of the incident-edge partitions by the other ends of those edges.
This file records that dictionary and packages the final operation of adding the three prescribed
end edges to a middle track.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm56Basics

open Workspace.Types.Tracks.SPGT

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The ends different from the named center of edges in `A`.  Loops cannot occur in a simple
graph, so membership in an incident-edge part later implies that these ends are different from
the center. -/
def endsAt (c : W) (A : Set (Sym2 W)) : Set W := {x | s(c, x) ∈ A}

/-- One oriented conclusion of Theorem 5.6. -/
def Outcome (H : SimpleGraph W) (c d : W)
    (A B C : Set (Sym2 W)) : Prop :=
  ∃ (q : List W) (_hq : 3 ≤ q.length),
    IsTrackList H q ∧
    s(q[0], q[1]) ∈ A ∧ s(q[1], q[2]) ∈ B ∧
    q.getLast? = some d ∧ s(q[q.length - 2], q[q.length - 1]) ∈ C

theorem part_subset_incident {H : SimpleGraph W} {c : W} {A B : Set (Sym2 W)}
    (hpart : A ∪ B = incidentEdges H c) : A ⊆ incidentEdges H c := by
  intro e he
  rw [← hpart]
  exact Or.inl he

theorem endpoints_nonempty {H : SimpleGraph W} {c : W} {A B : Set (Sym2 W)}
    (hpart : A ∪ B = incidentEdges H c) (hA : A.Nonempty) : (endsAt c A).Nonempty := by
  obtain ⟨e, heA⟩ := hA
  have heI := part_subset_incident hpart heA
  obtain ⟨x, hex⟩ := Sym2.mem_iff_exists.mp heI.2
  exact ⟨x, by simpa [endsAt] using hex.symm ▸ heA⟩

theorem adj_of_mem_endpoints {H : SimpleGraph W} {c : W} {A B : Set (Sym2 W)}
    (hpart : A ∪ B = incidentEdges H c) {x : W} (hx : x ∈ endsAt c A) : H.Adj c x := by
  rw [← SimpleGraph.mem_edgeSet]
  exact (part_subset_incident hpart hx).1

theorem ne_center_of_mem_endpoints {H : SimpleGraph W} {c : W} {A B : Set (Sym2 W)}
    (hpart : A ∪ B = incidentEdges H c) {x : W} (hx : x ∈ endsAt c A) : x ≠ c := by
  exact (adj_of_mem_endpoints hpart hx).ne'

/-- Every edge of a part is the center joined to a member of its endpoint set. -/
theorem exists_endpoint_of_mem {H : SimpleGraph W} {c : W} {A B : Set (Sym2 W)}
    (hpart : A ∪ B = incidentEdges H c) {e : Sym2 W} (he : e ∈ A) :
    ∃ x ∈ endsAt c A, e = s(c, x) := by
  have heI := part_subset_incident hpart he
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp heI.2
  exact ⟨x, by simpa [endsAt, hx] using he, hx⟩

/-- Add `x-c` at the front and `y-d` at the back of a middle track from `p` to `y`.
The result has exactly the four edge/endpoint fields in alternative 1 of Theorem 5.6. -/
theorem assemble_first_alternative {H : SimpleGraph W} {c d x p y : W}
    {A B C : Set (Sym2 W)} {P : List W}
    (hP : IsTrackFrom H P p y) (hcP : c ∉ P) (hdP : d ∉ P) (hxP : x ∉ P)
    (hcne : c ≠ d) (hncd : ¬ H.Adj c d)
    (hxc : H.Adj x c) (hcp : H.Adj c p) (hyd : H.Adj y d)
    (hxA : s(x, c) ∈ A) (hpB : s(c, p) ∈ B) (hyC : s(y, d) ∈ C) :
    Outcome H c d A B C := by
  have hPpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  have hxp : x ≠ p := fun h => hxP (h ▸ List.mem_of_head? hP.2.1)
  have hxd : x ≠ d := by
    intro h
    apply hncd
    rw [← h]
    exact hxc.symm
  have hP' : IsTrackFrom H (P ++ [d]) p d :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_concat hP hyd hdP
  have hcP' : c ∉ P ++ [d] := by
    intro hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcP hc
    · exact hcne (List.eq_of_mem_singleton hc)
  have hR : IsTrackFrom H (c :: (P ++ [d])) c d :=
    Workspace.ProofLemmas.Thm61Claim1Helpers.isTrackFrom_cons hP' hcp hcP'
  have hxR : x ∉ c :: (P ++ [d]) := by
    intro hx
    rcases List.mem_cons.mp hx with hx | hx
    · exact hxc.ne hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hxP hx
      · exact hxd (List.eq_of_mem_singleton hx)
  let q : List W := x :: c :: (P ++ [d])
  have hq : IsTrackFrom H q x d :=
    Workspace.ProofLemmas.Thm61Claim1Helpers.isTrackFrom_cons hR hxc hxR
  have hqlen : q.length = P.length + 3 := by simp [q]
  have hq3 : 3 ≤ q.length := by omega
  have hp0 : P[0]'hPpos = p :=
    Workspace.ProofLemmas.Thm61Claim1Helpers.head_getElem hP.2.1 hPpos
  have hyLast : P[P.length - 1]'(by omega) = y :=
    Workspace.ProofLemmas.Thm61Claim1Helpers.last_getElem hP.2.2 hPpos
  refine ⟨q, hq3, hq.1, ?_, ?_, hq.2.2, ?_⟩
  · simpa [q] using hxA
  · have hsecond : q[2]'(by omega) = p := by
      simp only [q, List.getElem_cons_succ]
      rw [List.getElem_append_left hPpos, hp0]
    have hmiddle : q[1]'(by omega) = c := by rfl
    rw [hmiddle]
    convert hpB using 1
    exact congrArg (fun z => s(c, z)) hsecond
  · have hpen : q[q.length - 2]'(by omega) = y := by
      rw [Workspace.ProofLemmas.Thm61Claim1Helpers.geq q
        (show q.length - 2 = (P.length - 1) + 2 by omega) (by omega) (by omega)]
      simp only [q, List.getElem_cons_succ]
      rw [List.getElem_append_left (show P.length - 1 < P.length by omega), hyLast]
    have hlast : q[q.length - 1]'(by omega) = d := by
      rw [Workspace.ProofLemmas.Thm61Claim1Helpers.geq q
        (show q.length - 1 = P.length + 2 by omega) (by omega) (by omega)]
      simp only [q, List.getElem_cons_succ]
      rw [List.getElem_append_right (show P.length ≤ P.length by omega)]
      simp
    simpa [hpen, hlast] using hyC

end Workspace.ProofLemmas.Thm56Basics
