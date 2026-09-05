import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.HoleBasics

/-!
# Reading a hole backwards from its first vertex

A hole is a cyclic object, so it may be listed starting anywhere and in either direction.
This file records the one symmetry that the assembly of 5.8 (6) needs: reading the hole
backwards while keeping its first vertex in place.  It is used to normalise the order of the
two neighbours `r`, `s` of `pₙ` on the hole, which the paper leaves unspecified.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarBranchMixedHoleMirror

open Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- The hole `L` read backwards, still starting at `L[0]`. -/
def mirror (L : List V) : List V := L.reverse.rotate (L.length - 1)

theorem mirror_length (L : List V) : (mirror L).length = L.length := by
  simp [mirror]

theorem mem_mirror {L : List V} {x : V} : x ∈ mirror L ↔ x ∈ L := by
  simp [mirror, List.mem_rotate]

theorem mirror_getElem_zero (L : List V) (h : 0 < (mirror L).length) (h' : 0 < L.length) :
    (mirror L)[0] = L[0]'h' := by
  simp only [mirror] at h ⊢
  rw [List.getElem_rotate, List.getElem_reverse]
  refine SubdivisionCounting.getElem_eq_of_index_eq L ?_ _ _
  rw [List.length_reverse, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem mirror_getElem_pos (L : List V) (m : ℕ) (hm : 1 ≤ m) (h : m < (mirror L).length)
    (h' : L.length - m < L.length) :
    (mirror L)[m] = L[L.length - m]'h' := by
  have hlen : (mirror L).length = L.length := mirror_length L
  have hm2 : m < L.length := by omega
  simp only [mirror] at h ⊢
  rw [List.getElem_rotate, List.getElem_reverse]
  refine SubdivisionCounting.getElem_eq_of_index_eq L ?_ _ _
  rw [List.length_reverse]
  have he : m + (L.length - 1) = (m - 1) + 1 * L.length := by omega
  rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem isHoleList_mirror {L : List V} (h : IsHoleList G L) : IsHoleList G (mirror L) :=
  HoleBasics.isHoleList_rotate (HoleBasics.isHoleList_reverse h) _

end Workspace.ProofLemmas.Thm58StarBranchMixedHoleMirror
