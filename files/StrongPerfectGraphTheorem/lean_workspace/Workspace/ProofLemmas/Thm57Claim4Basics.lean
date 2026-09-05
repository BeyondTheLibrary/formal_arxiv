import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice

/-!
# 5.7 (4): small list/track utilities

Bookkeeping lemmas used by the auxiliary-graph argument of printed claim (4).  Nothing here
is a mathematical claim of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm57Claim4Basics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*}

theorem getElem_zero_of_head? {R : List W} {a : W} (h : R.head? = some a)
    (hne : 0 < R.length) : R[0]'hne = a := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hne] at h
  exact Option.some_injective _ h

theorem getElem_last_of_getLast? {R : List W} {b : W} (h : R.getLast? = some b)
    (hne : 0 < R.length) : R[R.length - 1]'(by omega) = b := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
  exact Option.some_injective _ h

/-- A track of `H \ X` is a track of `H`. -/
theorem isTrackList_of_delete {H : SimpleGraph W} {X : Set (Sym2 W)} {R : List W}
    (h : IsTrackList (H.deleteEdges X) R) : IsTrackList H R :=
  ⟨h.1, h.2.1, fun i hi => (SimpleGraph.deleteEdges_adj.mp (h.2.2 i hi)).1⟩

theorem isTrackFrom_of_delete {H : SimpleGraph W} {X : Set (Sym2 W)} {R : List W} {a b : W}
    (h : IsTrackFrom (H.deleteEdges X) R a b) : IsTrackFrom H R a b :=
  ⟨isTrackList_of_delete h.1, h.2.1, h.2.2⟩

/-- No edge of a track of `H \ X` is in `X`. -/
theorem edge_not_mem_of_delete {H : SimpleGraph W} {X : Set (Sym2 W)} {R : List W}
    (h : IsTrackList (H.deleteEdges X) R) {n : ℕ} (hn : n + 1 < R.length) :
    s(R[n], R[n + 1]) ∉ X :=
  (SimpleGraph.deleteEdges_adj.mp (h.2.2 n hn)).2

theorem mem_trackEdges_of_index {R : List W} {n : ℕ} (hn : n + 1 < R.length) :
    s(R[n], R[n + 1]) ∈ trackEdges R := ⟨n, hn, rfl⟩

/-- The last edge of `R ++ [y]`. -/
theorem last_edge_mem_concat {R : List W} (hne : 0 < R.length) (y : W) :
    s(R[R.length - 1]'(by omega), y) ∈ trackEdges (R ++ [y]) := by
  refine ⟨R.length - 1, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
  have h1 : (R ++ [y])[R.length - 1]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = R[R.length - 1]'(by omega) :=
    List.getElem_append_left (by omega)
  have h2 : (R ++ [y])[R.length - 1 + 1]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = y := by
    rw [List.getElem_append_right (by omega)]
    simp
  rw [h1, h2]

/-- The first edge of `R ++ [y]` when `R` has at least two vertices. -/
theorem first_edge_concat {R : List W} (hne : 2 ≤ R.length) (y : W) :
    s((R ++ [y])[0]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega), (R ++ [y])[1]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
      = s(R[0]'(by omega), R[1]'(by omega)) := by
  rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]

theorem mem_concat_iff {R : List W} {y z : W} : z ∈ R ++ [y] ↔ z ∈ R ∨ z = y := by
  simp

end Workspace.ProofLemmas.Thm57Claim4Basics
