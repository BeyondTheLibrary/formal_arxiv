import Workspace.ProofLemmas.CyclicThreeConnectedAttachments
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.TrackSlice

/-!
# A track with a prescribed first edge

PAPER (proof of 5.8 (2), printed p. 26): *"Now `H` is a subdivision of a 3-connected graph, so
if we delete all edges of `H` incident with `u` except `s₁`, the graph we produce is still
connected.  Consequently there is a track of `H` from `u` to `v` with first edge `s₁`."*

Deleting all edges at `u` except one leaves `u` hanging on that one edge, and what remains after
also deleting `u` is `H` minus a single vertex, which is connected because `H` is cyclically
3-connected.  So the graph stays connected, and a track from `u` to any other vertex must leave
`u` along the surviving edge.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Connectivity58FirstEdge

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments

variable {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}

/-- **The first sentence of 5.8 (2).**  A track from `u` to `v` whose first edge is a
prescribed edge `ux` at `u`. -/
theorem exists_track_first_edge (hc3 : CyclicallyThreeConnected H) {u x v : W}
    (hux : H.Adj u x) (hvu : v ≠ u) :
    ∃ t : List W, IsTrackFrom H t u v ∧ 2 ≤ t.length ∧ t[1]? = some x := by
  classical
  by_cases hxv : x = v
  · subst hxv
    refine ⟨[u, x], ⟨⟨by simp, by simp [hux.ne], ?_⟩, rfl, rfl⟩, by simp, by simp⟩
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using hux
  · have hcard : ({u} : Set W).ncard ≤ 1 := by simp
    have hconn := connectedSet_compl_of_ncard_le_one hc3 hcard
    have hxS : x ∈ ({u} : Set W)ᶜ := fun hh => hux.ne' (by simpa using hh)
    have hvS : v ∈ ({u} : Set W)ᶜ := fun hh => hvu (by simpa using hh)
    have hrch : RchIn H ({u} : Set W)ᶜ x v := ⟨hxS, hvS, hconn ⟨x, hxS⟩ ⟨v, hvS⟩⟩
    obtain ⟨wlk, hwlk⟩ := NoCrossTrackBranch.walk_of_rchIn hrch
    obtain ⟨R, hR, hRsupp, -⟩ := NoCrossTrackBranch.exists_track_of_walk wlk
    have huR : u ∉ R := fun hh => hwlk u (hRsupp u hh) rfl
    have ht : IsTrackFrom H (u :: R) u v := by
      have h1 := TrackSlice.isTrackFrom_concat (TrackSlice.isTrackFrom_reverse hR)
        hux.symm (by simpa using huR)
      simpa using TrackSlice.isTrackFrom_reverse h1
    refine ⟨u :: R, ht, ?_, ?_⟩
    · have : 0 < R.length := List.length_pos_of_ne_nil hR.1.1
      simp only [List.length_cons]; omega
    · rw [List.getElem?_cons_succ]
      rw [← List.head?_eq_getElem?]; exact hR.2.1

end Workspace.ProofLemmas.Connectivity58FirstEdge
