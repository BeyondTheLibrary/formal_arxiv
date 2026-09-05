import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim4Basics
import Workspace.ProofLemmas.Thm57Claim4Config
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack

/-!
# 5.7 (4): every two ends inside `A` are joined in `K`

PAPER (printed p. 24):

> *"Since `A` is connected and meets all of `x₁, x₂, x₃` it follows that there is a component
> of `K` containing an end of each of these three edges."*

The proof is the obvious one: take a track of `A` between the two ends and cut it at every
end of a marked edge it passes through.  Each piece is then a track of `A` using no other end,
that is, an edge of `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim4Reach

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Config
open Workspace.ProofLemmas.Thm57Claim4Basics
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Adjacency in `K`, restricted to the six ends: this is the relation whose transitive
closure is *"being in the same component of `K`"*. -/
def KAdjT (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W) (x : Fin 3 → Sym2 W)
    (u v : W) : Prop :=
  u ∈ Terminals x ∧ v ∈ Terminals x ∧ KAdj H X A x u v

private theorem reach_aux (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W)
    (x : Fin 3 → Sym2 W) :
    ∀ n : ℕ, ∀ P : List W, P.length ≤ n → ∀ u v : W,
      IsTrackFrom (H.deleteEdges X) P u v → (∀ z ∈ P, z ∈ A) →
      u ∈ Terminals x → v ∈ Terminals x →
      Relation.ReflTransGen (KAdjT H X A x) u v := by
  intro n
  induction n with
  | zero =>
    intro P hlen u v hPt _ _ _
    exact absurd (List.length_pos_of_ne_nil hPt.1.1) (by omega)
  | succ n ih =>
    intro P hlen u v hPt hPA huT hvT
    by_cases hclean : ∀ z ∈ P, z ∈ Terminals x → z = u ∨ z = v
    · exact Relation.ReflTransGen.single ⟨huT, hvT, P, hPt, hPA, hclean⟩
    · push_neg at hclean
      obtain ⟨z, hzP, hzT, hzuv⟩ := hclean
      have hzu : z ≠ u := hzuv.1
      have hzv : z ≠ v := hzuv.2
      have hPne : 0 < P.length := List.length_pos_of_ne_nil hPt.1.1
      have hP0 : P[0]'hPne = u := getElem_zero_of_head? hPt.2.1 hPne
      have hPl : P[P.length - 1]'(by omega) = v := getElem_last_of_getLast? hPt.2.2 hPne
      obtain ⟨r, hr, hrz⟩ := List.mem_iff_getElem.mp hzP
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · refine absurd ?_ hzu
          rw [← hrz]
          exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
            P h hr hPne).trans hP0
        · exact h
      have hrl : r < P.length - 1 := by
        rcases lt_or_eq_of_le (show r ≤ P.length - 1 by omega) with h | h
        · exact h
        · refine absurd ?_ hzv
          rw [← hrz]
          exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
            P h hr (by omega)).trans hPl
      have h1 : IsTrackFrom (H.deleteEdges X) (slice P 0 r) u z := by
        have h := isTrackFrom_slice (i := 0) (j := r) hPt.1 hr (Nat.zero_le _)
        rw [hP0, hrz] at h
        exact h
      have h2 : IsTrackFrom (H.deleteEdges X) (slice P r (P.length - 1)) z v := by
        have h := isTrackFrom_slice (i := r) (j := P.length - 1) hPt.1
          (show P.length - 1 < P.length by omega) (by omega)
        rw [hPl, hrz] at h
        exact h
      have hlen1 : (slice P 0 r).length ≤ n := by
        have := length_slice P hr (Nat.zero_le r)
        omega
      have hlen2 : (slice P r (P.length - 1)).length ≤ n := by
        have := length_slice P (show P.length - 1 < P.length by omega) (show r ≤ P.length - 1 by omega)
        omega
      exact (ih _ hlen1 u z h1 (fun w hw => hPA w (mem_of_mem_slice hw)) huT hzT).trans
        (ih _ hlen2 z v h2 (fun w hw => hPA w (mem_of_mem_slice hw)) hzT hvT)

/-- Any two ends of marked edges lying in `A` are in the same component of `K`. -/
theorem reach_of_mem_A (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W)
    (x : Fin 3 → Sym2 W) (hconn : ConnectedSet (H.deleteEdges X) A)
    {u v : W} (hu : u ∈ A) (hv : v ∈ A) (huT : u ∈ Terminals x) (hvT : v ∈ Terminals x) :
    Relation.ReflTransGen (KAdjT H X A x) u v := by
  obtain ⟨p, hp, q, hq, P, hPt, hPA, -, -⟩ :=
    Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
      (H.deleteEdges X) A {u} {v} hconn ⟨u, rfl⟩ ⟨v, rfl⟩
      (Set.singleton_subset_iff.mpr hu) (Set.singleton_subset_iff.mpr hv)
  have hpu : p = u := by simpa using hp
  have hqv : q = v := by simpa using hq
  subst hpu
  subst hqv
  exact reach_aux H X A x P.length P le_rfl p q hPt hPA huT hvT

end Workspace.ProofLemmas.Thm57Claim4Reach
