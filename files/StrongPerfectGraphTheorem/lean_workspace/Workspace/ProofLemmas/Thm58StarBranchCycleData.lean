import Workspace.ProofLemmas.Connectivity58Tracks
import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm75BranchEnds

/-!
# The host-graph data of 5.8 (6), in the star--branch context

PAPER (proof of 5.8 (6), printed p. 28): *"Choose a cycle `C₁` of `H` using the branch between
`v₁` and `v₂` and not using `u`, and choose a minimal track `S` in `H \ {v₁,v₂}` between `u` and
`V(C₁)`.  Let the ends of `S` be `u` and `w` say."*

`Connectivity58Tracks.exists_cycle_and_minimal_track` proves that sentence for an arbitrary
branch and an arbitrary branch-vertex off it.  This file feeds it the star--branch context of
5.8, so that the two remaining gaps of claim (6) can be stated with the host graph already
under control: what is left there is the assembly of the three paths of `G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchCycleData

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- The two ends of the branch, named. -/
theorem branch_ends (h : Context G m J n H K φ N F P p₁ p₂ c q) :
    ∃ v₁ v₂ : Fin n, IsTrackFrom H q v₁ v₂ ∧ v₁ ∈ branchVertices H ∧
      v₂ ∈ branchVertices H := by
  have hq2 := branch_two_le_length h
  have hne : q ≠ [] := h.branch.1.1
  refine ⟨q.head hne, q.getLast hne, ⟨h.branch.1, List.head?_eq_some_head hne,
    List.getLast?_eq_some_getLast hne⟩, ?_, ?_⟩ <;>
  · have := Thm75BranchEnds.branchEnds_mem_branchVertices J h.ready.2.1 H h.ready.2.2.1.1 q
      (q.head hne) (q.getLast hne) h.branch
      ⟨h.branch.1, List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne⟩
      (by simp only [trackLength]; omega)
    first
      | exact this.1
      | exact this.2

/-- **The first sentence of 5.8 (6) in the star--branch context.**  The branch `q`, a return
track `D` closing it into a cycle that avoids the star vertex `c`, and a minimal track `S` from
`c` to an internal vertex `w` of `D`. -/
theorem exists_host_data (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q) :
    ∃ (v₁ v₂ w : Fin n) (D S : List (Fin n)) (k : ℕ),
      IsTrackFrom H q v₁ v₂ ∧ v₁ ∈ branchVertices H ∧ v₂ ∈ branchVertices H ∧
      IsTrackFrom H D v₁ v₂ ∧ c ∉ D ∧
      (∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂) ∧
      (∀ e ∈ trackEdges D, e ∉ trackEdges q) ∧
      0 < k ∧ k + 1 < D.length ∧ D[k]? = some w ∧
      IsTrackFrom H S c w ∧ 2 ≤ S.length ∧
      (∀ x ∈ S, x ∈ D → x = w) ∧ (∀ x ∈ S, x ∉ q) ∧
      (∀ y ∈ S, H.Adj c y → S[1]? = some y) := by
  classical
  obtain ⟨v₁, v₂, hqe, hbv₁, hbv₂⟩ := branch_ends h
  have hsub : IsSubdivision J H := h.ready.2.2.1.1
  have hc3 : CyclicallyThreeConnected H := ⟨m, J, h.ready.2.1, hsub⟩
  obtain ⟨D, S, w, k, hD, hcD, hDq, hDe, hk0, hklt, hkw, hS, hS2, hSD, hSq, hSchord⟩ :=
    Connectivity58Tracks.exists_cycle_and_minimal_track h.ready.2.1 hsub hc3 h.branch
      (branch_two_le_length h) hqe hbv₁ hbv₂ h.star hcq
  exact ⟨v₁, v₂, w, D, S, k, hqe, hbv₁, hbv₂, hD, hcD, hDq, hDe, hk0, hklt, hkw,
    hS, hS2, hSD, hSq, hSchord⟩

end Workspace.ProofLemmas.Thm58StarBranchCycleData
