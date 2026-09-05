import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# Dropping the `B`-complete vertices of `A` does not affect balancedness

The proof of 4.2 (printed p. 15) ends *"Let `A_i'` be the set of vertices in `A_i` that are not
`B_1`-complete.  … by 2.7.2, so is `(A_i', B_1)`, and consequently so is `(A_i, B_1)`."*  The
word *consequently* stands for the following observation, which this module supplies.

Write `A₀ = {x ∈ A : x is not B-complete}`.  If `(A₀,B)` is balanced then so is `(A,B)`:

* an odd path between nonadjacent `u, v ∈ B` with interior in `A` automatically has its interior
  in `A₀`, since a `B`-complete interior vertex would be adjacent to both ends, forcing the path
  to have exactly three vertices and hence even length `2`;
* an odd antipath between adjacent `u, v ∈ A` with interior in `B` automatically has both ends in
  `A₀`, since its length is at least `3` (its ends are `G`-adjacent, so they are not
  `Ḡ`-adjacent) and so each end has a `Ḡ`-neighbour in `B`, i.e. a non-neighbour in `B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.BalancedRestrictNonComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`(A₀,B)` balanced implies `(A,B)` balanced**, where `A₀` is the set of vertices of `A`
that are not `B`-complete. -/
theorem balanced_of_notComplete {G : SimpleGraph V} {A B : Set V}
    (h : Workspace.Types.Core.SPGT.Balanced G {x : V | x ∈ A ∧ ¬ VertexComplete G x B} B) :
    Workspace.Types.Core.SPGT.Balanced G A B := by
  constructor
  · -- no odd path between nonadjacent vertices of `B` with interior in `A`
    intro u v p hu hv hnadj hp hint hodd
    refine h.1 u v p hu hv hnadj hp (fun x hx => ⟨hint x hx, ?_⟩) hodd
    intro hcomp
    -- `x` sits at some interior position `k`
    obtain ⟨k, hk, hk1, hk2, hkx⟩ :=
      Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hp.1 hx
    have hpos : 0 < p.length := Workspace.ProofLemmas.PathBasics.path_length_pos hp.1
    have h0 : p[0]'hpos = u :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 hpos
    have hl : p[p.length - 1]'(by omega) = v :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 hpos
    -- `x` is adjacent to both ends
    have hxu : G.Adj (p[k]'hk) (p[0]'hpos) := by rw [hkx, h0]; exact hcomp u hu
    have hxv : G.Adj (p[k]'hk) (p[p.length - 1]'(by omega)) := by
      rw [hkx, hl]; exact hcomp v hv
    have e1 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp.1 hk hpos).mp hxu
    have e2 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp.1 hk
      (show p.length - 1 < p.length by omega)).mp hxv
    -- hence `p` has exactly three vertices, so its length is `2`, contradicting oddness
    have hlen3 : p.length = 3 := by omega
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq, hlen3] at hodd
    exact (Nat.not_odd_iff_even.mpr ⟨1, rfl⟩) hodd
  · -- no odd antipath between adjacent vertices of `A` with interior in `B`
    intro u v q hu hv hadj hq hint hodd
    have hqpos : 0 < q.length := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    have h0 : q[0]'hqpos = u :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hq.2.1 hqpos
    have hl : q[q.length - 1]'(by omega) = v :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hq.2.2 hqpos
    -- the ends are `G`-adjacent, hence not `Ḡ`-adjacent, so the antipath has length `≥ 2`
    have hne1 : pathLength q ≠ 1 := by
      intro h1
      exact ((SimpleGraph.compl_adj G u v).mp
        (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hq h1)).2 hadj
    have hlen1 : 1 ≤ pathLength q := by obtain ⟨k, hk⟩ := hodd; omega
    have hlen4 : 4 ≤ q.length := by
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hne1 hlen1
      obtain ⟨k, hk⟩ := hodd
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hk
      omega
    -- position `1` is interior, and is a `Ḡ`-neighbour of `u`
    have h1int : (q[1]'(by omega)) ∈ SPGT.interior q :=
      Workspace.ProofLemmas.PathBasics.getElem_mem_interior hq.1 (by omega) le_rfl (by omega)
    have h1adj : Gᶜ.Adj (q[0]'hqpos) (q[1]'(by omega)) :=
      (Workspace.ProofLemmas.PathBasics.path_adj_iff hq.1 hqpos (by omega)).mpr (Or.inl rfl)
    -- position `q.length - 2` is interior, and is a `Ḡ`-neighbour of `v`
    have h2int : (q[q.length - 2]'(by omega)) ∈ SPGT.interior q :=
      Workspace.ProofLemmas.PathBasics.getElem_mem_interior hq.1 (by omega) (by omega) (by omega)
    have h2adj : Gᶜ.Adj (q[q.length - 1]'(by omega)) (q[q.length - 2]'(by omega)) :=
      (Workspace.ProofLemmas.PathBasics.path_adj_iff hq.1 (by omega) (by omega)).mpr
        (Or.inr (by omega))
    refine h.2 u v q ⟨hu, ?_⟩ ⟨hv, ?_⟩ hadj hq hint hodd
    · intro hcomp
      have := hcomp _ (hint _ h1int)
      rw [h0] at h1adj
      exact ((SimpleGraph.compl_adj G _ _).mp h1adj).2 this
    · intro hcomp
      have := hcomp _ (hint _ h2int)
      rw [hl] at h2adj
      exact ((SimpleGraph.compl_adj G _ _).mp h2adj).2 this

end Workspace.ProofLemmas.BalancedRestrictNonComplete
