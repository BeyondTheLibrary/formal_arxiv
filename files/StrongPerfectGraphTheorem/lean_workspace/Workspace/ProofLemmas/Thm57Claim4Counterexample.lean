import Workspace.ProofLemmas.Thm57Claim4Core
import Workspace.ProofLemmas.Thm57Claim3
import Workspace.ProofLemmas.SubdivisionCounting

/-!
The frozen `sixTerminalCore` omits the assumption that the marked pairs are edges.
Here all three marked pairs are nonedges on one branch of a bipartite subdivision
of `K₃,₃`. They satisfy the other hypotheses. See `REPORT.md` for the diagnosis.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm57Claim4Counterexample

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Core Workspace.ProofLemmas.Thm57Setup

private instance trackDecidable {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (q : List W) : Decidable (IsTrackList H q) :=
  decidable_of_iff (q ≠ [] ∧ q.Nodup ∧ q.IsChain H.Adj)
    (by simp only [IsTrackList, List.isChain_iff_getElem])

private instance trackFromDecidable {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (q : List W) (a b : W) :
    Decidable (IsTrackFrom H q a b) :=
  inferInstanceAs (Decidable (IsTrackList H q ∧ q.head? = some a ∧ q.getLast? = some b))

private instance trackEdgeDecidable {W : Type*} [DecidableEq W]
    (q : List W) (e : Sym2 W) : Decidable (e ∈ trackEdges q) :=
  decidable_of_iff (∃ i : Fin (q.length - 1),
    e = s(q[i.val]'(by omega), q[i.val + 1]'(by omega))) (by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i.val, by omega, hi⟩
      · rintro ⟨i, hi, he⟩
        exact ⟨⟨i, by omega⟩, he⟩)

/-- The ends of the long branch are `0,13`. Its internal vertices are `1,…,12`.
The other four old vertices are `14,15,16,17`. -/
def H : SimpleGraph (Fin 18) := SimpleGraph.fromEdgeSet
  {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,6), s(6,7),
   s(7,8), s(8,9), s(9,10), s(10,11), s(11,12), s(12,13),
   s(0,15), s(0,17), s(14,13), s(14,15), s(14,17),
   s(16,13), s(16,15), s(16,17)}

instance : DecidableRel H.Adj := by
  intro u v
  change Decidable (s(u,v) ∈ ({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,6), s(6,7),
   s(7,8), s(8,9), s(9,10), s(10,11), s(11,12), s(12,13),
   s(0,15), s(0,17), s(14,13), s(14,15), s(14,17),
   s(16,13), s(16,15), s(16,17)} : Set (Sym2 (Fin 18))) ∧ u ≠ v)
  infer_instance

/-- The three marked pairs are pairwise disjoint nonedges. -/
def x : Fin 3 → Sym2 (Fin 18) := ![s(1,4), s(5,8), s(9,12)]

def X : Set (Sym2 (Fin 18)) := {x 0, x 1, x 2}

instance : DecidablePred (· ∈ X) := by unfold X; infer_instance

/-- The two parts are given by the parity of the vertex number. -/
def col : H.Coloring Bool := SimpleGraph.Coloring.mk (fun v => decide (v.val % 2 = 1))
  (by change ∀ u v, H.Adj u v → decide (u.val % 2 = 1) ≠ decide (v.val % 2 = 1); decide)

/-- A numbered copy of `K₃,₃`. -/
def J : SimpleGraph (Fin 6) where
  Adj u v := (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)
  symm := by tauto
  loopless := ⟨by intro u h; rcases h with h | h <;> omega⟩

instance : DecidableRel J.Adj := fun u v => inferInstanceAs (Decidable
  ((u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)))

private def jIso : completeBipartiteGraph (Fin 3) (Fin 3) ≃g J where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by
    intro u v
    rcases u with i | i <;> rcases v with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [completeBipartiteGraph_adj, J, finSumFinEquiv]

private def old : Fin 6 → Fin 18 := ![0,14,16,13,15,17]

private def T (u v : Fin 6) : List (Fin 18) :=
  if u = 0 ∧ v = 3 then [0,1,2,3,4,5,6,7,8,9,10,11,12,13]
  else if u = 3 ∧ v = 0 then [13,12,11,10,9,8,7,6,5,4,3,2,1,0]
  else [old u, old v]

/-- This is a subdivision of `K₃,₃`: only its `0`–`3` edge is subdivided. -/
theorem cyclicallyThreeConnected : CyclicallyThreeConnected H := by
  refine ⟨6, J, SubdivisionCounting.isKConnected_of_iso jIso
    SubdivisionCounting.k33_three_connected, old, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · change ∀ u v, J.Adj u v → ∀ w ∈ trackInterior (T u v), ¬ ∃ z, old z = w
    decide
  · decide
  · ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Set.mem_iUnion]
      change H.Adj a b ↔ ∃ u v, ∃ _ : J.Adj u v, s(a,b) ∈ trackEdges (T u v)
      revert a b
      decide

end Workspace.ProofLemmas.Thm57Claim4Counterexample
