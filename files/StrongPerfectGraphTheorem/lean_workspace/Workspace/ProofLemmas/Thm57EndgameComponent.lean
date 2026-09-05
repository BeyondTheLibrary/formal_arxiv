import Workspace.ProofLemmas.Thm57EndgameEdgeDeletion
import Workspace.Types.Appearances

/-! # The maximal unmarked component in the endgame of 5.7

The paper chooses a maximal connected subgraph of `H \\ X` containing a branch vertex
and two edges at that vertex. Its vertex set has at least three vertices and is contained
in no branch. We use the connected component of that vertex.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameComponent

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.NoCrossTrackBranch
open Workspace.ProofLemmas.BranchClassification
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A branch cannot contain two distinct neighbours of one of its branch vertices. -/
theorem no_branch_two_neighbours (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {a b c : W} (hb : b ∈ branchVertices H) (hba : H.Adj b a) (hbc : H.Adj b c)
    (hac : a ≠ c) {q : List W} (hq : IsBranch H q) (haq : a ∈ q) (hbq : b ∈ q)
    (hcq : c ∈ q) : False := by
  have hlen : 2 ≤ q.length := by
    by_contra h
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp haq
    obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hbq
    have hij : i = j := by omega
    have hab : a = b := hia.symm.trans ((getElem_eq_of_index_eq q hij hi hj).trans hjb)
    exact hba.ne hab.symm
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsub
  obtain ⟨u, v, huv, heq⟩ := exists_trackEdges_eq_of_isBranch
    hS.inj hS.track hS.len hS.rev hS.disj hS.new hS.cover hS.edges
    (three_le_degree_of_three_connected J hJ) hq hlen
  have hverts : ∀ w ∈ q, w ∈ T u v := by
    intro w hw
    obtain ⟨i, hi, hw⟩ := exists_edge_of_mem hlen hw
    have he : s(q[i], q[i + 1]) ∈ trackEdges (T u v) := heq ▸ ⟨i, hi, rfl⟩
    have hm := mem_of_mem_trackEdges he
    rcases hw with rfl | rfl
    · exact hm.1
    · exact hm.2
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp (hverts a haq)
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp (hverts b hbq)
  obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.mp (hverts c hcq)
  have hji := Thm57EndgameEdgeDeletion.adjacent_indices hS huv hj hi
    (by simpa only [hjb, hia] using hba)
  have hjk := Thm57EndgameEdgeDeletion.adjacent_indices hS huv hj hk
    (by simpa only [hjb, hkc] using hbc)
  have hik : i ≠ k := by
    intro h
    exact hac (hia.symm.trans ((getElem_eq_of_index_eq (T u v) h hi hk).trans hkc))
  have hjint : (T u v)[j]'hj ∈ trackInterior (T u v) := by
    apply (mem_trackInterior_iff _ _).mpr
    exact ⟨j - 1, by omega, getElem_eq_of_index_eq _ (by omega) _ _⟩
  have hbint : b ∈ trackInterior (T u v) := hjb ▸ hjint
  exact hS.new u v huv b hbint ((branch_eq_range hJ hS) ▸ hb)

/-- The component chosen in the paper has at least three vertices, lies in no branch,
and has only marked edges leaving it. -/
theorem exists_component (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hnotsat : ¬ SaturatesLineGraph H X) :
    ∃ A : Set W, ConnectedSet (H.deleteEdges X) A ∧ 3 ≤ A.ncard ∧
      (¬ ∃ q : List W, IsBranch H q ∧ A ⊆ {v | v ∈ q}) ∧
      (∀ u ∈ A, ∀ v ∉ A, H.Adj u v → s(u, v) ∈ X) := by
  classical
  have hex : ∃ b ∈ branchVertices H, ¬ (incidentEdges H b \ X).Subsingleton := by
    simpa only [SaturatesLineGraph, not_forall, exists_prop] using hnotsat
  obtain ⟨b, hb, hbad⟩ := hex
  obtain ⟨e, he, f, hf, hef⟩ := Set.not_subsingleton_iff.mp hbad
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp he.1.2
  obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp hf.1.2
  have hba : H.Adj b a := he.1.1
  have hbc : H.Adj b c := hf.1.1
  have hac : a ≠ c := fun h => hef (congrArg (fun w => s(b, w)) h)
  let K := H.deleteEdges X
  let A := (K.connectedComponentMk b).supp
  have hbA : b ∈ A := rfl
  have haA : a ∈ A := (K.connectedComponentMk b).mem_supp_of_adj_mem_supp hbA
    (SimpleGraph.deleteEdges_adj.mpr ⟨hba, he.2⟩)
  have hcA : c ∈ A := (K.connectedComponentMk b).mem_supp_of_adj_mem_supp hbA
    (SimpleGraph.deleteEdges_adj.mpr ⟨hbc, hf.2⟩)
  refine ⟨A, (K.connectedComponentMk b).connected_toSimpleGraph.preconnected, ?_, ?_, ?_⟩
  · have hsub : ({b, a, c} : Set W) ⊆ A := by
      intro w hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hbnot : b ∉ ({a, c} : Set W) := by simp [hba.ne, hbc.ne]
    rwa [Set.ncard_insert_of_notMem hbnot, Set.ncard_pair hac] at hcard
  · rintro ⟨q, hq, hAq⟩
    exact no_branch_two_neighbours H hc3 hb hba hbc hac hq (hAq haA) (hAq hbA) (hAq hcA)
  · intro u hu v hv huv
    by_contra heX
    exact hv ((K.connectedComponentMk b).mem_supp_of_adj_mem_supp hu
      (SimpleGraph.deleteEdges_adj.mpr ⟨huv, heX⟩))

end Workspace.ProofLemmas.Thm57EndgameComponent
