import Workspace.ProofLemmas.Thm61OddBranchSubdivision
import Workspace.ProofLemmas.Thm85Five8Transported

/-! The fixed six-vertex enlargement used in 6.1(7). -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm61OddFiniteModel
open Workspace.Types.Tracks.SPGT Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

/-- The host `K₃,₃`, with its two parts numbered `0,1,2` and `3,4,5`. -/
def k33 : SimpleGraph (Fin 6) where
  Adj u v := (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)
  symm := by tauto
  loopless := ⟨by intro u h; rcases h with h | h <;> omega⟩

instance : DecidableRel k33.Adj := fun u v => inferInstanceAs (Decidable
  ((u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)))

/-- The map sends the left part to `0,1,2` and the right part to `3,4,5`. -/
def k33Iso : completeBipartiteGraph (Fin 3) (Fin 3) ≃g k33 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by
    intro u v
    rcases u with i | i <;> rcases v with j | j <;> fin_cases i <;> fin_cases j <;> simp [completeBipartiteGraph_adj, k33, finSumFinEquiv]

/-- The old host edges, indexed by their two ends. -/
def edgeVal (ij : Fin 3 × Fin 3) : Sym2 (Fin 6) :=
  s(Fin.castAdd 3 ij.1, Fin.natAdd 3 ij.2)

theorem edge_mem (ij : Fin 3 × Fin 3) : edgeVal ij ∈ k33.edgeSet := by
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide

def edge (ij : Fin 3 × Fin 3) : k33.edgeSet := ⟨edgeVal ij, edge_mem ij⟩

theorem edge_bijective : Function.Bijective edge := by
  constructor
  · intro i j h
    have hval : edgeVal i = edgeVal j := congrArg Subtype.val h
    exact (show Function.Injective edgeVal by decide) hval
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      change k33.Adj u v at he
      fin_cases u <;> fin_cases v <;> try (contradiction)
      all_goals first
        | exact ⟨(0, 0), by apply Subtype.ext; dsimp only [edge]; decide⟩ | exact ⟨(0, 1), by apply Subtype.ext; dsimp only [edge]; decide⟩ | exact ⟨(0, 2), by apply Subtype.ext; dsimp only [edge]; decide⟩
        | exact ⟨(1, 0), by apply Subtype.ext; dsimp only [edge]; decide⟩ | exact ⟨(1, 1), by apply Subtype.ext; dsimp only [edge]; decide⟩ | exact ⟨(1, 2), by apply Subtype.ext; dsimp only [edge]; decide⟩
        | exact ⟨(2, 0), by apply Subtype.ext; dsimp only [edge]; decide⟩ | exact ⟨(2, 1), by apply Subtype.ext; dsimp only [edge]; decide⟩ | exact ⟨(2, 2), by apply Subtype.ext; dsimp only [edge]; decide⟩

noncomputable def edgeEquiv : (Fin 3 × Fin 3) ≃ k33.edgeSet :=
  Equiv.ofBijective edge edge_bijective

theorem line_adj (i j : Fin 3 × Fin 3) :
    k33.lineGraph.Adj (edge i) (edge j) ↔ i ≠ j ∧ (i.1 = j.1 ∨ i.2 = j.2) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  have hinj := edge_bijective.1
  simp only [ne_eq, hinj.eq_iff]
  change (i ≠ j ∧ ∃ v : Fin 6, v ∈ edgeVal i ∧ v ∈ edgeVal j) ↔ _
  revert i j
  decide

/-- The coordinate change taking disjoint old edges to incident new edges. -/
def oldIndex (ij : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (ij.1 - ij.2, -ij.1 - ij.2)

theorem oldIndex_injective : Function.Injective oldIndex := by decide

theorem oldIndex_disjoint (i j : Fin 3 × Fin 3) :
    (oldIndex i).1 ≠ (oldIndex j).1 ∧ (oldIndex i).2 ≠ (oldIndex j).2 ↔
      i ≠ j ∧ (i.1 = j.1 ∨ i.2 = j.2) := by revert i j; decide

theorem oldIndex_class (i : Fin 3 × Fin 3) :
    ((oldIndex i).2 = (oldIndex i).1 ↔ i.1 = 0) ∧
    ((oldIndex i).2 = (oldIndex i).1 + 1 ↔ i.1 = 1) := by revert i; decide

theorem zero_incident (i : Fin 3 × Fin 3) : (0 : Fin 6) ∈ edgeVal i ↔ i.1 = 0 := by
  revert i; decide

theorem one_incident (i : Fin 3 × Fin 3) : (1 : Fin 6) ∈ edgeVal i ↔ i.1 = 1 := by
  revert i; decide

/-- The enlargement adds the edge between the first two vertices of the left part. -/
def enlarged : SimpleGraph (Fin 6) := k33 ⊔ SimpleGraph.edge 0 1

/-- The bipartite colouring of the old host. -/
def coloring : k33.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun v => if v.val < 3 then 0 else 1) (by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [k33])

/-- Paper, 6.1(7): "there is a `J`-enlargement". The added edge makes the
old `K₃,₃` a proper spanning subgraph, and preserves 3-connectivity. -/
theorem is_enlargement {m : ℕ} (J : SimpleGraph (Fin m))
    (hJ : Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))) :
    IsJEnlargement J enlarged := by
  obtain ⟨ψ⟩ := hJ
  have h3 : IsKConnected k33 3 := isKConnected_of_iso k33Iso k33_three_connected
  refine ⟨⟨h3.1, ?_⟩, ?_⟩
  · intro S hS
    exact (h3.2 S hS).mono (fun _ _ h => Or.inl h)
  · let S : enlarged.Subgraph := SimpleGraph.toSubgraph k33 (show k33 ≤ enlarged from le_sup_left)
    refine ⟨S, ?_, 6, k33, ?_, ?_⟩
    · intro htop
      have h01 : S.Adj 0 1 := by
        rw [htop]
        exact Or.inr (by simp [SimpleGraph.edge_adj])
      exact (show ¬ k33.Adj 0 1 by decide) h01
    · exact Thm85Five8Transported.isSubdivision_of_iso (ψ.trans k33Iso).symm
        (isSubdivision_self k33)
    · exact ⟨(SimpleGraph.toSubgraph k33 (show k33 ≤ enlarged from le_sup_left)).spanningCoeEquivCoeOfSpanning
        (SimpleGraph.toSubgraph.isSpanning k33 (show k33 ≤ enlarged from le_sup_left)) |>.symm⟩

end Workspace.ProofLemmas.Thm61OddFiniteModel
