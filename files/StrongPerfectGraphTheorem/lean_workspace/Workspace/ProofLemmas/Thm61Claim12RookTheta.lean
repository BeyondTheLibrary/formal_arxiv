import Workspace.ProofLemmas.L33SelfComplementary
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-!
# The eight-edge model of `K₃,₃` minus one edge used in 6.1(12)

The nine vertices of the appearance in claim (12) are the cells of a `3 × 3` board: they carry
the rook's graph `L(K₃,₃)` in `G`.  In `Gᶜ` they carry the *complementary* rook's graph, which
is again `L(K₃,₃)` after the shear `(i, j) ↦ (i + j, i + 2j)` of
`Workspace.ProofLemmas.L33SelfComplementary`.

This module fixes the concrete host graph of that second copy.  Its six vertices are
`0, 1, 2` (the three "rows" of the sheared board) and `3, 4, 5` (the three "columns"); `k33Six`
is the complete bipartite graph between them and `rookTheta` is `k33Six` with the single edge
`s(1, 3)` deleted.  The deleted edge is the cell that the paper omits, namely the cell
`(2, 2)`, whose shear is the row/column pair `(1, 0)`.

The eight remaining edges are indexed by `Fin 8` through `rookEdgeVal`, and `rookCell` records
which original cell each of them comes from.  The one fact the construction needs is
`rookEdge_lineGraph_adj`: under this indexing, `L(rookTheta)` is the complementary rook's graph
on those eight cells.  Everything here is a finite check.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Claim12RookTheta

open Workspace.ProofLemmas.L33SelfComplementary

/-! ### The two fixed graphs on `Fin 6` -/

/-- Adjacency of the complete bipartite graph between `{0,1,2}` and `{3,4,5}`. -/
def k33Adj (a b : Fin 6) : Prop :=
  ((a : ℕ) < 3 ∧ 3 ≤ (b : ℕ)) ∨ ((b : ℕ) < 3 ∧ 3 ≤ (a : ℕ))

instance : DecidableRel k33Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- `K₃,₃` on `Fin 6`, with parts `{0,1,2}` and `{3,4,5}`. -/
def k33Six : SimpleGraph (Fin 6) where
  Adj := k33Adj
  symm := by intro a b h; exact h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel k33Six.Adj := inferInstanceAs (DecidableRel k33Adj)

/-- Adjacency of `k33Six` with the edge `s(1, 3)` removed. -/
def rookThetaAdj (a b : Fin 6) : Prop :=
  k33Adj a b ∧ ¬ ((a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1))

instance : DecidableRel rookThetaAdj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `K₃,₃` on `Fin 6` with the edge `s(1, 3)` deleted: the host of the appearance before the
antipath is put back in place of that edge. -/
def rookTheta : SimpleGraph (Fin 6) where
  Adj := rookThetaAdj
  symm := by
    intro a b h
    exact ⟨h.1.symm, by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact h.2 (by simp)⟩
  loopless := ⟨by decide⟩

instance : DecidableRel rookTheta.Adj := inferInstanceAs (DecidableRel rookThetaAdj)

/-! ### The eight edges -/

/-- The eight edges of `rookTheta`, in the order of the cells listed by `rookCell`. -/
def rookEdgeVal : Fin 8 → Sym2 (Fin 6)
  | 0 => s(0, 3)
  | 1 => s(1, 5)
  | 2 => s(2, 4)
  | 3 => s(1, 4)
  | 4 => s(2, 3)
  | 5 => s(0, 5)
  | 6 => s(2, 5)
  | 7 => s(0, 4)

/-- The cell of the original `3 × 3` board that each edge of `rookTheta` comes from: the eight
cells other than `(2, 2)`, in lexicographic order.  The pairing is the shear
`(i, j) ↦ (i + j, i + 2j)`, with a row `p` written as the vertex `p` and a column `q` as the
vertex `q + 3`. -/
def rookCell : Fin 8 → Fin 3 × Fin 3
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)
  | 6 => (2, 0)
  | 7 => (2, 1)

theorem rookCell_injective : Function.Injective rookCell := by decide

theorem rookCell_ne_two_two (k : Fin 8) : rookCell k ≠ (2, 2) := by revert k; decide

theorem rookCell_surjective (i : Fin 3 × Fin 3) (hi : i ≠ (2, 2)) : ∃ k, rookCell k = i := by
  revert i
  decide

theorem rookEdgeVal_mem (k : Fin 8) : rookEdgeVal k ∈ rookTheta.edgeSet := by revert k; decide

/-- The eight edges of `rookTheta` as elements of its edge set. -/
def rookEdge (k : Fin 8) : rookTheta.edgeSet := ⟨rookEdgeVal k, rookEdgeVal_mem k⟩

theorem rookEdgeVal_surj (a b : Fin 6) (h : rookTheta.Adj a b) :
    ∃ k, rookEdgeVal k = s(a, b) := by
  revert a b
  decide

theorem rookEdge_bijective : Function.Bijective rookEdge := by
  constructor
  · intro k l h
    have hv : rookEdgeVal k = rookEdgeVal l := congrArg Subtype.val h
    revert hv
    revert k l
    decide
  · rintro ⟨e, he⟩
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨k, hk⟩ := rookEdgeVal_surj a b ((SimpleGraph.mem_edgeSet _).mp he)
      exact ⟨k, Subtype.ext hk⟩

/-- The equivalence `Fin 8 ≃ E(rookTheta)`. -/
noncomputable def rookEdgeEquiv : Fin 8 ≃ rookTheta.edgeSet :=
  Equiv.ofBijective rookEdge rookEdge_bijective

/-- **The dictionary.**  Two of the eight edges of `rookTheta` share an end exactly when the
two cells they come from differ in both coordinates, i.e. are adjacent in `rook33ᶜ`. -/
theorem rookEdge_lineGraph_adj (k l : Fin 8) :
    rookTheta.lineGraph.Adj (rookEdge k) (rookEdge l) ↔ rook33ᶜ.Adj (rookCell k) (rookCell l) := by
  simp only [SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.compl_adj]
  revert k l
  decide

/-! ### The two ends of the deleted edge -/

theorem rookEdge_mem_three (k : Fin 8) :
    (3 : Fin 6) ∈ (rookEdge k : Sym2 (Fin 6)) ↔ (k = 0 ∨ k = 4) := by
  revert k
  decide

theorem rookEdge_mem_one (k : Fin 8) :
    (1 : Fin 6) ∈ (rookEdge k : Sym2 (Fin 6)) ↔ (k = 1 ∨ k = 3) := by
  revert k
  decide

theorem rookTheta_not_adj : ¬ rookTheta.Adj 3 1 := by decide

theorem rookTheta_adj_three_zero : rookTheta.Adj 3 0 := by decide

theorem rookTheta_adj_three_two : rookTheta.Adj 3 2 := by decide

theorem rookTheta_adj_one_four : rookTheta.Adj 1 4 := by decide

theorem rookTheta_adj_one_five : rookTheta.Adj 1 5 := by decide

/-! ### Putting the deleted edge back -/

theorem rookTheta_sup_edge : rookTheta ⊔ SimpleGraph.edge (3 : Fin 6) 1 = k33Six := by
  ext a b
  simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  revert a b
  decide

theorem k33Six_iso : Nonempty (k33Six ≃g completeBipartiteGraph (Fin 3) (Fin 3)) :=
  Workspace.ProofLemmas.Thm61EvenEndgameHelpers.iso_completeBipartite_three_three
    ![0, 1, 2] ![3, 4, 5] (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- The bipartition of `rookTheta` that puts the two ends of the deleted edge on opposite
sides, with the column end `3` coloured `0`. -/
def rookColoring : rookTheta.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun v => if (v : ℕ) < 3 then 1 else 0) (by decide)

theorem rookColoring_three : rookColoring 3 = 0 := by decide

theorem rookColoring_one : rookColoring 1 = 1 := by decide

end Workspace.ProofLemmas.Thm61Claim12RookTheta
