import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.Statements.S16.Thm_16_1
import Workspace.Statements.S22.Thm_22_3

/-!
# 23.2 — two opposite, nonadjacent neighbours

This is the consequence of 16.1 used in step (3).  The paper checks its three alternatives
locally.  The first alternative cannot contain two nonadjacent neighbours.  In the second,
three consecutive `Y`-complete neighbours either make a kite or exhaust the rim-neighbours;
in the latter case the two nonadjacent neighbours are the ends of that three-vertex path and
have the same wheel-parity.  The last alternative contradicts optimality.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232OppositeNeighbours

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem mem_rim_of_block {C : List V} {a b c : V}
    (hblock : ∃ k : ℕ, [a, b, c] <+: C.rotate k ∨ [c, b, a] <+: C.rotate k) :
    a ∈ C ∧ b ∈ C ∧ c ∈ C := by
  obtain ⟨k, h | h⟩ := hblock
  · exact ⟨List.mem_rotate.mp (h.subset (by simp)),
      List.mem_rotate.mp (h.subset (by simp)), List.mem_rotate.mp (h.subset (by simp))⟩
  · exact ⟨List.mem_rotate.mp (h.subset (by simp)),
      List.mem_rotate.mp (h.subset (by simp)), List.mem_rotate.mp (h.subset (by simp))⟩

private theorem four_neighbours_of_extra {G : SimpleGraph V} {C : List V}
    {v p₁ p₂ p₃ r : V} (hP : IsPathList G [p₁, p₂, p₃])
    (hp₁C : p₁ ∈ C) (hp₂C : p₂ ∈ C) (hp₃C : p₃ ∈ C) (hrC : r ∈ C)
    (hvp₁ : G.Adj v p₁) (hvp₂ : G.Adj v p₂) (hvp₃ : G.Adj v p₃) (hvr : G.Adj v r)
    (hr : r ∉ ({p₁, p₂, p₃} : Set V)) :
    4 ≤ {c : V | c ∈ C ∧ G.Adj v c}.ncard := by
  have hnd : ([p₁, p₂, p₃] : List V).Nodup := hP.2.1
  have h12 : p₁ ≠ p₂ := by intro h; subst p₂; simp at hnd
  have h13 : p₁ ≠ p₃ := by intro h; subst p₃; simp at hnd
  have h23 : p₂ ≠ p₃ := by intro h; subst p₃; simp at hnd
  have hr1 : r ≠ p₁ := by intro h; apply hr; simp [h]
  have hr2 : r ≠ p₂ := by intro h; apply hr; simp [h]
  have hr3 : r ≠ p₃ := by intro h; apply hr; simp [h]
  have hcard : ({p₁, p₂, p₃, r} : Set V).ncard = 4 := by
    simp [h12, h13, h23, Ne.symm hr1, Ne.symm hr2, Ne.symm hr3]
  have hsub : ({p₁, p₂, p₃, r} : Set V) ⊆ {c : V | c ∈ C ∧ G.Adj v c} := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨hp₁C, hvp₁⟩
    · exact ⟨hp₂C, hvp₂⟩
    · exact ⟨hp₃C, hvp₃⟩
    · exact ⟨hrC, hvr⟩
  rw [← hcard]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- PAPER (23.2, step (3), use of 16.1): a vertex outside an optimal wheel cannot have two
nonadjacent rim-neighbours of opposite wheel-parity. -/
theorem impossible (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (v a b : V) (hvC : v ∉ C) (hvY : v ∉ Y) (hvnc : ¬ VertexComplete G v Y)
    (haC : a ∈ C) (hbC : b ∈ C) (hva : G.Adj v a) (hvb : G.Adj v b)
    (hnab : ¬ G.Adj a b) (hopp : OppositeWheelParity G C Y a b) : False := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hBerge : Berge G := hG.1.1.1.1.1
  have hnokite : ¬ ∃ q : V, IsKite G C Y q :=
    _root_.Workspace.Statements.S22.SPGT.thm_22_3 G hG hbsp C Y hopt
  have htri := _root_.Workspace.Statements.S16.SPGT.thm_16_1
    G hG.1.1 C Y hw v hvC hvY hvnc a b hva hvb hopp
  rcases htri.2 with ⟨a₁, a₂, ha₁a₂, hneighbors, ha₁a₂adj, -, -⟩ |
      ⟨p₁, p₂, p₃, hP, hblock, hp₁, hp₂, hp₃, -⟩ | hlarger
  · have hamem : a ∈ ({a₁, a₂} : Set V) := by
      rw [← hneighbors]
      exact ⟨haC, hva⟩
    have hbmem : b ∈ ({a₁, a₂} : Set V) := by
      rw [← hneighbors]
      exact ⟨hbC, hvb⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hamem hbmem
    rcases hamem with rfl | rfl <;> rcases hbmem with rfl | rfl
    · exact hopp.1 rfl
    · exact hnab ha₁a₂adj
    · exact hnab ha₁a₂adj.symm
    · exact hopp.1 rfl
  · obtain ⟨hp₁C, hp₂C, hp₃C⟩ := mem_rim_of_block hblock
    have hvp₁ : G.Adj v p₁ := (hp₁ v (Or.inr rfl)).symm
    have hvp₂ : G.Adj v p₂ := (hp₂ v (Or.inr rfl)).symm
    have hvp₃ : G.Adj v p₃ := (hp₃ v (Or.inr rfl)).symm
    by_cases hfour : 4 ≤ {c : V | c ∈ C ∧ G.Adj v c}.ncard
    · apply hnokite
      refine ⟨v, hw, hvY, hvC, hvnc, hfour, ?_⟩
      obtain ⟨q, hq | hq⟩ := hblock
      · exact ⟨p₁, p₂, p₃, ⟨q, hq⟩, hvp₁, hvp₂, hvp₃,
          fun x hx => hp₁ x (Or.inl hx), fun x hx => hp₂ x (Or.inl hx),
          fun x hx => hp₃ x (Or.inl hx)⟩
      · exact ⟨p₃, p₂, p₁, ⟨q, hq⟩, hvp₃, hvp₂, hvp₁,
          fun x hx => hp₃ x (Or.inl hx), fun x hx => hp₂ x (Or.inl hx),
          fun x hx => hp₁ x (Or.inl hx)⟩
    · have haP : a ∈ ({p₁, p₂, p₃} : Set V) := by
        by_contra ha
        exact hfour (four_neighbours_of_extra hP hp₁C hp₂C hp₃C haC
          hvp₁ hvp₂ hvp₃ hva ha)
      have hbP : b ∈ ({p₁, p₂, p₃} : Set V) := by
        by_contra hb
        exact hfour (four_neighbours_of_extra hP hp₁C hp₂C hp₃C hbC
          hvp₁ hvp₂ hvp₃ hvb hb)
      have hnd : ([p₁, p₂, p₃] : List V).Nodup := hP.2.1
      have h12 : p₁ ≠ p₂ := by intro h; subst p₂; simp at hnd
      have h13 : p₁ ≠ p₃ := by intro h; subst p₃; simp at hnd
      have h23 : p₂ ≠ p₃ := by intro h; subst p₃; simp at hnd
      have heven := Workspace.ProofLemmas.WheelBasics.even_cycCount_of_wheel hBerge hw
      obtain ⟨π, hπlt, hπ⟩ :=
        Workspace.ProofLemmas.OddWheelParityFacts.exists_parity' hC heven
      have hE12 : EdgeComplete G Y p₁ p₂ :=
        ⟨by simpa using Workspace.ProofLemmas.PathBasics.path_adj_succ hP (i := 0) (by simp),
          fun x hx => hp₁ x (Or.inl hx), fun x hx => hp₂ x (Or.inl hx)⟩
      have hE23 : EdgeComplete G Y p₂ p₃ :=
        ⟨by simpa using Workspace.ProofLemmas.PathBasics.path_adj_succ hP (i := 1) (by simp),
          fun x hx => hp₂ x (Or.inl hx), fun x hx => hp₃ x (Or.inl hx)⟩
      have hpi12 : π p₁ ≠ π p₂ := fun heq =>
        (Workspace.ProofLemmas.OddWheelParityFacts.not_sameWheelParity_of_edgeComplete
          hC heven hp₁C hp₂C hE12) ((hπ p₁ p₂ hp₁C hp₂C h12).mpr heq)
      have hpi23 : π p₂ ≠ π p₃ := fun heq =>
        (Workspace.ProofLemmas.OddWheelParityFacts.not_sameWheelParity_of_edgeComplete
          hC heven hp₂C hp₃C hE23) ((hπ p₂ p₃ hp₂C hp₃C h23).mpr heq)
      have hpi13 : π p₁ = π p₃ := by
        have hp₁lt := hπlt p₁
        have hp₂lt := hπlt p₂
        have hp₃lt := hπlt p₃
        omega
      have hsame13 : SameWheelParity G C Y p₁ p₃ :=
        (hπ p₁ p₃ hp₁C hp₃C h13).mpr hpi13
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at haP hbP
      rcases haP with rfl | rfl | rfl <;> rcases hbP with rfl | rfl | rfl
      · exact hopp.1 rfl
      · exact hnab hE12.1
      · exact hopp.2.2.2 hsame13
      · exact hnab hE12.1.symm
      · exact hopp.1 rfl
      · exact hnab hE23.1
      · exact hopp.2.2.2 (Workspace.ProofLemmas.WheelParity.sameWheelParity_symm hsame13)
      · exact hnab hE23.1.symm
      · exact hopp.1 rfl
  · exact hopt.2 ⟨C, Y ∪ {v}, hlarger,
      Workspace.ProofLemmas.KiteTailBasics.ssubset_union_singleton hvY⟩

end Workspace.ProofLemmas.Thm232OppositeNeighbours
