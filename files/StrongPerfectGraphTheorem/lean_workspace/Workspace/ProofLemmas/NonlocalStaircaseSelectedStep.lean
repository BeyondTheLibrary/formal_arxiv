import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

/-!
# The selected step in the last paragraph of 12.2

This file isolates the choice made after claim (1) in the proof of 12.2.  The
first end of the minimal attachment path has a neighbour in `A ∪ C`, but it
is not complete to `A`.  Step-connectedness then supplies a step whose first
rung contains a neighbour away from its `B`-end and whose other `A`-end is a
nonneighbour.
-/

namespace Workspace.ProofLemmas.NonlocalStaircaseSelectedStep

open Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT

variable {V : Type*}

/-- Exchanging the two rungs of a step preserves the step. -/
theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [G.adj_comm, h.2.2.2 v hv u hu]
    tauto

/-- Every vertex of a rung lies in the strip. -/
theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hR : IsRungOfStrip G A C B a R b) :
    ∀ z ∈ R, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hR.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hR.2.2.1))
  · exact Or.inr (hR.2.2.2.2.2 z
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
        ⟨hz, hza, hzb⟩))

/-- PAPER (12.2, printed p. 72): *"By (1), we may assume there is a step
`a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` such that `f₁` has a neighbour in
`R₁ \ b₁`, and `a₂` is not adjacent to `f₁`."*

The proof follows the parenthetical argument in the paper.  Start with a step
containing a chosen neighbour in `A ∪ C`.  If the other `A`-end is adjacent
to `f₁`, split `A` into the neighbours and nonneighbours of `f₁` and use
the partition clause of step-connectedness. -/
theorem exists_selected_step [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (f₁ : V)
    (hS : StepConnected G A C B)
    (hattach : ∃ u ∈ A ∪ C, G.Adj f₁ u)
    (hnotComplete : ¬ VertexComplete G f₁ A) :
    ∃ (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧
      (∃ y ∈ R₁, y ≠ b₁ ∧ G.Adj f₁ y) ∧
      ¬ G.Adj f₁ a₂ := by
  classical
  obtain ⟨y, hyAC, hf₁y⟩ := hattach
  have hyS : y ∈ A ∪ B ∪ C := hyAC.elim
    (fun hyA => Or.inl (Or.inl hyA)) Or.inr
  obtain ⟨c₁, Q₁, d₁, c₂, Q₂, d₂, hstep₀, hyQ⟩ :=
    hS.2.2.2.1 y hyS
  obtain ⟨a₁, b₁, a₂, b₂, R₁, R₂, hstep, hyR₁⟩ :
      ∃ (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V),
        IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ y ∈ R₁ := by
    rcases hyQ with hyQ₁ | hyQ₂
    · exact ⟨c₁, d₁, c₂, d₂, Q₁, Q₂, hstep₀, hyQ₁⟩
    · exact ⟨c₂, d₂, c₁, d₁, Q₂, Q₁, step_symm hstep₀, hyQ₂⟩
  have hyb₁ : y ≠ b₁ := by
    intro hyb
    rcases hyAC with hyA | hyC
    · exact Set.disjoint_left.mp hS.1.1 hyA (hyb ▸ hstep.1.2.2.1)
    · exact Set.disjoint_left.mp hS.1.2.2 (hyb ▸ hstep.1.2.2.1) hyC
  by_cases hfa₂ : G.Adj f₁ a₂
  · have hnon : ∃ a ∈ A, ¬ G.Adj f₁ a := by
      by_contra h
      push Not at h
      exact hnotComplete h
    obtain ⟨a, haA, hfa⟩ := hnon
    let X : Set V := {x : V | x ∈ A ∧ G.Adj f₁ x}
    let Y : Set V := {x : V | x ∈ A ∧ ¬ G.Adj f₁ x}
    have hXY : X ∪ Y = A := by
      ext x
      simp only [X, Y, Set.mem_union, Set.mem_setOf_eq]
      tauto
    have hdisj : Disjoint X Y := Set.disjoint_left.2 (by
      intro x hxX hxY
      exact hxY.2 hxX.2)
    have hXne : X.Nonempty := ⟨a₂, hstep.2.1.2.1, hfa₂⟩
    have hYne : Y.Nonempty := ⟨a, haA, hfa⟩
    obtain ⟨p₁, P₁, q₁, p₂, P₂, q₂, hs, hendX, hendY⟩ :=
      hS.2.2.2.2 X Y (Or.inl hXY) hdisj hXne hYne
    have hp₁X : p₁ ∈ X := by
      rcases hendX with hp₁X | hq₁X
      · exact hp₁X
      · exact (Set.disjoint_left.mp hS.1.1 hq₁X.1 hs.1.2.2.1).elim
    have hp₂Y : p₂ ∈ Y := by
      rcases hendY with hp₂Y | hq₂Y
      · exact hp₂Y
      · exact (Set.disjoint_left.mp hS.1.1 hq₂Y.1 hs.2.1.2.2.1).elim
    have hp₁P₁ : p₁ ∈ P₁ :=
      Workspace.ProofLemmas.PathBasics.head_mem hs.1.1.2.1
    have hp₁q₁ : p₁ ≠ q₁ := by
      intro e
      exact Set.disjoint_left.mp hS.1.1 hp₁X.1 (e ▸ hs.1.2.2.1)
    exact ⟨p₁, q₁, p₂, q₂, P₁, P₂, hs,
      ⟨p₁, hp₁P₁, hp₁q₁, hp₁X.2⟩, hp₂Y.2⟩
  · exact ⟨a₁, b₁, a₂, b₂, R₁, R₂, hstep,
      ⟨y, hyR₁, hyb₁, hf₁y⟩, hfa₂⟩

end Workspace.ProofLemmas.NonlocalStaircaseSelectedStep
