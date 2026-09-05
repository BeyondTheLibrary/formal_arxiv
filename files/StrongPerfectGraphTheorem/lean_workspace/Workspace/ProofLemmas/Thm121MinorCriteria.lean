import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics

/-!
# The two "we may assume" reductions used inside the proof of 12.1

Both cases (3) and (4) of the printed proof of 12.1 open by discharging the vertices whose
neighbourhood in `V(K)` is too small to be interesting, with the phrase *"we may assume `v` has
a neighbour in `V(S)`"* (and, in case (3), *"we may assume it has a neighbour in `B ∪ C`, for
otherwise it is minor and statement 1 of the theorem holds"*).  In both situations the
neighbours of `v` in `V(K)` are confined to one of the four local sets, so `v` is minor, and the
two extra clauses of the published form of alternative 1 come for free:

* `v` has no neighbour in `B`, so it is certainly not `B`-complete;
* `v` is anticomplete to `B ∪ C`, so if it happens to be `A`-complete then it is by definition a
  left-star.

This module isolates the two reductions; they need only the strip axioms and the fact that
`R₀` is a banister, no numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm121MinorCriteria

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (case (3), and again case (4)): *"we may assume that `v` has a neighbour in `V(S)`,
for otherwise statement 1 of the theorem holds."*

If `v` has no neighbour at all in `V(S) = A ∪ B ∪ C`, then all its neighbours in `V(K)` lie on
`R₀`, so it is minor, and it is neither `A`-complete nor `B`-complete. -/
theorem thm121AltOneOfNoStripNeighbour (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V)
    (R₀ : List V) (hS : StepConnected G A C B) (v : V)
    (hv : v ∉ staircaseVertices A C B R₀)
    (hno : ∀ x ∈ A ∪ B ∪ C, ¬ G.Adj v x) :
    MinorForStaircase G A C B a₀ R₀ b₀ v ∧
      (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
      (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B) := by
  obtain ⟨a, haA⟩ := hS.2.1.1
  obtain ⟨b, hbB⟩ := hS.2.1.2
  refine ⟨⟨hv, Or.inr (Or.inl ?_)⟩, Or.inr ?_, Or.inr ?_⟩
  · rintro y ⟨hadj, hy | hy⟩
    · exact hy
    · exact absurd hadj (hno y hy)
  · exact fun hc => hno a (Or.inl (Or.inl haA)) (hc a haA)
  · exact fun hc => hno b (Or.inl (Or.inr hbB)) (hc b hbB)

/-- PAPER (case (3)): *"We may assume it has a neighbour in `B ∪ C`, for otherwise it is minor
and statement 1 of the theorem holds."*

The standing assumptions of that point of case (3) are that `v` is nonadjacent to `b₀` and has
no neighbour in `R₀*`; so a neighbour of `v` on `R₀` can only be `a₀`, and all its neighbours in
`V(K)` lie in `A ∪ {a₀}`. -/
theorem thm121AltOneOfNoNeighbourInBC (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V)
    (R₀ : List V) (hS : StepConnected G A C B)
    (hban : IsBanister G A C B a₀ R₀ b₀) (v : V)
    (hv : v ∉ staircaseVertices A C B R₀)
    (hBC : ∀ x ∈ B ∪ C, ¬ G.Adj v x)
    (hint : ∀ x ∈ SPGT.interior R₀, ¬ G.Adj v x)
    (hb : ¬ G.Adj v b₀) :
    MinorForStaircase G A C B a₀ R₀ b₀ v ∧
      (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
      (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B) := by
  obtain ⟨b, hbB⟩ := hS.2.1.2
  have hvS : v ∉ A ∪ B ∪ C := fun h => hv (Or.inr h)
  have hanti : SPGT.VertexAnticomplete G v (B ∪ C) := hBC
  refine ⟨⟨hv, Or.inr (Or.inr (Or.inl ?_))⟩, ?_, Or.inr ?_⟩
  · rintro y ⟨hadj, hy | hy⟩
    · -- a neighbour of `v` on `R₀` is neither in `R₀*` nor `b₀`, hence is `a₀`
      by_cases hya : y = a₀
      · exact Or.inr hya
      · have hyb : y ≠ b₀ := fun h => hb (h ▸ hadj)
        exact absurd hadj
          (hint y
            ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr
              ⟨hy, hya, hyb⟩))
    · rcases hy with hy | hy
      · rcases hy with hy | hy
        · exact Or.inl hy
        · exact absurd hadj (hBC y (Or.inl hy))
      · exact absurd hadj (hBC y (Or.inr hy))
  · by_cases hAc : SPGT.VertexComplete G v A
    · exact Or.inl ⟨hvS, hAc, hanti⟩
    · exact Or.inr hAc
  · exact fun hc => hBC b (Or.inl hbB) (hc b hbB)

end Workspace.ProofLemmas.Thm121MinorCriteria
