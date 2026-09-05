import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics

/-!
# The symmetry invoked at the end of the printed proof of 12.1
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm121Symmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

/-- Exchanging the two ends of the strip does not change `V(K)`. -/
theorem thm121SwapVertices {V : Type*} (A C B : Set V) (R₀ : List V) :
    staircaseVertices B C A R₀.reverse = staircaseVertices A C B R₀ := by
  ext x
  simp only [staircaseVertices, Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
  tauto

section Helpers

variable {V : Type*} {G : SimpleGraph V} {A C B : Set V}

private theorem union_comm3 (X Y Z : Set V) : X ∪ Y ∪ Z = Y ∪ X ∪ Z := by
  rw [Set.union_comm X Y]

private theorem rung_swap {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : IsRungOfStrip G B C A b p.reverse a := by
  obtain ⟨hp, haA, hbB, hA, hB, hC⟩ := h
  refine ⟨PathBasics.isPathFrom_reverse hp, hbB, haA, ?_, ?_, ?_⟩
  · intro w hw hwB
    exact hB w (List.mem_reverse.mp hw) hwB
  · intro w hw hwA
    exact hA w (List.mem_reverse.mp hw) hwA
  · intro w hw
    exact hC w (PathBasics.mem_interior_reverse.mp hw)

private theorem step_swap {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G B C A b₁ R₁.reverse a₁ b₂ R₂.reverse a₂ := by
  obtain ⟨h1, h2, hdisj, hadj⟩ := h
  refine ⟨rung_swap h1, rung_swap h2, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_reverse] at hx ⊢
    exact hdisj x hx
  · intro u hu w hw
    simp only [List.mem_reverse] at hu hw
    have := hadj u hu w hw
    tauto

private theorem stepConnected_swap (h : StepConnected G A C B) : StepConnected G B C A := by
  obtain ⟨⟨dAB, dAC, dBC⟩, ⟨hA, hB⟩, hrung, hstep, hpart⟩ := h
  refine ⟨⟨dAB.symm, dBC, dAC⟩, ⟨hB, hA⟩, ?_, ?_, ?_⟩
  · intro w hw
    rw [union_comm3 B A C] at hw
    obtain ⟨a, p, b, hr, hwp⟩ := hrung w hw
    exact ⟨b, p.reverse, a, rung_swap hr, List.mem_reverse.mpr hwp⟩
  · intro w hw
    rw [union_comm3 B A C] at hw
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hm⟩ := hstep w hw
    refine ⟨b₁, R₁.reverse, a₁, b₂, R₂.reverse, a₂, step_swap hs, ?_⟩
    simpa [List.mem_reverse] using hm
  · intro X Y hXY hd hXne hYne
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hx, hy⟩ := hpart X Y hXY.symm hd hXne hYne
    exact ⟨b₁, R₁.reverse, a₁, b₂, R₂.reverse, a₂, step_swap hs, hx.symm, hy.symm⟩

private theorem leftStar_swap {v : V} (h : IsLeftStar G A C B v) :
    IsRightStar G B C A v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  rw [union_comm3 B A C]
  exact h1

private theorem rightStar_swap {v : V} (h : IsRightStar G A C B v) :
    IsLeftStar G B C A v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  rw [union_comm3 B A C]
  exact h1

private theorem banister_swap {a b : V} {R : List V} (h : IsBanister G A C B a R b) :
    IsBanister G B C A b R.reverse a := by
  obtain ⟨hp, hnot, hls, hrs, hac⟩ := h
  refine ⟨PathBasics.isPathFrom_reverse hp, ?_, rightStar_swap hrs, leftStar_swap hls, ?_⟩
  · intro w hw
    rw [union_comm3 B A C]
    exact hnot w (List.mem_reverse.mp hw)
  · intro x hx
    have hx' : x ∈ SPGT.interior R := PathBasics.mem_interior_reverse.mp hx
    rw [union_comm3 B A C]
    exact hac x hx'

private theorem isStaircase_swap {a₀ b₀ : V} {R₀ : List V}
    (h : IsStaircase G A C B a₀ R₀ b₀) : IsStaircase G B C A b₀ R₀.reverse a₀ := by
  refine ⟨stepConnected_swap h.1, banister_swap h.2.1, ?_⟩
  rw [PathBasics.pathLength_reverse]
  exact h.2.2

private theorem minor_swap {a₀ b₀ v : V} {R₀ : List V}
    (h : MinorForStaircase G B C A b₀ R₀.reverse a₀ v) :
    MinorForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨h1, h2⟩ := h
  rw [thm121SwapVertices A C B R₀] at h1 h2
  simp only [LocalForStaircase] at h2 ⊢
  refine ⟨h1, ?_⟩
  rcases h2 with hh | hh | hh | hh
  · exact Or.inl (by rwa [union_comm3 B A C] at hh)
  · refine Or.inr (Or.inl ?_)
    intro x hx
    simpa using hh hx
  · exact Or.inr (Or.inr (Or.inr hh))
  · exact Or.inr (Or.inr (Or.inl hh))

private theorem major_swap {a₀ b₀ v : V} {R₀ : List V}
    (h : MajorForStaircase G B C A b₀ R₀.reverse a₀ v) :
    MajorForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨h1, hB, hA, hR⟩ := h
  rw [thm121SwapVertices A C B R₀] at h1
  obtain ⟨z, hz, hzz⟩ := hR
  exact ⟨h1, hA, hB, z, List.mem_reverse.mp hz, hzz⟩

private theorem leftDiag_swap {a₀ b₀ v : V} {R₀ : List V}
    (h : LeftDiagonal G B C A b₀ R₀.reverse a₀ v) :
    RightDiagonal G A C B a₀ R₀ b₀ v := by
  obtain ⟨h1, h2⟩ := h
  rw [thm121SwapVertices A C B R₀] at h1
  exact ⟨h1, h2⟩

private theorem rightDiag_swap {a₀ b₀ v : V} {R₀ : List V}
    (h : RightDiagonal G B C A b₀ R₀.reverse a₀ v) :
    LeftDiagonal G A C B a₀ R₀ b₀ v := by
  obtain ⟨h1, h2⟩ := h
  rw [thm121SwapVertices A C B R₀] at h1
  exact ⟨h1, h2⟩

private theorem central_swap {a₀ b₀ v : V} {R₀ : List V}
    (h : CentralForStaircase G B C A b₀ R₀.reverse a₀ v) :
    CentralForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [thm121SwapVertices A C B R₀] at h1
  refine ⟨h1, ?_, h4, h3⟩
  rw [Set.union_comm A B]
  exact h2

end Helpers

/-- Exchanging the two ends of the strip carries a maximal staircase to a maximal staircase:
a left-star for `(A, C, B)` is exactly a right-star for `(B, C, A)`, so the banister
`a₀`-`R₀`-`b₀` becomes the banister `b₀`-`R₀ᵣ`-`a₀`, and `V(S)` is unchanged. -/
theorem thm121SwapStaircase {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀) :
    MaximalStaircase G B C A b₀ R₀.reverse a₀ := by
  refine ⟨isStaircase_swap hK.1, ?_⟩
  rintro ⟨A', C', B', a₀', R₀', b₀', hst, hBA', hAB', hCC', hsub⟩
  refine hK.2 ⟨B', C', A', b₀', R₀'.reverse, a₀', isStaircase_swap hst, hAB', hBA', hCC', ?_⟩
  rw [union_comm3 B' A' C']
  rw [union_comm3 B A C] at hsub
  exact hsub

/-- Exchanging the two ends of the strip permutes the three alternatives of 12.1 among
themselves: it fixes alternative 1 (swapping its two conjuncts), fixes alternative 2 (swapping
left- and right-diagonal), and swaps the two disjuncts of alternative 3. -/
theorem thm121SwapConclusion {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V) (v : V)
    (h :
      (MinorForStaircase G B C A b₀ R₀.reverse a₀ v ∧
          (IsLeftStar G B C A v ∨ ¬ SPGT.VertexComplete G v B) ∧
          (IsRightStar G B C A v ∨ ¬ SPGT.VertexComplete G v A)) ∨
        (MajorForStaircase G B C A b₀ R₀.reverse a₀ v ∧
          (LeftDiagonal G B C A b₀ R₀.reverse a₀ v ∨
            RightDiagonal G B C A b₀ R₀.reverse a₀ v ∨
            CentralForStaircase G B C A b₀ R₀.reverse a₀ v)) ∨
        ((IsLeftStar G B C A v ∧ ∃ x ∈ R₀.reverse, x ≠ b₀ ∧ G.Adj v x) ∨
          (IsRightStar G B C A v ∧ ∃ x ∈ R₀.reverse, x ≠ a₀ ∧ G.Adj v x))) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  rcases h with ⟨hmin, h2, h3⟩ | ⟨hmaj, hd⟩ | (⟨hls, hx⟩ | ⟨hrs, hx⟩)
  · exact Or.inl ⟨minor_swap hmin, h3.imp rightStar_swap id, h2.imp leftStar_swap id⟩
  · refine Or.inr (Or.inl ⟨major_swap hmaj, ?_⟩)
    rcases hd with hd | hd | hd
    · exact Or.inr (Or.inl (leftDiag_swap hd))
    · exact Or.inl (rightDiag_swap hd)
    · exact Or.inr (Or.inr (central_swap hd))
  · refine Or.inr (Or.inr (Or.inr ⟨leftStar_swap hls, ?_⟩))
    obtain ⟨x, hx1, hx2, hx3⟩ := hx
    exact ⟨x, List.mem_reverse.mp hx1, hx2, hx3⟩
  · refine Or.inr (Or.inr (Or.inl ⟨rightStar_swap hrs, ?_⟩))
    obtain ⟨x, hx1, hx2, hx3⟩ := hx
    exact ⟨x, List.mem_reverse.mp hx1, hx2, hx3⟩

end Workspace.ProofLemmas.Thm121Symmetry
