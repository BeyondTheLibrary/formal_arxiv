import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

/-!
# Left–right symmetry of a staircase

PAPER (§13, printed p. 84, in the proof of 13.4): *"… and therefore from the
symmetry we may assume that `X` meets `A ∪ C`."*

The proof of 13.4 uses "the symmetry" twice — once inside (1) and once in the
"and similarly every `B`-complete vertex is in `B₀ ∪ N`" of the paragraph before
it.  The symmetry in question is the one that exchanges the two ends of the
strip and of the banister: a staircase
`K = (S = (A, C, B), a₀-R₀-b₀)` read backwards is the staircase
`(S' = (B, C, A), b₀-R₀ʳ-a₀)`, under which left-stars become right-stars and
vice versa.  This file makes that transport explicit; every clause is a purely
definitional unfolding, using only that `∪` is commutative on the two outer
sets, that reversal preserves paths (`PathBasics.isPathFrom_reverse`), list
membership (`List.mem_reverse`), interiors (`PathBasics.mem_interior_reverse`)
and lengths (`PathBasics.pathLength_reverse`).
-/

namespace Workspace.ProofLemmas.StaircaseLeftRightSymmetry

open Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT

variable {V : Type*}

/-- `V(S) = A ∪ B ∪ C` does not see the order of the two ends of the strip. -/
private theorem union3_comm (A B C : Set V) : A ∪ B ∪ C = B ∪ A ∪ C := by
  rw [Set.union_comm A B]

/-- A rung read backwards is a rung of the reversed strip. -/
private theorem rung_swap {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : IsRungOfStrip G B C A b p.reverse a := by
  obtain ⟨hp, ha, hb, hA, hB, hC⟩ := h
  refine ⟨PathBasics.isPathFrom_reverse hp, hb, ha, ?_, ?_, ?_⟩
  · intro w hw hwB
    exact hB w (List.mem_reverse.mp hw) hwB
  · intro w hw hwA
    exact hA w (List.mem_reverse.mp hw) hwA
  · intro w hw
    exact hC w (PathBasics.mem_interior_reverse.mp hw)

/-- A step read backwards is a step of the reversed strip. -/
private theorem step_swap {G : SimpleGraph V} {A C B : Set V} {a₁ b₁ a₂ b₂ : V}
    {R₁ R₂ : List V} (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G B C A b₁ R₁.reverse a₁ b₂ R₂.reverse a₂ := by
  obtain ⟨hr1, hr2, hdisj, hadj⟩ := h
  refine ⟨rung_swap hr1, rung_swap hr2, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_reverse] at hv ⊢
    exact hdisj v hv
  · intro u hu v hv
    simp only [List.mem_reverse] at hu hv
    exact (hadj u hu v hv).trans or_comm

/-- A step-connected strip stays step-connected when its two ends are exchanged. -/
private theorem stepConnected_swap {G : SimpleGraph V} {A C B : Set V}
    (h : StepConnected G A C B) : StepConnected G B C A := by
  obtain ⟨⟨hAB, hAC, hBC⟩, ⟨hAne, hBne⟩, hrung, hstep, hpart⟩ := h
  refine ⟨⟨hAB.symm, hBC, hAC⟩, ⟨hBne, hAne⟩, ?_, ?_, ?_⟩
  · intro v hv
    rw [union3_comm B A C] at hv
    obtain ⟨a, p, b, hr, hvp⟩ := hrung v hv
    exact ⟨b, p.reverse, a, rung_swap hr, List.mem_reverse.mpr hvp⟩
  · intro v hv
    rw [union3_comm B A C] at hv
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hv'⟩ := hstep v hv
    exact ⟨b₁, R₁.reverse, a₁, b₂, R₂.reverse, a₂, step_swap hs,
      hv'.imp List.mem_reverse.mpr List.mem_reverse.mpr⟩
  · intro X Y hXY hd hX hY
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, h1, h2⟩ := hpart X Y hXY.symm hd hX hY
    exact ⟨b₁, R₁.reverse, a₁, b₂, R₂.reverse, a₂, step_swap hs, h1.symm, h2.symm⟩

/-- Left-stars of `(A, C, B)` are exactly the right-stars of `(B, C, A)`. -/
theorem isLeftStar_swap {G : SimpleGraph V} {A C B : Set V} {v : V} :
    IsLeftStar G A C B v ↔ IsRightStar G B C A v := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C], h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C] at h1, h2, h3⟩

/-- Right-stars of `(A, C, B)` are exactly the left-stars of `(B, C, A)`. -/
theorem isRightStar_swap {G : SimpleGraph V} {A C B : Set V} {v : V} :
    IsRightStar G A C B v ↔ IsLeftStar G B C A v := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C], h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rwa [union3_comm B A C] at h1, h2, h3⟩

/-- A banister read backwards is a banister of the reversed strip. -/
private theorem banister_swap {G : SimpleGraph V} {A C B : Set V} {a b : V} {R : List V}
    (h : IsBanister G A C B a R b) : IsBanister G B C A b R.reverse a := by
  obtain ⟨hp, hnot, hls, hrs, hanti⟩ := h
  refine ⟨PathBasics.isPathFrom_reverse hp, ?_, isRightStar_swap.mp hrs,
    isLeftStar_swap.mp hls, ?_⟩
  · intro v hv
    rw [List.mem_reverse] at hv
    rw [union3_comm B A C]
    exact hnot v hv
  · intro x hx
    rw [union3_comm B A C]
    exact hanti x (by simpa using PathBasics.mem_interior_reverse.mp hx)

/-- `V(K)` does not see the order of the two ends. -/
private theorem sv_swap (A C B : Set V) (R₀ : List V) :
    staircaseVertices B C A R₀.reverse = staircaseVertices A C B R₀ := by
  ext v
  simp only [staircaseVertices, Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
  tauto

/-- A staircase read backwards is a staircase. -/
private theorem staircase_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (h : IsStaircase G A C B a₀ R₀ b₀) : IsStaircase G B C A b₀ R₀.reverse a₀ := by
  obtain ⟨hsc, hban, hlen⟩ := h
  exact ⟨stepConnected_swap hsc, banister_swap hban, by
    rwa [PathBasics.pathLength_reverse]⟩

theorem isStaircase_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} :
    IsStaircase G A C B a₀ R₀ b₀ ↔ IsStaircase G B C A b₀ R₀.reverse a₀ := by
  refine ⟨staircase_swap, fun h => ?_⟩
  have := staircase_swap h
  rwa [List.reverse_reverse] at this

/-- Maximality is invariant under the left–right exchange. -/
private theorem maximal_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (h : MaximalStaircase G A C B a₀ R₀ b₀) :
    MaximalStaircase G B C A b₀ R₀.reverse a₀ := by
  obtain ⟨hst, hmax⟩ := h
  refine ⟨staircase_swap hst, ?_⟩
  rintro ⟨A', C', B', a₀', R₀', b₀', hst', hA, hB, hC, hlt⟩
  refine hmax ⟨B', C', A', b₀', R₀'.reverse, a₀', staircase_swap hst', hB, hA, hC, ?_⟩
  rw [union3_comm A B C, union3_comm B' A' C']
  exact hlt

theorem maximalStaircase_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} :
    MaximalStaircase G A C B a₀ R₀ b₀ ↔ MaximalStaircase G B C A b₀ R₀.reverse a₀ := by
  refine ⟨maximal_swap, fun h => ?_⟩
  have := maximal_swap h
  rwa [List.reverse_reverse] at this

/-- Strong maximality is invariant under the left–right exchange. -/
private theorem stronglyMaximal_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} (h : StronglyMaximalStaircase G A C B a₀ R₀ b₀) :
    StronglyMaximalStaircase G B C A b₀ R₀.reverse a₀ := by
  obtain ⟨hmax, hstrong⟩ := h
  refine ⟨maximal_swap hmax, ?_⟩
  rcases hstrong with hC | hno
  · exact Or.inl hC
  · refine Or.inr ?_
    rintro ⟨A', C', B', a₀', R', b₀', hst', hlt⟩
    exact hno ⟨A', C', B', a₀', R', b₀', hst', by rwa [union3_comm A B C]⟩

theorem stronglyMaximalStaircase_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} :
    StronglyMaximalStaircase G A C B a₀ R₀ b₀ ↔
      StronglyMaximalStaircase G B C A b₀ R₀.reverse a₀ := by
  refine ⟨stronglyMaximal_swap, fun h => ?_⟩
  have := stronglyMaximal_swap h
  rwa [List.reverse_reverse] at this

/-- Being major is invariant under the left–right exchange. -/
theorem majorForStaircase_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {v : V} :
    MajorForStaircase G A C B a₀ R₀ b₀ v ↔ MajorForStaircase G B C A b₀ R₀.reverse a₀ v := by
  simp only [MajorForStaircase, sv_swap, List.mem_reverse]
  constructor
  · rintro ⟨h0, hA, hB, hR⟩; exact ⟨h0, hB, hA, hR⟩
  · rintro ⟨h0, hB, hA, hR⟩; exact ⟨h0, hA, hB, hR⟩

theorem staircaseLeftRightSymmetry
    {V : Type*} (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V) (v : V) :
    (IsStaircase G A C B a₀ R₀ b₀ ↔ IsStaircase G B C A b₀ R₀.reverse a₀) ∧
    (MaximalStaircase G A C B a₀ R₀ b₀ ↔ MaximalStaircase G B C A b₀ R₀.reverse a₀) ∧
    (StronglyMaximalStaircase G A C B a₀ R₀ b₀ ↔
      StronglyMaximalStaircase G B C A b₀ R₀.reverse a₀) ∧
    (IsLeftStar G A C B v ↔ IsRightStar G B C A v) ∧
    (IsRightStar G A C B v ↔ IsLeftStar G B C A v) ∧
    (MajorForStaircase G A C B a₀ R₀ b₀ v ↔
      MajorForStaircase G B C A b₀ R₀.reverse a₀ v) :=
  ⟨isStaircase_swap, maximalStaircase_swap, stronglyMaximalStaircase_swap,
    isLeftStar_swap, isRightStar_swap, majorForStaircase_swap⟩

end Workspace.ProofLemmas.StaircaseLeftRightSymmetry
