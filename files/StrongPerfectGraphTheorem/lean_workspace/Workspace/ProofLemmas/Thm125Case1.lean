import Workspace.ProofLemmas.Thm125Setup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm125Case1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Part (1) of the printed proof of 12.5. -/
theorem case1
    (G : SimpleGraph V) (hG : Berge G)
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : G.Adj q₁ a₀) (hqkb₀ : G.Adj qk b₀) :
    IsLeftStar G A C B q₁ ∧ IsRightStar G A C B qk := by
  classical
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hban := hstair.2.1
  have hodd : Odd (pathLength R₀) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG hprism A C B hstair.1
      a₀ b₀ R₀ hban).2
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have ha₀Q : VertexComplete G a₀ {z : V | z ∈ q} := by
    intro z hz
    by_cases hz₁ : z = q₁
    · simpa [hz₁] using hqa₀.symm
    exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 a₀
      (Or.inr rfl)).symm
  have hb₀Q : VertexComplete G b₀ {z : V | z ∈ q} := by
    intro z hz
    by_cases hzk : z = qk
    · simpa [hzk] using hqkb₀.symm
    exact ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hzk).2 b₀
      (Or.inr rfl)).symm
  have hmissB : ∃ b ∈ B, ¬ G.Adj q₁ b := by
    by_contra hno
    push_neg at hno
    apply hq₁.2
    refine ⟨hq₁.1.1, ?_⟩
    rintro z (hzB | rfl)
    · exact hno z hzB
    · exact hqa₀
  have hmissA : ∃ a ∈ A, ¬ G.Adj qk a := by
    by_contra hno
    push_neg at hno
    apply hqk.2
    refine ⟨hqk.1.1, ?_⟩
    rintro z (hzA | rfl)
    · exact hno z hzA
    · exact hqkb₀
  have hqF : ∀ z ∈ q, ∃ f ∈ interior R₀, G.Adj z f := by
    intro z hz
    exact exists_interior_neighbour hG hban hstair.2.2 hodd
      (fun hzR => outside_of_mem hq hqint hq₁.1 hqk.1 hz (Or.inl hzR))
      (ha₀Q z hz).symm (hb₀Q z hz).symm
  exact stars_of_complete_ends_and_interior_neighbours G hbreaker A C B a₀ b₀ R₀ hK
    q q₁ qk hq hqint hq₁ hqk ha₀Q hb₀Q hqF hmissB hmissA

end Workspace.ProofLemmas.Thm125Case1
