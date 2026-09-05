import Workspace.Statements.S12.Thm_12_1
import Workspace.Statements.S11.Thm_11_3
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Common setup for Theorem 12.5

This file contains the elementary list bookkeeping and the direct `1`-breaker
construction used in parts (1) and (2) of the printed proof of 12.5.  In
particular, it does not appeal to 11.4: the breaker prohibited by the hypotheses
is assembled directly from the interior of the old banister and the given
antipath.
-/

namespace Workspace.ProofLemmas.Thm125Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two specially classified ends of the antipath are distinct. -/
theorem endpoint_ne
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ q : List V} {q₁ qk : V}
    (hq : IsAntipathFrom G q q₁ qk)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk) :
    q₁ ≠ qk := by
  intro he
  exact hqk.2 (he ▸ hq₁.1)

/-- Every antipath vertex other than its last one inherits left-diagonality. -/
theorem leftDiagonal_of_mem_ne_last
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ q : List V} {q₁ qk w : V}
    (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ z ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ z ∧
        RightDiagonal G A C B a₀ R₀ b₀ z)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁)
    (hwq : w ∈ q) (hwk : w ≠ qk) :
    LeftDiagonal G A C B a₀ R₀ b₀ w := by
  by_cases hw₁ : w = q₁
  · simpa [hw₁] using hq₁
  · exact (hqint w ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).2
      ⟨hwq, hw₁, hwk⟩)).1

/-- Every antipath vertex other than its first one inherits right-diagonality. -/
theorem rightDiagonal_of_mem_ne_first
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ q : List V} {q₁ qk w : V}
    (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ z ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ z ∧
        RightDiagonal G A C B a₀ R₀ b₀ z)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk)
    (hwq : w ∈ q) (hw₁ : w ≠ q₁) :
    RightDiagonal G A C B a₀ R₀ b₀ w := by
  by_cases hwk : w = qk
  · simpa [hwk] using hqk
  · exact (hqint w ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).2
      ⟨hwq, hw₁, hwk⟩)).2

/-- All vertices of the displayed antipath lie outside the staircase. -/
theorem outside_of_mem
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ q : List V} {q₁ qk w : V}
    (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ z ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ z ∧
        RightDiagonal G A C B a₀ R₀ b₀ z)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk)
    (hwq : w ∈ q) : w ∉ staircaseVertices A C B R₀ := by
  by_cases hw₁ : w = q₁
  · simpa [hw₁] using hq₁.1
  by_cases hwk : w = qk
  · simpa [hwk] using hqk.1
  exact (hqint w ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).2
    ⟨hwq, hw₁, hwk⟩)).1.1

/-- A vertex outside a banister and adjacent to both its ends has an interior
neighbour when the banister has odd length.  Otherwise it closes the banister
to an odd hole. -/
theorem exists_interior_neighbour
    {G : SimpleGraph V} (hG : Berge G) {A C B : Set V} {a₀ b₀ z : V} {R₀ : List V}
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (hR3 : 3 ≤ pathLength R₀) (hodd : Odd (pathLength R₀))
    (hzout : z ∉ R₀) (hza : G.Adj z a₀) (hzb : G.Adj z b₀) :
    ∃ w ∈ interior R₀, G.Adj z w := by
  by_contra hno
  push_neg at hno
  have hR4 : 4 ≤ R₀.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hR3
    omega
  have heven := Workspace.ProofLemmas.PrismBasics.even_of_path_closed_by_vertex
    hG hban.1 hR4 hzout hza hzb hno
  obtain ⟨ko, hko⟩ := hodd
  obtain ⟨ke, hke⟩ := heven
  rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hko
  omega

/-- The final logical step in the one-sided 1-breaker argument: if every
possible clause of a 1-breaker has been verified and the only possible
left-star in `Q` is `q₁`, then `q₁` must be a left-star. -/
theorem designated_leftStar_of_no_oneBreaker
    (G : SimpleGraph V)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B F Q : Set V) (q₁ : V)
    (hS : StepConnected G A C B)
    (hF : (∀ z ∈ F, z ∉ A ∪ B ∪ C) ∧ ConnectedSet G F ∧
      Anticomplete G F (A ∪ B ∪ C) ∧
      (∃ u, IsLeftStar G A C B u ∧ ∃ f ∈ F, G.Adj u f) ∧
      (∃ w, IsRightStar G A C B w ∧ ∃ f ∈ F, G.Adj w f))
    (hQ : (∀ z ∈ Q, z ∉ (A ∪ B ∪ C) ∪ F) ∧ AnticonnectedSet G Q)
    (hmiss : (∃ a ∈ A, ∃ z ∈ Q, ¬ G.Adj a z) ∧
      (∃ b ∈ B, ∃ z ∈ Q, ¬ G.Adj b z))
    (hnbr : ∀ z ∈ Q,
      (∃ f ∈ F, G.Adj z f) ∧ (∃ w ∈ A ∪ B ∪ C, G.Adj z w))
    (hcomplete : ∃ u, IsLeftStar G A C B u ∧
      (∃ f ∈ F, G.Adj u f) ∧ VertexComplete G u Q)
    (honly : ∀ z ∈ Q, IsLeftStar G A C B z → z = q₁) :
    IsLeftStar G A C B q₁ := by
  by_contra hnot
  apply hbreaker
  exact ⟨A, C, B, F, Q, hS, hF, hQ, hmiss, hnbr, hcomplete,
    fun z hz hs => hnot ((honly z hz hs).symm ▸ hs)⟩

/-- Under the hypotheses of part (1), the forbidden 1-breakers in the two
orientations force both antipath ends to be stars. -/
theorem stars_of_complete_ends_and_interior_neighbours
    (G : SimpleGraph V)
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
    (ha₀Q : VertexComplete G a₀ {z : V | z ∈ q})
    (hb₀Q : VertexComplete G b₀ {z : V | z ∈ q})
    (hqF : ∀ z ∈ q, ∃ f ∈ interior R₀, G.Adj z f)
    (hmissB : ∃ b ∈ B, ¬ G.Adj q₁ b)
    (hmissA : ∃ a ∈ A, ¬ G.Adj qk a) :
    IsLeftStar G A C B q₁ ∧ IsRightStar G A C B qk := by
  classical
  let F : Set V := {z : V | z ∈ interior R₀}
  let Q : Set V := {z : V | z ∈ q}
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS : StepConnected G A C B := hstair.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hstair.2.1
  have hR4 : 4 ≤ R₀.length := by
    have hlen := hstair.2.2
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
    omega
  have hFconn : ConnectedSet G F := by
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathGlue.isPathFrom_interior hban.1.1 (by omega)).1
  have hFant : Anticomplete G F (A ∪ B ∪ C) := by
    simpa [F] using hban.2.2.2.2
  have hFout : ∀ z ∈ F, z ∉ A ∪ B ∪ C := by
    intro z hz
    exact hban.2.1 z (Workspace.ProofLemmas.PathBasics.interior_subset hz)
  let fL : V := R₀[1]'(by omega)
  let fR : V := R₀[R₀.length - 2]'(by omega)
  have hfLF : fL ∈ F := by
    exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1
      (k := 1) (by omega) (by omega) (by omega)
  have hfRF : fR ∈ F := by
    exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1
      (k := R₀.length - 2) (by omega) (by omega) (by omega)
  have ha₀fL : G.Adj a₀ fL := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hban.1.1 (i := 0) (by omega)
    have h0 : R₀[0]'(by omega) = a₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 (by omega)
    simpa [fL, h0] using h
  have hb₀fR : G.Adj b₀ fR := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hban.1.1
      (i := R₀.length - 2) (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
    have he : R₀[R₀.length - 2 + 1]'(by omega) = b₀ := by
      calc
        R₀[R₀.length - 2 + 1]'(by omega) =
            R₀[R₀.length - 1]'(by omega) := by congr 1 <;> omega
        _ = b₀ := hl
    exact he ▸ h.symm
  have hQanti : AnticonnectedSet G Q := by
    exact Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      hq.1
  have hQout : ∀ z ∈ Q, z ∉ (A ∪ B ∪ C) ∪ F := by
    intro z hz hmem
    have hzout := outside_of_mem hq hqint hq₁.1 hqk.1 hz
    rcases hmem with hzS | hzF
    · exact hzout (Or.inr hzS)
    · exact hzout (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset hzF))
  have hQstripNbr : ∀ z ∈ Q, ∃ w ∈ A ∪ B ∪ C, G.Adj z w := by
    intro z hz
    by_cases hz₁ : z = q₁
    · obtain ⟨a, haA⟩ := hS.2.1.1
      exact ⟨a, Or.inl (Or.inl haA), by
        subst z
        exact hq₁.1.2 a (Or.inl haA)⟩
    · obtain ⟨b, hbB⟩ := hS.2.1.2
      exact ⟨b, Or.inl (Or.inr hbB),
        (rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 b (Or.inl hbB)⟩
  have honlyLeft : ∀ z ∈ Q, IsLeftStar G A C B z → z = q₁ := by
    intro z hz hstar
    by_contra hne
    obtain ⟨b, hbB⟩ := hS.2.1.2
    exact hstar.2.2 b (Or.inl hbB)
      ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hne).2 b (Or.inl hbB))
  have honlyRight : ∀ z ∈ Q, IsRightStar G A C B z → z = qk := by
    intro z hz hstar
    by_contra hne
    obtain ⟨a, haA⟩ := hS.2.1.1
    exact hstar.2.2 a (Or.inl haA)
      ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hne).2 a (Or.inl haA))
  have hexLeft : ∃ z ∈ Q, IsLeftStar G A C B z := by
    by_contra hno
    push_neg at hno
    apply hbreaker
    refine ⟨A, C, B, F, Q, hS, ⟨hFout, hFconn, hFant,
      ⟨a₀, hban.2.2.1, fL, hfLF, ha₀fL⟩,
      ⟨b₀, hban.2.2.2.1, fR, hfRF, hb₀fR⟩⟩,
      ⟨hQout, hQanti⟩, ?_, ?_, ?_, hno⟩
    · obtain ⟨a, haA, hqa⟩ := hmissA
      obtain ⟨b, hbB, hqb⟩ := hmissB
      exact ⟨⟨a, haA, qk, Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2,
        fun h => hqa h.symm⟩,
        ⟨b, hbB, q₁, Workspace.ProofLemmas.PathBasics.head_mem hq.2.1,
          fun h => hqb h.symm⟩⟩
    · intro z hz
      obtain ⟨f, hf, hzf⟩ := hqF z hz
      exact ⟨⟨f, hf, hzf⟩, hQstripNbr z hz⟩
    · exact ⟨a₀, hban.2.2.1, ⟨fL, hfLF, ha₀fL⟩,
        fun z hz => ha₀Q z hz⟩
  have hleft : IsLeftStar G A C B q₁ := by
    obtain ⟨z, hz, hs⟩ := hexLeft
    simpa [honlyLeft z hz hs] using hs
  have hexRight : ∃ z ∈ Q, IsRightStar G A C B z := by
    by_contra hno
    push_neg at hno
    apply hbreaker
    have hKswap :=
      Workspace.ProofLemmas.StaircaseLeftRightSymmetry.stronglyMaximalStaircase_swap.mp hK
    have hSswap : StepConnected G B C A := hKswap.1.1.1
    have hFantSwap : Anticomplete G F (B ∪ A ∪ C) := by
      simpa [Set.union_comm A B] using hFant
    have hQoutSwap : ∀ z ∈ Q, z ∉ (B ∪ A ∪ C) ∪ F := by
      simpa [Set.union_comm A B] using hQout
    have hFoutSwap : ∀ z ∈ F, z ∉ B ∪ A ∪ C := by
      simpa [Set.union_comm A B] using hFout
    refine ⟨B, C, A, F, Q, hSswap, ⟨hFoutSwap, hFconn, hFantSwap,
      ⟨b₀, Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mp
          hban.2.2.2.1, fR, hfRF, hb₀fR⟩,
      ⟨a₀, Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isLeftStar_swap.mp
          hban.2.2.1, fL, hfLF, ha₀fL⟩⟩,
      ⟨hQoutSwap, hQanti⟩, ?_, ?_, ?_, ?_⟩
    · obtain ⟨a, haA, hqa⟩ := hmissA
      obtain ⟨b, hbB, hqb⟩ := hmissB
      exact ⟨⟨b, hbB, q₁, Workspace.ProofLemmas.PathBasics.head_mem hq.2.1,
          fun h => hqb h.symm⟩,
        ⟨a, haA, qk, Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2,
          fun h => hqa h.symm⟩⟩
    · intro z hz
      obtain ⟨f, hf, hzf⟩ := hqF z hz
      obtain ⟨w, hw, hzw⟩ := hQstripNbr z hz
      have hw' : w ∈ B ∪ A ∪ C := by
        rcases hw with (ha | hb) | hc
        · exact Or.inl (Or.inr ha)
        · exact Or.inl (Or.inl hb)
        · exact Or.inr hc
      exact ⟨⟨f, hf, hzf⟩, w, hw', hzw⟩
    · exact ⟨b₀,
        Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mp hban.2.2.2.1,
        ⟨fR, hfRF, hb₀fR⟩, fun z hz => hb₀Q z hz⟩
    · intro z hz hleftSwap
      exact hno z hz
        (Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mpr hleftSwap)
  have hright : IsRightStar G A C B qk := by
    obtain ⟨z, hz, hs⟩ := hexRight
    simpa [honlyRight z hz hs] using hs
  exact ⟨hleft, hright⟩

end Workspace.ProofLemmas.Thm125Setup
