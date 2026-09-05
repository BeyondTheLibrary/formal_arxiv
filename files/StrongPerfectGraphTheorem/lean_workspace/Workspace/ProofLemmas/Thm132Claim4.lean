import Workspace.ProofLemmas.Thm132Claim3
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Claim (4) of 13.2

The vertex set of the trajectory is anticonnected.  For a rung `a-P-b`,
adjoining the two old banister ends gives the odd path
`a₀-a-P-b-b₀`.  Its ends are trajectory-complete, whereas no rung vertex
can be complete to the trajectory: the trajectory contains both the left-star
`r` and the right-star `wₙ`.  The Roussel--Rubio consequence 2.2 therefore
rules out a trajectory-complete vertex in the interior of the old banister.
-/

namespace Workspace.ProofLemmas.Thm132Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex of a rung belongs to the underlying strip. -/
private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {p : List V} (h : IsRungOfStrip G A C B a p b) :
    ∀ w ∈ p, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (by simpa [hwa] using h.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (by simpa [hwb] using h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 w
      ((PathBasics.mem_interior_iff_of_pathFrom h.1).mpr ⟨hw, hwa, hwb⟩))

/-- A rung, with a left-star prepended and a right-star appended, is the
induced path displayed in claim (4). -/
private theorem extended_rung_path {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ a b : V} {p : List V}
    (hLS : IsLeftStar G A C B a₀)
    (hRS : IsRightStar G A C B b₀)
    (ha₀b₀_ne : a₀ ≠ b₀) (ha₀b₀_non : ¬ G.Adj a₀ b₀)
    (hr : IsRungOfStrip G A C B a p b) :
    IsPathFrom G (a₀ :: (p ++ [b₀])) a₀ b₀ := by
  have ha₀p : a₀ ∉ p := by
    intro ha₀mem
    exact hLS.1 (rung_mem_strip hr a₀ ha₀mem)
  have hleftEdges : ∀ y ∈ p, (G.Adj a₀ y ↔ y = a) := by
    intro y hy
    have hyS := rung_mem_strip hr y hy
    constructor
    · intro hadj
      rcases hyS with (hyA | hyB) | hyC
      · exact hr.2.2.2.1 y hy hyA
      · exact absurd hadj (hLS.2.2 y (Or.inl hyB))
      · exact absurd hadj (hLS.2.2 y (Or.inr hyC))
    · intro hya
      subst y
      exact hLS.2.1 a hr.2.1
  have hfirst : IsPathFrom G (a₀ :: p) a₀ b :=
    isPathFrom_cons hr.1 ha₀p hleftEdges
  have hb₀p : b₀ ∉ p := by
    intro hb₀mem
    exact hRS.1 (rung_mem_strip hr b₀ hb₀mem)
  have hdisj : ∀ y ∈ a₀ :: p, y ∉ [b₀] := by
    intro y hy
    simp only [List.mem_singleton]
    intro hyb₀
    rcases List.mem_cons.mp hy with hya₀ | hyp
    · exact ha₀b₀_ne (hya₀.symm.trans hyb₀)
    · exact hb₀p (hyb₀ ▸ hyp)
  have hright : ∀ y ∈ a₀ :: p, ∀ z ∈ [b₀],
      (G.Adj y z ↔ (y = b ∧ z = b₀)) := by
    intro y hy z hz
    simp only [List.mem_singleton] at hz
    subst z
    constructor
    · intro hadj
      rcases List.mem_cons.mp hy with hya₀ | hyp
      · subst y
        exact absurd hadj ha₀b₀_non
      · have hyS := rung_mem_strip hr y hyp
        refine ⟨?_, rfl⟩
        rcases hyS with (hyA | hyB) | hyC
        · exact absurd hadj.symm (hRS.2.2 y (Or.inl hyA))
        · exact hr.2.2.2.2.1 y hyp hyB
        · exact absurd hadj.symm (hRS.2.2 y (Or.inr hyC))
    · rintro ⟨hyb, hzb₀⟩
      simpa [hyb] using (hRS.2.1 b hr.2.2.1).symm
  have hlast : IsPathFrom G ((a₀ :: p) ++ [b₀]) a₀ b₀ :=
    Workspace.ProofLemmas.PathGlue.glue_path hfirst
      ⟨PathBasics.isPathList_singleton G b₀, by simp, by simp⟩ hdisj hright
  simpa using hlast

/-- PAPER claim (4): no interior vertex of the original banister is complete
to the trajectory together with its initial left-star. -/
theorem no_trajectory_complete_interior
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w})
    (hra : G.Adj a₀ d.r)
    (hlast : IsRightStar G A C B d.last) :
    ¬ ∃ v ∈ interior R₀, VertexComplete G v {z : V | z ∈ d.r :: d.w} := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hrb : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hwne : d.w ≠ [] := by
    intro he
    have ho := d.w_odd
    rw [he] at ho
    simp at ho
  have hlastMem : d.last ∈ d.w := by
    have hc := d.trajectory_antipath.2.2
    have hc' : d.w.getLast? = some d.last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hc
    exact PathBasics.getLast_mem hc'
  let T : Set V := {z : V | z ∈ d.r :: d.w}
  have hTanti : AnticonnectedSet G T := by
    exact Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      d.trajectory_antipath.1
  have ha₀T : VertexComplete G a₀ T := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z
      exact hra
    · exact d.a₀_complete_w z hzw
  have hb₀T : VertexComplete G b₀ T := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z
      exact hrb.symm
    · exact hbW z hzw
  obtain ⟨a, haA⟩ := hS.2.1.1
  obtain ⟨a₁, P, b₁, hP, -⟩ := hS.2.2.1 a (Or.inl (Or.inl haA))
  have ha₀b₀_ne : a₀ ≠ b₀ :=
    PathBasics.isPathFrom_ends_ne hban₀.1 (by
      have hp3 : 3 ≤ pathLength R₀ := hK.1.1.2.2
      omega)
  have ha₀b₀_non : ¬ G.Adj a₀ b₀ := by
    have hn := PathBasics.path_ends_not_adj hban₀.1.1 (by
      have := hK.1.1.2.2
      rw [PathBasics.pathLength_eq] at this
      omega)
    have h0 : R₀[0]'(by
        have := PathBasics.path_length_pos hban₀.1.1
        omega) = a₀ :=
      PathBasics.getElem_zero_of_head? hban₀.1.2.1 (by
        exact PathBasics.path_length_pos hban₀.1.1)
    have hl : R₀[R₀.length - 1]'(by
        have := PathBasics.path_length_pos hban₀.1.1
        omega) = b₀ :=
      PathBasics.getElem_last_of_getLast? hban₀.1.2.2
        (PathBasics.path_length_pos hban₀.1.1)
    simpa [h0, hl] using hn
  have hEP : IsPathFrom G (a₀ :: (P ++ [b₀])) a₀ b₀ :=
    extended_rung_path hban₀.2.2.1 hban₀.2.2.2.1 ha₀b₀_ne ha₀b₀_non hP

  have hPodd : Odd (pathLength P) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS
      a₀ b₀ R₀ hban₀).1 a₁ P b₁ hP
  have hEPodd : Odd (pathLength (a₀ :: (P ++ [b₀]))) := by
    obtain ⟨k, hk⟩ := hPodd
    refine ⟨k + 1, ?_⟩
    simp only [pathLength, List.length_cons, List.length_append, List.length_singleton,
      List.length_nil] at hk ⊢
    omega

  have hTout : ∀ z ∈ T, z ∉ A ∪ B ∪ C := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z
      exact d.optimal.1.2.2.1.1
    · exact bComplete_not_mem_strip hS (d.w_B_complete z hzw)
  have hEPT : ∀ z ∈ a₀ :: (P ++ [b₀]), z ∉ T := by
    intro z hzP hzT
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hzP
    rcases hzP with hza₀ | hzP | hzb₀
    · subst z
      exact G.irrefl (ha₀T a₀ hzT)
    · exact hTout z hzT (rung_mem_strip hP z hzP)
    · subst z
      exact G.irrefl (hb₀T b₀ hzT)

  have hRungNotComplete : ∀ z ∈ P, ¬ VertexComplete G z T := by
    intro z hzP hzC
    have hzS := rung_mem_strip hP z hzP
    have hzr : G.Adj z d.r := hzC d.r (by simp [T])
    have hzl : G.Adj z d.last := hzC d.last (by
      simp only [T, List.mem_cons]
      exact Or.inr hlastMem)
    rcases hzS with (hzA | hzB) | hzCmem
    · exact hlast.2.2 z (Or.inl hzA) hzl.symm
    · exact d.optimal.1.2.2.1.2.2 z (Or.inl hzB) hzr.symm
    · exact d.optimal.1.2.2.1.2.2 z (Or.inr hzCmem) hzr.symm

  have hcomplete_ends : ∀ z ∈ a₀ :: (P ++ [b₀]),
      VertexComplete G z T → z = a₀ ∨ z = b₀ := by
    intro z hzP hzC
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hzP
    rcases hzP with hza₀ | hzP | hzb₀
    · exact Or.inl hza₀
    · exact absurd hzC (hRungNotComplete z hzP)
    · exact Or.inr hzb₀
  have hnoedge : ¬ ∃ u ∈ a₀ :: (P ++ [b₀]),
      ∃ v ∈ a₀ :: (P ++ [b₀]), EdgeComplete G T u v := by
    rintro ⟨u, hu, v, hv, huv, huT, hvT⟩
    rcases hcomplete_ends u hu huT with rfl | rfl <;>
      rcases hcomplete_ends v hv hvT with rfl | rfl
    · exact G.irrefl huv
    · exact ha₀b₀_non huv
    · exact ha₀b₀_non huv.symm
    · exact G.irrefl huv

  rintro ⟨v, hvint, hvT⟩
  obtain ⟨z, hzint, hvz⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hG T hTanti
      (a₀ :: (P ++ [b₀])) a₀ b₀ hEP hEPT hEPodd ha₀T hb₀T hnoedge v hvT
  have hzmem := (PathBasics.mem_interior_iff_of_pathFrom hEP).mp hzint
  have hzP : z ∈ P := by
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hzmem
    rcases hzmem.1 with hza | hzP | hzb
    · exact absurd hza hzmem.2.1
    · exact hzP
    · exact absurd hzb hzmem.2.2
  exact hban₀.2.2.2.2 v hvint z (rung_mem_strip hP z hzP) hvz

end Workspace.ProofLemmas.Thm132Claim4
