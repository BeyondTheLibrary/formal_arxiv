import Workspace.ProofLemmas.Thm132Claim5ShortFinish
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S02.Thm_2_1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # Claim (5) of 13.2: the trajectory has one term. -/

namespace Workspace.ProofLemmas.Thm132Claim5

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup
open Workspace.ProofLemmas.Thm132Claim5Long
open Workspace.ProofLemmas.Thm132Claim5ShortFinish

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER claim (5). -/
theorem trajectory_length_one
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w})
    (hra : G.Adj a₀ d.r)
    (hlast : IsRightStar G A C B d.last) : d.w.length = 1 := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hrb₀ : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hrout : d.r ∉ staircaseVertices A C B R₀ :=
    Workspace.ProofLemmas.Thm132Claim2.leftStar_adj_rightEnd_outside
      hK.1.1 d.optimal.1.2.2.1 hra.ne' hrb₀
  let T : Set V := {z : V | z ∈ d.r :: d.w}
  have hTanti : AnticonnectedSet G T :=
    Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      d.trajectory_antipath.1
  have hTout : ∀ z ∈ T, z ∉ staircaseVertices A C B R₀ := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z; exact hrout
    · exact bComplete_adj_left_not_mem_staircase hK.1.1
        (d.w_B_complete z hzw) (d.a₀_complete_w z hzw).symm
  have hR₀T : ∀ z ∈ R₀, z ∉ T := by
    intro z hzR hzT
    exact hTout z hzT (Or.inl hzR)
  have ha₀T : VertexComplete G a₀ T := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z; exact hra
    · exact d.a₀_complete_w z hzw
  have hb₀T : VertexComplete G b₀ T := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z; exact hrb₀.symm
    · exact hbW z hzw
  have hRodd : Odd (pathLength R₀) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS
      a₀ b₀ R₀ hban₀).2
  have ha₀b₀ : ¬ G.Adj a₀ b₀ := by
    have hlen : 3 ≤ R₀.length := by
      have := hK.1.1.2.2
      rw [PathBasics.pathLength_eq] at this
      omega
    have hn := PathBasics.path_ends_not_adj hban₀.1.1 hlen
    have h0 : R₀[0]'(by omega) = a₀ :=
      PathBasics.getElem_zero_of_head? hban₀.1.2.1 (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      PathBasics.getElem_last_of_getLast? hban₀.1.2.2 (by omega)
    simpa [h0, hl] using hn
  have hcompleteEnds : ∀ z ∈ R₀, VertexComplete G z T → z = a₀ ∨ z = b₀ := by
    intro z hz hzT
    by_cases hza : z = a₀
    · exact Or.inl hza
    by_cases hzb : z = b₀
    · exact Or.inr hzb
    have hzint : z ∈ interior R₀ :=
      (PathBasics.mem_interior_iff_of_pathFrom hban₀.1).mpr ⟨hz, hza, hzb⟩
    exact absurd ⟨z, hzint, hzT⟩
      (Workspace.ProofLemmas.Thm132Claim4.no_trajectory_complete_interior
        hG heven hK d hbW hra hlast)
  have hnoedge : ¬ ∃ u ∈ R₀, ∃ v ∈ R₀, EdgeComplete G T u v := by
    rintro ⟨u, hu, v, hv, huv, huT, hvT⟩
    rcases hcompleteEnds u hu huT with rfl | rfl <;>
      rcases hcompleteEnds v hv hvT with rfl | rfl
    · exact G.irrefl huv
    · exact ha₀b₀ huv
    · exact ha₀b₀ huv.symm
    · exact G.irrefl huv

  by_contra hne
  have hwlong : 1 < d.w.length := by
    obtain ⟨k, hk⟩ := d.w_odd
    omega
  rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG T hTanti R₀ a₀ b₀
      hban₀.1 hR₀T hRodd ha₀T hb₀T with hedge | hleap | hshort
  · exact hnoedge hedge
  · obtain ⟨hR5, u, huT, v, hvT, huv⟩ := hleap
    exact no_leap_of_long_trajectory hG heven hK d hbW hra hwlong hR5
      (by simpa [T] using huT) (by simpa [T] using hvT) huv
  · obtain ⟨hR3, c, e, hinterior, q, hq, hqodd, hqinner⟩ := hshort
    exact no_short_antipath_of_long_trajectory hG heven hK d hbW hra hlast
      hwlong hR3 hinterior hq hqodd (by simpa [T] using hqinner)

end Workspace.ProofLemmas.Thm132Claim5
