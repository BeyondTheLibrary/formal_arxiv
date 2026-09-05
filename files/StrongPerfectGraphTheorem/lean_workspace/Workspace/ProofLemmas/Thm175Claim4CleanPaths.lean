import Workspace.ProofLemmas.Thm175Claim4Setup
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-! The clean-path consequences of 2.2 and 13.6 used in 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4CleanPaths

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A : Set V} {P : List V} {u v : V}

theorem noedge (hP : IsPathFrom G P u v) (hlen : 2 ≤ pathLength P)
    (hclean : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w A) :
    ¬ ∃ x ∈ P, ∃ y ∈ P, EdgeComplete G A x y := by
  have hn : ¬ G.Adj u v := by
    have hh := PathBasics.path_ends_not_adj hP.1 (by dsimp [pathLength] at hlen; omega)
    rw [PathBasics.getElem_zero_of_head? hP.2.1 (by dsimp [pathLength] at hlen; omega),
      PathBasics.getElem_last_of_getLast? hP.2.2 (by dsimp [pathLength] at hlen; omega)] at hh
    exact hh
  have honly : ∀ w ∈ P, VertexComplete G w A → w = u ∨ w = v := by
    intro w hw hc
    by_cases hwu : w = u
    · exact Or.inl hwu
    by_cases hwv : w = v
    · exact Or.inr hwv
    exact (hclean w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨hw, hwu, hwv⟩) hc).elim
  rintro ⟨x, hx, y, hy, ha, hxA, hyA⟩
  rcases honly x hx hxA with hx | hx <;> rcases honly y hy hyA with hy | hy
  · rw [hx, hy] at ha
    exact G.irrefl ha
  · rw [hx, hy] at ha
    exact hn ha
  · rw [hx, hy] at ha
    exact hn ha.symm
  · rw [hx, hy] at ha
    exact G.irrefl ha

/-- A complete vertex avoiding the interior excludes an odd clean path by 2.2. -/
theorem even (hG : Berge G) (hA : AnticonnectedSet G A)
    (hP : IsPathFrom G P u v) (hlen : 2 ≤ pathLength P)
    (hout : ∀ w ∈ P, w ∉ A) (hu : VertexComplete G u A) (hv : VertexComplete G v A)
    (hclean : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w A)
    (z : V) (hz : VertexComplete G z A)
    (hzanti : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w) : Even (pathLength P) := by
  apply Nat.not_odd_iff_even.mp
  intro ho
  obtain ⟨w, hw, ha⟩ := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hG A hA
    P u v hP hout ho hu hv (noedge hP hlen hclean) z hz
  exact hzanti w hw ha

/-- An odd clean path has length three by 13.6. -/
theorem length_three (hG : InF5 G) (hA : AnticonnectedSet G A)
    (hP : IsPathFrom G P u v) (hlen : 2 ≤ pathLength P)
    (hout : ∀ w ∈ P, w ∉ A) (hu : VertexComplete G u A) (hv : VertexComplete G v A)
    (hclean : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w A)
    (ho : Odd (pathLength P)) : pathLength P = 3 := by
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG P u v hP ho A
    (fun w hw hwP => hout w hwP hw) hA hu hv with he | hthree
  · exact (noedge hP hlen hclean he).elim
  · exact hthree.1

end Workspace.ProofLemmas.Thm175Claim4CleanPaths
