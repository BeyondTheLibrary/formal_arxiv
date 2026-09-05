import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim3
import Workspace.ProofLemmas.Thm192Claim8Basics
import Workspace.ProofLemmas.Thm192Claim8Triangles
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics

/-!
# Claim (8) of 19.2: the path `f₁-⋯-f_k` and the standing bookkeeping

PAPER (printed p. 121):

> *"Consequently from (3), `A` is the vertex set of a path `f₁-⋯-f_k`, where `f₁` is adjacent
> to `x₀,x₂`, and `f_k` to `x₁,y`.  Since `f₁ ∈ A` it follows that `f₁` is not adjacent to
> `x₁`."*

`Thm192Claim8Triangles` produced the two vertices; an induced path of `A` joining them is
connected, meets `x₀,x₁,x₂,y`, and so is all of `A` by claim (3).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8Path

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"`A` is the vertex set of a path `f₁-⋯-f_k`, where `f₁` is adjacent to `x₀,x₂`, and
`f_k` to `x₁,y`."* -/
theorem path_structure (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hx20 : G.Adj (x 2) (x 0)) (h2y : ¬ G.Adj (x 2) y) :
    ∃ R : List V, ∃ f₁ fk : V, IsPathFrom G R f₁ fk ∧ {w : V | w ∈ R} = A ∧
      G.Adj (x 0) f₁ ∧ G.Adj (x 2) f₁ ∧ G.Adj (x 1) fk ∧ G.Adj y fk ∧ f₁ ≠ fk := by
  classical
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hzA : ∀ g ∈ A, ¬ G.Adj z g := fun g hg => wheelSystemA_no_z g (hAsub hg)
  have hxA : ∀ j : ℕ, j ≤ 2 → x j ∉ A := fun j hj hm => hzA _ hm (hzx j hj)
  have hzAmem : z ∉ A := Thm192Claim8Basics.z_notMem hws hAsub
  have hyA : y ∉ A := fun hm => hzA _ hm hyz.symm
  have hnoc : ∀ g ∈ A, ¬ (G.Adj (x 0) g ∧ G.Adj (x 1) g) := by
    intro g hg hc
    exact Thm192Claim8Basics.no_X1_complete hAsub g hg ⟨hc.1.symm, hc.2.symm⟩
  have hx21 : ¬ G.Adj (x 2) (x 1) := by
    intro hadj
    refine hws.2.2.2.2.2.1 2 (by omega) (by omega) ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx20
    · exact hadj
  have hx01 : ¬ G.Adj (x 0) (x 1) := x0_not_adj_x1 hws
  have hy0 : G.Adj y (x 0) := (hHyp.2.2.1 y hyY).symm
  have hy1 : G.Adj y (x 1) := (hHyp.2.2.2.1 y hyY).symm
  have hne : ∀ i j : ℕ, i ≤ 2 → j ≤ 2 → i ≠ j → x i ≠ x j := by
    intro i j hi hj hij he
    exact hij (hws.2.1 i hi j hj he)
  have hx2y : x 2 ≠ y := fun he => (hHyp.1 y hyY).2.2.2 he.symm
  obtain ⟨g₁, hg₁A, h0g₁, h2g₁⟩ :=
    Thm192Claim8Triangles.catch_x0x2 G hG z (x 0) (x 1) (x 2) A (hzx 0 (by omega))
      (hzx 1 (by omega)) (hzx 2 (by omega)) hx20 hx21 hx01 (hne 0 1 (by omega) (by omega)
      (by omega)) (hne 1 2 (by omega) (by omega) (by omega)) hA.2.1 hzA hzAmem
      (hxA 0 (by omega)) (hxA 1 (by omega)) (hxA 2 (by omega)) hnoc hA.2.2.1 hA.2.2.2.1
      hA.2.2.2.2.1
  obtain ⟨g₂, hg₂A, h1g₂, hyg₂⟩ :=
    Thm192Claim8Triangles.catch_x1y G hG z (x 0) (x 1) (x 2) y A (hzx 0 (by omega))
      (hzx 1 (by omega)) (hzx 2 (by omega)) hyz.symm hy0 hy1 hx20 hx21 hx01 h2y hx2y
      (hne 1 2 (by omega) (by omega) (by omega)) (hne 0 1 (by omega) (by omega) (by omega))
      hA.2.1 hzA hzAmem (hxA 0 (by omega)) (hxA 1 (by omega)) (hxA 2 (by omega)) hyA hnoc
      hA.2.2.2.1 hA.2.2.2.2.2.2 hA.2.2.2.2.1
  have hg₁g₂ : g₁ ≠ g₂ := by
    rintro rfl
    exact hnoc g₁ hg₁A ⟨h0g₁, h1g₂⟩
  obtain ⟨R, hR, hRA⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hA.2.1 hg₁A hg₂A
  have hg₁R : g₁ ∈ R := List.mem_of_mem_head? hR.2.1
  have hg₂R : g₂ ∈ R := List.mem_of_mem_getLast? hR.2.2
  have hFA : {w : V | w ∈ R} = A := by
    refine Thm192Claim3.claim3 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      _ (fun w hw => hRA w hw)
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1)
      ⟨g₁, hg₁R, h0g₁⟩ ⟨g₂, hg₂R, h1g₂⟩ ⟨g₁, hg₁R, h2g₁⟩ ⟨g₂, hg₂R, hyg₂⟩
  exact ⟨R, g₁, g₂, hR, hFA, h0g₁, h2g₁, h1g₂, hyg₂, hg₁g₂⟩

end Workspace.ProofLemmas.Thm192Claim8Path
