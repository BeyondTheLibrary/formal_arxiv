import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim4
import Workspace.ProofLemmas.Thm192Symmetry
import Workspace.ProofLemmas.Thm192Claim7GapEndpoint
import Workspace.ProofLemmas.Thm192Claim7GapEndgame

/-!
# The endpoint-nonadjacent cases of claim (7) of 19.2

Claim (6), together with the symmetry between `x₀` and `x₁`, reduces claim (7) to the
case in which `x₂` is adjacent to neither end of the path.  The printed proof then has two
long cases according to whether `x₂` is `Y₀`-complete.  They are isolated here so the
symmetry reduction and all surrounding logic can be checked without hiding a gap in the public
claim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm192Claim7Gap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (printed pp. 119–120, claim (7)), the case beginning:
*"Suppose first that `x₂` is not `Y₀`-complete. By (2), `z` is `Y`-complete and
`(C,Y₀)` is a wheel."*  The conclusion is the contradiction at the end of that case,
where the three antipaths form a long prism. -/
theorem noncomplete_endpoint_nonadjacent_case (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀) (x : ℕ → V)
    (hws : IsWheelSystem G z A₀ x 2) (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hwheel : IsWheel G (z :: P) (Y \ {y}))
    (htwo : ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
      VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hboth : (∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧
      (∃ w ∈ SPGT.interior P, G.Adj y w)) : False := by
  have h4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
    A hA hAmin hcex P hP hPint hPlen
  have hP5 : 5 ≤ P.length :=
    (Thm192Claim6Basics.path_facts hG.1.1.1.1 hws hA.1 hP hPint hPlen).2.2.2
  have hPI := fun w hw => hA.1 (hPint w hw)
  have hzY := Thm192Claim6Basics.z_complete_of_noncomplete hHyp ih hyY hyz hY0 hx2nc
  obtain ⟨hq2, hqc, hqny, hy2⟩ := Thm192Claim7GapEndpoint.noncomplete_right_endpoint
    hG hws hHyp hyY hyz hP hPI hP5 hwheel hx2nc hx20 hx21 hzY (h4.2.1 hzY) hboth
  -- Apply the same local argument after swapping `x₀,x₁` and reversing `P`.
  have hwsS := Thm192Symmetry.sw_ws hws
  have hHypS := Thm192Symmetry.sw_hyp hHyp
  have hPS : IsPathFrom G P.reverse (Thm192Symmetry.sw x 0) (Thm192Symmetry.sw x 1) := by
    simpa only [Thm192Symmetry.sw_zero, Thm192Symmetry.sw_one] using PathBasics.isPathFrom_reverse hP
  have hPIS : ∀ w ∈ SPGT.interior P.reverse, w ∈ wheelSystemA G z A₀ (Thm192Symmetry.sw x) 1 := by
    intro w hw
    rw [Thm192Symmetry.sw_A1]
    exact hPI w (PathBasics.mem_interior_reverse.mp hw)
  have hP5S : 5 ≤ P.reverse.length := by simpa using hP5
  have hCS := (Thm192Claim6Basics.path_facts hG.1.1.1.1 hwsS Set.Subset.rfl hPS hPIS
    (by omega)).2.2.1
  have hWS : IsWheel G (z :: P.reverse) (Y \ {y}) :=
    Thm192Symmetry.isWheel_congr hCS (by simp) (fun v => by simp) hwheel
  have hbothS : (∃ w ∈ SPGT.interior P.reverse, G.Adj (Thm192Symmetry.sw x 2) w) ∧
      (∃ w ∈ SPGT.interior P.reverse, G.Adj y w) := by
    simpa only [Thm192Symmetry.sw_two, PathBasics.mem_interior_reverse] using hboth
  have hleft := Thm192Claim7GapEndpoint.noncomplete_right_endpoint hG hwsS hHypS hyY hyz
    hPS hPIS hP5S hWS (by simpa only [Thm192Symmetry.sw_two] using hx2nc)
    (by simpa only [Thm192Symmetry.sw_two, Thm192Symmetry.sw_zero] using hx21)
    (by simpa only [Thm192Symmetry.sw_two, Thm192Symmetry.sw_one] using hx20)
    hzY (Thm192Claim7GapEndpoint.no_edge_reverse hP.1 (h4.2.1 hzY)) hbothS
  simp only [Thm192Claim7GapEndpoint.penultimate_reverse P hPlen, Thm192Symmetry.sw_two] at hleft
  exact Thm192Claim7GapEndgame.noncomplete_endpoints_absurd hG hws hHyp hyY hP hP5 hx2nc
    hx20 hx21 hleft.1 hq2 hleft.2.2.1 hqny hleft.2.1 hqc hy2

/-- PAPER (printed p. 120, claim (7)), the case beginning:
*"We therefore assume that `x₂` is `Y₀`-complete, and consequently nonadjacent to `y`."*
The conclusion is the final contradiction from 17.1 in the complement. -/
theorem complete_endpoint_nonadjacent_case (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀) (x : ℕ → V)
    (hws : IsWheelSystem G z A₀ x 2) (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hx2c : VertexComplete G (x 2) (Y \ {y})) (hx2y : ¬ G.Adj (x 2) y)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hboth : (∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧
      (∃ w ∈ SPGT.interior P, G.Adj y w)) : False := by
  have h4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
    A hA hAmin hcex P hP hPint hPlen
  have hP5 : 5 ≤ P.length :=
    (Thm192Claim6Basics.path_facts hG.1.1.1.1 hws hA.1 hP hPint hPlen).2.2.2
  have hPI := fun w hw => hA.1 (hPint w hw)
  obtain ⟨hq2, hqy⟩ := Thm192Claim7GapEndpoint.complete_right_endpoint hG hws hHyp hyY hyz
    hY0 hP hPI hP5 hx2c hx2y hx20 hx21 h4.1 h4.2.1 h4.2.2.2 hboth
  have hwsS := Thm192Symmetry.sw_ws hws
  have hHypS := Thm192Symmetry.sw_hyp hHyp
  have hPS : IsPathFrom G P.reverse (Thm192Symmetry.sw x 0) (Thm192Symmetry.sw x 1) := by
    simpa only [Thm192Symmetry.sw_zero, Thm192Symmetry.sw_one] using PathBasics.isPathFrom_reverse hP
  have hPIS : ∀ w ∈ SPGT.interior P.reverse, w ∈ wheelSystemA G z A₀ (Thm192Symmetry.sw x) 1 := by
    intro w hw
    rw [Thm192Symmetry.sw_A1]
    exact hPI w (PathBasics.mem_interior_reverse.mp hw)
  have hP5S : 5 ≤ P.reverse.length := by simpa using hP5
  have hbothS : (∃ w ∈ SPGT.interior P.reverse, G.Adj (Thm192Symmetry.sw x 2) w) ∧
      (∃ w ∈ SPGT.interior P.reverse, G.Adj y w) := by
    simpa only [Thm192Symmetry.sw_two, PathBasics.mem_interior_reverse] using hboth
  have hfirstS : (∃ w ∈ SPGT.interior P.reverse,
      VertexComplete G w (Y ∪ {Thm192Symmetry.sw x 2})) → VertexComplete G z Y := by
    rintro ⟨w, hw, hwc⟩
    exact h4.1 ⟨w, PathBasics.mem_interior_reverse.mp hw,
      by simpa only [Thm192Symmetry.sw_two] using hwc⟩
  have hendS : ¬ VertexComplete G (P.reverse[P.reverse.length - 2]'(by omega))
      (Y ∪ {Thm192Symmetry.sw x 2}) := by
    simpa only [Thm192Claim7GapEndpoint.penultimate_reverse P hPlen, Thm192Symmetry.sw_two]
      using h4.2.2.1
  have hleft := Thm192Claim7GapEndpoint.complete_right_endpoint hG hwsS hHypS hyY hyz hY0
    hPS hPIS hP5S (by simpa only [Thm192Symmetry.sw_two] using hx2c)
    (by simpa only [Thm192Symmetry.sw_two] using hx2y)
    (by simpa only [Thm192Symmetry.sw_two, Thm192Symmetry.sw_zero] using hx21)
    (by simpa only [Thm192Symmetry.sw_two, Thm192Symmetry.sw_one] using hx20)
    hfirstS (fun hzY => Thm192Claim7GapEndpoint.no_edge_reverse hP.1 (h4.2.1 hzY)) hendS hbothS
  simp only [Thm192Claim7GapEndpoint.penultimate_reverse P hPlen, Thm192Symmetry.sw_two] at hleft
  have hpnc : ¬ VertexComplete G (P[1]'(by omega)) Y := by
    intro hc
    apply h4.2.2.1
    intro w hw
    rcases hw with hw | rfl
    · exact hc w hw
    · exact hleft.1
  have hqnc : ¬ VertexComplete G (P[P.length - 2]'(by omega)) Y := by
    intro hc
    apply h4.2.2.2
    intro w hw
    rcases hw with hw | rfl
    · exact hc w hw
    · exact hq2
  exact Thm192Claim7GapEndgame.complete_endpoints_absurd hG hws hHyp hA.1 hyY hP hPint hP5
    hx2c hx2y hx20 hx21 hleft.1 hq2 hleft.2 hqy hpnc hqnc

end Workspace.ProofLemmas.Thm192Claim7Gap
