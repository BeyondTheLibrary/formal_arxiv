import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Symmetry
import Workspace.ProofLemmas.Thm192Claim6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics

/-!
# Symmetric use of claim (6) in claim (7) of 19.2

The first sentence of claim (7) applies claim (6) at both ends of the path.  This module
packages the second application, which reverses the path and swaps `x₀,x₁`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim7Reduction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm192Setup
open Workspace.ProofLemmas.Thm192Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Wheel-system bookkeeping used when closing the path through `z`. -/
private theorem adj_z_x {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) {j : ℕ} (hj : j ≤ t) : G.Adj z (x j) :=
  hws.2.2.2.2.2.2 j hj

private theorem x_ne_z {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) {j : ℕ} (hj : j ≤ t) : x j ≠ z :=
  (hws.2.2.1 j hj).2

private theorem z_notMem_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hws : IsWheelSystem G z A₀ x t) : z ∉ wheelSystemA G z A₀ x 1 := by
  intro hz
  refine wheelSystemA_no_complete _ hz ?_
  rw [wheelSystemX_one]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact adj_z_x hws (Nat.zero_le t)
  · exact adj_z_x hws hws.1

/-- The three wheel-system vertices and `z` lie outside `A₁`, so `z` does not occur on
an `x₀`–`x₁` path whose interior is in a subset of `A₁`. -/
private theorem z_notMem_path {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) {A : Set V}
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) : z ∉ P := by
  intro hz
  by_cases h0 : z = x 0
  · exact x_ne_z hws (Nat.zero_le 2) h0.symm
  by_cases h1 : z = x 1
  · exact x_ne_z hws (by omega) h1.symm
  · exact z_notMem_A1 hws
      (hAsub (hPint z ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hz, h0, h1⟩)))

/-- The hole obtained by closing such a path through `z`. -/
private theorem hole_zP {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) {A : Set V}
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length) :
    IsHoleList G (z :: P) := by
  refine PrismBasics.isHoleList_of_path_add_vertex hP ?_ (adj_z_x hws (Nat.zero_le 2))
    (adj_z_x hws (by omega)) (z_notMem_path hws hAsub hP hPint) ?_
  · have := PathBasics.pathLength_eq P
    omega
  · intro w hw
    exact wheelSystemA_no_z _ (hAsub (hPint w hw))

/-- The `x₀ ↔ x₁` transport of claim (6).  It is the formal version of the first
sentence of claim (7): *"and similarly nonadjacent to `x₁`"*. -/
theorem claim6_at_x1 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (h12 : G.Adj (x 1) (x 2)) :
    ¬ ((∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧
      (∃ w ∈ SPGT.interior P, G.Adj y w)) := by
  have hwsS : IsWheelSystem G z A₀ (sw x) 2 := sw_ws hws
  have hHypS : Hyp192 G z A₀ (sw x) Y := sw_hyp hHyp
  have ihS : (∀ Y' : Set V, Y'.ncard < Y.ncard →
      Hyp192 G z A₀ (sw x) Y' → Concl192 G z A₀ (sw x) Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard := sw_ih ih
  have hAS : GoodA G z A₀ (sw x) Y y A := sw_goodA hA
  have hAminS : ∀ B : Set V, GoodA G z A₀ (sw x) Y y B → A.ncard ≤ B.ncard :=
    sw_goodA_min hAmin
  have hcexS : ¬ Concl192 G z A₀ (sw x) Y := by
    intro hcon
    have hh := sw_concl hcon
    rw [sw_sw] at hh
    exact hcex hh
  have hPS : IsPathFrom G P.reverse (sw x 0) (sw x 1) := by
    rw [sw_zero, sw_one]
    exact PathBasics.isPathFrom_reverse hP
  have hPintS : ∀ w ∈ SPGT.interior P.reverse, w ∈ A := fun w hw =>
    hPint w (PathBasics.mem_interior_reverse.mp hw)
  have hPlenS : 3 ≤ P.reverse.length := by simpa using hPlen
  have hchoiceS : VertexComplete G (sw x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P.reverse) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P.reverse, ∃ d ∈ SPGT.interior P.reverse, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})) := by
    rcases hchoice with hc | ⟨hw, c, hcI, d, hdI, hcd, hcY, hdY⟩
    · exact Or.inl (by simpa only [sw_two] using hc)
    · refine Or.inr ⟨?_, c, PathBasics.mem_interior_reverse.mpr hcI,
        d, PathBasics.mem_interior_reverse.mpr hdI, hcd, hcY, hdY⟩
      exact isWheel_congr (hole_zP hwsS hAS.1 hPS hPintS hPlenS)
        (by simp) (fun v => by simp) hw
  have h12S : G.Adj (sw x 0) (sw x 2) := by
    rw [sw_zero, sw_two]
    exact h12
  have h6 := Thm192Claim6.claim6 G hG z A₀ hframe (sw x) hwsS Y hHypS ihS y hyY hyz
    hY0 A hAS hAminS hcexS P.reverse hPS hPintS hPlenS hchoiceS h12S
  intro hboth
  apply h6
  constructor
  · obtain ⟨w, hw, hadj⟩ := hboth.1
    refine ⟨w, PathBasics.mem_interior_reverse.mpr hw, ?_⟩
    rwa [sw_two]
  · obtain ⟨w, hw, hadj⟩ := hboth.2
    exact ⟨w, PathBasics.mem_interior_reverse.mpr hw, hadj⟩

end Workspace.ProofLemmas.Thm192Claim7Reduction
