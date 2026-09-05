import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.ReflectionAntihole
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm192Claim10Endgame
import Workspace.Statements.S15.Thm_15_7
import Workspace.Statements.S17.Thm_17_1

/-!
# The two paper steps in the one-sided proof of claim (10)

These statements isolate the two parts of the printed proof that are not mere
`x₀`--`x₁` symmetry or direct uses of earlier claims.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm192Claim10Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The path-carrying form of `firstReflectionForcesAdjacency`.  The fixed rim
`z :: P` supplies the hole that excludes the reflection by 15.7. -/
theorem firstReflectionForcesAdjacencyWithPath (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (y : V) (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (f : V) (hfA : f ∈ A) (hfadj : G.Adj (x 2) f)
    (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (hx20 : G.Adj (x 2) (x 0)) :
    G.Adj (x 0) f := by
  classical
  have hzx : ∀ i ≤ 2, G.Adj z (x i) := hws.2.2.2.2.2.2
  have hxne : ∀ i ≤ 2, x i ≠ z := fun i hi => (hws.2.2.1 i hi).2
  have hxij : ∀ i ≤ 2, ∀ j ≤ 2, i ≠ j → x i ≠ x j := by
    intro i hi j hj hij he
    exact hij (hws.2.1 i hi j hj he)
  have hzA : ∀ a ∈ A, ¬ G.Adj z a :=
    fun a ha => Thm192Setup.wheelSystemA_no_z a (hA.1 ha)
  have hznotA : z ∉ A := by
    intro hzAmem
    refine Thm192Setup.wheelSystemA_no_complete z (hA.1 hzAmem) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hzx 0 (by omega)
    · exact hzx 1 (by omega)
  have hxiA : ∀ i ≤ 2, x i ∉ A := by
    intro i hi hmem
    exact hzA (x i) hmem (hzx i hi)
  have hx21 : ¬ G.Adj (x 2) (x 1) := by
    intro hx21
    have hn := hws.2.2.2.2.2.1 2 (by omega) (by omega)
    apply hn
    rw [show 2 - 1 = 1 by omega, Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx20
    · exact hx21
  by_contra h0f
  let T : Set V := {z, x 2, x 0}
  let F : Set V := A ∪ {x 1}
  have htri : Workspace.Types.RousselRubio.SPGT.IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr
      ⟨z, x 2, x 0, (hxne 2 (by omega)).symm, (hxne 0 (by omega)).symm,
        hxij 2 (by omega) 0 (by omega) (by omega), rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact hzx 2 (by omega)
    · exact hzx 0 (by omega)
    · exact (hzx 2 (by omega)).symm
    · exact (huv rfl).elim
    · exact hx20
    · exact (hzx 0 (by omega)).symm
    · exact hx20.symm
    · exact (huv rfl).elim
  have hFsub : F ⊆ Tᶜ := by
    intro g hgF hgT
    rcases hgF with hgA | hg1
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
      rcases hgT with h | h | h
      · exact hznotA (h ▸ hgA)
      · exact hxiA 2 (by omega) (h ▸ hgA)
      · exact hxiA 0 (by omega) (h ▸ hgA)
    · have hg : g = x 1 := by simpa using hg1
      subst g
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
      rcases hgT with h | h | h
      · exact hxne 1 (by omega) h
      · exact hxij 1 (by omega) 2 (by omega) (by omega) h
      · exact hxij 1 (by omega) 0 (by omega) (by omega) h
  have hFconn : ConnectedSet G F :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hA.2.1 hA.2.2.2.1
  have hcatch : Workspace.Types.TriangleCatching.SPGT.Catches G F T := by
    refine ⟨htri, hFconn, Set.disjoint_left.mpr hFsub, ?_⟩
    intro u hu
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨x 1, Or.inr rfl, hzx 1 (by omega)⟩
    · exact ⟨f, Or.inl hfA, hfadj⟩
    · obtain ⟨a, haA, h0a⟩ := hA.2.2.1
      exact ⟨a, Or.inl haA, h0a⟩
  have hnoTwo : ¬ ∃ g ∈ F, 2 ≤ (G.neighborSet g ∩ T).ncard := by
    rintro ⟨g, hgF, hcard⟩
    have hsubsingle : (G.neighborSet g ∩ T).Subsingleton := by
      intro u hu v hv
      rcases hgF with hgA | hg1
      · have hzu : u ≠ z := fun h => hzA g hgA (h ▸ hu.1).symm
        have hzv : v ≠ z := fun h => hzA g hgA (h ▸ hv.1).symm
        have huT : u = z ∨ u = x 2 ∨ u = x 0 := by simpa [T] using hu.2
        have hvT : v = z ∨ v = x 2 ∨ v = x 0 := by simpa [T] using hv.2
        have hu' := huT.resolve_left hzu
        have hv' := hvT.resolve_left hzv
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
        · rfl
        · have hgf : g = f := hfuniq g hgA hu.1.symm
          exact absurd (hgf ▸ hv.1.symm) h0f
        · have hgf : g = f := hfuniq g hgA hv.1.symm
          exact absurd (hgf ▸ hu.1.symm) h0f
        · rfl
      · have hg : g = x 1 := by simpa using hg1
        subst g
        have hu' : u = z := by
          rcases (show u = z ∨ u = x 2 ∨ u = x 0 by simpa [T] using hu.2) with h | h | h
          · exact h
          · exact absurd (h ▸ hu.1) (fun e => hx21 e.symm)
          · exact absurd (h ▸ hu.1) (fun e => Thm192Setup.x0_not_adj_x1 hws e.symm)
        have hv' : v = z := by
          rcases (show v = z ∨ v = x 2 ∨ v = x 0 by simpa [T] using hv.2) with h | h | h
          · exact h
          · exact absurd (h ▸ hv.1) (fun e => hx21 e.symm)
          · exact absurd (h ▸ hv.1) (fun e => Thm192Setup.x0_not_adj_x1 hws e.symm)
        exact hu'.trans hv'.symm
    have hle : (G.neighborSet g ∩ T).ncard ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).mpr hsubsingle
    omega
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T htri F hFsub hcatch with
    href | htwo
  · obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, hTeq, hBsub, hreff⟩ := href
    let D : List V := [a₀, b₁, a₂, b₀, a₁, b₂]
    have hD : IsAntiholeList G D := by
      exact ReflectionAntihole.isAntiholeList_of_reflection hreff
    have hzFirst : z ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have hx0First : x 0 ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have firstMemD : ∀ w ∈ ({a₀, a₁, a₂} : Set V), w ∈ D := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;> simp [D]
    have secondMemD : ∀ w ∈ ({b₀, b₁, b₂} : Set V), w ∈ D := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;> simp [D]
    obtain ⟨bz, hbzB, hzbz⟩ :
        ∃ bz ∈ ({b₀, b₁, b₂} : Set V), G.Adj z bz := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzFirst
      rcases hzFirst with h | h | h
      · refine ⟨b₀, by simp, ?_⟩
        rw [h]
        exact (hreff.2.2.2 a₀ (by simp) b₀ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨b₁, by simp, ?_⟩
        rw [h]
        exact (hreff.2.2.2 a₁ (by simp) b₁ (by simp)).mpr
          (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · refine ⟨b₂, by simp, ?_⟩
        rw [h]
        exact (hreff.2.2.2 a₂ (by simp) b₂ (by simp)).mpr
          (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have hbzF := hBsub hbzB
    have hbz1 : bz = x 1 := by
      rcases hbzF with hbzA | hbz1
      · exact absurd hzbz (hzA bz hbzA)
      · simpa using hbz1
    have hx1D : x 1 ∈ D := hbz1 ▸ secondMemD bz hbzB
    have hznotP : z ∉ P := by
      intro hzP
      by_cases hz0 : z = x 0
      · exact hxne 0 (by omega) hz0.symm
      by_cases hz1 : z = x 1
      · exact hxne 1 (by omega) hz1.symm
      exact hznotA (hPint z ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
        ⟨hzP, hz0, hz1⟩))
    have hzint : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w :=
      fun w hw => hzA w (hPint w hw)
    have hC : IsHoleList G (z :: P) :=
      PrismBasics.isHoleList_of_path_add_vertex hP (by rw [pathLength]; omega)
        (hzx 0 (by omega)) (hzx 1 (by omega)) hznotP hzint
    have hPfour : 4 ≤ P.length := by
      by_contra hnot
      have hlen : P.length = 3 := by omega
      have hpos : 0 < P.length := by omega
      have h0 : P[0]'hpos = x 0 := PathBasics.getElem_zero_of_head? hP.2.1 hpos
      have hlast : P[P.length - 1]'(by omega) = x 1 :=
        PathBasics.getElem_last_of_getLast? hP.2.2 hpos
      have h01 := PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
      have h12 := PathBasics.path_adj_succ hP.1 (i := 1) (by omega)
      rw [h0] at h01
      have hlast2 : P[2]'(by omega) = x 1 := by
        simpa only [hlen] using hlast
      rw [hlast2] at h12
      have hmA := hPint (P[1]'(by omega))
        (PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega))
      refine Thm192Setup.wheelSystemA_no_complete (P[1]'(by omega)) (hA.1 hmA) ?_
      rw [Thm192Setup.wheelSystemX_one]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact h01.symm
      · exact h12
    have hClong : 4 < holeLength (z :: P) := by
      simp [holeLength]
      omega
    have hDlong : 4 < holeLength D := by simp [D, holeLength]
    have hncard := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hG.1
      (z :: P) D hC hClong hD hDlong
    have hsub : ({z, x 0, x 1} : Set V) ⊆
        {w : V | w ∈ z :: P} ∩ {w : V | w ∈ D} := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hwz | hw0 | hw1
      · subst w
        exact ⟨by simp, firstMemD z hzFirst⟩
      · subst w
        exact ⟨List.mem_cons_of_mem z (PathBasics.head_mem hP.2.1),
          firstMemD (x 0) hx0First⟩
      · subst w
        exact ⟨List.mem_cons_of_mem z (PathBasics.getLast_mem hP.2.2), hx1D⟩
    have hthree : ({z, x 0, x 1} : Set V).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨z, x 0, x 1, (hxne 0 (by omega)).symm,
        (hxne 1 (by omega)).symm,
        hxij 0 (by omega) 1 (by omega) (by omega), rfl⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · exact (hnoTwo htwo).elim

/-- PAPER (19.2, claim (10), printed p. 122):

*"For suppose that `x₂` is adjacent to `x₀` say. Suppose first that `x₀` is not
adjacent to `f`. Then `A ∪ {x₁}` catches the triangle `{z,x₂,x₀}`; the only
neighbour of `z` in `A ∪ {x₁}` is `x₁`; the only neighbour of `x₂` in
`A ∪ {x₁}` is `f`; `x₁,f` are both nonadjacent to `x₀`; and `A ∪ {x₁}` contains
no reflection of the triangle since that would give a 6-antihole with 3 vertices
in common with `C`, contradicting 17.1. So `x₀` is adjacent to `f`."* -/
theorem firstReflectionForcesAdjacency (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (y : V) (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (f : V) (hfA : f ∈ A) (hfadj : G.Adj (x 2) f)
    (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (hx20 : G.Adj (x 2) (x 0)) :
    G.Adj (x 0) f := by
  have hzx : ∀ i ≤ 2, G.Adj z (x i) := hws.2.2.2.2.2.2
  have hxij : x 0 ≠ x 1 := by
    intro h
    exact (by omega : (0 : ℕ) ≠ 1) (hws.2.1 0 (by omega) 1 (by omega) h)
  have hxiA : ∀ i ≤ 1, x i ∉ A := by
    intro i hi hmem
    exact Thm192Setup.wheelSystemA_no_z (x i) (hA.1 hmem) (hzx i (by omega))
  obtain ⟨P, hP, hPint⟩ := MinimalConnectedIsPath.exists_path_interior_in hA.2.1
    (hxiA 0 (by omega)) (hxiA 1 (by omega)) hA.2.2.1 hA.2.2.2.1
  have hPlen : 3 ≤ P.length := MinimalConnectedIsPath.three_le_length_of_not_adj hP
    hxij (Thm192Setup.x0_not_adj_x1 hws)
  exact firstReflectionForcesAdjacencyWithPath G hG z A₀ x hws Y y A hA P hP hPint
    hPlen f hfA hfadj hfuniq hx20

/-- PAPER (19.2, claim (10), printed p. 122), the remainder after the first
17.1 application:

*"So `x₀` is adjacent to `f`, and therefore `x₁` is nonadjacent to both `x₂,f`.
By (8) `x₂` is adjacent to `y`, and therefore not `Y₀`-complete. By (2) `z` is
`Y₀`-complete and `(C,Y₀)` is a wheel. Let `x₂-q₁-⋯-q_k-x₁` be a path ...
By 2.10, `Y` contains a leap or hat for `C₁`. But `y` is adjacent to `x₂`, and
all other vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`, which is
a subset of `{q₁,…,q_k}`, a contradiction."*

The hypotheses below record the four elementary consequences in the first two
sentences, leaving this lemma to encode only the wheel/path/leap argument. -/
theorem wheelLeapEndgame (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
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
    (f : V) (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (hx20 : G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (h0f : G.Adj (x 0) f) (h1f : ¬ G.Adj (x 1) f)
    (h2y : G.Adj (x 2) y) (h2Y0 : ¬ VertexComplete G (x 2) (Y \ {y})) :
    False :=
  Thm192Claim10Endgame.endgame G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
    hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq hx20 hx21
    h0f h1f h2y h2Y0

end Workspace.ProofLemmas.Thm192Claim10Core
