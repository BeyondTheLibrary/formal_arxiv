import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.KiteTailBasics

/-! Basic facts about the path used in claims (6) and (7) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim6Basics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem z_not_mem_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) : z ∉ wheelSystemA G z A₀ x 1 := by
  intro hz
  apply wheelSystemA_no_complete z hz
  rw [wheelSystemX_one]
  intro w hw
  rcases hw with rfl | rfl
  · exact hws.2.2.2.2.2.2 0 (by omega)
  · exact hws.2.2.2.2.2.2 1 (by omega)

theorem no_pair_complete {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {A : Set V} (hA : A ⊆ wheelSystemA G z A₀ x 1) :
    ∀ w ∈ A, ¬ (G.Adj w (x 0) ∧ G.Adj w (x 1)) := by
  rintro w hw ⟨h0, h1⟩
  apply wheelSystemA_no_complete w (hA hw)
  rw [wheelSystemX_one]
  intro v hv
  rcases hv with rfl | rfl
  · exact h0
  · exact h1

/-- The paper's hole `C = z-x₀-p₁-⋯-pₙ-x₁-z` has length at least six. -/
theorem path_facts {G : SimpleGraph V} (hG : Berge G) {z : V} {A₀ : Set V}
    {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2) {A : Set V}
    (hA : A ⊆ wheelSystemA G z A₀ x 1) {P : List V}
    (hP : IsPathFrom G P (x 0) (x 1)) (hPI : ∀ w ∈ SPGT.interior P, w ∈ A)
    (hlen : 3 ≤ P.length) :
    z ∉ P ∧ x 2 ∉ P ∧ IsHoleList G (z :: P) ∧ 5 ≤ P.length := by
  have hout : ∀ v, v ∉ A → v ≠ x 0 → v ≠ x 1 → v ∉ P := by
    intro v hv h0 h1 hvP
    exact hv (hPI v ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hvP, h0, h1⟩))
  have hzP : z ∉ P := hout z (fun h => z_not_mem_A1 hws (hA h))
    (hws.2.2.1 0 (by omega)).2.symm (hws.2.2.1 1 (by omega)).2.symm
  have hx2P : x 2 ∉ P := hout (x 2)
    (fun h => wheelSystemA_no_z _ (hA h) (hws.2.2.2.2.2.2 2 le_rfl))
    (fun h => by have := hws.2.1 2 le_rfl 0 (by omega) h; omega)
    (fun h => by have := hws.2.1 2 le_rfl 1 (by omega) h; omega)
  have hC : IsHoleList G (z :: P) := PrismBasics.isHoleList_of_path_add_vertex hP
    (by simp only [pathLength]; omega) (hws.2.2.2.2.2.2 0 (by omega))
    (hws.2.2.2.2.2.2 1 (by omega)) hzP
    (fun w hw => wheelSystemA_no_z w (hA (hPI w hw)))
  refine ⟨hzP, hx2P, hC, ?_⟩
  have heven := hG.1 _ hC
  rw [Nat.even_iff] at heven
  simp only [holeLength, List.length_cons] at heven
  have hnot3 : P.length ≠ 3 := by
    intro h3
    have h0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have h1 := PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    have ha0 : G.Adj (P[1]'(by omega)) (x 0) := by
      rw [← h0]
      exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (by omega)
    have ha1 : G.Adj (P[1]'(by omega)) (x 1) := by
      rw [← h1]
      exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (by omega)
    exact no_pair_complete hA _
      (hPI _ (PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)))
      ⟨ha0, ha1⟩
  omega

theorem Y_disjoint_path {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {Y A : Set V} (hH : Hyp192 G z A₀ x Y) (hA : A ⊆ wheelSystemA G z A₀ x 1)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ A) : ∀ w ∈ P, w ∉ Y := by
  intro w hw hwY
  have h0 := (hH.1 w hwY).2.1
  have h1 := (hH.1 w hwY).2.2.1
  exact no_pair_complete hA w
    (hPI w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, h0, h1⟩))
    ⟨(hH.2.2.1 w hwY).symm, (hH.2.2.2.1 w hwY).symm⟩

/-- Anticonnectedness supplies the antipath ending at the removed vertex `y`. -/
theorem antipath_to_y {G : SimpleGraph V} {Y : Set V} {y u : V}
    (hY : AnticonnectedSet G Y) (hyY : y ∈ Y) (huY : u ∉ Y)
    (hu : ¬ VertexComplete G u (Y \ {y})) :
    ∃ Q : List V, IsAntipathFrom G Q u y ∧
      ∀ w ∈ SPGT.interior Q, w ∈ Y \ {y} := by
  have hUY : AnticonnectedSet G (Y ∪ {u}) :=
    KiteTailBasics.anticonnectedSet_union_singleton hY (fun h => hu (fun w hw => h w hw.1))
  obtain ⟨Q, hQ, hQsub⟩ := InducedPathExtraction.exists_isAntipathFrom_of_anticonnected
    hUY (Or.inr rfl) (Or.inl hyY)
  refine ⟨Q, hQ, ?_⟩
  intro w hw
  obtain ⟨hwQ, hwu, hwy⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw
  refine ⟨?_, hwy⟩
  rcases hQsub w hwQ with hwY | hwU
  · exact hwY
  · exact (hwu hwU).elim

/-- PAPER (claim (2)): "From the minimality of `|Y|`, `z` is `Y₀`-complete
and therefore `Y`-complete." This uses only the conclusion for the smaller hub. -/
theorem z_complete_of_noncomplete {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {Y : Set V} (hH : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y})) : VertexComplete G z Y := by
  have hY0a : AnticonnectedSet G (Y \ {y}) := by
    rcases hY0 with h | h
    · exact (hx2nc (by rw [h]; intro v hv; exact (Set.notMem_empty v hv).elim)).elim
    · exact h
  have hcard : (Y \ {y}).ncard < Y.ncard := by
    rw [Set.ncard_diff_singleton_of_mem hyY]
    have hpos := (Set.ncard_pos (Set.toFinite Y)).mpr ⟨y, hyY⟩
    omega
  have hH0 : Hyp192 G z A₀ x (Y \ {y}) :=
    ⟨fun v hv => hH.1 v hv.1, hY0a, fun v hv => hH.2.2.1 v hv.1,
      (fun v hv => hH.2.2.2.1 v hv.1), hx2nc,
      fun v hv hn => hH.2.2.2.2.2 v hv.1 hn⟩
  have hz0 := (ih.1 _ hcard hH0).1
  intro v hv
  by_cases hvy : v = y
  · simpa only [hvy] using hyz.symm
  · exact hz0 v ⟨hv, hvy⟩

end Workspace.ProofLemmas.Thm192Claim6Basics
