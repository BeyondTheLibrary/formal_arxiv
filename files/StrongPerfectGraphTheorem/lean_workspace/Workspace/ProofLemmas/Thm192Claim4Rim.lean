import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics

/-! The hole and wheel used in claim (4) of 19.2 (printed p. 119). -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm192Claim4Rim

open Workspace.Types.Core.SPGT Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No vertex of `A₁` is adjacent to both `x₀,x₁`. -/
theorem no_common {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {a : V} (ha : a ∈ wheelSystemA G z A₀ x 1) :
    ¬ (G.Adj a (x 0) ∧ G.Adj a (x 1)) := by
  rintro ⟨h0, h1⟩
  apply wheelSystemA_no_complete a ha
  rw [wheelSystemX_one]
  rintro b (rfl | rfl)
  · exact h0
  · exact h1

/-- The hub misses `A₁`, since its vertices are adjacent to both `x₀,x₁`. -/
theorem hub_outside {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {a : V}
    (ha : a ∈ wheelSystemA G z A₀ x 1) : a ∉ Y := by
  intro haY
  exact no_common ha ⟨(hHyp.2.2.1 a haY).symm, (hHyp.2.2.2.1 a haY).symm⟩

/-- PAPER: "let `C` be the hole `z-x₀-p₁-⋯-pₙ-x₁-z`."
It has at least six vertices: a four-hole gives a common neighbour in `A₁`, and
its length is even because the graph is Berge. -/
theorem rim {G : SimpleGraph V} (hG : Berge G) {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) {P : List V}
    (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ interior P, w ∈ wheelSystemA G z A₀ x 1) (hPlen : 3 ≤ P.length) :
    IsHoleList G (z :: P) ∧ 6 ≤ holeLength (z :: P) := by
  have hz0 := hws.2.2.2.2.2.2 0 (by omega)
  have hz1 := hws.2.2.2.2.2.2 1 (by omega)
  have hzP : z ∉ P := by
    intro hz
    have hzi := (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hz, hz0.ne, hz1.ne⟩
    exact no_common (hPint z hzi) ⟨hz0, hz1⟩
  have hC : IsHoleList G (z :: P) :=
    PrismBasics.isHoleList_of_path_add_vertex hP (by simp only [pathLength]; omega)
      hz0 hz1 hzP (fun w hw => wheelSystemA_no_z w (hPint w hw))
  refine ⟨hC, ?_⟩
  have hnot3 : P.length ≠ 3 := by
    intro h3
    have h0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have h1 := PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    have hi := PathBasics.getElem_mem_interior hP.1 (k := 1) (by omega) (by omega) (by omega)
    apply no_common (hPint _ hi)
    constructor
    · rw [← h0]
      exact (PathBasics.path_adj_succ hP.1 (i := 0) (by omega)).symm
    · rw [← h1]
      exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (Or.inl (by omega))
  obtain ⟨k, hk⟩ := hG.1 _ hC
  simp only [holeLength, List.length_cons] at hk ⊢
  omega

/-- PAPER: "The second is immediate, for otherwise `(C,Y)` satisfies the theorem."
A complete edge of `P` is disjoint from at least one of `zx₀,zx₁`. -/
theorem wheel_of_complete_edge {G : SimpleGraph V} (hG : Berge G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) (hzY : VertexComplete G z Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ interior P, w ∈ wheelSystemA G z A₀ x 1) (hPlen : 3 ≤ P.length)
    {u v : V} (hu : u ∈ P) (hv : v ∈ P) (he : EdgeComplete G Y u v) :
    Concl192 G z A₀ x Y := by
  have hrim := rim hG hws hP hPint hPlen
  have hzP : z ∉ P := (List.nodup_cons.mp hrim.1.2.1).1
  have h0 := PathBasics.head_mem hP.2.1
  have h1 := PathBasics.getLast_mem hP.2.2
  have hdisj : ∀ w ∈ z :: P, w ∉ Y := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (hHyp.1 w hwY).1 rfl
    · have hint := (PathBasics.mem_interior_iff_of_pathFrom hP).mpr
        ⟨hw, (hHyp.1 w hwY).2.1, (hHyp.1 w hwY).2.2.1⟩
      exact hub_outside hHyp (hPint w hint) hwY
  have hsub : {w : V | w ∈ z :: P} ⊆
      ({x 0, x 1, z} : Set V) ∪ wheelSystemA G z A₀ x 1 := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl (by simp)
    · by_cases hw0 : w = x 0
      · exact Or.inl (by simp [hw0])
      by_cases hw1 : w = x 1
      · exact Or.inl (by simp [hw1])
      · exact Or.inr (hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, hw0, hw1⟩))
  refine ⟨hzY, z :: P, ?_, List.mem_cons_of_mem _ h0, List.mem_cons_of_mem _ h1,
    List.mem_cons_self, hsub⟩
  refine ⟨hrim, ⟨Y_nonempty hHyp, hHyp.2.1, hdisj⟩, ?_⟩
  have hzU : z ≠ u := fun heq => hzP (heq ▸ hu)
  have hzV : z ≠ v := fun heq => hzP (heq ▸ hv)
  have h01 := x0_not_adj_x1 hws
  have choose_end : (x 0 ≠ u ∧ x 0 ≠ v) ∨ (x 1 ≠ u ∧ x 1 ≠ v) := by
    by_cases h0u : x 0 = u
    · right
      constructor
      · intro h1u
        have := hws.2.1 0 (by omega) 1 (by omega) (h0u.trans h1u.symm)
        omega
      · intro h1v
        exact h01 (by rw [h0u, h1v]; exact he.1)
    by_cases h0v : x 0 = v
    · right
      constructor
      · intro h1u
        exact h01 (by rw [h0v, h1u]; exact he.1.symm)
      · intro h1v
        have := hws.2.1 0 (by omega) 1 (by omega) (h0v.trans h1v.symm)
        omega
    · exact Or.inl ⟨h0u, h0v⟩
  rcases choose_end with hh | hh
  · exact ⟨z, x 0, u, v, List.mem_cons_self, List.mem_cons_of_mem _ h0,
      List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv,
      ⟨hws.2.2.2.2.2.2 0 (by omega), hzY, hHyp.2.2.1⟩, he, hzU, hzV, hh.1, hh.2⟩
  · exact ⟨z, x 1, u, v, List.mem_cons_self, List.mem_cons_of_mem _ h1,
      List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv,
      ⟨hws.2.2.2.2.2.2 1 (by omega), hzY, hHyp.2.2.2.1⟩, he, hzU, hzV, hh.1, hh.2⟩

end Workspace.ProofLemmas.Thm192Claim4Rim
