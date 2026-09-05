import Workspace.ProofLemmas.Thm131ComplementStars
import Workspace.ProofLemmas.Thm131EdgeCases
import Workspace.ProofLemmas.Thm132BanisterSeparation
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm131LastCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131OptimalLength
open Workspace.ProofLemmas.Thm131ComplementStars
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [G.adj_comm, h.2.2.2 v hv u hu]
    tauto

/-- Claim (5), in the reduced edge-banister setting: a long trajectory whose
last term is a right-star forces the middle class of the strip to be empty. -/
theorem middle_empty_of_last_rightStar
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    {a last : V} (ha : IsLeftStar G A C B a)
    (hlast : IsRightStar G A C B last)
    {w : List V} (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length) (hwlong : 1 < w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B) : C = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro c hcC
  have hstepAt : ∃ (a₁ : V) (R₁ : List V) (b₁ a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ c ∈ R₁ := by
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hcR⟩ :=
      hK.1.1.1.2.2.2.1 c (Or.inr hcC)
    rcases hcR with hcR | hcR
    · exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hcR⟩
    · exact ⟨a₂, R₂, b₂, a₁, R₁, b₁, step_symm hs, hcR⟩
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hcR₁⟩ := hstepAt
  have ha₁A := hs.1.2.1
  have hb₁B := hs.1.2.2.1
  have hb₂B := hs.2.1.2.2.1
  have hca : c ≠ a₁ := fun he =>
    Set.disjoint_left.mp hK.1.1.1.1.2.1 ha₁A (he.symm ▸ hcC)
  have hcb : c ≠ b₁ := fun he =>
    Set.disjoint_left.mp hK.1.1.1.1.2.2 hb₁B (he.symm ▸ hcC)
  have hcint : c ∈ interior R₁ :=
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).2
      ⟨hcR₁, hca, hcb⟩
  have hR₁len : 3 ≤ R₁.length := by
    obtain ⟨i, hi, hi1, hi2, -⟩ :=
      Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hs.1.1.1 hcint
    omega
  have hR₁odd : Odd (pathLength R₁) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      a₀ b₀ R₀ hK.1.1.2.1).1 a₁ R₁ b₁ hs.1

  let W : Set V := {z : V | z ∈ w.dropLast}
  have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlastW : w.getLast? = some last := by
    have hh := hanti.2.2
    rw [List.getLast?_cons_of_ne_nil hwne] at hh
    exact hh
  have hlastEq : w.getLast hwne = last := by
    have hh := hlastW
    rw [List.getLast?_eq_some_getLast hwne] at hh
    exact Option.some.inj hh
  have hWmem : ∀ z ∈ W, z ∈ w ∧ z ≠ last := by
    intro z hz
    have hzw : z ∈ w := List.mem_of_mem_dropLast hz
    have hzne : z ≠ last := by
      have hlastEq : w.getLast hwne = last := by
        have hh := hlastW
        rw [List.getLast?_eq_some_getLast hwne] at hh
        exact Option.some.inj hh
      have hznot := (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff
        (List.nodup_cons.mp hanti.1.2.1).2 hwne).1 hz |>.2
      intro he
      exact hznot (by rw [hlastEq, he])
    exact ⟨hzw, hzne⟩
  have hWanti : AnticonnectedSet G W := by
    apply Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    have htail : IsPathList Gᶜ w :=
      HyperprismRungStructure.isPathList_tail hanti.1 (by simp; omega)
    exact HyperprismRungStructure.isPathList_dropLast htail (by
      have := hodd
      obtain ⟨k, hk⟩ := this
      omega)
  have hR₁W : ∀ z ∈ R₁, z ∉ W := by
    intro z hzR hzW
    have hzstrip := rung_mem_strip hs.1 z hzR
    exact bComplete_not_mem_strip hK.1.1.1 (hwB z (hWmem z hzW).1) hzstrip
  have ha₁W : VertexComplete G a₁ W := by
    intro z hz
    exact (hbeforeA z (hWmem z hz).1 (hWmem z hz).2 a₁ ha₁A).symm
  have hb₁W : VertexComplete G b₁ W := by
    intro z hz
    exact (hwB z (hWmem z hz).1 b₁ hb₁B).symm
  have hb₂W : VertexComplete G b₂ W := by
    intro z hz
    exact (hwB z (hWmem z hz).1 b₂ hb₂B).symm

  by_cases hex : ∃ v ∈ interior R₁, VertexComplete G v W
  · obtain ⟨v, hvint, hvW⟩ := hex
    have hvC := hs.1.2.2.2.2.2 v hvint
    have hva : ¬ G.Adj v a := fun hadj =>
      ha.2.2 v (Or.inr hvC) hadj.symm
    have hvlast : ¬ G.Adj v last := fun hadj =>
      hlast.2.2 v (Or.inr hvC) hadj.symm
    have hvout : v ∉ a :: w := by
      intro hv
      rcases List.mem_cons.mp hv with hvaeq | hvw
      · exact ha.1 (hvaeq ▸ Or.inr hvC)
      · exact bComplete_not_mem_strip hK.1.1.1 (hwB v hvw) (Or.inr hvC)
    have hvpath : IsPathFrom Gᶜ [v] v v :=
      ⟨Workspace.ProofLemmas.PathBasics.isPathList_singleton Gᶜ v, rfl, rfl⟩
    have hcross : ∀ z ∈ a :: w, ∀ y ∈ [v],
        (Gᶜ.Adj z y ↔ (z = last ∧ y = v) ∨ (z = a ∧ y = v)) := by
      intro z hz y hy
      have hyv : y = v := by simpa using hy
      subst y
      constructor
      · intro hcomp
        by_cases hza : z = a
        · exact Or.inr ⟨hza, rfl⟩
        by_cases hzl : z = last
        · exact Or.inl ⟨hzl, rfl⟩
        have hzw : z ∈ w := (List.mem_cons.mp hz).resolve_left hza
        have hzW : z ∈ W := by
          change z ∈ w.dropLast
          apply (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff
            (List.nodup_cons.mp hanti.1.2.1).2 hwne).2
          exact ⟨hzw, fun he => hzl (he.trans hlastEq)⟩
        exact absurd (hvW z hzW).symm hcomp.2
      · rintro (⟨hzlast, -⟩ | ⟨hza, -⟩)
        · subst z
          exact (G.compl_adj last v).2 ⟨fun he => hvout (he ▸ List.mem_cons.mpr
              (Or.inr (Workspace.ProofLemmas.PathBasics.getLast_mem hlastW))),
            fun h => hvlast h.symm⟩
        · subst z
          exact (G.compl_adj a v).2
            ⟨fun he => hvout (he ▸ List.mem_cons.mpr (Or.inl rfl)), fun h => hva h.symm⟩
    have hhole : IsHoleList Gᶜ ((a :: w) ++ [v]) :=
      Workspace.ProofLemmas.PathGlue.glue_hole hanti hvpath
        (by intro z hz h; simp at h; exact hvout (h ▸ hz)) hcross (by simp; omega)
    have hev := hG.2 _ hhole
    simp only [holeLength, List.length_append, List.length_cons,
      List.length_singleton, List.length_nil, Nat.add_zero] at hev
    obtain ⟨ko, hko⟩ := hodd
    obtain ⟨ke, hke⟩ := hev
    omega
  · have hnoedge : ¬ ∃ u ∈ R₁, ∃ v ∈ R₁, EdgeComplete G W u v := by
      rintro ⟨u, hu, v, hv, huv, huW, hvW⟩
      by_cases hua : u = a₁
      · by_cases hub : u = b₁
        · have heq : a₁ = b₁ := hua.symm.trans hub
          exact Set.disjoint_left.mp hK.1.1.1.1.1 ha₁A (heq.symm ▸ hb₁B)
        · by_cases hva : v = a₁
          · subst u; subst v; exact G.irrefl huv
          · by_cases hvb : v = b₁
            · subst u; subst v
              have hn := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hs.1.1.1 hR₁len
              have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head?
                hs.1.1.2.1 (by omega)
              have hl := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
                hs.1.1.2.2 (by omega)
              rw [h0, hl] at hn
              exact hn huv
            · exact hex ⟨v,
                (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).2
                  ⟨hv, hva, hvb⟩, hvW⟩
      · by_cases hub : u = b₁
        · by_cases hva : v = a₁
          · subst u; subst v
            have hn := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hs.1.1.1 hR₁len
            have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head?
              hs.1.1.2.1 (by omega)
            have hl := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
              hs.1.1.2.2 (by omega)
            rw [h0, hl] at hn
            exact hn huv.symm
          · by_cases hvb : v = b₁
            · subst u; subst v; exact G.irrefl huv
            · exact hex ⟨v,
                (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).2
                  ⟨hv, hva, hvb⟩, hvW⟩
        · exact hex ⟨u,
            (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).2
              ⟨hu, hua, hub⟩, huW⟩
    have hhit := Workspace.Statements.S02.SPGT.thm_2_2 G hG W hWanti
      R₁ a₁ b₁ hs.1.1 hR₁W hR₁odd ha₁W hb₁W hnoedge b₂ hb₂W
    obtain ⟨z, hzint, hzb₂⟩ := hhit
    have hcross := (hs.2.2.2 z
      (Workspace.ProofLemmas.PathBasics.interior_subset hzint)
      b₂ (Workspace.ProofLemmas.PathBasics.getLast_mem hs.2.1.1.2.2)).1 hzb₂.symm
    rcases hcross with h | h
    · exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).1
        hzint |>.2.1 h.1
    · exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hs.1.1).1
        hzint |>.2.2 h.1

end Workspace.ProofLemmas.Thm131LastCase
