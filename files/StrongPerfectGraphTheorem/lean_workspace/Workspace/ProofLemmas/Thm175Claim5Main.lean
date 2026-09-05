import Workspace.ProofLemmas.Thm175Claim5Reduction
import Workspace.ProofLemmas.Thm175Claim5Hole
import Workspace.ProofLemmas.Thm175Claim5Prism

/-! Assembly of the printed proof of claim (5) of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim5Main

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup
open Workspace.ProofLemmas.Thm175Claim5Reduction
open Workspace.ProofLemmas.Thm175Claim5Hole

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- PAPER: "For assume `h=1`; so `p₁` is the only neighbour of `x₁` in `P`."
The two complement arguments, 17.4, 15.7, and the final long prism contradict
this assumption. -/
theorem not_unique_neighbor (hG : InF7 G) (s : Setup c) (hopt : IsOptimal c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (hxonly : ∀ v ∈ c.core.p, G.Adj s.x₁ v → v = c.core.p₁) : False := by
  have hlen := path_length_four c
  obtain ⟨h1, hp₂W, hmax⟩ := last_complete_is_second hG s hopt hxonly
  obtain ⟨d, hd, hd2, hdy, hybefore⟩ := exists_first_neighbor hG s hfirst
  let p₂ := c.core.p[1]'h1
  let y := s.qY[s.t₀]'s.ht₀
  let C := s.x₁ :: (c.core.p.take (d + 1) ++ [y])
  let D := p₂ :: antiPrefix s
  have hC := first_neighbor_hole s hxonly d hd hd2 hdy hybefore
  have hD := second_prefix_antihole hG s hfirst hxonly h1 hp₂W
  have hxy := x₁_adj_missed_vertex s
  have hp₂P : p₂ ∈ c.core.p := List.getElem_mem h1
  have hyY : y ∈ c.Y := (s.hYverts _).mp (List.getElem_mem s.ht₀)
  have hyP : y ∉ c.core.p := fun hm => c.core.houtY y hm hyY
  have hxp₂ : s.x₁ ≠ p₂ := fun he => x₁_notMem_p s (he ▸ hp₂P)
  have hyp₂ : y ≠ p₂ := fun he => hyP (he ▸ hp₂P)
  have hxD : s.x₁ ∈ D := List.mem_cons_of_mem _ (PathBasics.head_mem (prefix_from s).2.1)
  have hyD : y ∈ D := List.mem_cons_of_mem _ (PathBasics.getLast_mem (prefix_from s).2.2)
  have hp₂C : p₂ ∈ C := by
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact Thm182EdgeSetTake.getElem_mem_take c.core.p h1 (by omega)
  have hDlen : D.length = 4 := four_of_three_shared hG.1 C D hC
    (by simp only [C, List.length_cons, List.length_append, List.length_singleton,
      List.length_take]; omega) hD s.x₁ y p₂ hxy.ne hxp₂ hyp₂
    (by simp [C]) (by simp [C]) hp₂C hxD hyD (by simp [D])
  have hs2 : s.qX.length = 2 := by
    simp only [D, antiPrefix, List.length_cons, List.length_append, List.length_take] at hDlen
    have := s.hXlong
    have := s.ht₀
    omega
  have ht0 : s.t₀ = 0 := by
    simp only [D, antiPrefix, List.length_cons, List.length_append, List.length_take] at hDlen
    have := s.hXlong
    have := s.ht₀
    omega
  obtain ⟨a, x₂, hq⟩ := PrismBasics.length_eq_two hs2
  have ha : a = s.x₁ := by have hh := s.hxhead; rw [hq] at hh; simpa using hh
  have hqX : s.qX = [s.x₁, x₂] := by simpa only [ha] using hq
  have hx₂X : x₂ ∈ c.X := (s.hXverts x₂).mp (by rw [hqX]; simp)
  have hx₂P : x₂ ∉ c.core.p := fun hm => c.core.houtX x₂ hm hx₂X
  have htake : s.qY.take (s.t₀ + 1) = [y] := by
    have hy0 : s.qY[0]'(by have := s.ht₀; omega) = y := by
      dsimp [y]
      congr 1
      omega
    rw [ht0]
    simp [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem
      (show 0 < s.qY.length by have := s.ht₀; omega), hy0]
  have hprefix : antiPrefix s = [s.x₁, x₂, y] := by
    rw [antiPrefix, hqX, htake]
    rfl
  have hpref : IsPathList Gᶜ [s.x₁, x₂, y] := by
    rw [← hprefix]
    exact (prefix_from s).1
  have hx₁x₂ : ¬ G.Adj s.x₁ x₂ := by
    have hadj := PathBasics.path_adj_succ hpref (i := 0) (by simp)
    exact ((SimpleGraph.compl_adj G s.x₁ x₂).mp (by simpa using hadj)).2
  have hx₂y : ¬ G.Adj x₂ y := by
    have hadj := PathBasics.path_adj_succ hpref (i := 1) (by simp)
    exact ((SimpleGraph.compl_adj G x₂ y).mp (by simpa using hadj)).2
  have hz₁ : G.Adj z s.x₁ := c.hzXY _ (Or.inl (x₁_mem s))
  have hz₂ : G.Adj z x₂ := c.hzXY _ (Or.inl hx₂X)
  have hzy : G.Adj z y := c.hzXY _ (Or.inr hyY)
  have hnodup : [s.x₁, x₂, y, z].Nodup := by
    have hn := hpref.2.1
    exact
      (List.nodup_append.mpr ⟨hn, (by simp : [z].Nodup), by
        intro v hv w hw he
        have hwz : w = z := by simpa using hw
        have hvz : v = z := he.trans hwz
        have hvR : v ∈ antiPrefix s := by rw [hprefix]; exact hv
        exact c.hz ((congrArg (fun u => u ∈ c.X ∪ c.Y) hvz).mp
          (prefix_subset s v hvR))⟩ : ([s.x₁, x₂, y] ++ [z]).Nodup)
  have hW : wSet s = {x₂} := by
    rw [wSet_eq_list, hqX, ht0]
    ext v
    simp
  have hx₁iff : ∀ v ∈ c.core.p, G.Adj s.x₁ v ↔ v = c.core.p₁ := by
    intro v hv
    exact ⟨hxonly v hv, fun he => he ▸ (c.core.hp₁X s.x₁ (x₁_mem s)).symm⟩
  have hx₂iff : ∀ v ∈ c.core.p, G.Adj x₂ v ↔ v = c.core.p₁ ∨ v = p₂ := by
    intro v hv
    constructor
    · intro ha
      have hvW : VertexComplete G v (wSet s) := by
        rw [hW]
        intro w hw
        have he : w = x₂ := hw
        simpa [he] using ha.symm
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      have hk1 := hmax k hk hvW
      rcases (show k = 0 ∨ k = 1 by omega) with hk0 | hk1
      · left
        subst k
        exact PathBasics.getElem_zero_of_head? c.core.hp.2.1 hk
      · right
        subst k
        rfl
    · rintro (he | he)
      · rw [he]
        exact (c.core.hp₁X x₂ hx₂X).symm
      · rw [he]
        exact (hp₂W x₂ (by rw [hW]; rfl)).symm
  exact Thm175Claim5Prism.contradiction G hG.1.1 c.core.p c.core.p₁ c.core.pₙ
    s.x₁ x₂ y z c.core.hp h1 (x₁_notMem_p s) hx₂P hyP c.core.hzP hnodup
    hx₁x₂ hx₂y hxy hz₁ hz₂ hzy hx₁iff hx₂iff c.core.hzanti d hd hd2 hdy hybefore

end Workspace.ProofLemmas.Thm175Claim5Main
