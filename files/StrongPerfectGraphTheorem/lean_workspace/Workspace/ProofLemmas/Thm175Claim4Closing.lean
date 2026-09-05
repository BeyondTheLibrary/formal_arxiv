import Workspace.ProofLemmas.Thm175Claim5Reduction

/-! The two antiholes at the end of the proof of 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Closing

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- PAPER: "Then `z-p_b-x₁-⋯-x_s-p_c-z` is an antihole, so `s` is odd.
But then `p₂-x₁-⋯-x_s-y₁-p₂` is an odd antihole, a contradiction."
The two antiholes differ in length by one. -/
theorem adjacent_complete_contradiction (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (ht0 : s.t₀ = 0) (h1 : 1 < c.core.p.length)
    (hp₂W : VertexComplete G (c.core.p[1]'h1) (wSet s))
    (u v : V) (huP : u ∈ c.core.p) (hvP : v ∈ c.core.p)
    (hune : u ≠ c.core.p₁) (hvne : v ≠ c.core.p₁)
    (huv : G.Adj u v) (huW : VertexComplete G u (wSet s))
    (hvV : VertexComplete G v
      (c.X \ {s.qX[s.qX.length - 1]'(by have := s.hXlong; omega)})) : False := by
  have hs := s.hXlong
  let xs := s.qX[s.qX.length - 1]'(by omega)
  have hxsX : xs ∈ c.X := (s.hXverts xs).mp (List.getElem_mem (by omega))
  have hW : wSet s = c.X \ {s.x₁} := by simp [wSet, ht0]
  have hux : ¬ G.Adj u s.x₁ := by
    intro ha
    exact hune ((hfirst u huP).mp (complete_X_of_complete_wSet s huW ha.symm))
  have hvxs : ¬ G.Adj v xs := by
    intro ha
    apply hvne
    apply (hfirst v hvP).mp
    intro x hx
    by_cases he : x = xs
    · simpa [he] using ha
    · exact hvV x ⟨hx, he⟩
  have hqpath : IsPathList Gᶜ s.qX := by
    have ht := PathBasics.isPathList_take s.hanti.1 (k := s.qX.length) (by omega)
    simpa using ht
  have hq : IsAntipathFrom G s.qX s.x₁ xs := by
    refine ⟨hqpath, s.hxhead, ?_⟩
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have huq : u ∉ s.qX := fun hm => c.core.houtX u huP ((s.hXverts u).mp hm)
  have hvq : v ∉ s.qX := fun hm => c.core.houtX v hvP ((s.hXverts v).mp hm)
  have hR : IsAntipathFrom G (u :: (s.qX ++ [v])) u v := by
    apply PathAttach.isPathFrom_cons_concat hq
    · exact (SimpleGraph.compl_adj G u s.x₁).mpr
        ⟨fun he => c.core.houtX u huP (he ▸ x₁_mem s), hux⟩
    · exact (SimpleGraph.compl_adj G v xs).mpr
        ⟨fun he => c.core.houtX v hvP (he ▸ hxsX), hvxs⟩
    · exact fun ha => ((SimpleGraph.compl_adj G u v).mp ha).2 huv
    · exact huv.ne
    · exact huq
    · exact hvq
    · intro x hx hne ha
      apply ((SimpleGraph.compl_adj G u x).mp ha).2
      apply huW x
      rw [hW]
      exact ⟨(s.hXverts x).mp hx, hne⟩
    · intro x hx hne ha
      exact ((SimpleGraph.compl_adj G v x).mp ha).2
        (hvV x ⟨(s.hXverts x).mp hx, hne⟩)
  have hzR : z ∉ u :: (s.qX ++ [v]) := by
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · exact c.core.hzP ((congrArg (fun w => w ∈ c.core.p) he).mpr huP)
    · rcases List.mem_append.mp hm with hzq | hzv
      · exact c.hz (Or.inl ((s.hXverts z).mp hzq))
      · have he : z = v := by simpa using hzv
        exact c.core.hzP ((congrArg (fun w => w ∈ c.core.p) he).mpr hvP)
  have hD₁ : IsAntiholeList G (z :: u :: (s.qX ++ [v])) := by
    apply PrismBasics.isAntiholeList_of_antipath_add_vertex hR
    · simp only [pathLength, List.length_cons, List.length_append, List.length_singleton]
      omega
    · exact (SimpleGraph.compl_adj G z u).mpr
        ⟨fun he => c.core.hzP ((congrArg (fun w => w ∈ c.core.p) he).mpr huP),
          c.core.hzanti u huP⟩
    · exact (SimpleGraph.compl_adj G z v).mpr
        ⟨fun he => c.core.hzP ((congrArg (fun w => w ∈ c.core.p) he).mpr hvP),
          c.core.hzanti v hvP⟩
    · exact hzR
    · intro x hx ha
      have hxq : x ∈ s.qX := by simpa [SPGT.interior] using hx
      exact ((SimpleGraph.compl_adj G z x).mp ha).2
        (c.hzXY x (Or.inl ((s.hXverts x).mp hxq)))
  have hp₂P := List.getElem_mem h1
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (show 0 < c.core.p.length by omega)
  have hp₂x : ¬ G.Adj (c.core.p[1]'h1) s.x₁ := by
    intro ha
    have he := (hfirst _ hp₂P).mp (complete_X_of_complete_wSet s hp₂W ha.symm)
    have := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
    omega
  have hp₂out : c.core.p[1]'h1 ∉ antiPrefix s := by
    intro hm
    rcases prefix_subset s _ hm with hx | hy
    · exact c.core.houtX _ hp₂P hx
    · exact c.core.houtY _ hp₂P hy
  have hD₂ : IsAntiholeList G ((c.core.p[1]'h1) :: antiPrefix s) := by
    apply PrismBasics.isAntiholeList_of_antipath_add_vertex (prefix_from s)
    · simp only [pathLength, antiPrefix, List.length_append, List.length_take]
      have := s.ht₀
      omega
    · exact (SimpleGraph.compl_adj G _ _).mpr
        ⟨fun he => c.core.houtX _ hp₂P (he ▸ x₁_mem s), hp₂x⟩
    · exact (SimpleGraph.compl_adj G _ _).mpr
        ⟨fun he => c.core.houtY _ hp₂P (he ▸
          (s.hYverts _).mp (List.getElem_mem s.ht₀)),
          Thm175Claim4Miss.second_misses hG s hfirst h1⟩
    · exact hp₂out
    · intro x hx ha
      exact ((SimpleGraph.compl_adj G _ _).mp ha).2
        (hp₂W x (Thm175Claim5Reduction.prefix_interior_wSet s x hx))
  have hB : Berge G := hG.1.1.1.1
  have he₁ := hB.2 _ hD₁
  have he₂ := hB.2 _ hD₂
  rw [Nat.even_iff] at he₁ he₂
  simp only [holeLength, List.length_cons, List.length_append,
    List.length_nil] at he₁
  simp only [holeLength, antiPrefix, List.length_cons, List.length_append,
    List.length_take, ht0] at he₂
  have := s.hYlong
  omega

end Workspace.ProofLemmas.Thm175Claim4Closing
