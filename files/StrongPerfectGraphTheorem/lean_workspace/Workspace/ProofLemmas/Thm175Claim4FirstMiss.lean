import Workspace.ProofLemmas.Thm175Claim4CleanPaths
import Workspace.ProofLemmas.Thm175Claim5Reduction
import Workspace.ProofLemmas.Thm175Claim5Hole

/-! The first-neighbour argument showing `t₀=1` in the proof of 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4FirstMiss

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- The last vertex of the antipath prefix misses its predecessor in `W`. -/
theorem missed_not_complete (s : Setup c) :
    ¬ VertexComplete G (s.qY[s.t₀]'s.ht₀) (wSet s) := by
  have hp := prefix_from s
  have hl : 3 ≤ (antiPrefix s).length := by
    simp only [antiPrefix, List.length_append, List.length_take]
    have := s.hXlong
    have := s.ht₀
    omega
  let i := (antiPrefix s).length - 2
  have hi : i < (antiPrefix s).length := by dsimp [i]; omega
  have hvW := Thm175Claim5Reduction.prefix_interior_wSet s _
    (PathBasics.getElem_mem_interior hp.1 hi (by dsimp [i]; omega) (by dsimp [i]; omega))
  have ha : Gᶜ.Adj ((antiPrefix s)[i]'hi) (s.qY[s.t₀]'s.ht₀) := by
    rw [← PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)]
    exact (PathBasics.path_adj_iff hp.1 hi (by omega)).mpr (Or.inl (by dsimp [i]; omega))
  intro hc
  exact ((SimpleGraph.compl_adj G _ _).mp ha).2 (hc _ hvW).symm

/-- PAPER: "... so the other end `y_{t₀}` is not [X-complete]; and hence
`t₀=1`, since all other vertices of `Y` are `X`-complete." -/
theorem first_miss_zero (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁)) :
    s.t₀ = 0 := by
  obtain ⟨d, hd, hd2, hdy, hybefore⟩ := Thm175Claim5Hole.exists_first_neighbor hG s hfirst
  let y := s.qY[s.t₀]'s.ht₀
  let A : Set V := c.X ∪ {v | v ∈ s.qY.take s.t₀}
  let T := c.core.p.take (d + 1)
  let R := T ++ [y]
  have hAxy : A ⊆ c.X ∪ c.Y := by
    rintro v (hx | hy)
    · exact Or.inl hx
    · exact Or.inr ((s.hYverts v).mp (List.take_subset _ _ hy))
  have hXA : c.X ⊆ A := Set.subset_union_left
  have hWA : wSet s ⊆ A := by rintro v (hx | hy); exact Or.inl hx.1; exact Or.inr hy
  have hAc : AnticonnectedSet G A := by
    have ht := PathBasics.isPathList_take s.hanti.1
      (k := s.qX.length + s.t₀) (by have := s.hXlong; omega)
    have hlist : (s.qX ++ s.qY).take (s.qX.length + s.t₀) = s.qX ++ s.qY.take s.t₀ := by
      rw [List.take_append, List.take_of_length_le (by omega)]
      simp
    rw [hlist] at ht
    have he : A = {v | v ∈ s.qX ++ s.qY.take s.t₀} := by
      ext v
      simp only [A, Set.mem_union, Set.mem_setOf_eq, List.mem_append, s.hXverts]
    rw [he]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList ht
  have hp₁A : VertexComplete G c.core.p₁ A := by
    rintro v (hx | hy)
    · exact c.core.hp₁X v hx
    · exact p₁_complete_wSet s v (Or.inr hy)
  have hzA : VertexComplete G z A := fun v hv => c.hzXY v (hAxy hv)
  have hyY : y ∈ c.Y := (s.hYverts _).mp (List.getElem_mem s.ht₀)
  have hyX : y ∉ c.X := fun hx => Set.disjoint_left.mp (blocks_disjoint s) hx hyY
  have hyP : y ∉ c.core.p := fun hy => c.core.houtY y hy hyY
  have hyA : y ∉ A := by
    rintro (hx | hy)
    · exact hyX hx
    · obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hy
      have hit : i < s.t₀ := lt_of_lt_of_le hi (List.length_take_le _ _)
      have he : s.qY[i]'(by have := s.ht₀; omega) = s.qY[s.t₀]'s.ht₀ := by
        simpa only [List.getElem_take] using hei
      have := (List.nodup_append.mp s.hanti.1.2.1).2.1.getElem_inj_iff.mp he
      omega
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (show 0 < c.core.p.length by omega)
  have hT : IsPathFrom G T c.core.p₁ (c.core.p[d]'hd) := by
    simpa only [List.drop_zero, Nat.sub_zero, hp0] using
      PathBasics.isPathFrom_slice c.core.hp.1 (show 0 < d by omega) hd
  have hTsub : ∀ v ∈ T, v ∈ c.core.p := fun v hv => List.take_subset _ _ hv
  have hR : IsPathFrom G R c.core.p₁ y := by
    apply PathAttach.isPathFrom_concat hT hdy (fun hy => hyP (hTsub y hy))
    intro v hv hne ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hid : i ≤ d := by
      have hh : i < (c.core.p.take (d + 1)).length := hi
      have := List.length_take_le (d + 1) c.core.p
      omega
    have hip : i < c.core.p.length := by omega
    have hine : i ≠ d := by intro he; apply hne; simp [T, he]
    exact hybefore i hip (by omega) (by simpa [T] using ha)
  have hzR : z ∉ R := by
    intro hz
    rcases List.mem_append.mp hz with hz | hz
    · exact c.core.hzP (hTsub z hz)
    · exact (c.hzXY y (Or.inr hyY)).ne (by simpa using hz)
  have hQ : IsPathFrom G (R ++ [z]) c.core.p₁ z := by
    apply PathAttach.isPathFrom_concat hR (c.hzXY y (Or.inr hyY)) hzR
    intro v hv hne
    rcases List.mem_append.mp hv with hv | hv
    · exact c.core.hzanti v (hTsub v hv)
    · exact (hne (by simpa using hv)).elim
  have hQout : ∀ v ∈ R ++ [z], v ∉ A := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · intro ha
        rcases hAxy ha with hx | hy
        · exact c.core.houtX v (hTsub v hv) hx
        · exact c.core.houtY v (hTsub v hv) hy
      · have he : v = y := by simpa using hv
        exact fun ha => hyA (he ▸ ha)
    · have he : v = z := by simpa using hv
      exact fun ha => c.hz ((congrArg (fun u => u ∈ c.X ∪ c.Y) he).mp (hAxy ha))
  have hcleanQ : ∀ v ∈ SPGT.interior (R ++ [z]), ¬ VertexComplete G v A := by
    intro v hv hc
    have hparts := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hv
    rcases List.mem_append.mp hparts.1 with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · exact hparts.2.1 ((hfirst v (hTsub v hv)).mp (fun x hx => hc x (hXA hx)))
      · have he : v = y := by simpa using hv
        exact missed_not_complete s (fun x hx => by simpa only [he] using hc x (hWA hx))
    · exact hparts.2.2 (by simpa using hv)
  have hQl : pathLength (R ++ [z]) = d + 2 := by
    simp [R, T, pathLength, Nat.min_eq_left (show d + 1 ≤ c.core.p.length by omega)]
  have hQeven : Even (pathLength (R ++ [z])) := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    have hthree := Thm175Claim4CleanPaths.length_three hG.1.1 hAc hQ
      (by rw [hQl]; omega) hQout hp₁A hzA hcleanQ ho
    omega
  have hRl : pathLength R = d + 1 := by
    simp [R, T, pathLength, Nat.min_eq_left (show d + 1 ≤ c.core.p.length by omega)]
  have hRodd : Odd (pathLength R) := by
    rw [Nat.odd_iff, hRl]
    rw [Nat.even_iff, hQl] at hQeven
    omega
  have hyNotX : ¬ VertexComplete G y c.X := by
    intro hyc
    have hRout : ∀ v ∈ R, v ∉ c.X := fun v hv hx =>
      hQout v (List.mem_append_left _ hv) (hXA hx)
    have hcleanR : ∀ v ∈ SPGT.interior R, ¬ VertexComplete G v c.X := by
      intro v hv hc
      have hparts := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hv
      rcases List.mem_append.mp hparts.1 with hv | hv
      · exact hparts.2.1 ((hfirst v (hTsub v hv)).mp hc)
      · exact hparts.2.2 (by simpa using hv)
    have hzantiR : ∀ v ∈ SPGT.interior R, ¬ G.Adj z v := by
      intro v hv
      have hparts := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hv
      rcases List.mem_append.mp hparts.1 with hv | hv
      · exact c.core.hzanti v (hTsub v hv)
      · exact (hparts.2.2 (by simpa using hv)).elim
    have he := Thm175Claim4CleanPaths.even hG.1.1.1.1 c.hXa hR (by rw [hRl]; omega)
      hRout c.core.hp₁X hyc hcleanR z (fun x hx => c.hzXY x (Or.inl hx)) hzantiR
    exact Nat.not_odd_iff_even.mpr he hRodd
  by_contra htne
  apply hyNotX
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem ((s.hXverts x).mpr hx)
  have ht := s.ht₀
  have hij : s.qX.length + s.t₀ < (s.qX ++ s.qY).length := by simp; omega
  have hii : i < (s.qX ++ s.qY).length := by simp; omega
  have hn := PathBasics.path_not_adj_of_gap s.hanti.1 hii hij (by omega) (by omega)
  have hxget : (s.qX ++ s.qY)[i]'hii = x := by
    rw [List.getElem_append_left hi]
    exact hix
  have hyget : (s.qX ++ s.qY)[s.qX.length + s.t₀]'hij = y := by simp [y]
  rw [hxget, hyget] at hn
  by_contra ha
  exact hn ((SimpleGraph.compl_adj G x y).mpr
    ⟨fun he => hyX (he ▸ hx), fun hh => ha hh.symm⟩)

end Workspace.ProofLemmas.Thm175Claim4FirstMiss
