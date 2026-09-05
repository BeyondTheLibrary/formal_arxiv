import Workspace.ProofLemmas.Thm175Claim4FirstMiss

/-! Choosing the first `X\{x_s}`-complete vertex after `p₁` in 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4OtherComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- The first `V`-complete vertex after `p₁` has positive even zero-based
index, where `V=X\{x_s}`.  This is the choice of `c` in printed claim (4). -/
theorem first_other_complete (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (ht0 : s.t₀ = 0) (h1 : 1 < c.core.p.length)
    (hp₂W : VertexComplete G (c.core.p[1]'h1) (wSet s)) :
    ∃ k, ∃ hk : k < c.core.p.length, 2 ≤ k ∧ Even k ∧
      VertexComplete G (c.core.p[k]'hk)
        (c.X \ {s.qX[s.qX.length - 1]'(by have := s.hXlong; omega)}) ∧
      ∀ i (hi : i < c.core.p.length), 0 < i → i < k →
        ¬ VertexComplete G (c.core.p[i]'hi)
          (c.X \ {s.qX[s.qX.length - 1]'(by have := s.hXlong; omega)}) := by
  classical
  have hs := s.hXlong
  let xs := s.qX[s.qX.length - 1]'(by omega)
  let U := c.X \ {xs}
  let y := s.qY[s.t₀]'s.ht₀
  have hW : wSet s = c.X \ {s.x₁} := by simp [wSet, ht0]
  have hqpath : IsPathList Gᶜ s.qX := by
    have hh := PathBasics.isPathList_take s.hanti.1 (k := s.qX.length) (by omega)
    simpa using hh
  have hq : IsAntipathFrom G s.qX s.x₁ xs := by
    refine ⟨hqpath, s.hxhead, ?_⟩
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hxne : s.x₁ ≠ xs := PathBasics.isPathFrom_ends_ne hq (by dsimp [pathLength]; omega)
  have hUlist : U = {v | v ∈ s.qX.dropLast} := by
    ext v
    change (v ∈ c.X ∧ v ≠ xs) ↔ v ∈ s.qX.dropLast
    rw [PathBasics.mem_dropLast_iff hqpath.2.1 hqpath.1, s.hXverts]
    have he : s.qX.getLast hqpath.1 = xs := by simp [xs, List.getLast_eq_getElem]
    rw [he]
  have hUa : AnticonnectedSet G U := by
    rw [hUlist, List.dropLast_eq_take]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_take hqpath (by omega))
  have hyY : y ∈ c.Y := (s.hYverts _).mp (List.getElem_mem s.ht₀)
  have hyX : y ∉ c.X := fun hx => Set.disjoint_left.mp (blocks_disjoint s) hx hyY
  have hyP : y ∉ c.core.p := fun hy => c.core.houtY y hy hyY
  have hyNotX : ¬ VertexComplete G y c.X := by
    intro hc
    apply Thm175Claim4FirstMiss.missed_not_complete s
    rw [hW]
    exact fun v hv => hc v hv.1
  have hyU : VertexComplete G y U := by
    intro v hv
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem ((s.hXverts v).mpr hv.1)
    have hil : i + 1 < s.qX.length := by
      have hine : i ≠ s.qX.length - 1 := by
        intro he
        apply hv.2
        change v = xs
        rw [← hiv]
        dsimp [xs]
        congr 1
      omega
    have ht := s.ht₀
    have hi' : i < (s.qX ++ s.qY).length := by simp; omega
    have hy' : s.qX.length + s.t₀ < (s.qX ++ s.qY).length := by simp; omega
    have hnon := PathBasics.path_not_adj_of_gap s.hanti.1 hi' hy' (by omega) (by omega)
    have hvi : (s.qX ++ s.qY)[i]'hi' = v := by rw [List.getElem_append_left hi]; exact hiv
    have hyi : (s.qX ++ s.qY)[s.qX.length + s.t₀]'hy' = y := by simp [y]
    rw [hvi, hyi] at hnon
    by_contra ha
    exact hnon ((SimpleGraph.compl_adj G v y).mpr
      ⟨fun he => hyX (he ▸ hv.1), fun hh => ha hh.symm⟩)
  obtain ⟨d, hd, hd2, hdy, hybefore⟩ := Thm175Claim5Hole.exists_first_neighbor hG s hfirst
  let T := c.core.p.take (d + 1)
  let R := T ++ [y]
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
    have hit : i < (c.core.p.take (d + 1)).length := hi
    have hid : i ≤ d := by have := List.length_take_le (d + 1) c.core.p; omega
    have hip : i < c.core.p.length := by omega
    have hine : i ≠ d := by intro he; apply hne; simp [T, he]
    exact hybefore i hip (by omega) (by simpa [T] using ha)
  have hRoutX : ∀ v ∈ R, v ∉ c.X := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact c.core.houtX v (hTsub v hv)
    · have he : v = y := by simpa using hv
      exact fun hx => hyX (he ▸ hx)
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
  have hQout : ∀ v ∈ R ++ [z], v ∉ c.X := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hRoutX v hv
    · have he : v = z := by simpa using hv
      exact fun hx => c.hz (Or.inl ((congrArg (fun w => w ∈ c.X) he).mp hx))
  have hcleanQ : ∀ v ∈ SPGT.interior (R ++ [z]), ¬ VertexComplete G v c.X := by
    intro v hv hc
    have hh := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hv
    rcases List.mem_append.mp hh.1 with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · exact hh.2.1 ((hfirst v (hTsub v hv)).mp hc)
      · have he : v = y := by simpa using hv
        exact hyNotX (he ▸ hc)
    · exact hh.2.2 (by simpa using hv)
  have hQl : pathLength (R ++ [z]) = d + 2 := by
    simp [R, T, pathLength, Nat.min_eq_left (show d + 1 ≤ c.core.p.length by omega)]
  have hRl : pathLength R = d + 1 := by
    simp [R, T, pathLength, Nat.min_eq_left (show d + 1 ≤ c.core.p.length by omega)]
  have hRodd : Odd (pathLength R) := by
    have he : Even (pathLength (R ++ [z])) := by
      apply Nat.not_odd_iff_even.mp
      intro ho
      have hthree := Thm175Claim4CleanPaths.length_three hG.1.1 c.hXa hQ
        (by rw [hQl]; omega) hQout c.core.hp₁X
        (fun v hv => c.hzXY v (Or.inl hv)) hcleanQ ho
      omega
    rw [Nat.even_iff, hQl] at he
    rw [Nat.odd_iff, hRl]
    omega
  have hintR : ∀ v ∈ SPGT.interior R, v ∈ c.core.p ∧ v ≠ c.core.p₁ := by
    intro v hv
    have hh := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hv
    rcases List.mem_append.mp hh.1 with hv | hv
    · exact ⟨hTsub v hv, hh.2.1⟩
    · exact (hh.2.2 (by simpa using hv)).elim
  have hex : ∃ i, ∃ hi : i < c.core.p.length, 0 < i ∧
      VertexComplete G (c.core.p[i]'hi) U := by
    by_contra hn
    have hclean : ∀ v ∈ SPGT.interior R, ¬ VertexComplete G v U := by
      intro v hv hc
      obtain ⟨hvP, hvne⟩ := hintR v hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvP
      have hi0 : i ≠ 0 := by intro he; subst i; exact hvne hp0
      exact hn ⟨i, hi, by omega, hc⟩
    have he := Thm175Claim4CleanPaths.even hG.1.1.1.1 hUa hR (by rw [hRl]; omega)
      (fun v hv hu => hRoutX v hv hu.1) (fun v hv => c.core.hp₁X v hv.1) hyU hclean
      z (fun v hv => c.hzXY v (Or.inl hv.1)) (fun v hv => c.core.hzanti v (hintR v hv).1)
    exact Nat.not_odd_iff_even.mpr he hRodd
  obtain ⟨hk, hkpos, hkU⟩ := Nat.find_spec hex
  have hmin : ∀ i (hi : i < c.core.p.length), 0 < i → i < Nat.find hex →
      ¬ VertexComplete G (c.core.p[i]'hi) U := by
    intro i hi hip hik hc
    exact Nat.find_min hex hik ⟨hi, hip, hc⟩
  have hk2 : 2 ≤ Nat.find hex := by
    have hkne : Nat.find hex ≠ 1 := by
      intro he
      have hc : VertexComplete G (c.core.p[1]'h1) U := by
        have hget : c.core.p[Nat.find hex]'hk = c.core.p[1]'h1 :=
          c.core.hp.1.2.1.getElem_inj_iff.mpr he
        rw [← hget]
        exact hkU
      have hx : G.Adj (c.core.p[1]'h1) s.x₁ := hc s.x₁ ⟨x₁_mem s, hxne⟩
      have heq := (hfirst _ (List.getElem_mem h1)).mp
        (complete_X_of_complete_wSet s hp₂W hx.symm)
      have := c.core.hp.1.2.1.getElem_inj_iff.mp (heq.trans hp0.symm)
      omega
    omega
  have hK : IsPathFrom G (c.core.p.take (Nat.find hex + 1)) c.core.p₁
      (c.core.p[Nat.find hex]'hk) := by
    simpa only [List.drop_zero, Nat.sub_zero, hp0] using
      PathBasics.isPathFrom_slice c.core.hp.1 hkpos hk
  have hKlen : pathLength (c.core.p.take (Nat.find hex + 1)) = Nat.find hex := by
    simp only [pathLength, List.length_take]
    omega
  have hKclean : ∀ v ∈ SPGT.interior (c.core.p.take (Nat.find hex + 1)),
      ¬ VertexComplete G v U := by
    intro v hv hc
    have hv' : v ∈ SPGT.interior ((c.core.p.drop 0).take (Nat.find hex - 0 + 1)) := by simpa using hv
    obtain ⟨i, hi, hi0, hik, hiv⟩ :=
      (PathBasics.mem_interior_slice_iff c.core.hp.1 hkpos hk).mp hv'
    exact hmin i hi hi0 hik (hiv ▸ hc)
  have heven := Thm175Claim4CleanPaths.even hG.1.1.1.1 hUa hK (by rw [hKlen]; omega)
    (fun v hv hu => c.core.houtX v (List.take_subset _ _ hv) hu.1)
    (fun v hv => c.core.hp₁X v hv.1) hkU hKclean z
    (fun v hv => c.hzXY v (Or.inl hv.1))
    (fun v hv => c.core.hzanti v (List.take_subset _ _ (PathBasics.interior_subset hv)))
  rw [hKlen] at heven
  exact ⟨Nat.find hex, hk, hk2, heven, hkU, hmin⟩

end Workspace.ProofLemmas.Thm175Claim4OtherComplete
