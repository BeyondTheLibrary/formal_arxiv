import Workspace.ProofLemmas.Thm131Claim6
import Workspace.ProofLemmas.Thm131LastMiss
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Claim (7) of the printed proof of 13.1

PAPER (printed p. 81):

*"(7) If no vertex in `R` is `W`-complete then the theorem holds.*

*For by (6) we may assume that there is a vertex `v` of `R` which is
`(W \ {wₙ})`-complete.  Hence `v` is nonadjacent to `wₙ`.  Since `n ≥ 3` and is
odd, and `a-w₁-⋯-wₙ-v-a` is not an odd antihole, it follows that `v` is adjacent
to `a`.  Consequently `v` is the unique `(W \ {wₙ})`-complete vertex in `R`.
From (6) we may assume that `v = b`, and `R` has length 1.  …  This proves (7)."*

The endgame of (7) — the antipath `b₁-a-w₁-⋯-wₙ-b`, the application of 2.1 in
`G`, and the two staircases obtained from `R'` of length 1 and of length > 1 —
is `Thm131LastMiss.terminal_miss_absurd`.
-/

namespace Workspace.ProofLemmas.Thm131Claim7

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131Claim6
open Workspace.ProofLemmas.Thm131LastMiss
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim (7). -/
theorem claim_seven
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    {b : V} (hb : IsRightStar G A C B b)
    {a : V} {R w : List V}
    (hopt : BOptimalBanister G A C B x a R b)
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hIH : ∀ (y : List V), y.length < x.length →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (Q : List V), BOptimalBanister G A C B y c Q d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c Q d z)
    {last : V} (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length) (hwlong : 1 < w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (hlast : IsRightStar G A C B last)
    (hnoW : ∀ r ∈ R, ¬ VertexComplete G r {u : V | u ∈ w}) :
    TrajectoryConclusion G a R b w := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hR : IsBanister G A C B a R b := hopt.1
  have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hwnodup : w.Nodup := (List.nodup_cons.mp hanti.1.2.1).2
  have hlastW : w.getLast? = some last := by
    simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
  have hlastEq : w.getLast hwne = last := by
    have hh := hlastW
    rw [List.getLast?_eq_some_getLast hwne] at hh
    exact Option.some.inj hh
  have hlastw : last ∈ w := Workspace.ProofLemmas.PathBasics.getLast_mem hlastW
  have hW'mem : ∀ z, z ∈ w.dropLast ↔ (z ∈ w ∧ z ≠ last) := by
    intro z
    rw [Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hwnodup hwne, hlastEq]
  have hbP : b ∈ R := Workspace.ProofLemmas.PathBasics.getLast_mem hR.1.2.2
  have haP : a ∈ R := Workspace.ProofLemmas.PathBasics.head_mem hR.1.2.1
  have hRpos : 0 < R.length :=
    Workspace.ProofLemmas.PathBasics.path_length_pos hR.1.1
  have hR0 : R[0]'hRpos = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR.1.2.1 hRpos
  have hRb : R[R.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.1.2.2 hRpos
  have hlastElem : w[w.length - 1]'(by omega) = last :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlastW (by omega)
  have hw0 : (w[0]'(by omega)) ∈ w.dropLast := by
    rw [hW'mem]
    refine ⟨List.getElem_mem _, ?_⟩
    intro he
    have := (List.Nodup.getElem_inj_iff hwnodup).mp (he.trans hlastElem.symm)
    omega
  have haNotW' : ¬ VertexComplete G a {z : V | z ∈ w.dropLast} := by
    intro hc
    have hadj : Gᶜ.Adj a (w[0]'(by omega)) := by
      have hp := Workspace.ProofLemmas.PathBasics.path_adj_succ hanti.1 (i := 0)
        (by simp; omega)
      simpa using hp
    exact hadj.2 (hc _ hw0)
  -- the neighbours of the left end on an induced path are unique
  have hnbA : ∀ z ∈ R, G.Adj a z → ∀ z' ∈ R, G.Adj a z' → z = z' := by
    have key : ∀ z ∈ R, G.Adj a z → ∃ h : 1 < R.length, z = R[1]'h := by
      intro z hz haz
      obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
      have h1 : G.Adj (R[0]'hRpos) (R[k]'hk) := by
        rw [hR0, hkz]; exact haz
      have hcase := (Workspace.ProofLemmas.PathBasics.path_adj_iff hR.1.1 hRpos hk).1 h1
      have hk1 : k = 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [← hkz]
      exact getElem_congr rfl hk1 hk
    intro z hz haz z' hz' haz'
    obtain ⟨h1, hz1⟩ := key z hz haz
    obtain ⟨h1', hz1'⟩ := key z' hz' haz'
    rw [hz1, hz1']
  -- PAPER: *"Hence `v` is nonadjacent to `wₙ`."*
  have hmissLast : ∀ u ∈ R, VertexComplete G u {z : V | z ∈ w.dropLast} →
      ¬ G.Adj u last := by
    intro u huR huW hadj
    refine hnoW u huR ?_
    intro z hz
    by_cases hzl : z = last
    · exact hzl ▸ hadj
    · exact huW z ((hW'mem z).2 ⟨hz, hzl⟩)
  have hnotw : ∀ u ∈ R, u ∉ w := by
    intro u huR hmem
    obtain ⟨b', hb'B⟩ := hS.2.1.2
    by_cases hua : u = a
    · exact (List.nodup_cons.mp hanti.1.2.1).1 (hua ▸ hmem)
    by_cases hub : u = b
    · exact hbnotw (hub ▸ hmem)
    · exact hR.2.2.2.2 u
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
          ⟨huR, hua, hub⟩) b' (Or.inl (Or.inr hb'B)) (hwB u hmem b' hb'B)
  -- PAPER: *"Since `n ≥ 3` and is odd, and `a-w₁-⋯-wₙ-v-a` is not an odd
  -- antihole, it follows that `v` is adjacent to `a`."*
  have hadjA : ∀ u ∈ R, VertexComplete G u {z : V | z ∈ w.dropLast} → G.Adj a u := by
    intro u huR huW
    by_contra hnadj
    have hune : u ≠ a := fun he => haNotW' (he ▸ huW)
    have hunotw : u ∉ w := hnotw u huR
    have hulast : ¬ G.Adj u last := hmissLast u huR huW
    have hone : IsPathFrom Gᶜ [u] u u := by
      refine ⟨⟨by simp, by simp, ?_⟩, rfl, by simp⟩
      intro i j hi hj
      simp only [List.length_singleton] at hi hj
      interval_cases i <;> interval_cases j <;> simp
    have hdisj : ∀ z ∈ a :: w, z ∉ [u] := by
      intro z hz hzv
      have hzeq : z = u := by simpa using hzv
      rcases List.mem_cons.mp hz with h | h
      · exact hune (hzeq ▸ h)
      · exact hunotw (hzeq ▸ h)
    have hcross : ∀ z ∈ a :: w, ∀ y ∈ [u],
        (Gᶜ.Adj z y ↔ (z = last ∧ y = u) ∨ (z = a ∧ y = u)) := by
      intro z hz y hy
      have hyv : y = u := by simpa using hy
      rw [hyv]
      constructor
      · intro hzy
        rcases List.mem_cons.mp hz with h | h
        · exact Or.inr ⟨h, rfl⟩
        · by_cases hzl : z = last
          · exact Or.inl ⟨hzl, rfl⟩
          · exact absurd (huW z ((hW'mem z).2 ⟨h, hzl⟩)).symm hzy.2
      · rintro (⟨hzl, -⟩ | ⟨hza, -⟩)
        · subst z
          exact (G.compl_adj last u).mpr ⟨fun he => hunotw (he ▸ hlastw), fun hh => hulast hh.symm⟩
        · subst z
          exact (G.compl_adj a u).mpr ⟨fun he => hune he.symm, hnadj⟩
    have hhole : IsHoleList Gᶜ ((a :: w) ++ [u]) :=
      Workspace.ProofLemmas.PathGlue.glue_hole hanti hone hdisj hcross
        (by simp; omega)
    have hev := hG.2 _ hhole
    simp only [holeLength, List.length_append, List.length_cons,
      List.length_nil] at hev
    obtain ⟨kk, hkk⟩ := hodd
    rw [Nat.even_iff] at hev
    omega
  by_cases hv : ∃ v ∈ R, VertexComplete G v {z : V | z ∈ w.dropLast}
  · obtain ⟨v, hvR, hvW⟩ := hv
    have hvlast : ¬ G.Adj v last := hmissLast v hvR hvW
    have hva : G.Adj a v := hadjA v hvR hvW
    -- PAPER: *"Consequently `v` is the unique `(W \ {wₙ})`-complete vertex in
    -- `R`.  From (6) we may assume that `v = b`, and `R` has length 1."*
    have huniq : ∀ u ∈ R, VertexComplete G u {z : V | z ∈ w.dropLast} → u = v :=
      fun u huR huW => hnbA u huR (hadjA u huR huW) v hvR hva
    by_cases hvb : v = b
    · subst hvb
      have hRone : pathLength R = 1 := by
        have h1 : G.Adj (R[0]'hRpos) (R[R.length - 1]'(by omega)) := by
          rw [hR0, hRb]; exact hva
        have hcase := (Workspace.ProofLemmas.PathBasics.path_adj_iff hR.1.1 hRpos
          (show R.length - 1 < R.length by omega)).1 h1
        have hRlen : R.length = 2 := by omega
        simp [pathLength, hRlen]
      have hbBefore : ∀ z ∈ w, z ≠ last → G.Adj v z := by
        intro z hz hzl
        exact hvW z ((hW'mem z).2 ⟨hz, hzl⟩)
      exact absurd (terminal_miss_absurd hG hK4 heven h1br h2br hK hx hb hopt
        htraj hIH hRone hanti hodd hwlong hbeforeA hwB hbnotw hbBefore hvlast
        hlast) (fun h => h.elim)
    · refine claim_six hG heven hK hR hanti hodd hwlong hbeforeA hwB hbnotw ?_ ?_
      · intro hbW
        exact hvb (huniq b hbP hbW).symm
      · rintro ⟨u, huR, u', hu'R, huu', huW, hu'W⟩
        exact huu'.ne ((huniq u huR huW).trans (huniq u' hu'R hu'W).symm)
  · -- no `(W \ {wₙ})`-complete vertex in `R` at all: claim (6) applies.
    push Not at hv
    refine claim_six hG heven hK hR hanti hodd hwlong hbeforeA hwB hbnotw ?_ ?_
    · exact hv b hbP
    · rintro ⟨u, huR, u', hu'R, huu', huW, hu'W⟩
      exact hv u huR huW

end Workspace.ProofLemmas.Thm131Claim7
