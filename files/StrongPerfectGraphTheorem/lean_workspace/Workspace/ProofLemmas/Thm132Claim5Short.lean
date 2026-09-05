import Workspace.ProofLemmas.Thm132Claim5Long
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S03.Thm_3_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The length-three half of claim (5) in 13.2

This module contains the first structural consequence used in the short-path
case.  If the trajectory had more than one term, 3.3 applied to an arbitrary
nontrivial rung, the hole `r-a-P-b-b₀-r`, and the even antipath
`r-W-a` would give two distinct vertices where 3.3 permits at most one.
Consequently the middle class of the strip is empty.
-/

namespace Workspace.ProofLemmas.Thm132Claim5Short

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {P : List V} (hP : IsRungOfStrip G A C B a P b) :
    ∀ z ∈ P, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hP.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hP.2.2.1))
  · exact Or.inr (hP.2.2.2.2.2 z
      ((PathBasics.mem_interior_iff_of_pathFrom hP.1).mpr ⟨hz, hza, hzb⟩))

/-- The hole `r-a-P-b-b₀-r` used in the 3.3 application. -/
private theorem rung_trajectory_hole
    {G : SimpleGraph V} {A C B : Set V} {r b₀ a b : V} {P : List V}
    (hleft : IsLeftStar G A C B r) (hright : IsRightStar G A C B b₀)
    (hrb₀ : G.Adj r b₀) (hP : IsRungOfStrip G A C B a P b)
    (hP3 : 3 ≤ pathLength P) :
    IsHoleList G (r :: (P ++ [b₀])) := by
  have hb₀P : b₀ ∉ P := by
    intro hb₀P
    exact hright.1 (rung_mem_strip hP b₀ hb₀P)
  have hb₀single : IsPathFrom G [b₀] b₀ b₀ :=
    ⟨PathBasics.isPathList_singleton G b₀, by simp, by simp⟩
  have hPS : IsPathFrom G (P ++ [b₀]) a b₀ := by
    refine Workspace.ProofLemmas.PathGlue.glue_path
      (u₀ := a) (u₁ := b) (w₀ := b₀) (w₁ := b₀)
      hP.1 hb₀single ?_ ?_
    · intro z hz
      simp only [List.mem_singleton]
      exact fun he => hb₀P (he ▸ hz)
    · intro z hz y hy
      simp only [List.mem_singleton] at hy
      subst y
      constructor
      · intro hzb₀
        have hzS := rung_mem_strip hP z hz
        refine ⟨?_, rfl⟩
        rcases hzS with (hzA | hzB) | hzC
        · exact absurd hzb₀.symm (hright.2.2 z (Or.inl hzA))
        · exact hP.2.2.2.2.1 z hz hzB
        · exact absurd hzb₀.symm (hright.2.2 z (Or.inr hzC))
      · rintro ⟨hzb, -⟩
        subst z
        exact (hright.2.1 b hP.2.2.1).symm
  have hrPS : r ∉ P ++ [b₀] := by
    intro hr
    rcases List.mem_append.mp hr with hrP | hrb
    · exact hleft.1 (rung_mem_strip hP r hrP)
    · exact hrb₀.ne (by simpa using hrb)
  have hr : IsPathFrom G [r] r r :=
    ⟨PathBasics.isPathList_singleton G r, by simp, by simp⟩
  have hcross : ∀ x ∈ [r], ∀ y ∈ P ++ [b₀],
      (G.Adj x y ↔ (x = r ∧ y = a) ∨ (x = r ∧ y = b₀)) := by
    intro x hx y hy
    simp only [List.mem_singleton] at hx
    subst x
    simp only [true_and]
    rcases List.mem_append.mp hy with hyP | hyb₀
    · have hyS := rung_mem_strip hP y hyP
      constructor
      · intro hry
        left
        rcases hyS with (hyA | hyB) | hyC
        · exact hP.2.2.2.1 y hyP hyA
        · exact absurd hry (hleft.2.2 y (Or.inl hyB))
        · exact absurd hry (hleft.2.2 y (Or.inr hyC))
      · rintro (hya | hyb)
        · subst y
          exact hleft.2.1 a hP.2.1
        · subst y
          exact hrb₀
    · have hyb : y = b₀ := by simpa using hyb₀
      subst y
      exact iff_of_true hrb₀ (Or.inr rfl)
  have hh := Workspace.ProofLemmas.PathGlue.glue_hole hr hPS
    (by
      intro z hz
      simp only [List.mem_singleton] at hz
      subst z
      exact hrPS)
    hcross (by
      rw [PathBasics.pathLength_eq] at hP3
      simp only [List.length_singleton, List.length_append]
      omega)
  simpa using hh

/-- If the trajectory has at least three terms (equivalently, more than one
under its known oddness), then 3.3 forces the middle strip class to be empty. -/
theorem C_eq_empty_of_long_trajectory
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w})
    (hra : G.Adj a₀ d.r)
    (hlast : IsRightStar G A C B d.last)
    (hwlong : 1 < d.w.length) : C = ∅ := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hrb₀ : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hwne : d.w ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlastMem : d.last ∈ d.w := by
    have hc := d.trajectory_antipath.2.2
    have hc' : d.w.getLast? = some d.last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hc
    exact PathBasics.getLast_mem hc'
  have hTout : ∀ z ∈ d.r :: d.w, z ∉ A ∪ B ∪ C := by
    intro z hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z
      exact d.optimal.1.2.2.1.1
    · exact bComplete_not_mem_strip hS (d.w_B_complete z hzw)
  have ha₀b₀_non : ¬ G.Adj a₀ b₀ := by
    have hlen : 3 ≤ R₀.length := by
      have := hK.1.1.2.2
      rw [PathBasics.pathLength_eq] at this
      omega
    have hn := PathBasics.path_ends_not_adj hban₀.1.1 hlen
    have h0 : R₀[0]'(by omega) = a₀ :=
      PathBasics.getElem_zero_of_head? hban₀.1.2.1 (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      PathBasics.getElem_last_of_getLast? hban₀.1.2.2 (by omega)
    simpa [h0, hl] using hn
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro c hcC
  obtain ⟨a, P, b, hP, hcP⟩ := hS.2.2.1 c (Or.inr hcC)
  have hca : c ≠ a := fun hca =>
    Set.disjoint_left.mp hS.1.2.1 hP.2.1 (hca.symm ▸ hcC)
  have hcb : c ≠ b := fun hcb =>
    Set.disjoint_left.mp hS.1.2.2 hP.2.2.1 (hcb.symm ▸ hcC)
  have hcint : c ∈ interior P :=
    (PathBasics.mem_interior_iff_of_pathFrom hP.1).mpr ⟨hcP, hca, hcb⟩
  have hP2 : 2 ≤ pathLength P := by
    have hlen : 3 ≤ P.length := by
      obtain ⟨k, hk, hk1, hk2, -⟩ := PathBasics.exists_getElem_of_mem_interior hP.1.1 hcint
      omega
    rw [PathBasics.pathLength_eq]
    omega
  have hPodd : Odd (pathLength P) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS
      a₀ b₀ R₀ hban₀).1 a P b hP
  have hP3 : 3 ≤ pathLength P := by
    obtain ⟨k, hk⟩ := hPodd
    omega
  have hH : IsHoleList G (d.r :: (P ++ [b₀])) :=
    rung_trajectory_hole d.optimal.1.2.2.1 hban₀.2.2.2.1 hrb₀ hP hP3
  let H : List V := d.r :: (P ++ [b₀])
  let p₃ : V := P[1]'(by
    rw [PathBasics.pathLength_eq] at hP3
    omega)
  let rest : List V := P.drop 2 ++ [b₀]
  have hPpos : 0 < P.length := PathBasics.path_length_pos hP.1.1
  have hP1 : 1 < P.length := by
    rw [PathBasics.pathLength_eq] at hP3
    omega
  have hd0 : P = P[0]'hPpos :: P.drop 1 := by
    simpa using (List.drop_eq_getElem_cons (l := P) (i := 0) hPpos)
  have hd1 : P.drop 1 = P[1]'hP1 :: P.drop 2 := by
    simpa using (List.drop_eq_getElem_cons (l := P) (i := 1) hP1)
  have hPa : P[0]'hPpos = a :=
    PathBasics.getElem_zero_of_head? hP.1.2.1 hPpos
  have hHdef : H = d.r :: a :: p₃ :: rest := by
    have hPdef : P = a :: p₃ :: P.drop 2 := by
      calc
        P = P[0]'hPpos :: P.drop 1 := hd0
        _ = a :: P.drop 1 := by rw [hPa]
        _ = a :: P[1]'hP1 :: P.drop 2 := by rw [hd1]
        _ = a :: p₃ :: P.drop 2 := by rfl
    calc
      H = d.r :: (P ++ [b₀]) := rfl
      _ = d.r :: ((a :: p₃ :: P.drop 2) ++ [b₀]) :=
        congrArg (fun L => d.r :: (L ++ [b₀])) hPdef
      _ = d.r :: a :: p₃ :: (P.drop 2 ++ [b₀]) := rfl
      _ = d.r :: a :: p₃ :: rest := rfl
  have hHH : IsHoleList G H := by simpa [H] using hH
  have hHlast : H.getLast? = some b₀ := by
    simp only [H]
    rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat]
  have hH6 : 6 ≤ holeLength H := by
    simp only [H, holeLength, List.length_cons, List.length_append, List.length_singleton]
    rw [PathBasics.pathLength_eq] at hP3
    omega

  have haNotTraj : a ∉ d.r :: d.w := by
    intro haT
    exact hTout a haT (Or.inl (Or.inl hP.2.1))
  have haLastC : Gᶜ.Adj a d.last := by
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hlast.1 (he.symm ▸ Or.inl (Or.inl hP.2.1)),
      fun hadj => hlast.2.2 a (Or.inl hP.2.1) hadj.symm⟩
  have haOther : ∀ z ∈ d.r :: d.w, z ≠ d.last → ¬ Gᶜ.Adj a z := by
    intro z hz hzlast hcomp
    have haz : G.Adj a z := by
      rcases List.mem_cons.mp hz with hzr | hzw
      · subst z
        exact (d.optimal.1.2.2.1.2.1 a hP.2.1).symm
      · exact (d.before_last_A_complete z hzw hzlast a hP.2.1).symm
    exact (G.compl_adj a z).mp hcomp |>.2 haz
  let Q : List V := d.r :: (d.w ++ [a])
  have hQanti : IsAntipathFrom G Q d.r a := by
    simpa [Q] using (PathAttach.isPathFrom_concat (G := Gᶜ)
      d.trajectory_antipath haLastC haNotTraj haOther)
  have hQeven : Even (pathLength Q) := by
    obtain ⟨k, hk⟩ := d.w_odd
    refine ⟨k + 1, ?_⟩
    simp only [Q, pathLength, List.length_cons, List.length_append,
      List.length_singleton, List.length_nil] at hk ⊢
    omega
  have hQ4 : 4 ≤ pathLength Q := by
    simp only [Q, pathLength, List.length_cons, List.length_append,
      List.length_singleton, List.length_nil]
    obtain ⟨k, hk⟩ := d.w_odd
    omega
  have ha₀Q : VertexComplete G a₀ {z : V | z ∈ Q} := by
    intro z hz
    simp only [Q, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with hzr | hzw | hza
    · subst z
      exact hra
    · exact d.a₀_complete_w z hzw
    · subst z
      exact hban₀.2.2.1.2.1 a hP.2.1
  have ha₀H : VertexAnticomplete G a₀ {z : V | z ∈ H.drop 2} := by
    intro z hz
    change z ∈ H.drop 2 at hz
    have hzH : z ∈ H := List.mem_of_mem_drop hz
    have hnd := hHH.2.1
    rw [hHdef] at hnd hz
    simp only [List.drop_succ_cons, List.drop_zero] at hz
    have hrnot : d.r ∉ a :: p₃ :: rest := (List.nodup_cons.mp hnd).1
    have hanot : a ∉ p₃ :: rest := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    have hzr : z ≠ d.r := fun he =>
      hrnot (he ▸ List.mem_cons.mpr (Or.inr hz))
    have hza : z ≠ a := fun he => hanot (he ▸ hz)
    simp only [H, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hzH
    rcases hzH with hzrr | hzP | hzb₀
    · exact absurd hzrr hzr
    · have hzS := rung_mem_strip hP z hzP
      rcases hzS with (hzA | hzB) | hzC
      · exact absurd (hP.2.2.2.1 z hzP hzA) hza
      · exact hban₀.2.2.1.2.2 z (Or.inl hzB)
      · exact hban₀.2.2.1.2.2 z (Or.inr hzC)
    · subst z
      exact ha₀b₀_non

  have h33 := Workspace.Statements.S03.SPGT.thm_3_3 G hG H d.r a p₃ b₀ rest
    hH hH6 hHdef hHlast d.w Q rfl hQanti hQ4 hQeven a₀ ha₀Q ha₀H
  have hbH : b ∈ H := by
    simp only [H, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl (PathBasics.getLast_mem hP.1.2.2))
  have hb₀H : b₀ ∈ H := by simp [H]
  have hbDrop : b ∈ H.drop 2 := by
    have hb := hbH
    rw [hHdef] at hb ⊢
    simp only [List.mem_cons, List.drop_succ_cons, List.drop_zero] at hb ⊢
    rcases hb with hbr | hba | hbrest
    · exact absurd hbr (fun he => d.optimal.1.2.2.1.1
        (he.symm ▸ Or.inl (Or.inr hP.2.2.1)))
    · exact False.elim
        (Set.disjoint_left.mp hS.1.1 hP.2.1 (hba ▸ hP.2.2.1))
    · exact hbrest
  have hb₀Drop : b₀ ∈ H.drop 2 := by
    have hb := hb₀H
    rw [hHdef] at hb ⊢
    simp only [List.mem_cons, List.drop_succ_cons, List.drop_zero] at hb ⊢
    rcases hb with hb₀r | hb₀a | hbrest
    · exact absurd hb₀r hrb₀.ne.symm
    · exact absurd hb₀a (fun he => hban₀.2.2.2.1.1
        (he.symm ▸ Or.inl (Or.inl hP.2.1)))
    · exact hbrest
  have hbComp : VertexComplete G b {z : V | z ∈ d.w.dropLast} := by
    intro z hz
    exact (d.w_B_complete z (List.mem_of_mem_dropLast hz) b hP.2.2.1).symm
  have hb₀Comp : VertexComplete G b₀ {z : V | z ∈ d.w.dropLast} := by
    intro z hz
    exact hbW z (List.mem_of_mem_dropLast hz)
  have hbb₀ : b = b₀ := h33.1 b hbDrop b₀ hb₀Drop
    (Or.inl hbComp) (Or.inl hb₀Comp)
  exact hban₀.2.2.2.1.1 (hbb₀.symm ▸ Or.inl (Or.inr hP.2.2.1))

end Workspace.ProofLemmas.Thm132Claim5Short
