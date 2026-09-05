import Workspace.ProofLemmas.Thm132Claim2
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S12.Thm_12_5

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Claim (3) of 13.2

The last trajectory vertex has the diagonal pattern in 12.5 and hence is a
right-star.  To prove the remaining edge `a₀r`, assume it is absent and glue
the trajectory antipath in `G` to the three-vertex complementary path
`last-a-b₀-a₀`.  The result is an odd hole of `Gᶜ`.
-/

namespace Workspace.ProofLemmas.Thm132Claim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup
open Workspace.ProofLemmas.Thm132Claim2

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem pathList_three {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hacne : a ≠ c)
    (hac : ¬ G.Adj a c) :
    IsPathList G [a, b, c] := by
  have habne : a ≠ b := hab.ne
  have hbcne : b ≠ c := hbc.ne
  refine ⟨by simp, by simp [habne, hbcne, hacne], ?_⟩
  have key : ∀ i j : ℕ, i < 3 → j < 3 →
      ∀ (hi : i < [a, b, c].length) (hj : j < [a, b, c].length),
      (G.Adj ([a, b, c][i]'hi) ([a, b, c][j]'hj) ↔
        (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi3 hj3
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true hab (by first | omega | simp | tauto)
      | exact iff_of_true hab.symm (by first | omega | simp | tauto)
      | exact iff_of_true hbc (by first | omega | simp | tauto)
      | exact iff_of_true hbc.symm (by first | omega | simp | tauto)
      | exact iff_of_false hac (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => hac h.symm) (by first | omega | simp | tauto)
  exact fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj

/-- PAPER claim (3): the new left end sees the old left end, and the trajectory
ends in a right-star. -/
theorem left_end_adj_and_last_rightStar
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
    {i : ℕ} (hi : i < x.length)
    (hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a₀)
    (hbad : ¬ G.Adj x[i] a₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w}) :
    G.Adj a₀ d.r ∧ IsRightStar G A C B d.last := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hrb : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hrne : d.r ≠ a₀ := by
    intro hre
    obtain ⟨j', hj', hj'eq, hj'non, -⟩ := d.birth_r.2.2
    have hj'j : j' = d.birthIndex :=
      (List.Nodup.getElem_inj_iff hx.1.1).mp hj'eq
    subst j'
    exact hj'non (by simpa [hre] using (hprev d.birthIndex d.birth_before_bad).symm)
  have hrout := leftStar_adj_rightEnd_outside hK.1.1 d.optimal.1.2.2.1 hrne hrb
  have hrleft : LeftDiagonal G A C B a₀ R₀ b₀ d.r := by
    refine ⟨hrout, ?_⟩
    intro z hz
    rcases hz with hzA | rfl
    · exact d.optimal.1.2.2.1.2.1 z hzA
    · exact hrb
  have hrright : ¬ RightDiagonal G A C B a₀ R₀ b₀ d.r := by
    rintro ⟨-, hc⟩
    obtain ⟨b, hb⟩ := hS.2.1.2
    exact d.optimal.1.2.2.1.2.2 b (Or.inl hb) (hc b (Or.inl hb))
  have hwne : d.w ≠ [] := by
    intro he
    have ho := d.w_odd
    rw [he] at ho
    simp at ho
  have hlastMem : d.last ∈ d.w := by
    have hc := d.trajectory_antipath.2.2
    have hc' : d.w.getLast? = some d.last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hc
    exact PathBasics.getLast_mem hc'
  have hlastOut : d.last ∉ staircaseVertices A C B R₀ :=
    bComplete_adj_left_not_mem_staircase hK.1.1
      (d.w_B_complete d.last hlastMem) (d.a₀_complete_w d.last hlastMem).symm
  have hlastRightDiag : RightDiagonal G A C B a₀ R₀ b₀ d.last := by
    refine ⟨hlastOut, ?_⟩
    intro z hz
    rcases hz with hzB | rfl
    · exact d.w_B_complete d.last hlastMem z hzB
    · exact (d.a₀_complete_w d.last hlastMem).symm
  have hlastNotLeft : ¬ LeftDiagonal G A C B a₀ R₀ b₀ d.last := by
    rintro ⟨-, hc⟩
    obtain ⟨a, ha, hna⟩ := d.last_misses_A
    exact hna (hc a (Or.inl ha))
  have hInt : ∀ z ∈ interior (d.r :: d.w),
      LeftDiagonal G A C B a₀ R₀ b₀ z ∧
        RightDiagonal G A C B a₀ R₀ b₀ z := by
    intro z hz
    have hzall := (PathBasics.mem_interior_iff_of_pathFrom d.trajectory_antipath).mp hz
    have hzw : z ∈ d.w := by simpa [hzall.2.1] using hzall.1
    have hzA := d.before_last_A_complete z hzw hzall.2.2
    have hzout := bComplete_adj_left_not_mem_staircase hK.1.1
      (d.w_B_complete z hzw) (d.a₀_complete_w z hzw).symm
    constructor
    · refine ⟨hzout, ?_⟩
      intro y hy
      rcases hy with hyA | rfl
      · exact hzA y hyA
      · exact (hbW z hzw).symm
    · refine ⟨hzout, ?_⟩
      intro y hy
      rcases hy with hyB | rfl
      · exact d.w_B_complete z hzw y hyB
      · exact (d.a₀_complete_w z hzw).symm
  have hlastStar : IsRightStar G A C B d.last :=
    (Workspace.Statements.S12.SPGT.thm_12_5 G hG hK4 heven h1br h2br
      A C B a₀ b₀ R₀ hK (d.r :: d.w) d.r d.last d.trajectory_antipath
        hInt ⟨hrleft, hrright⟩ ⟨hlastRightDiag, hlastNotLeft⟩).2

  have hra₀ : G.Adj a₀ d.r := by
    by_contra hnra
    obtain ⟨a, ha, hlastA⟩ := d.last_misses_A
    have ha₀a : G.Adj a₀ a := hban₀.2.2.1.2.1 a ha
    have hb₀a_non : ¬ G.Adj b₀ a := hban₀.2.2.2.1.2.2 a (Or.inl ha)
    have hb₀a_ne : b₀ ≠ a := by
      intro heq
      subst a
      exact hban₀.2.2.2.1.1 (Or.inl (Or.inl ha))
    have ha_b₀c : Gᶜ.Adj a b₀ :=
      (G.compl_adj a b₀).mpr ⟨hb₀a_ne.symm, fun h => hb₀a_non h.symm⟩
    have hRlen : 3 ≤ R₀.length := by
      have := hK.1.1.2.2
      rw [PathBasics.pathLength_eq] at this
      omega
    have ha₀b₀_non : ¬ G.Adj a₀ b₀ := by
      have hn := PathBasics.path_ends_not_adj hban₀.1.1 hRlen
      have h0 : R₀[0]'(by omega) = a₀ :=
        PathBasics.getElem_zero_of_head? hban₀.1.2.1 (by omega)
      have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
        PathBasics.getElem_last_of_getLast? hban₀.1.2.2 (by omega)
      simpa [h0, hl] using hn
    have ha₀b₀_ne : a₀ ≠ b₀ := by
      have hp3 : 3 ≤ pathLength R₀ := hK.1.1.2.2
      exact PathBasics.isPathFrom_ends_ne hban₀.1 (by omega)
    have hb₀_a₀c : Gᶜ.Adj b₀ a₀ :=
      (G.compl_adj b₀ a₀).mpr ⟨ha₀b₀_ne.symm, fun h => ha₀b₀_non h.symm⟩
    have ha_a₀c_non : ¬ Gᶜ.Adj a a₀ := by
      intro hc
      exact (G.compl_adj a a₀).mp hc |>.2 ha₀a.symm
    have hsmall : IsPathFrom Gᶜ [a, b₀, a₀] a a₀ :=
      ⟨pathList_three ha_b₀c hb₀_a₀c ha₀a.ne' ha_a₀c_non, by simp, by simp⟩
    have hdisj : ∀ z ∈ d.r :: d.w, z ∉ [a, b₀, a₀] := by
      intro z hz
      rcases List.mem_cons.mp hz with hzr | hzw
      · subst z
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨?_, hrb.ne, hrne⟩
        exact fun heq => d.optimal.1.2.2.1.1 (heq ▸ Or.inl (Or.inl ha))
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨?_, ?_, ?_⟩
        · intro heq
          subst z
          exact bComplete_not_mem_strip hS (d.w_B_complete a hzw)
            (Or.inl (Or.inl ha))
        · intro heq
          subst z
          exact G.irrefl (hbW b₀ hzw)
        · intro heq
          subst z
          exact G.irrefl (d.a₀_complete_w a₀ hzw)
    have hcross : ∀ z ∈ d.r :: d.w, ∀ y ∈ [a, b₀, a₀],
        (Gᶜ.Adj z y ↔ (z = d.last ∧ y = a) ∨ (z = d.r ∧ y = a₀)) := by
      intro z hz y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hya | hyb | hya₀
      · subst y
        by_cases hzl : z = d.last
        · subst z
          refine iff_of_true ((G.compl_adj d.last a).mpr
            ⟨fun heq => hlastStar.1 (heq ▸ Or.inl (Or.inl ha)), hlastA⟩) ?_
          exact Or.inl ⟨rfl, rfl⟩
        · refine iff_of_false ?_ ?_
          · intro hc
            rcases List.mem_cons.mp hz with hzr | hzw
            · subst z
              exact (G.compl_adj d.r a).mp hc |>.2 (d.optimal.1.2.2.1.2.1 a ha)
            · exact (G.compl_adj z a).mp hc |>.2
                (d.before_last_A_complete z hzw hzl a ha)
          · rintro (⟨h, -⟩ | ⟨hzr, haa⟩)
            · exact hzl h
            · exact ha₀a.ne' haa
      · subst y
        refine iff_of_false ?_ ?_
        · intro hc
          rcases List.mem_cons.mp hz with hzr | hzw
          · subst z
            exact (G.compl_adj d.r b₀).mp hc |>.2 hrb
          · exact (G.compl_adj z b₀).mp hc |>.2 (hbW z hzw).symm
        · rintro (⟨-, h⟩ | ⟨-, h⟩)
          · exact hb₀a_ne h
          · exact ha₀b₀_ne h.symm
      · subst y
        by_cases hzr : z = d.r
        · subst z
          refine iff_of_true ((G.compl_adj d.r a₀).mpr ⟨hrne, fun h => hnra h.symm⟩) ?_
          exact Or.inr ⟨rfl, rfl⟩
        · refine iff_of_false ?_ ?_
          · intro hc
            have hzw : z ∈ d.w := by simpa [hzr] using hz
            exact (G.compl_adj z a₀).mp hc |>.2 (d.a₀_complete_w z hzw).symm
          · rintro (⟨hzl, h⟩ | ⟨h, -⟩)
            · exact ha₀a.ne h
            · exact hzr h
    have hh : IsHoleList Gᶜ ((d.r :: d.w) ++ [a, b₀, a₀]) :=
      Workspace.ProofLemmas.PathGlue.glue_hole d.trajectory_antipath hsmall hdisj hcross
        (by simp)
    have hevenHole := (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG).1 _ hh
    obtain ⟨kw, hkw⟩ := d.w_odd
    obtain ⟨ke, hke⟩ := hevenHole
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hke
    omega
  exact ⟨hra₀, hlastStar⟩

end Workspace.ProofLemmas.Thm132Claim3
