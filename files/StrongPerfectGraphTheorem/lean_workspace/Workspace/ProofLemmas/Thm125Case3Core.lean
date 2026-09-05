import Workspace.ProofLemmas.Thm125Setup
import Workspace.ProofLemmas.Thm114Aux
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The Roussel--Rubio core of case (3) of Theorem 12.5

This module proves the part of the printed argument that reduces the endpoint-nonadjacent
case to a two-vertex antipath and produces the crossed old endpoints used to enlarge the
strip.
-/

namespace Workspace.ProofLemmas.Thm125Case3Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- When `qk` has an `A`-neighbour, case (3) supplies a crossed pair of old strip
vertices, proves that the antipath has just its two ends, and proves that both ends miss
the interior of the old banister. -/
theorem core
    (G : SimpleGraph V) (hG : Berge G)
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (h2breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' : V)
      (Q' : Set V), IsTwoBreaker G A' C' B' a₀' R₀' b₀' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : ¬ G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀)
    (aneigh : V) (haneighA : aneigh ∈ A) (hqkaneigh : G.Adj qk aneigh) :
    ∃ a₁ ∈ A, ∃ b₁ ∈ B,
      G.Adj qk a₁ ∧ G.Adj q₁ b₁ ∧ ¬ G.Adj a₁ b₁ ∧
      q = [q₁, qk] ∧
      (∀ z ∈ interior R₀, ¬ G.Adj q₁ z) ∧
      (∀ z ∈ interior R₀, ¬ G.Adj qk z) := by
  classical
  let Q : Set V := {z : V | z ∈ q}
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS : StepConnected G A C B := hstair.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hstair.2.1
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have hq2 : 2 ≤ q.length := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    by_contra hc
    have hlen : q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h1 : x = q₁ := by simpa using hq.2.1
    have hk : x = qk := by simpa using hq.2.2
    exact hne (h1.symm.trans hk)
  have ha₀b₀ : ¬ G.Adj a₀ b₀ := by
    have hlen : 4 ≤ R₀.length := by
      have hR3 := hstair.2.2
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hR3
      omega
    have hn := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hban.1.1 (by omega)
    have h0 : R₀[0]'(by omega) = a₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
    simpa [h0, hl] using hn
  have ha₀b₀ne : a₀ ≠ b₀ :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hban.1 (by exact hstair.2.2.trans' (by omega))
  have ha₀out : a₀ ∉ q := by
    intro h
    exact outside_of_mem hq hqint hq₁.1 hqk.1 h
      (Or.inl (Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1))
  have hb₀out : b₀ ∉ q := by
    intro h
    exact outside_of_mem hq hqint hq₁.1 hqk.1 h
      (Or.inl (Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2))
  have hqeven : Even q.length := by
    have hh : IsHoleList Gᶜ (b₀ :: a₀ :: q) := by
      apply Workspace.ProofLemmas.PrismBasics.isHoleList_of_path_add_two_vertices hq
        (by rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]; omega)
      · exact (G.compl_adj a₀ q₁).2 ⟨fun he => ha₀out
          (he ▸ Workspace.ProofLemmas.PathBasics.head_mem hq.2.1), fun h => hqa₀ h.symm⟩
      · exact (G.compl_adj b₀ qk).2 ⟨fun he => hb₀out
          (he ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2), fun h => hqkb₀ h.symm⟩
      · exact (G.compl_adj a₀ b₀).2 ⟨ha₀b₀ne, ha₀b₀⟩
      · exact ha₀out
      · exact hb₀out
      · intro hc
        exact hc.2 ((rightDiagonal_of_mem_ne_first hq hqint hqk.1
          (Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2) hne.symm).2 a₀
            (Or.inr rfl)).symm
      · intro hc
        exact hc.2 ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1
          (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1) hne).2 b₀
            (Or.inr rfl)).symm
      · intro z hz hc
        have hzq := Workspace.ProofLemmas.PathBasics.interior_subset hz
        have hz₁ := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.2.1
        exact hc.2 ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hzq hz₁).2
          a₀ (Or.inr rfl)).symm
      · intro z hz hc
        have hzq := Workspace.ProofLemmas.PathBasics.interior_subset hz
        have hzk := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.2.2
        exact hc.2 ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hzq hzk).2
          b₀ (Or.inr rfl)).symm
    have he := (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG).1 _ hh
    simp only [holeLength, List.length_cons] at he
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩

  let a₁ : V := aneigh
  have ha₁A : a₁ ∈ A := haneighA
  have hqka₁ : G.Adj qk a₁ := hqkaneigh
  obtain ⟨b₁, hb₁B, ha₁b₁⟩ :=
    Workspace.ProofLemmas.Thm114Aux.exists_nonneighbour_in_B hS ha₁A
  have ha₁neb₁ : a₁ ≠ b₁ := fun he =>
    Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₁B)
  have hq₁b₁ : G.Adj q₁ b₁ := by
    by_contra hq₁b₁
    have hb₁out : b₁ ∉ q := by
      intro h
      exact outside_of_mem hq hqint hq₁.1 hqk.1 h (Or.inr (Or.inl (Or.inr hb₁B)))
    let L : List V := b₁ :: (q ++ [b₀])
    have hL : IsPathFrom Gᶜ L b₁ b₀ := by
      dsimp [L]
      apply Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hq
      · exact (G.compl_adj b₁ q₁).2 ⟨fun he => hb₁out
          (he ▸ Workspace.ProofLemmas.PathBasics.head_mem hq.2.1), fun h => hq₁b₁ h.symm⟩
      · exact (G.compl_adj b₀ qk).2 ⟨fun he => hb₀out
          (he ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2), fun h => hqkb₀ h.symm⟩
      · intro hc
        exact hc.2 (hban.2.2.2.1.2.1 b₁ hb₁B).symm
      · exact (hban.2.2.2.1.2.1 b₁ hb₁B).ne'
      · exact hb₁out
      · exact hb₀out
      · intro z hz hz₁ hc
        exact hc.2 ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2
          b₁ (Or.inl hb₁B)).symm
      · intro z hz hzk hc
        exact hc.2 ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hzk).2
          b₀ (Or.inr rfl)).symm
    have ha₁outL : a₁ ∉ L := by
      intro h
      simp only [L, List.mem_cons, List.mem_append, List.mem_singleton] at h
      rcases h with hab | h
      · exact ha₁neb₁ hab
      · rcases h with hqmem | hb
        · exact outside_of_mem hq hqint hq₁.1 hqk.1 hqmem
            (Or.inr (Or.inl (Or.inl ha₁A)))
        · rcases hb with hb | hb
          · exact hban.2.2.2.1.1 (hb.symm ▸ Or.inl (Or.inl ha₁A))
          · simp at hb
    have ha₁b₀ : ¬ G.Adj a₁ b₀ := fun h =>
      hban.2.2.2.1.2.2 a₁ (Or.inl ha₁A) h.symm
    have hh : IsHoleList Gᶜ (a₁ :: L) := by
      apply Workspace.ProofLemmas.PrismBasics.isHoleList_of_path_add_vertex hL
        (by rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]; simp [L]; omega)
      · exact (G.compl_adj a₁ b₁).2 ⟨fun he =>
          Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₁B), ha₁b₁⟩
      · exact (G.compl_adj a₁ b₀).2 ⟨fun he => hban.2.2.2.1.1
          (he.symm ▸ Or.inl (Or.inl ha₁A)), ha₁b₀⟩
      · exact ha₁outL
      · intro z hz hc
        have hzmem := Workspace.ProofLemmas.PathBasics.interior_subset hz
        simp only [L, List.mem_cons, List.mem_append, List.mem_singleton] at hzmem
        have hzq : z ∈ q := by
          rcases hzmem with hzb | hzrest
          · exact (((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).1
              hz).2.1 hzb).elim
          · rcases hzrest with hzq | hzb₀
            · exact hzq
            · rcases hzb₀ with hzb₀ | hzb₀
              · exact (((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).1
                  hz).2.2 hzb₀).elim
              · simp at hzb₀
        by_cases hzk : z = qk
        · exact hc.2 (hzk ▸ hqka₁.symm)
        · exact hc.2 ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hzq hzk).2
            a₁ (Or.inl ha₁A)).symm
    have he := (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG).1 _ hh
    have hoddL : Odd (holeLength (a₁ :: L)) := by
      obtain ⟨k, hk⟩ := hqeven
      refine ⟨k + 1, ?_⟩
      simp [holeLength, L]
      omega
    exact (Nat.not_even_iff_odd.mpr hoddL) he

  have ha₁Q : VertexComplete G a₁ Q := by
    intro z hz
    by_cases hzk : z = qk
    · simpa [hzk] using hqka₁.symm
    · exact ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hzk).2
        a₁ (Or.inl ha₁A)).symm
  have hb₁Q : VertexComplete G b₁ Q := by
    intro z hz
    by_cases hz₁ : z = q₁
    · simpa [hz₁] using hq₁b₁.symm
    · exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2
        b₁ (Or.inl hb₁B)).symm
  have hQanti : AnticonnectedSet G Q :=
    Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList hq.1
  have hQout : ∀ z ∈ Q, z ∉ staircaseVertices A C B R₀ :=
    fun z hz => outside_of_mem hq hqint hq₁.1 hqk.1 hz
  have ha₀notQ : ¬ VertexComplete G a₀ Q := fun hc =>
    hqa₀ (hc q₁ (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1)).symm
  have hb₀notQ : ¬ VertexComplete G b₀ Q := fun hc =>
    hqkb₀ (hc qk (Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2)).symm
  have hnoIntQ : ∀ z ∈ interior R₀, ¬ VertexComplete G z Q := by
    intro z hz hzc
    apply h2breaker
    exact ⟨A, C, B, a₀, R₀, b₀, Q, hK, ⟨hQout, hQanti⟩,
      ⟨⟨a₁, ha₁A, ha₁Q⟩, ⟨b₁, hb₁B, hb₁Q⟩⟩,
      ⟨ha₀notQ, hb₀notQ⟩, ⟨z, Workspace.ProofLemmas.PathBasics.interior_subset hz, hzc⟩⟩

  let P : List V := a₁ :: (R₀ ++ [b₁])
  have ha₁R₀ : a₁ ∉ R₀ := fun h => hban.2.1 a₁ h (Or.inl (Or.inl ha₁A))
  have hb₁R₀ : b₁ ∉ R₀ := fun h => hban.2.1 b₁ h (Or.inl (Or.inr hb₁B))
  have ha₁a₀ : G.Adj a₁ a₀ := (hban.2.2.1.2.1 a₁ ha₁A).symm
  have hb₁b₀ : G.Adj b₁ b₀ := (hban.2.2.2.1.2.1 b₁ hb₁B).symm
  have ha₁b₀ : ¬ G.Adj a₁ b₀ := fun h =>
    hban.2.2.2.1.2.2 a₁ (Or.inl ha₁A) h.symm
  have hb₁a₀ : ¬ G.Adj b₁ a₀ := fun h =>
    hban.2.2.1.2.2 b₁ (Or.inl hb₁B) h.symm
  have hP : IsPathFrom G P a₁ b₁ := by
    dsimp [P]
    apply Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hban.1
    · exact ha₁a₀
    · exact hb₁b₀
    · exact ha₁b₁
    · exact fun he => Set.disjoint_left.mp hS.1.1 ha₁A (he ▸ hb₁B)
    · exact ha₁R₀
    · exact hb₁R₀
    · intro z hz hza₀ hadj
      by_cases hzb₀ : z = b₀
      · exact ha₁b₀ (hzb₀ ▸ hadj)
      · have hzint : z ∈ interior R₀ :=
          (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
            ⟨hz, hza₀, hzb₀⟩
        exact hban.2.2.2.2 z hzint a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
    · intro z hz hzb₀ hadj
      by_cases hza₀ : z = a₀
      · exact hb₁a₀ (hza₀ ▸ hadj)
      · have hzint : z ∈ interior R₀ :=
          (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
            ⟨hz, hza₀, hzb₀⟩
        exact hban.2.2.2.2 z hzint b₁ (Or.inl (Or.inr hb₁B)) hadj.symm
  have hPodd : Odd (pathLength P) := by
    have hRodd := (Workspace.Statements.S11.SPGT.thm_11_3 G hG hprism A C B hS
      a₀ b₀ R₀ hban).2
    obtain ⟨k, hk⟩ := hRodd
    refine ⟨k + 1, ?_⟩
    simp [P, pathLength] at hk ⊢
    omega
  have hP5 : 5 ≤ pathLength P := by
    simp only [P, pathLength, List.length_cons, List.length_append, List.length_singleton]
    have := hstair.2.2
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at this
    omega
  have hPout : ∀ z ∈ P, z ∉ Q := by
    intro z hzP hzQ
    have hzout := hQout z hzQ
    simp only [P, List.mem_cons, List.mem_append, List.mem_singleton] at hzP
    rcases hzP with hza | hzrest
    · exact hzout (hza ▸ Or.inr (Or.inl (Or.inl ha₁A)))
    · rcases hzrest with hzR | hzb
      · exact hzout (Or.inl hzR)
      · rcases hzb with hzb | hzb
        · exact hzout (hzb ▸ Or.inr (Or.inl (Or.inr hb₁B)))
        · simp at hzb
  have honlyP : ∀ z ∈ P, VertexComplete G z Q → z = a₁ ∨ z = b₁ := by
    intro z hzP hzc
    simp only [P, List.mem_cons, List.mem_append, List.mem_singleton] at hzP
    rcases hzP with hza | hzrest
    · exact Or.inl hza
    · rcases hzrest with hzR | hzb
      · by_cases hza : z = a₀
        · exact (ha₀notQ (hza ▸ hzc)).elim
        · by_cases hzb₀ : z = b₀
          · exact (hb₀notQ (hzb₀ ▸ hzc)).elim
          · exact (hnoIntQ z
              ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
                ⟨hzR, hza, hzb₀⟩) hzc).elim
      · rcases hzb with hzb | hzb
        · exact Or.inr hzb
        · simp at hzb
  have hrr := Workspace.Statements.S02.SPGT.thm_2_1 G hG Q hQanti P a₁ b₁ hP hPout
    hPodd ha₁Q hb₁Q
  rcases hrr with hedge | hleap | hshort
  · obtain ⟨u, huP, v, hvP, huv, huQ, hvQ⟩ := hedge
    have huend := honlyP u huP huQ
    have hvend := honlyP v hvP hvQ
    rcases huend with rfl | rfl <;> rcases hvend with rfl | rfl
    · exact (G.irrefl huv).elim
    · exact (ha₁b₁ huv).elim
    · exact (ha₁b₁ huv.symm).elim
    · exact (G.irrefl huv).elim
  · obtain ⟨-, x, hxQ, y, hyQ, hleap⟩ := hleap
    obtain ⟨-, -, hxyne, hxynon, hxadj, hyadj⟩ := hleap
    have hP6 : 6 ≤ P.length := by
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hP5
      omega
    have hPlen : P.length = R₀.length + 2 := by simp [P]
    have hRpos : 0 < R₀.length :=
      Workspace.ProofLemmas.PathBasics.path_length_pos hban.1.1
    have hRzero : R₀[0]'hRpos = a₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 hRpos
    have hRlast : R₀[R₀.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 hRpos
    have hPget : ∀ (k : ℕ) (hk : k < R₀.length) (hkP : k + 1 < P.length),
        P[k + 1]'hkP = R₀[k]'hk := by
      intro k hk hkP
      dsimp [P]
      rw [List.getElem_append_left hk]
    have hPone : P[1]'(by omega) = a₀ := by
      calc
        P[1]'(by omega) = R₀[0]'hRpos := hPget 0 hRpos (by omega)
        _ = a₀ := hRzero
    have hPpenult : P[P.length - 2]'(by omega) = b₀ := by
      calc
        P[P.length - 2]'(by omega) = P[(R₀.length - 1) + 1]'(by omega) :=
          Workspace.ProofLemmas.Thm114Aux.getElem_eq_index P _ _ (by omega)
        _ = R₀[R₀.length - 1]'(by omega) := hPget _ (by omega) (by omega)
        _ = b₀ := hRlast
    have hxb₀ : ¬ G.Adj x b₀ := by
      intro hxb
      have hxat : G.Adj x (P[P.length - 2]'(by omega)) := by
        rw [hPpenult]
        exact hxb
      rcases (hxadj (P.length - 2) (by omega)).mp hxat with h | h | h <;> omega
    have hya₀ : ¬ G.Adj y a₀ := by
      intro hya
      have hyat : G.Adj y (P[1]'(by omega)) := by
        rw [hPone]
        exact hya
      rcases (hyadj 1 (by omega)).mp hyat with h | h | h <;> omega
    have hxq : x ∈ q := by simpa [Q] using hxQ
    have hyq : y ∈ q := by simpa [Q] using hyQ
    have hxend : x = q₁ ∨ x = qk := by
      by_cases hx₁ : x = q₁
      · exact Or.inl hx₁
      by_cases hxk : x = qk
      · exact Or.inr hxk
      have hxint : x ∈ interior q :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).2
          ⟨hxq, hx₁, hxk⟩
      exact (hxb₀ ((hqint x hxint).1.2 b₀ (Or.inr rfl))).elim
    have hyend : y = q₁ ∨ y = qk := by
      by_cases hy₁ : y = q₁
      · exact Or.inl hy₁
      by_cases hyk : y = qk
      · exact Or.inr hyk
      have hyint : y ∈ interior q :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).2
          ⟨hyq, hy₁, hyk⟩
      exact (hya₀ ((hqint y hyint).2.2 a₀ (Or.inr rfl))).elim
    have hends : (x = q₁ ∧ y = qk) ∨ (x = qk ∧ y = q₁) := by
      rcases hxend with hx₁ | hxk <;> rcases hyend with hy₁ | hyk
      · exact (hxyne (hx₁.trans hy₁.symm)).elim
      · exact Or.inl ⟨hx₁, hyk⟩
      · exact Or.inr ⟨hxk, hy₁⟩
      · exact (hxyne (hxk.trans hyk.symm)).elim
    have hq₁qk : ¬ G.Adj q₁ qk := by
      rcases hends with ⟨hx₁, hyk⟩ | ⟨hxk, hy₁⟩
      · simpa [hx₁, hyk] using hxynon
      · intro hadj
        exact hxynon (by simpa [hxk, hy₁] using hadj.symm)
    have hq₁qkC : Gᶜ.Adj q₁ qk := (G.compl_adj q₁ qk).2 ⟨hne, hq₁qk⟩
    have hq0 : q[0]'(by omega) = q₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hq.2.1 (by omega)
    have hqlast : q[q.length - 1]'(by omega) = qk :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hq.2.2 (by omega)
    have hqlen : q.length = 2 := by
      have hadj : Gᶜ.Adj (q[0]'(by omega)) (q[q.length - 1]'(by omega)) := by
        rw [hq0, hqlast]
        exact hq₁qkC
      rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hq.1
          (i := 0) (j := q.length - 1) (by omega) (by omega)).mp hadj with h | h <;>
        omega
    obtain ⟨r, s, hqrs⟩ := Workspace.ProofLemmas.PrismBasics.length_eq_two hqlen
    have hr : r = q₁ := by simpa [hqrs] using hq.2.1
    have hs : s = qk := by simpa [hqrs] using hq.2.2
    have hqshape : q = [q₁, qk] := by simpa [hr, hs] using hqrs
    have hxNoInt : ∀ z ∈ interior R₀, ¬ G.Adj x z := by
      intro z hz hadj
      obtain ⟨k, hk, hk1, hk2, hkz⟩ :=
        (Workspace.ProofLemmas.Thm114Aux.mem_interior_iff_index hban.1).1 hz
      have hkP : k + 1 < P.length := by omega
      have hPk : P[k + 1]'hkP = z := by
        exact (hPget k hk hkP).trans hkz
      have hxat : G.Adj x (P[k + 1]'hkP) := by rw [hPk]; exact hadj
      rcases (hxadj (k + 1) hkP).mp hxat with h | h | h <;> omega
    have hyNoInt : ∀ z ∈ interior R₀, ¬ G.Adj y z := by
      intro z hz hadj
      obtain ⟨k, hk, hk1, hk2, hkz⟩ :=
        (Workspace.ProofLemmas.Thm114Aux.mem_interior_iff_index hban.1).1 hz
      have hkP : k + 1 < P.length := by omega
      have hPk : P[k + 1]'hkP = z := by
        exact (hPget k hk hkP).trans hkz
      have hyat : G.Adj y (P[k + 1]'hkP) := by rw [hPk]; exact hadj
      rcases (hyadj (k + 1) hkP).mp hyat with h | h | h <;> omega
    refine ⟨a₁, ha₁A, b₁, hb₁B, hqka₁, hq₁b₁, ha₁b₁, hqshape, ?_⟩
    rcases hends with ⟨hx₁, hyk⟩ | ⟨hxk, hy₁⟩
    · exact ⟨by simpa [hx₁] using hxNoInt, by simpa [hyk] using hyNoInt⟩
    · exact ⟨by simpa [hy₁] using hyNoInt, by simpa [hxk] using hxNoInt⟩
  · omega

end Workspace.ProofLemmas.Thm125Case3Core
