import Workspace.ProofLemmas.Thm125Setup
import Workspace.Statements.S02.Thm_2_2
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm125Case2Prelude

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem path_three {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬ G.Adj x z) (hxz' : x ≠ z) :
    IsPathList G [x, y, z] := by
  have hxy' := hxy.ne
  have hyz' := hyz.ne
  have hxzsym : ¬ G.Adj z x := fun h => hxz h.symm
  refine ⟨by simp, by simp [hxy', hyz', hxz'], ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp [hxy, hxy.symm, hyz, hyz.symm, hxz, hxzsym]

private theorem banister_ends_nonadjacent
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hban : IsBanister G A C B a₀ R₀ b₀) (hR3 : 3 ≤ pathLength R₀) :
    ¬ G.Adj a₀ b₀ := by
  have hlen : 4 ≤ R₀.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hR3
    omega
  have h := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hban.1.1 (by omega)
  have h0 : R₀[0]'(by omega) = a₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 (by omega)
  have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
  simpa [h0, hl] using h

/-- The parity/Roussel--Rubio prelude to part (2): an interior vertex of the
old banister is complete to the whole antipath. -/
theorem case2_prelude
    (G : SimpleGraph V) (hG : Berge G)
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀) :
    Odd q.length ∧ ∃ t ∈ interior R₀, VertexComplete G t {z : V | z ∈ q} := by
  classical
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS := hstair.1
  have hban := hstair.2.1
  have hR3 := hstair.2.2
  have hR4 : 4 ≤ R₀.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hR3
    omega
  have hRodd : Odd (pathLength R₀) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG hprism A C B hS
      a₀ b₀ R₀ hban).2
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have hq2 : 2 ≤ q.length := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    by_contra hc
    have hlen : q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h1 : x = q₁ := by simpa using hq.2.1
    have h2 : x = qk := by simpa using hq.2.2
    exact hne (h1.symm.trans h2)
  have ha₀b₀ : ¬ G.Adj a₀ b₀ := banister_ends_nonadjacent hban hstair.2.2
  have ha₀b₀ne : a₀ ≠ b₀ := by
    have := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hban.1 (by omega)
    exact this
  have hmissB : ∃ b ∈ B, ¬ G.Adj q₁ b := by
    by_contra hno
    push_neg at hno
    exact hq₁.2 ⟨hq₁.1.1, fun z hz => hz.elim (hno z) (fun e => e ▸ hqa₀)⟩
  obtain ⟨b, hbB, hq₁b⟩ := hmissB
  have hbout : b ∉ q := by
    intro hbq
    exact outside_of_mem hq hqint hq₁.1 hqk.1 hbq (Or.inr (Or.inl (Or.inr hbB)))
  have ha₀out : a₀ ∉ q := by
    intro ha
    exact outside_of_mem hq hqint hq₁.1 hqk.1 ha
      (Or.inl (Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1))
  have hb₀out : b₀ ∉ q := by
    intro hbq
    exact outside_of_mem hq hqint hq₁.1 hqk.1 hbq
      (Or.inl (Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2))
  have hb₀b : G.Adj b₀ b := hban.2.2.2.1.2.1 b hbB
  have ha₀b : ¬ G.Adj a₀ b := hban.2.2.1.2.2 b (Or.inl hbB)
  have hRb : IsPathFrom Gᶜ [b₀, a₀, b] b₀ b := by
    have e1 : Gᶜ.Adj b₀ a₀ := (G.compl_adj b₀ a₀).2 ⟨ha₀b₀ne.symm,
      fun h => ha₀b₀ h.symm⟩
    have e2 : Gᶜ.Adj a₀ b := (G.compl_adj a₀ b).2
      ⟨fun he => hban.2.2.1.1 (he ▸ Or.inl (Or.inr hbB)), ha₀b⟩
    have e3 : ¬ Gᶜ.Adj b₀ b := fun h => (G.compl_adj b₀ b).1 h |>.2 hb₀b
    exact ⟨path_three e1 e2 e3 hb₀b.ne, rfl, by simp⟩
  have hcross : ∀ z ∈ q, ∀ y ∈ [b₀, a₀, b],
      (Gᶜ.Adj z y ↔ (z = qk ∧ y = b₀) ∨ (z = q₁ ∧ y = b)) := by
    intro z hz y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy | hy
    · subst y
      by_cases hzk : z = qk
      · subst z
        exact iff_of_true ((G.compl_adj qk b₀).2
          ⟨fun he => hb₀out (he.symm ▸ hz), hqkb₀⟩) (Or.inl ⟨rfl, rfl⟩)
      · have hadj := (leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hzk).2 b₀
          (Or.inr rfl)
        exact iff_of_false (fun hc => (G.compl_adj z b₀).1 hc |>.2 hadj)
          (by rintro (⟨h, -⟩ | ⟨-, h⟩); exact hzk h; exact hb₀b.ne h)
    · subst y
      have hadj : G.Adj z a₀ := by
        by_cases hz₁ : z = q₁
        · simpa [hz₁] using hqa₀
        · exact (rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 a₀
            (Or.inr rfl)
      exact iff_of_false (fun hc => (G.compl_adj z a₀).1 hc |>.2 hadj)
        (by
          rintro (⟨-, h⟩ | ⟨-, h⟩)
          · exact ha₀b₀ne h
          · apply hban.2.2.1.1
            rw [h]
            exact Or.inl (Or.inr hbB))
    · subst y
      by_cases hz₁ : z = q₁
      · subst z
        exact iff_of_true ((G.compl_adj q₁ b).2
          ⟨fun he => hbout (he.symm ▸ hz), hq₁b⟩) (Or.inr ⟨rfl, rfl⟩)
      · have hadj := (rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 b
          (Or.inl hbB)
        exact iff_of_false (fun hc => (G.compl_adj z b).1 hc |>.2 hadj)
          (by rintro (⟨-, h⟩ | ⟨h, -⟩); exact hb₀b.ne h.symm; exact hz₁ h)
  have hhole : IsHoleList Gᶜ (q ++ [b₀, a₀, b]) :=
    Workspace.ProofLemmas.PathGlue.glue_hole hq hRb
      (by
        intro z hz hzmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzmem
        rcases hzmem with hz0 | hza | hzb
        · subst z; exact hb₀out hz
        · subst z; exact ha₀out hz
        · subst z; exact hbout hz)
      hcross (by simp; omega)
  have hqodd : Odd q.length := by
    have hev := (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG).1 _ hhole
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil,
      Nat.add_zero] at hev
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 2, by omega⟩

  let X : Set V := {z : V | z ∈ q.dropLast}
  have hXanti : AnticonnectedSet G X := by
    apply Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    rw [List.dropLast_eq_take]
    exact Workspace.ProofLemmas.PathBasics.isPathList_take hq.1 (by omega)
  have hXmem : ∀ z : V, z ∈ X ↔ z ∈ q ∧ z ≠ qk := by
    intro z
    change z ∈ q.dropLast ↔ _
    rw [Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hq.1.2.1 hq.1.1]
    have hlast : q.getLast hq.1.1 = qk := by
      have h := hq.2.2
      rw [List.getLast?_eq_some_getLast hq.1.1] at h
      exact Option.some_injective _ h
    rw [hlast]
  have hRoutX : ∀ z ∈ R₀, z ∉ X := by
    intro z hzR hzX
    exact outside_of_mem hq hqint hq₁.1 hqk.1 ((hXmem z).1 hzX).1 (Or.inl hzR)
  have ha₀X : VertexComplete G a₀ X := by
    intro z hzX
    obtain ⟨hzq, hzk⟩ := (hXmem z).1 hzX
    by_cases hz₁ : z = q₁
    · simpa [hz₁] using hqa₀.symm
    exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hzq hz₁).2 a₀
      (Or.inr rfl)).symm
  have hb₀X : VertexComplete G b₀ X := by
    intro z hzX
    obtain ⟨hzq, hzk⟩ := (hXmem z).1 hzX
    exact ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hzq hzk).2 b₀
      (Or.inr rfl)).symm
  have hexedge : ∃ u ∈ R₀, ∃ v ∈ R₀, EdgeComplete G X u v := by
    by_contra hno
    obtain ⟨a, haA⟩ := hS.2.1.1
    have haX : VertexComplete G a X := by
      intro z hzX
      obtain ⟨hzq, hzk⟩ := (hXmem z).1 hzX
      exact (leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hzq hzk).2 a (Or.inl haA) |>.symm
    obtain ⟨w, hwint, haw⟩ := Workspace.Statements.S02.SPGT.thm_2_2 G hG X hXanti
      R₀ a₀ b₀ hban.1 hRoutX hRodd ha₀X hb₀X hno a haX
    exact hban.2.2.2.2 w hwint a (Or.inl (Or.inl haA)) haw.symm
  obtain ⟨u, huR, v, hvR, huv, huX, hvX⟩ := hexedge
  have ht : ∃ t ∈ interior R₀, VertexComplete G t X := by
    by_cases hua : u = a₀
    · refine ⟨v, (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
          ⟨hvR, ?_, ?_⟩, hvX⟩
      · exact fun hva => huv.ne (hua.trans hva.symm)
      · exact fun hvb => ha₀b₀ (hua ▸ hvb ▸ huv)
    · by_cases hub : u = b₀
      · refine ⟨v, (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
            ⟨hvR, ?_, ?_⟩, hvX⟩
        · exact fun hva => ha₀b₀ (hva ▸ hub ▸ huv.symm)
        · exact fun hvb => huv.ne (hub.trans hvb.symm)
      · exact ⟨u, (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
          ⟨huR, hua, hub⟩, huX⟩
  obtain ⟨t, htint, htX⟩ := ht
  have htqk : G.Adj t qk := by
    by_contra htqk
    have htout : t ∉ q := by
      intro htq
      exact outside_of_mem hq hqint hq₁.1 hqk.1 htq
        (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset htint))
    have htb : ¬ G.Adj t b := hban.2.2.2.2 t htint b (Or.inl (Or.inr hbB))
    have hanti := Workspace.ProofLemmas.PrismBasics.isHoleList_of_path_add_two_vertices
      (G := Gᶜ) hq (by rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]; omega)
      ((G.compl_adj b q₁).2 ⟨fun he => hbout (he ▸
          Workspace.ProofLemmas.PathBasics.head_mem hq.2.1), fun h => hq₁b h.symm⟩)
      ((G.compl_adj t qk).2 ⟨fun he => htout (he ▸
          Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2), htqk⟩)
      ((G.compl_adj b t).2 ⟨fun he => hban.2.1 t
          (Workspace.ProofLemmas.PathBasics.interior_subset htint)
          (he.symm ▸ Or.inl (Or.inr hbB)), fun h => htb h.symm⟩)
      hbout htout
      (fun hc => (G.compl_adj b qk).1 hc |>.2
        ((hqk.1.2 b (Or.inl hbB)).symm))
      (fun hc => (G.compl_adj t q₁).1 hc |>.2
        (htX q₁ ((hXmem q₁).2
          ⟨Workspace.ProofLemmas.PathBasics.head_mem hq.2.1, hne⟩)))
      (by
        intro z hzint hc
        have hzq := Workspace.ProofLemmas.PathBasics.interior_subset hzint
        exact (G.compl_adj b z).1 hc |>.2
          ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hzq
            ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hzint).2.1).2
              b (Or.inl hbB)).symm)
      (by
        intro z hzint hc
        have hzq := Workspace.ProofLemmas.PathBasics.interior_subset hzint
        have hzk := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hzint |>.2.2
        exact (G.compl_adj t z).1 hc |>.2 (htX z ((hXmem z).2 ⟨hzq, hzk⟩)))
    have hev := (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG).1 _ hanti
    have hlen := Workspace.ProofLemmas.PrismBasics.holeLength_cons_cons b t hq.1.1
    rw [hlen] at hev
    obtain ⟨ke, hke⟩ := hev
    obtain ⟨ko, hko⟩ := hqodd
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hke
    omega
  have htQ : VertexComplete G t {z : V | z ∈ q} := by
    intro z hz
    by_cases hzk : z = qk
    · simpa [hzk] using htqk
    exact htX z ((hXmem z).2 ⟨hz, hzk⟩)
  exact ⟨hqodd, t, htint, htQ⟩

end Workspace.ProofLemmas.Thm125Case2Prelude
