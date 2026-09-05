import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.StrongStaircaseComponentStructure
import Workspace.Types.SkewTools
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.StrongStaircaseCrossPair
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S04.Thm_4_2

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.StrongStaircaseMiddleRegionDichotomy

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.SkewTools.SPGT
open Workspace.Types.RousselRubio.SPGT

theorem strongStaircaseMiddleRegionDichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀)
    (hodd : Odd (pathLength R₀)) :
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    let M : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      attachments H F VS = ∅}
    let D : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      (attachments H F VS).Nonempty}
    Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧ Disjoint A A₀ ∧ Disjoint A B₀ ∧
      Disjoint A N ∧ Disjoint A M ∧ Disjoint B C ∧ Disjoint B D ∧ Disjoint B A₀ ∧
      Disjoint B B₀ ∧ Disjoint B N ∧ Disjoint B M ∧ Disjoint C D ∧ Disjoint C A₀ ∧
      Disjoint C B₀ ∧ Disjoint C N ∧ Disjoint C M ∧ Disjoint D A₀ ∧ Disjoint D B₀ ∧
      Disjoint D N ∧ Disjoint D M ∧ Disjoint A₀ B₀ ∧ Disjoint A₀ N ∧ Disjoint A₀ M ∧
      Disjoint B₀ N ∧ Disjoint B₀ M ∧ Disjoint N M ∧
      A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M = Set.univ →
    ({v : V | v ∈ interior R₀}).Nonempty → {v : V | v ∈ interior R₀} ⊆ M →
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ M →
      attachments H F VS = ∅) →
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ D →
      attachments H F (A₀ ∪ B₀) = ∅ ∧
        (attachments H F (A ∪ C)).Nonempty ∧ (attachments H F (B ∪ C)).Nonempty) →
    N.Nonempty → AdmitsBalancedSkewPartition H ∨ C ∪ D = ∅ := by
  classical
  intro VS A₀ B₀ N H₀ M D hpart hintne hintM hMno hDatt hNne
  by_cases hCD : C ∪ D = ∅
  · exact Or.inr hCD
  left
  rcases hpart with ⟨hAB, hAC, hAD, hAA₀, hAB₀, hAN, hAM, hBC, hBD, hBA₀,
    hBB₀, hBN, hBM, hCDdisj, hCA₀, hCB₀, hCN, hCM, hDA₀, hDB₀, hDN, hDM,
    hA₀B₀, hA₀N, hA₀M, hB₀N, hB₀M, hNM, hcover⟩
  have hstair : IsStaircase H A C B a₀ R₀ b₀ := hstairs.1.1
  have hS : StepConnected H A C B := hstair.1
  have hban : IsBanister H A C B a₀ R₀ b₀ := hstair.2.1
  have hpath : IsPathFrom H R₀ a₀ b₀ := hban.1
  have ha₀A₀ : a₀ ∈ A₀ := hban.2.2.1
  have hb₀B₀ : b₀ ∈ B₀ := hban.2.2.2.1

  let P : Set V := C ∪ D
  let Q : Set V := (A₀ ∪ B₀) ∪ M
  let X : Set V := P ∪ Q
  let Y : Set V := N ∪ (A ∪ B)

  have hPne : P.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact hCD
  have hQne : Q.Nonempty := by
    obtain ⟨r, hr⟩ := hintne
    exact ⟨r, Or.inr (hintM hr)⟩
  have hNanti : Anticomplete Hᶜ N (A ∪ B) := by
    intro n hn z hz hadj
    exact ((SimpleGraph.compl_adj H n z).mp hadj).2 (hn z hz)
  have hNdisj : Disjoint N (A ∪ B) := by
    exact Set.disjoint_left.mpr fun z hzN hzAB => by
      rcases hzAB with hzA | hzB
      · exact Set.disjoint_right.mp hAN hzN hzA
      · exact Set.disjoint_right.mp hBN hzN hzB

  have hPQdisj : Disjoint P Q := by
    exact Set.disjoint_left.mpr fun z hzP hzQ => by
      rcases hzP with hzC | hzD
      · rcases hzQ with (hzA₀ | hzB₀) | hzM
        · exact Set.disjoint_left.mp hCA₀ hzC hzA₀
        · exact Set.disjoint_left.mp hCB₀ hzC hzB₀
        · exact Set.disjoint_left.mp hCM hzC hzM
      · rcases hzQ with (hzA₀ | hzB₀) | hzM
        · exact Set.disjoint_left.mp hDA₀ hzD hzA₀
        · exact Set.disjoint_left.mp hDB₀ hzD hzB₀
        · exact Set.disjoint_left.mp hDM hzD hzM
  have hPQanti : Anticomplete H P Q := by
    intro p hp q hq hpq
    rcases hp with hpC | hpD
    · rcases hq with (hqA₀ | hqB₀) | hqM
      · exact hqA₀.2.2 p (Or.inr hpC) hpq.symm
      · exact hqB₀.2.2 p (Or.inr hpC) hpq.symm
      · obtain ⟨F, hF, hqF, hFnone⟩ := hqM
        have hpatt : p ∈ attachments H F VS :=
          ⟨Or.inr hpC, q, hqF, hpq⟩
        rw [hFnone] at hpatt
        exact hpatt
    · obtain ⟨F, hF, hpF, hFatt⟩ := hpD
      rcases hq with (hqA₀ | hqB₀) | hqM
      · have hFsub : F ⊆ D := fun z hz => ⟨F, hF, hz, hFatt⟩
        have hempty := (hDatt F ⟨p, hpF⟩ hF hFsub).1
        have hqatt : q ∈ attachments H F (A₀ ∪ B₀) :=
          ⟨Or.inl hqA₀, p, hpF, hpq.symm⟩
        rw [hempty] at hqatt
        exact hqatt
      · have hFsub : F ⊆ D := fun z hz => ⟨F, hF, hz, hFatt⟩
        have hempty := (hDatt F ⟨p, hpF⟩ hF hFsub).1
        have hqatt : q ∈ attachments H F (A₀ ∪ B₀) :=
          ⟨Or.inr hqB₀, p, hpF, hpq.symm⟩
        rw [hempty] at hqatt
        exact hqatt
      · obtain ⟨F', hF', hqF', hF'none⟩ := hqM
        have hne : F ≠ F' := by
          intro he
          rw [he, hF'none] at hFatt
          exact Set.not_nonempty_empty hFatt
        exact Workspace.ProofLemmas.ComponentsOfSetBasics.anticomplete_of_isComponent
          H hF hF' hne p hpF q hqF' hpq
  have hXnotcon : ¬ ConnectedSet H X := by
    apply Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
      (A := X) (S := P) (T := Q)
    · rfl
    · exact hPne
    · exact hQne
    · exact hPQdisj
    · exact hPQanti
  have hYnotanti : ¬ AnticonnectedSet H Y := by
    unfold AnticonnectedSet
    apply Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
      (G := Hᶜ) (A := Y) (S := N) (T := A ∪ B)
    · rfl
    · exact hNne
    · exact (hS.2.1.1.mono Set.subset_union_left)
    · exact hNdisj
    · exact hNanti
  have hXYcover : X ∪ Y = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M := by
      rw [hcover]
      trivial
    rcases hz with (((((((hzA | hzB) | hzC) | hzD) | hzA₀) | hzB₀) | hzN) | hzM)
    · exact Or.inr (Or.inr (Or.inl hzA))
    · exact Or.inr (Or.inr (Or.inr hzB))
    · exact Or.inl (Or.inl (Or.inl hzC))
    · exact Or.inl (Or.inl (Or.inr hzD))
    · exact Or.inl (Or.inr (Or.inl (Or.inl hzA₀)))
    · exact Or.inl (Or.inr (Or.inl (Or.inr hzB₀)))
    · exact Or.inr (Or.inl hzN)
    · exact Or.inl (Or.inr (Or.inr hzM))
  have hXYdisj : Disjoint X Y := by
    exact Set.disjoint_left.mpr fun z hzX hzY => by
      rcases hzX with (hzC | hzD) | ((hzA₀ | hzB₀) | hzM)
      · rcases hzY with hzN | (hzA | hzB)
        · exact Set.disjoint_left.mp hCN hzC hzN
        · exact Set.disjoint_left.mp hAC hzA hzC
        · exact Set.disjoint_left.mp hBC hzB hzC
      · rcases hzY with hzN | (hzA | hzB)
        · exact Set.disjoint_left.mp hDN hzD hzN
        · exact Set.disjoint_left.mp hAD hzA hzD
        · exact Set.disjoint_left.mp hBD hzB hzD
      · rcases hzY with hzN | (hzA | hzB)
        · exact Set.disjoint_left.mp hA₀N hzA₀ hzN
        · exact Set.disjoint_left.mp hAA₀ hzA hzA₀
        · exact Set.disjoint_left.mp hBA₀ hzB hzA₀
      · rcases hzY with hzN | (hzA | hzB)
        · exact Set.disjoint_left.mp hB₀N hzB₀ hzN
        · exact Set.disjoint_left.mp hAB₀ hzA hzB₀
        · exact Set.disjoint_left.mp hBB₀ hzB hzB₀
      · rcases hzY with hzN | (hzA | hzB)
        · exact Set.disjoint_right.mp hNM hzM hzN
        · exact Set.disjoint_left.mp hAM hzA hzM
        · exact Set.disjoint_left.mp hBM hzB hzM
  have hskew : IsSkewPartition H X Y :=
    ⟨hXYcover, hXYdisj, hXnotcon, hYnotanti⟩
  by_cases hloose : IsLooseSkewPartition H X Y
  · exact Workspace.Statements.S04.SPGT.thm_4_2 H hBerge ⟨X, Y, hloose⟩
  -- Let `N'` be an anticomponent of `N`.  Completeness of `N` to `A ∪ B` makes it an
  -- anticomponent of the entire skew side `Y`.
  obtain ⟨n, hnN⟩ := hNne
  obtain ⟨N', hN'comp, hnN'⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem Hᶜ N hnN
  have hN'ne : N'.Nonempty := ⟨n, hnN'⟩
  have hN'anti : IsAnticomponent H Y N' := by
    exact Workspace.Statements.S04.SPGT.Helpers42.isComponent_of_split
      hN'comp hN'ne rfl hNanti

  have hR₀X : ∀ z ∈ R₀, z ∈ X := by
    intro z hz
    by_cases hza : z = a₀
    · exact Or.inr (Or.inl (Or.inl (hza ▸ ha₀A₀)))
    by_cases hzb : z = b₀
    · exact Or.inr (Or.inl (Or.inr (hzb ▸ hb₀B₀)))
    · exact Or.inr (Or.inr (hintM
        ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hz, hza, hzb⟩)))
  have hR₀notComplete : ∀ z ∈ R₀, ¬ VertexComplete H z N' := by
    intro z hz hzcomp
    apply hloose
    exact ⟨hskew, Or.inr ⟨z, hR₀X z hz, N', hN'anti, hzcomp⟩⟩

  -- Choose a step and attach its opposite ends to the banister.
  obtain ⟨a, haA⟩ := hS.2.1.1
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, -⟩ :=
    hS.2.2.2.1 a (Or.inl (Or.inl haA))
  obtain ⟨hr1, hr2, hRdisj, hRedges⟩ := hstep
  have ha₁A : a₁ ∈ A := hr1.2.1
  have hb₁B : b₁ ∈ B := hr1.2.2.1
  have ha₂A : a₂ ∈ A := hr2.2.1
  have hb₂B : b₂ ∈ B := hr2.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ := PathBasics.head_mem hr1.1.2.1
  have hb₁R₁ : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
  have ha₂R₂ : a₂ ∈ R₂ := PathBasics.head_mem hr2.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
  have ha₁b₂ : ¬ H.Adj a₁ b₂ := by
    intro hadj
    rcases (hRedges a₁ ha₁R₁ b₂ hb₂R₂).mp hadj with h | h
    · exact Set.disjoint_left.mp hAB ha₂A (h.2.symm ▸ hb₂B)
    · exact Set.disjoint_left.mp hAB ha₁A (h.1 ▸ hb₁B)
  have ha₁b₂ne : a₁ ≠ b₂ := fun h => Set.disjoint_left.mp hAB ha₁A (h ▸ hb₂B)
  have ha₁R₀ : a₁ ∉ R₀ := by
    intro hmem
    exact hban.2.1 a₁ hmem (Or.inl (Or.inl ha₁A))
  have hb₂R₀ : b₂ ∉ R₀ := by
    intro hmem
    exact hban.2.1 b₂ hmem (Or.inl (Or.inr hb₂B))
  have ha₁a₀ : H.Adj a₁ a₀ := (hban.2.2.1.2.1 a₁ ha₁A).symm
  have hb₂b₀ : H.Adj b₂ b₀ := (hban.2.2.2.1.2.1 b₂ hb₂B).symm
  have ha₁other : ∀ z ∈ R₀, z ≠ a₀ → ¬ H.Adj a₁ z := by
    intro z hz hza hadj
    by_cases hzb : z = b₀
    · subst z
      exact hban.2.2.2.1.2.2 a₁ (Or.inl ha₁A) hadj.symm
    · have hzint := (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hz, hza, hzb⟩
      exact hban.2.2.2.2 z hzint a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
  have hb₂other : ∀ z ∈ R₀, z ≠ b₀ → ¬ H.Adj b₂ z := by
    intro z hz hzb hadj
    by_cases hza : z = a₀
    · subst z
      exact hban.2.2.1.2.2 b₂ (Or.inl hb₂B) hadj.symm
    · have hzint := (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hz, hza, hzb⟩
      exact hban.2.2.2.2 z hzint b₂ (Or.inl (Or.inr hb₂B)) hadj.symm
  have hPpath : IsPathFrom H (a₁ :: (R₀ ++ [b₂])) a₁ b₂ :=
    PathAttach.isPathFrom_cons_concat hpath ha₁a₀ hb₂b₀ ha₁b₂ ha₁b₂ne
      ha₁R₀ hb₂R₀ ha₁other hb₂other
  have hPlen : pathLength (a₁ :: (R₀ ++ [b₂])) = R₀.length + 1 :=
    PathAttach.pathLength_cons_append_singleton a₁ b₂ R₀
  have hRlenEq : R₀.length = pathLength R₀ + 1 :=
    PathBasics.length_eq_pathLength_add_one hpath.1
  have hPodd : Odd (pathLength (a₁ :: (R₀ ++ [b₂]))) := by
    rw [hPlen, hRlenEq]
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k + 1, ?_⟩
    omega
  have hPfive : 5 ≤ pathLength (a₁ :: (R₀ ++ [b₂])) := by
    rw [hPlen, hRlenEq]
    have hge := hstair.2.2
    omega
  have hPint : interior (a₁ :: (R₀ ++ [b₂])) = R₀ := by
    simp [Workspace.Types.Core.SPGT.interior]
  have hPnotComplete : ∀ z ∈ interior (a₁ :: (R₀ ++ [b₂])),
      ¬ VertexComplete H z N' := by
    intro z hz
    exact hR₀notComplete z (hPint ▸ hz)
  have hPN' : ∀ z ∈ a₁ :: (R₀ ++ [b₂]), z ∉ N' := by
    intro z hz hzN'
    have hzN : z ∈ N := hN'comp.1 hzN'
    rcases (PathAttach.mem_cons_append_singleton (p := R₀) (s := a₁) (t := b₂)).mp hz with
      rfl | hzR | rfl
    · exact Set.disjoint_left.mp hAN ha₁A hzN
    · exact Set.disjoint_left.mp hXYdisj (hR₀X z hzR) (Or.inl hzN)
    · exact Set.disjoint_left.mp hBN hb₂B hzN
  have ha₁comp : VertexComplete H a₁ N' := by
    intro z hz
    exact (hN'comp.1 hz a₁ (Or.inl ha₁A)).symm
  have hb₂comp : VertexComplete H b₂ N' := by
    intro z hz
    exact (hN'comp.1 hz b₂ (Or.inr hb₂B)).symm

  rcases Workspace.Statements.S02.SPGT.thm_2_1 H hBerge N' hN'comp.2.1
      (a₁ :: (R₀ ++ [b₂])) a₁ b₂ hPpath hPN' hPodd ha₁comp hb₂comp with
    hedge | hleap | hthree
  · obtain ⟨u, huP, v, hvP, huv, hucomp, hvcomp⟩ := hedge
    have hend : ∀ z ∈ a₁ :: (R₀ ++ [b₂]), VertexComplete H z N' →
        z = a₁ ∨ z = b₂ := by
      intro z hz hzcomp
      by_cases hza : z = a₁
      · exact Or.inl hza
      by_cases hzb : z = b₂
      · exact Or.inr hzb
      exact absurd hzcomp (hPnotComplete z
        ((PathBasics.mem_interior_iff_of_pathFrom hPpath).mpr ⟨hz, hza, hzb⟩))
    exfalso
    rcases hend u huP hucomp with rfl | rfl <;>
      rcases hend v hvP hvcomp with rfl | rfl
    · exact H.irrefl huv
    · exact ha₁b₂ huv
    · exact ha₁b₂ huv.symm
    · exact H.irrefl huv
  · obtain ⟨-, x, hxN', y, hyN', hleapxy⟩ := hleap
    obtain ⟨-, -, hxyne, hxy, hxadj, hyadj⟩ := hleapxy
    have hRlen : 4 ≤ R₀.length := by omega
    have hPsize : (a₁ :: (R₀ ++ [b₂])).length = R₀.length + 2 := by simp
    have hRpos : 0 < R₀.length := by omega
    have hget : ∀ (j : ℕ) (hj : j < R₀.length),
        (a₁ :: (R₀ ++ [b₂]))[j + 1]'(by simp; omega) = R₀[j]'hj := by
      intro j hj
      rw [List.getElem_cons_succ, List.getElem_append_left hj]
    have hRzero : R₀[0]'hRpos = a₀ :=
      PathBasics.getElem_zero_of_head? hpath.2.1 hRpos
    have hRlast : R₀[R₀.length - 1]'(by omega) = b₀ :=
      PathBasics.getElem_last_of_getLast? hpath.2.2 hRpos
    have hxa₀ : H.Adj x a₀ := by
      have h := (hxadj 1 (by simp)).mpr (Or.inr (Or.inl rfl))
      rw [hget 0 hRpos, hRzero] at h
      exact h
    have hya₀ : ¬ H.Adj y a₀ := by
      intro hadj
      have h : H.Adj y ((a₁ :: (R₀ ++ [b₂]))[1]'(by simp)) := by
        rw [hget 0 hRpos, hRzero]
        exact hadj
      rcases (hyadj 1 (by simp)).mp h with h | h | h <;> omega
    have hxb₀ : ¬ H.Adj x b₀ := by
      intro hadj
      let j := R₀.length - 1
      have hj : j < R₀.length := by dsimp [j]; omega
      have hi : j + 1 < (a₁ :: (R₀ ++ [b₂])).length := by simp [j]
      have h : H.Adj x ((a₁ :: (R₀ ++ [b₂]))[j + 1]'hi) := by
        rw [hget j hj, show R₀[j]'hj = b₀ by simpa [j] using hRlast]
        exact hadj
      rcases (hxadj (j + 1) hi).mp h with h | h | h <;> simp [j] at h <;> omega
    have hyb₀ : H.Adj y b₀ := by
      let j := R₀.length - 1
      have hj : j < R₀.length := by dsimp [j]; omega
      have hi : j + 1 < (a₁ :: (R₀ ++ [b₂])).length := by simp [j]
      have h := (hyadj (j + 1) hi).mpr (Or.inr (Or.inl (by simp [j]; omega)))
      rw [hget j hj, show R₀[j]'hj = b₀ by simpa [j] using hRlast] at h
      exact h
    have hxint : ∀ z ∈ interior R₀, ¬ H.Adj x z := by
      intro z hz hadj
      obtain ⟨j, hj, hzj⟩ := List.mem_iff_getElem.mp
        (PathBasics.interior_subset hz)
      have hzends := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hz
      have hj0 : j ≠ 0 := by
        intro he
        subst j
        exact hzends.2.1 (hzj.symm.trans hRzero)
      have hjlast : j ≠ R₀.length - 1 := by
        intro he
        subst j
        exact hzends.2.2 (hzj.symm.trans hRlast)
      have hi : j + 1 < (a₁ :: (R₀ ++ [b₂])).length := by simp; omega
      have hadj' : H.Adj x ((a₁ :: (R₀ ++ [b₂]))[j + 1]'hi) := by
        rw [hget j hj, hzj]
        exact hadj
      rcases (hxadj (j + 1) hi).mp hadj' with h | h | h <;> simp at h <;> omega
    have hyint : ∀ z ∈ interior R₀, ¬ H.Adj y z := by
      intro z hz hadj
      obtain ⟨j, hj, hzj⟩ := List.mem_iff_getElem.mp
        (PathBasics.interior_subset hz)
      have hzends := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hz
      have hj0 : j ≠ 0 := by
        intro he
        subst j
        exact hzends.2.1 (hzj.symm.trans hRzero)
      have hjlast : j ≠ R₀.length - 1 := by
        intro he
        subst j
        exact hzends.2.2 (hzj.symm.trans hRlast)
      have hi : j + 1 < (a₁ :: (R₀ ++ [b₂])).length := by simp; omega
      have hadj' : H.Adj y ((a₁ :: (R₀ ++ [b₂]))[j + 1]'hi) := by
        rw [hget j hj, hzj]
        exact hadj
      rcases (hyadj (j + 1) hi).mp hadj' with h | h | h <;> simp at h <;> omega
    have hxN : x ∈ N := hN'comp.1 hxN'
    have hyN : y ∈ N := hN'comp.1 hyN'
    have hNVS : Disjoint N VS := by
      exact Set.disjoint_left.mpr fun z hzN hzVS => by
        rcases hzVS with (hzA | hzB) | hzC
        · exact Set.disjoint_right.mp hAN hzN hzA
        · exact Set.disjoint_right.mp hBN hzN hzB
        · exact Set.disjoint_right.mp hCN hzN hzC
    have hxK : x ∉ staircaseVertices A C B R₀ := by
      rintro (hxR | hxVS')
      · have hxRlist : x ∈ R₀ := hxR
        exact hPN' x (List.mem_cons_of_mem a₁ (List.mem_append_left [b₂] hxRlist)) hxN'
      · exact Set.disjoint_left.mp hNVS hxN hxVS'
    have hyK : y ∉ staircaseVertices A C B R₀ := by
      rintro (hyR | hyVS')
      · have hyRlist : y ∈ R₀ := hyR
        exact hPN' y (List.mem_cons_of_mem a₁ (List.mem_append_left [b₂] hyRlist)) hyN'
      · exact Set.disjoint_left.mp hNVS hyN hyVS'
    have hnew := Workspace.ProofLemmas.StrongStaircaseCrossPair.staircase_adjoin_cross_pair
      H A C B a₀ b₀ R₀ x y hstair hxK hyK hxyne hxy hxN hyN hxa₀ hxb₀ hya₀ hyb₀
        hxint hyint
    exfalso
    apply hstairs.1.2
    refine ⟨A ∪ {x}, C, B ∪ {y}, a₀, R₀, b₀, hnew,
      Set.subset_union_left, Set.subset_union_left, Set.Subset.rfl, ?_⟩
    constructor
    · intro z hz
      rcases hz with (hzA | hzB) | hzC
      · exact Or.inl (Or.inl (Or.inl hzA))
      · exact Or.inl (Or.inr (Or.inl hzB))
      · exact Or.inr hzC
    · intro hback
      have hxnew : x ∈ (A ∪ {x}) ∪ (B ∪ {y}) ∪ C :=
        Or.inl (Or.inl (Or.inr rfl))
      exact hxK (Or.inr (hback hxnew))
  · exact absurd hthree.1 (by omega)

end Workspace.ProofLemmas.StrongStaircaseMiddleRegionDichotomy
