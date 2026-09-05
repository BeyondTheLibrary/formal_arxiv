import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.StrongStaircaseComponentStructure

set_option autoImplicit false

namespace Workspace.ProofLemmas.EmptyCompleteClassForcesProperTwoJoin

open Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions.SPGT

private theorem mem_of_walk {V : Type*} {G : SimpleGraph V} {P Q C : Set V}
    (hPQ : Anticomplete G P Q) (hsub : C ⊆ P ∪ Q) :
    ∀ {a b : ↥C}, (G.induce C).Walk a b → (a : V) ∈ P → (b : V) ∈ P := by
  intro a b w
  induction w with
  | nil => exact id
  | @cons x y _ hadj _ ih =>
      intro hx
      refine ih ?_
      have hadj' : G.Adj (x : V) (y : V) := hadj
      rcases hsub y.2 with hy | hy
      · exact hy
      · exact absurd hadj' (hPQ (x : V) hx (y : V) hy)

private theorem connectedSet_subset_of_anticomplete
    {V : Type*} {G : SimpleGraph V} {P Q C : Set V}
    (hPQ : Anticomplete G P Q) (hC : ConnectedSet G C) (hsub : C ⊆ P ∪ Q)
    {x : V} (hx : x ∈ C) (hxP : x ∈ P) : C ⊆ P :=
  fun _ hy => mem_of_walk hPQ hsub (hC ⟨x, hx⟩ ⟨_, hy⟩).some hxP

private theorem path_subset_of_connected
    {V : Type*} {G : SimpleGraph V} {p : List V} {a₁ a₂ : V}
    (hp : IsPathFrom G p a₁ a₂) {C : Set V} (hCsub : C ⊆ {v : V | v ∈ p})
    (hC : ConnectedSet G C) (h₁ : a₁ ∈ C) (h₂ : a₂ ∈ C) :
    {v : V | v ∈ p} ⊆ C := by
  classical
  have hlen : 0 < p.length := PathBasics.path_length_pos hp.1
  have hzero : p[0]'hlen = a₁ := PathBasics.getElem_zero_of_head? hp.2.1 hlen
  have hlast : p[p.length - 1]'(by omega) = a₂ :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hlen
  intro x hx
  by_contra hxC
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  subst hxi
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact absurd (hzero ▸ h₁) hxC
    · exact h
  have hilast : i < p.length - 1 := by
    rcases Nat.lt_or_ge i (p.length - 1) with h | h
    · exact h
    · have : i = p.length - 1 := by omega
      subst this
      exact absurd (hlast ▸ h₂) hxC
  set P : Set V := {v : V | ∃ j, ∃ _ : j < p.length, j < i ∧ v = p[j]} with hP
  set Q : Set V := {v : V | ∃ j, ∃ _ : j < p.length, i < j ∧ v = p[j]} with hQ
  have hPQ : Anticomplete G P Q := by
    rintro a ⟨j, hj, hji, rfl⟩ b ⟨k, hk, hik, rfl⟩
    exact PathBasics.path_not_adj_of_gap hp.1 hj hk (by omega) (by omega)
  have hsub : C ⊆ P ∪ Q := by
    intro c hc
    obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.mp (hCsub hc)
    have hji : j ≠ i := by
      rintro rfl
      exact hxC (hcj ▸ hc)
    rcases Nat.lt_or_ge j i with h | h
    · exact Or.inl ⟨j, hj, h, hcj.symm⟩
    · exact Or.inr ⟨j, hj, by omega, hcj.symm⟩
  have ha₁P : a₁ ∈ P := ⟨0, hlen, hi0, hzero.symm⟩
  have hCP : C ⊆ P := connectedSet_subset_of_anticomplete hPQ hC hsub h₁ ha₁P
  obtain ⟨k, hk, hki, hak⟩ := hCP h₂
  have : k = p.length - 1 := by
    have hnd := PathBasics.path_nodup hp.1
    have heq : p[k]'hk = p[p.length - 1]'(by omega) := by rw [← hak, hlast]
    exact hnd.getElem_inj_iff.mp heq
  omega

private theorem meet_of_link
    {V : Type*} {G : SimpleGraph V} {X A : Set V}
    (hAX : A ⊆ X) (hAne : A.Nonempty)
    (hlink : ∀ v ∈ X, ∃ S : Set V, S ⊆ X ∧ ConnectedSet G S ∧ v ∈ S ∧ (S ∩ A).Nonempty)
    {Cc : Set V} (hC : IsComponent G X Cc) : (Cc ∩ A).Nonempty := by
  obtain ⟨a₀, ha₀⟩ := hAne
  have hCne : Cc.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hsing := hC.2.2 ({a₀} : Set V) (Set.empty_subset _)
      (Set.singleton_subset_iff.mpr (hAX ha₀))
      (Thm134RegionAux.connectedSet_singleton G a₀)
    exact absurd (hsing ▸ (rfl : a₀ ∈ ({a₀} : Set V))) (Set.notMem_empty a₀)
  obtain ⟨v, hv⟩ := hCne
  obtain ⟨S, hSX, hScon, hvS, hSA⟩ := hlink v (hC.1 hv)
  have hun : ConnectedSet G (Cc ∪ S) :=
    ConnectedSetUnionAttach.connectedSet_union hC.2.1 hScon (Or.inl ⟨v, hv, hvS⟩)
  have heq : Cc ∪ S = Cc :=
    hC.2.2 (Cc ∪ S) Set.subset_union_left (Set.union_subset hC.1 hSX) hun
  obtain ⟨x, hxS, hxA⟩ := hSA
  have hxC : x ∈ Cc := by rw [← heq]; exact Or.inr hxS
  exact ⟨x, hxC, hxA⟩

theorem emptyCompleteClassForcesProperTwoJoin
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
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
      (attachments H F A₀).Nonempty ∧ (attachments H F B₀).Nonempty) →
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ D →
      attachments H F (A₀ ∪ B₀) = ∅ ∧
        (attachments H F (A ∪ C)).Nonempty ∧ (attachments H F (B ∪ C)).Nonempty) →
    N = ∅ → AdmitsProper2Join H := by
  classical
  intro VS A₀ B₀ N H₀ M D hpart hintNe hintM hMatt hDatt hN
  rcases hpart with ⟨hAB, hAC, hAD, hAA₀, hAB₀, hAN, hAM, hBC, hBD, hBA₀,
    hBB₀, hBN, hBM, hCD, hCA₀, hCB₀, hCN, hCM, hDA₀, hDB₀, hDN, hDM,
    hA₀B₀, hA₀N, hA₀M, hB₀N, hB₀M, hNM, hcover⟩
  have hstep : StepConnected H A C B := hstairs.1.1.1
  have hban : IsBanister H A C B a₀ R₀ b₀ := hstairs.1.1.2.1
  have hpath : IsPathFrom H R₀ a₀ b₀ := hban.1
  have hlen : 3 ≤ pathLength R₀ := hstairs.1.1.2.2
  have haA₀ : a₀ ∈ A₀ := hban.2.2.1
  have hbB₀ : b₀ ∈ B₀ := hban.2.2.2.1
  let Q : Set V := A₀ ∪ B₀ ∪ M
  have hRQ : {v : V | v ∈ R₀} ⊆ Q := by
    intro v hv
    by_cases hva : v = a₀
    · exact Or.inl (Or.inl (hva ▸ haA₀))
    by_cases hvb : v = b₀
    · exact Or.inl (Or.inr (hvb ▸ hbB₀))
    · exact Or.inr (hintM ((PathBasics.mem_interior_iff_of_pathFrom hpath).2 ⟨hv, hva, hvb⟩))
  have hRcon : ConnectedSet H {v : V | v ∈ R₀} :=
    Thm134RegionAux.connectedSet_of_isPathList R₀ hpath.1
  obtain ⟨X₂, hX₂, haX₂⟩ :=
    ComponentsOfSetBasics.exists_isComponent_mem H Q (show a₀ ∈ Q from Or.inl (Or.inl haA₀))
  have hRsubX₂ : {v : V | v ∈ R₀} ⊆ X₂ := by
    have haR : a₀ ∈ R₀ := (PathBasics.isPathFrom_ends_mem hpath).1
    have hc : ConnectedSet H (X₂ ∪ {v : V | v ∈ R₀}) :=
      ConnectedSetUnionAttach.connectedSet_union hX₂.2.1 hRcon (Or.inl ⟨a₀, haX₂, haR⟩)
    have heq := hX₂.2.2 (X₂ ∪ {v : V | v ∈ R₀}) Set.subset_union_left
      (Set.union_subset hX₂.1 hRQ) hc
    intro v hv
    have : v ∈ X₂ ∪ {v : V | v ∈ R₀} := Or.inr hv
    rwa [heq] at this
  have hbX₂ : b₀ ∈ X₂ := hRsubX₂ (PathBasics.isPathFrom_ends_mem hpath).2
  let X₁ : Set V := Set.univ \ X₂
  let A₂ : Set V := A₀ ∩ X₂
  let B₂ : Set V := B₀ ∩ X₂
  have hclasses : ∀ v : V, v ∈ A ∨ v ∈ B ∨ v ∈ C ∨ v ∈ D ∨ v ∈ A₀ ∨
      v ∈ B₀ ∨ v ∈ N ∨ v ∈ M := by
    intro v
    have hv : v ∈ A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M := by rw [hcover]; trivial
    simp only [Set.mem_union] at hv
    tauto
  have hA_X₁ : A ⊆ X₁ := by
    intro v hv
    refine ⟨trivial, ?_⟩
    intro hvX
    rcases hX₂.1 hvX with (hvA₀ | hvB₀) | hvM
    · exact (Set.disjoint_left.mp hAA₀ hv) hvA₀
    · exact (Set.disjoint_left.mp hAB₀ hv) hvB₀
    · exact (Set.disjoint_left.mp hAM hv) hvM
  have hB_X₁ : B ⊆ X₁ := by
    intro v hv
    refine ⟨trivial, ?_⟩
    intro hvX
    rcases hX₂.1 hvX with (hvA₀ | hvB₀) | hvM
    · exact (Set.disjoint_left.mp hBA₀ hv) hvA₀
    · exact (Set.disjoint_left.mp hBB₀ hv) hvB₀
    · exact (Set.disjoint_left.mp hBM hv) hvM
  have hC_X₁ : C ⊆ X₁ := by
    intro v hv
    refine ⟨trivial, ?_⟩
    intro hvX
    rcases hX₂.1 hvX with (hvA₀ | hvB₀) | hvM
    · exact (Set.disjoint_left.mp hCA₀ hv) hvA₀
    · exact (Set.disjoint_left.mp hCB₀ hv) hvB₀
    · exact (Set.disjoint_left.mp hCM hv) hvM
  have hD_X₁ : D ⊆ X₁ := by
    intro v hv
    refine ⟨trivial, ?_⟩
    intro hvX
    rcases hX₂.1 hvX with (hvA₀ | hvB₀) | hvM
    · exact (Set.disjoint_left.mp hDA₀ hv) hvA₀
    · exact (Set.disjoint_left.mp hDB₀ hv) hvB₀
    · exact (Set.disjoint_left.mp hDM hv) hvM
  have hQoutside : ∀ q ∈ Q, q ∉ X₂ → ∀ x ∈ X₂, ¬ H.Adj q x := by
    intro q hq hqx
    exact Thm134RegionAux.component_no_outside_neighbour hX₂ hq hqx
  have hAne : A.Nonempty := hstep.2.1.1
  have hBne : B.Nonempty := hstep.2.1.2
  have hA2ne : A₂.Nonempty := ⟨a₀, haA₀, haX₂⟩
  have hB2ne : B₂.Nonempty := ⟨b₀, hbB₀, hbX₂⟩
  have hcross : ∀ u ∈ X₁, ∀ v ∈ X₂,
      H.Adj u v ↔ ((u ∈ A ∧ v ∈ A₂) ∨ (u ∈ B ∧ v ∈ B₂)) := by
    intro u hu v hv
    constructor
    · intro huv
      have huNX : u ∉ X₂ := hu.2
      have hvQ := hX₂.1 hv
      rcases hclasses u with huA | huB | huC | huD | huA₀ | huB₀ | huN | huM
      · rcases hvQ with (hvA₀ | hvB₀) | hvM
        · exact Or.inl ⟨huA, hvA₀, hv⟩
        · exact absurd huv.symm ((hvB₀ : IsRightStar H A C B v).2.2 u (Or.inl huA))
        · obtain ⟨F, hF, hvF, hatt⟩ := hvM
          have huatt : u ∈ attachments H F VS := ⟨Or.inl (Or.inl huA), v, hvF, huv⟩
          rw [hatt] at huatt
          exact absurd huatt (Set.notMem_empty u)
      · rcases hvQ with (hvA₀ | hvB₀) | hvM
        · exact absurd huv.symm ((hvA₀ : IsLeftStar H A C B v).2.2 u (Or.inl huB))
        · exact Or.inr ⟨huB, hvB₀, hv⟩
        · obtain ⟨F, hF, hvF, hatt⟩ := hvM
          have huatt : u ∈ attachments H F VS := ⟨Or.inl (Or.inr huB), v, hvF, huv⟩
          rw [hatt] at huatt
          exact absurd huatt (Set.notMem_empty u)
      · rcases hvQ with (hvA₀ | hvB₀) | hvM
        · exact absurd huv.symm ((hvA₀ : IsLeftStar H A C B v).2.2 u (Or.inr huC))
        · exact absurd huv.symm ((hvB₀ : IsRightStar H A C B v).2.2 u (Or.inr huC))
        · obtain ⟨F, hF, hvF, hatt⟩ := hvM
          have huatt : u ∈ attachments H F VS := ⟨Or.inr huC, v, hvF, huv⟩
          rw [hatt] at huatt
          exact absurd huatt (Set.notMem_empty u)
      · obtain ⟨F, hF, huF, hFatt⟩ := huD
        have hFD : F ⊆ D := fun z hz => ⟨F, hF, hz, hFatt⟩
        obtain ⟨hstar, -, -⟩ := hDatt F ⟨u, huF⟩ hF hFD
        rcases hvQ with (hvA₀ | hvB₀) | hvM
        · have : v ∈ attachments H F (A₀ ∪ B₀) := ⟨Or.inl hvA₀, u, huF, huv.symm⟩
          rw [hstar] at this
          exact absurd this (Set.notMem_empty v)
        · have : v ∈ attachments H F (A₀ ∪ B₀) := ⟨Or.inr hvB₀, u, huF, huv.symm⟩
          rw [hstar] at this
          exact absurd this (Set.notMem_empty v)
        · obtain ⟨F', hF', hvF', hF'att⟩ := hvM
          by_cases heq : F = F'
          · subst heq
            rw [hF'att] at hFatt
            exfalso
            exact Set.not_nonempty_empty hFatt
          · exact absurd huv (ComponentsOfSetBasics.anticomplete_of_isComponent H hF hF' heq u huF v hvF')
      · exact absurd huv (hQoutside u (Or.inl (Or.inl huA₀)) huNX v hv)
      · exact absurd huv (hQoutside u (Or.inl (Or.inr huB₀)) huNX v hv)
      · rw [hN] at huN
        exact absurd huN (Set.notMem_empty u)
      · exact absurd huv (hQoutside u (Or.inr huM) huNX v hv)
    · rintro (⟨huA, hvA₂⟩ | ⟨huB, hvB₂⟩)
      · exact ((hvA₂.1 : IsLeftStar H A C B v).2.1 u huA).symm
      · exact ((hvB₂.1 : IsRightStar H A C B v).2.1 u huB).symm
  have hRungLink : ∀ x ∈ VS, ∃ S : Set V, S ⊆ X₁ ∧ ConnectedSet H S ∧ x ∈ S ∧
      (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
    intro x hx
    obtain ⟨a, p, b, hr, hxp⟩ := hstep.2.2.1 x hx
    let S : Set V := {z : V | z ∈ p}
    have hSVS : S ⊆ VS := by
      intro z hz
      by_cases hza : z = a
      · exact Or.inl (Or.inl (hza ▸ hr.2.1))
      by_cases hzb : z = b
      · exact Or.inl (Or.inr (hzb ▸ hr.2.2.1))
      · exact Or.inr (hr.2.2.2.2.2 z ((PathBasics.mem_interior_iff_of_pathFrom hr.1).2 ⟨hz, hza, hzb⟩))
    have hSX₁ : S ⊆ X₁ := by
      intro z hz
      rcases hSVS hz with (hzA | hzB) | hzC
      · exact hA_X₁ hzA
      · exact hB_X₁ hzB
      · exact hC_X₁ hzC
    refine ⟨S, hSX₁, Thm134RegionAux.connectedSet_of_isPathList p hr.1.1, hxp, ?_, ?_⟩
    · exact ⟨a, (PathBasics.isPathFrom_ends_mem hr.1).1, hr.2.1⟩
    · exact ⟨b, (PathBasics.isPathFrom_ends_mem hr.1).2, hr.2.2.1⟩
  have hlink₁ : ∀ u ∈ X₁, ∃ S : Set V, S ⊆ X₁ ∧ ConnectedSet H S ∧ u ∈ S ∧
      (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
    intro u hu
    have huNX : u ∉ X₂ := hu.2
    rcases hclasses u with huA | huB | huC | huD | huA₀ | huB₀ | huN | huM
    · exact hRungLink u (Or.inl (Or.inl huA))
    · exact hRungLink u (Or.inl (Or.inr huB))
    · exact hRungLink u (Or.inr huC)
    · obtain ⟨F, hF, huF, hFatt⟩ := huD
      have hFD : F ⊆ D := fun z hz => ⟨F, hF, hz, hFatt⟩
      obtain ⟨-, ⟨x, hxAC, f, hfF, hxf⟩, -⟩ := hDatt F ⟨u, huF⟩ hF hFD
      obtain ⟨P, hPX, hPcon, hxP, hPA, hPB⟩ := hRungLink x (by rcases hxAC with hxA | hxC; exact Or.inl (Or.inl hxA); exact Or.inr hxC)
      refine ⟨F ∪ P, Set.union_subset (fun z hz => hD_X₁ (hFD hz)) hPX,
        ConnectedSetUnionAttach.connectedSet_union hF.2.1 hPcon (Or.inr ⟨f, hfF, x, hxP, hxf.symm⟩),
        Or.inl huF, ?_, ?_⟩
      · obtain ⟨a, haP, haA⟩ := hPA; exact ⟨a, Or.inr haP, haA⟩
      · obtain ⟨b, hbP, hbB⟩ := hPB; exact ⟨b, Or.inr hbP, hbB⟩
    · obtain ⟨a, haA⟩ := hAne
      obtain ⟨P, hPX, hPcon, haP, hPA, hPB⟩ := hRungLink a (Or.inl (Or.inl haA))
      have hua : H.Adj u a := (huA₀ : IsLeftStar H A C B u).2.1 a haA
      refine ⟨P ∪ {u}, Set.union_subset hPX (Set.singleton_subset_iff.mpr hu),
        ConnectedSetUnionAttach.connectedSet_union_singleton hPcon ⟨a, haP, hua⟩,
        Or.inr rfl, ?_, ?_⟩
      · obtain ⟨z, hzP, hzA⟩ := hPA; exact ⟨z, Or.inl hzP, hzA⟩
      · obtain ⟨z, hzP, hzB⟩ := hPB; exact ⟨z, Or.inl hzP, hzB⟩
    · obtain ⟨b, hbB⟩ := hBne
      obtain ⟨P, hPX, hPcon, hbP, hPA, hPB⟩ := hRungLink b (Or.inl (Or.inr hbB))
      have hub : H.Adj u b := (huB₀ : IsRightStar H A C B u).2.1 b hbB
      refine ⟨P ∪ {u}, Set.union_subset hPX (Set.singleton_subset_iff.mpr hu),
        ConnectedSetUnionAttach.connectedSet_union_singleton hPcon ⟨b, hbP, hub⟩,
        Or.inr rfl, ?_, ?_⟩
      · obtain ⟨z, hzP, hzA⟩ := hPA; exact ⟨z, Or.inl hzP, hzA⟩
      · obtain ⟨z, hzP, hzB⟩ := hPB; exact ⟨z, Or.inl hzP, hzB⟩
    · rw [hN] at huN
      exact absurd huN (Set.notMem_empty u)
    · obtain ⟨F, hF, huF, hFatt⟩ := huM
      have hFM : F ⊆ M := fun z hz => ⟨F, hF, hz, hFatt⟩
      have hFQ : F ⊆ Q := fun z hz => Or.inr (hFM hz)
      have hFX₁ : F ⊆ X₁ := by
        intro z hz
        refine ⟨trivial, ?_⟩
        intro hzX
        have hc : ConnectedSet H (X₂ ∪ F) :=
          ConnectedSetUnionAttach.connectedSet_union hX₂.2.1 hF.2.1 (Or.inl ⟨z, hzX, hz⟩)
        have heq := hX₂.2.2 (X₂ ∪ F) Set.subset_union_left (Set.union_subset hX₂.1 hFQ) hc
        exact huNX (by rw [← heq]; exact Or.inr huF)
      obtain ⟨⟨alpha, haA₀', f, hfF, haf⟩, -⟩ := hMatt F ⟨u, huF⟩ hF hFM
      have haX₁ : alpha ∈ X₁ := by
        refine ⟨trivial, ?_⟩
        intro haX
        exact (hQoutside f (hFQ hfF) (hFX₁ hfF).2 alpha haX) haf.symm
      obtain ⟨a, haA⟩ := hAne
      obtain ⟨P, hPX, hPcon, haP, hPA, hPB⟩ := hRungLink a (Or.inl (Or.inl haA))
      have hFaCon : ConnectedSet H (F ∪ {alpha}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨f, hfF, haf⟩
      have haa : H.Adj alpha a := (haA₀' : IsLeftStar H A C B alpha).2.1 a haA
      refine ⟨(F ∪ {alpha}) ∪ P,
        Set.union_subset (Set.union_subset hFX₁ (Set.singleton_subset_iff.mpr haX₁)) hPX,
        ConnectedSetUnionAttach.connectedSet_union hFaCon hPcon (Or.inr ⟨alpha, Or.inr rfl, a, haP, haa⟩),
        Or.inl (Or.inl huF), ?_, ?_⟩
      · obtain ⟨z, hzP, hzA⟩ := hPA; exact ⟨z, Or.inr hzP, hzA⟩
      · obtain ⟨z, hzP, hzB⟩ := hPB; exact ⟨z, Or.inr hzP, hzB⟩
  have hlink₂ : ∀ v ∈ X₂, ∃ S : Set V, S ⊆ X₂ ∧ ConnectedSet H S ∧ v ∈ S ∧
      (S ∩ A₂).Nonempty ∧ (S ∩ B₂).Nonempty := by
    intro v hv
    exact ⟨X₂, Set.Subset.rfl, hX₂.2.1, hv, ⟨a₀, haX₂, haA₀, haX₂⟩,
      ⟨b₀, hbX₂, hbB₀, hbX₂⟩⟩
  have hAnt : A.Nontrivial := by
    obtain ⟨a, haA⟩ := hAne
    obtain ⟨a₁, P₁, b₁, a₂, P₂, b₂, hs, -⟩ := hstep.2.2.2.1 a (Or.inl (Or.inl haA))
    refine ⟨a₁, hs.1.2.1, a₂, hs.2.1.2.1, ?_⟩
    intro heq
    exact hs.2.2.1 a₁ (PathBasics.isPathFrom_ends_mem hs.1.1).1 (heq ▸ (PathBasics.isPathFrom_ends_mem hs.2.1.1).1)
  have hpath₁ : ∀ a b : V, A = {a} → B = {b} → ∀ p : List V, IsPathFrom H p a b →
      {v : V | v ∈ p} = X₁ → Odd (pathLength p) ∧ 3 ≤ pathLength p := by
    intro a b hAeq hBeq p hp hpX
    exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hAnt
    rw [hAeq] at hx hy
    exact hxy ((hx : x = a).trans (hy : y = a).symm)
  have hpath₂ : ∀ a b : V, A₂ = {a} → B₂ = {b} → ∀ p : List V, IsPathFrom H p a b →
      {v : V | v ∈ p} = X₂ → Odd (pathLength p) ∧ 3 ≤ pathLength p := by
    intro a b hAeq hBeq p hp hpX
    have haa : a₀ = a := by
      have : a₀ ∈ ({a} : Set V) := hAeq ▸ (show a₀ ∈ A₂ from ⟨haA₀, haX₂⟩)
      simpa using this
    have hbb : b₀ = b := by
      have : b₀ ∈ ({b} : Set V) := hBeq ▸ (show b₀ ∈ B₂ from ⟨hbB₀, hbX₂⟩)
      simpa using this
    have hp' : IsPathFrom H p a₀ b₀ := by simpa [haa, hbb] using hp
    have hRp : {v : V | v ∈ R₀} ⊆ {v : V | v ∈ p} := by rw [hpX]; exact hRsubX₂
    have hpR : {v : V | v ∈ p} ⊆ {v : V | v ∈ R₀} :=
      path_subset_of_connected hp' hRp hRcon (PathBasics.isPathFrom_ends_mem hpath).1
        (PathBasics.isPathFrom_ends_mem hpath).2
    have hfin : R₀.toFinset = p.toFinset := by
      ext z
      simp only [List.mem_toFinset]
      exact ⟨fun hz => hRp hz, fun hz => hpR hz⟩
    have hlens : R₀.length = p.length := by
      have hRcard := List.toFinset_card_of_nodup hpath.1.2.1
      have hpcard := List.toFinset_card_of_nodup hp.1.2.1
      calc
        R₀.length = R₀.toFinset.card := hRcard.symm
        _ = p.toFinset.card := congrArg Finset.card hfin
        _ = p.length := hpcard
    have hpl : pathLength p = pathLength R₀ := by simp [pathLength, hlens]
    rw [hpl]
    exact ⟨hodd, hlen⟩
  have hcomp₁ : ∀ Cc : Set V, IsComponent H X₁ Cc →
      (Cc ∩ A).Nonempty ∧ (Cc ∩ B).Nonempty := by
    intro Cc hCc
    constructor
    · exact meet_of_link hA_X₁ hAne (fun v hv => by
        obtain ⟨S, hSX, hSc, hvS, hSA, hSB⟩ := hlink₁ v hv
        exact ⟨S, hSX, hSc, hvS, hSA⟩) hCc
    · exact meet_of_link hB_X₁ hBne (fun v hv => by
        obtain ⟨S, hSX, hSc, hvS, hSA, hSB⟩ := hlink₁ v hv
        exact ⟨S, hSX, hSc, hvS, hSB⟩) hCc
  have hcomp₂ : ∀ Cc : Set V, IsComponent H X₂ Cc →
      (Cc ∩ A₂).Nonempty ∧ (Cc ∩ B₂).Nonempty := by
    intro Cc hCc
    constructor
    · exact meet_of_link (Set.inter_subset_right) hA2ne (fun v hv => by
        obtain ⟨S, hSX, hSc, hvS, hSA, hSB⟩ := hlink₂ v hv
        exact ⟨S, hSX, hSc, hvS, hSA⟩) hCc
    · exact meet_of_link (Set.inter_subset_right) hB2ne (fun v hv => by
        obtain ⟨S, hSX, hSc, hvS, hSA, hSB⟩ := hlink₂ v hv
        exact ⟨S, hSX, hSc, hvS, hSB⟩) hCc
  refine ⟨X₁, X₂, ?_, ?_, A, B, A₂, B₂, hA_X₁, hB_X₁,
    Set.inter_subset_right, Set.inter_subset_right, hAne, hBne, hA2ne, hB2ne, hAB, ?_,
    hcross, hcomp₁, hcomp₂, hpath₁, hpath₂⟩
  · ext v
    simp [X₁]
  · exact Set.disjoint_left.mpr (fun v hv h => hv.2 h)
  · exact hA₀B₀.mono Set.inter_subset_left Set.inter_subset_left

end Workspace.ProofLemmas.EmptyCompleteClassForcesProperTwoJoin
