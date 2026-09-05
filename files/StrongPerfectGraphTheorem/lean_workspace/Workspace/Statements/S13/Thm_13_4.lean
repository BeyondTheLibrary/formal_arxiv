import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.NoEvenPrismsOrBreakersInEitherOrientation
import Workspace.ProofLemmas.LongOddPrismYieldsOddStrongStaircase
import Workspace.ProofLemmas.EmptyCompleteClassForcesProperTwoJoin
import Workspace.ProofLemmas.StrongStaircaseComponentStructure
import Workspace.ProofLemmas.StrongStaircaseMiddleRegionDichotomy
import Workspace.ProofLemmas.StaircaseClassesFormProperHomogeneousPair

set_option autoImplicit false

namespace Workspace.Statements.S13

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem properHomogeneousPair_compl_aux {W : Type*} {K : SimpleGraph W}
    {A B : Set W} (h : IsProperHomogeneousPair K A B) :
    IsProperHomogeneousPair Kᶜ A B := by
  obtain ⟨hdisj, hAne, hBne, hUA, hUB, h11, h12, h21, h22⟩ := h
  have hVC : ∀ (S : Set W) (v : W),
      VertexComplete Kᶜ v S ↔ (v ∉ S ∧ VertexAnticomplete K v S) := by
    intro S v
    constructor
    · intro hv
      exact ⟨fun hvS => ((SimpleGraph.compl_adj K v v).mp (hv v hvS)).1 rfl,
        fun x hx hadj => ((SimpleGraph.compl_adj K v x).mp (hv x hx)).2 hadj⟩
    · rintro ⟨hvS, hv⟩ x hx
      exact (SimpleGraph.compl_adj K v x).mpr ⟨by rintro rfl; exact hvS hx, hv x hx⟩
  have hVA2 : ∀ (S : Set W) (v : W),
      (v ∉ S ∧ VertexAnticomplete Kᶜ v S) ↔ VertexComplete K v S := by
    intro S v
    constructor
    · rintro ⟨hvS, hv⟩ x hx
      by_contra hadj
      exact hv x hx ((SimpleGraph.compl_adj K v x).mpr
        ⟨by rintro rfl; exact hvS hx, hadj⟩)
    · intro hv
      refine ⟨fun hvS => K.irrefl (hv v hvS), fun x hx hadj => ?_⟩
      exact ((SimpleGraph.compl_adj K v x).mp hadj).2 (hv x hx)
  have hVAc : ∀ (S : Set W) (v : W),
      VertexComplete K v S → VertexAnticomplete Kᶜ v S :=
    fun S v hv x hx hadj => ((SimpleGraph.compl_adj K v x).mp hadj).2 (hv x hx)
  have houtA : ∀ v : W, VertexComplete K v A → v ∉ A ∪ B := by
    intro v hv
    have hmem : v ∈ ({w : W | VertexComplete K w A} ∪
        {w : W | w ∉ A ∧ VertexAnticomplete K w A}) := Or.inl hv
    rw [hUA] at hmem
    exact hmem
  have houtB : ∀ v : W, VertexComplete K v B → v ∉ A ∪ B := by
    intro v hv
    have hmem : v ∈ ({w : W | VertexComplete K w B} ∪
        {w : W | w ∉ B ∧ VertexAnticomplete K w B}) := Or.inl hv
    rw [hUB] at hmem
    exact hmem
  have hout : ∀ v : W, VertexAnticomplete K v A →
      VertexAnticomplete K v B → v ∉ A ∪ B := by
    intro v hvA hvB hmem
    rcases hmem with hA | hB
    · have h' : v ∈ ({w : W | VertexComplete K w B} ∪
          {w : W | w ∉ B ∧ VertexAnticomplete K w B}) :=
        Or.inr ⟨Set.disjoint_left.mp hdisj hA, hvB⟩
      rw [hUB] at h'
      exact h' (Or.inl hA)
    · have h' : v ∈ ({w : W | VertexComplete K w A} ∪
          {w : W | w ∉ A ∧ VertexAnticomplete K w A}) :=
        Or.inr ⟨Set.disjoint_right.mp hdisj hB, hvA⟩
      rw [hUA] at h'
      exact h' (Or.inr hB)
  refine ⟨hdisj, hAne, hBne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : {v : W | VertexComplete Kᶜ v A}
        = {v : W | v ∉ A ∧ VertexAnticomplete K v A} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVC A v
    have e2 : {v : W | v ∉ A ∧ VertexAnticomplete Kᶜ v A}
        = {v : W | VertexComplete K v A} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVA2 A v
    rw [e1, e2, Set.union_comm]
    exact hUA
  · have e1 : {v : W | VertexComplete Kᶜ v B}
        = {v : W | v ∉ B ∧ VertexAnticomplete K v B} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVC B v
    have e2 : {v : W | v ∉ B ∧ VertexAnticomplete Kᶜ v B}
        = {v : W | VertexComplete K v B} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVA2 B v
    rw [e1, e2, Set.union_comm]
    exact hUB
  · obtain ⟨w, hwA, hwB⟩ := h22
    have hw := hout w hwA hwB
    exact ⟨w, (hVC A w).mpr ⟨fun hc => hw (Or.inl hc), hwA⟩,
      (hVC B w).mpr ⟨fun hc => hw (Or.inr hc), hwB⟩⟩
  · obtain ⟨w, hwA, hwB⟩ := h21
    have hw := houtB w hwB
    exact ⟨w, (hVC A w).mpr ⟨fun hc => hw (Or.inl hc), hwA⟩, hVAc B w hwB⟩
  · obtain ⟨w, hwA, hwB⟩ := h12
    have hw := houtA w hwA
    exact ⟨w, hVAc A w hwA, (hVC B w).mpr ⟨fun hc => hw (Or.inr hc), hwB⟩⟩
  · obtain ⟨w, hwA, hwB⟩ := h11
    exact ⟨w, hVAc A w hwA, hVAc B w hwB⟩

theorem thm_13_4 (G : SimpleGraph V) (hG : Berge G)
    (hK4G : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hK4Gc : ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4)))
    (hprism : ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsLongPrism G s t R₁ R₂ R₃ ∧ IsOddPrism G s t R₁ R₂ R₃) :
    (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨
      AdmitsBalancedSkewPartition G ∨ AdmitsProperHomogeneousPair G := by
  by_contra hout
  have h2join : ¬ AdmitsProper2Join G ∧ ¬ AdmitsProper2Join Gᶜ := by
    constructor
    · intro h; exact hout (Or.inl (Or.inl h))
    · intro h; exact hout (Or.inl (Or.inr h))
  have hskew : ¬ AdmitsBalancedSkewPartition G := by
    intro h; exact hout (Or.inr (Or.inl h))
  have hhom : ¬ AdmitsProperHomogeneousPair G := by
    intro h; exact hout (Or.inr (Or.inr h))
  obtain ⟨hevenG, honeG, htwoG, hthreeG, hevenGc, honeGc, htwoGc, hthreeGc⟩ :=
    Workspace.ProofLemmas.NoEvenPrismsOrBreakersInEitherOrientation.noEvenPrismsOrBreakersInEitherOrientation
      G hG hK4G hK4Gc hprism h2join hskew
  have hskewGc : ¬ AdmitsBalancedSkewPartition Gᶜ := by
    intro h
    exact hskew (Workspace.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp h)
  have hhomGc : ¬ AdmitsProperHomogeneousPair Gᶜ := by
    rintro ⟨A, B, hAB⟩
    apply hhom
    refine ⟨A, B, ?_⟩
    simpa using (properHomogeneousPair_compl_aux (K := Gᶜ) hAB)
  have finish : ∀ (H : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V),
      Berge H → ¬ Appears H (⊤ : SimpleGraph (Fin 4)) →
      (¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism H s t R₁ R₂ R₃) →
      (¬ ∃ A' C' B' F Q : Set V, IsOneBreaker H A' C' B' F Q) →
      (¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' x : V),
        IsThreeBreaker H A' C' B' a₀' R₀' b₀' x) →
      ¬ AdmitsProper2Join H → ¬ AdmitsBalancedSkewPartition H →
      ¬ AdmitsProperHomogeneousPair H →
      StronglyMaximalStaircase H A C B a₀ R₀ b₀ → Odd (pathLength R₀) → False := by
    intro H A C B a₀ b₀ R₀ hBerge hK4 heven hone hthree hjoin hbalanced hpair hstairs hodd
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    let M : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      attachments H F VS = ∅}
    let D : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      (attachments H F VS).Nonempty}
    obtain ⟨hattach, hAB, hAC, hAD, hAA₀, hAB₀, hAN, hAM,
      hBC, hBD, hBA₀, hBB₀, hBN, hBM, hCD, hCA₀, hCB₀, hCN, hCM,
      hDA₀, hDB₀, hDN, hDM, hA₀B₀, hA₀N, hA₀M, hB₀N, hB₀M, hNM, hcover,
      hintne, hintM, hMne, hMattach, hDattach⟩ :=
      Workspace.ProofLemmas.StrongStaircaseComponentStructure.strongStaircaseComponentStructure
        H hBerge hK4 heven hone hthree hbalanced A C B a₀ b₀ R₀ hstairs hodd
    have hparts :
        Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧ Disjoint A A₀ ∧ Disjoint A B₀ ∧
        Disjoint A N ∧ Disjoint A M ∧ Disjoint B C ∧ Disjoint B D ∧ Disjoint B A₀ ∧
        Disjoint B B₀ ∧ Disjoint B N ∧ Disjoint B M ∧ Disjoint C D ∧ Disjoint C A₀ ∧
        Disjoint C B₀ ∧ Disjoint C N ∧ Disjoint C M ∧ Disjoint D A₀ ∧ Disjoint D B₀ ∧
        Disjoint D N ∧ Disjoint D M ∧ Disjoint A₀ B₀ ∧ Disjoint A₀ N ∧ Disjoint A₀ M ∧
        Disjoint B₀ N ∧ Disjoint B₀ M ∧ Disjoint N M ∧
        A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M = Set.univ := by
      exact ⟨hAB, hAC, hAD, hAA₀, hAB₀, hAN, hAM, hBC, hBD, hBA₀, hBB₀,
        hBN, hBM, hCD, hCA₀, hCB₀, hCN, hCM, hDA₀, hDB₀, hDN, hDM,
        hA₀B₀, hA₀N, hA₀M, hB₀N, hB₀M, hNM, hcover⟩
    have hMno : ∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ M →
        attachments H F VS = ∅ := by
      intro F hF hcomp hFM
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨v, hv⟩ := hF
      have hvD : v ∈ D := ⟨F, hcomp, hv, ⟨z, hz⟩⟩
      exact Set.disjoint_left.mp hDM hvD (hFM hv)
    have hNne : N.Nonempty := by
      by_contra hN
      apply hjoin
      apply Workspace.ProofLemmas.EmptyCompleteClassForcesProperTwoJoin.emptyCompleteClassForcesProperTwoJoin
        H A C B a₀ b₀ R₀ hstairs hodd hparts
      · exact hintne
      · exact hintM
      · exact hMattach
      · exact hDattach
      · exact Set.not_nonempty_iff_eq_empty.mp hN
    rcases Workspace.ProofLemmas.StrongStaircaseMiddleRegionDichotomy.strongStaircaseMiddleRegionDichotomy
      H hBerge A C B a₀ b₀ R₀ hstairs hodd hparts hintne hintM hMno hDattach hNne with
      hbad | hCDempty
    · exact hbalanced hbad
    · apply hpair
      refine ⟨A, B, ?_⟩
      exact Workspace.ProofLemmas.StaircaseClassesFormProperHomogeneousPair.staircaseClassesFormProperHomogeneousPair
        H A C B a₀ b₀ R₀ hstairs hparts hMno hintne hintM hNne hCDempty
  obtain ⟨H, A, C, B, a₀, b₀, R₀, hHG, hstairs, hodd, hlen⟩ :=
    Workspace.ProofLemmas.LongOddPrismYieldsOddStrongStaircase.longOddPrismYieldsOddStrongStaircase
      G hG hprism hevenG hevenGc
  rcases hHG with hHG | hHG
  · subst H
    exact finish G A C B a₀ b₀ R₀ hG hK4G hevenG honeG hthreeG
      h2join.1 hskew hhom hstairs hodd
  · subst H
    exact finish Gᶜ A C B a₀ b₀ R₀
      (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) hK4Gc hevenGc honeGc hthreeGc
      h2join.2 hskewGc hhomGc hstairs hodd

end SPGT

end Workspace.Statements.S13
