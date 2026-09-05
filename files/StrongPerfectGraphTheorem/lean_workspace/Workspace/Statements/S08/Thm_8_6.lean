import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.NaturalAppearanceStripSystem
import Workspace.ProofLemmas.NormalizedMaximalStripSystemLocality
import Workspace.ProofLemmas.MajorAnticomponentSaturatesStripSystem
import Workspace.ProofLemmas.NoMajorVerticesOutsideMaximalStripSystem
import Workspace.ProofLemmas.NoComponentAttachmentInsideStripNeighbourhood
import Workspace.ProofLemmas.LineGraphOrSelectedEndgameStrip
import Workspace.ProofLemmas.SelectedStripSeparationData
import Workspace.ProofLemmas.DisjointStripEndsGiveProperTwoJoin
import Workspace.ProofLemmas.IntersectingStripEndsGiveBalancedSkewPartition

set_option autoImplicit false

namespace Workspace.Statements.S08

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_8_6 {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (n : ℕ) (H₀ : SimpleGraph (Fin n)) (K₀ : Set V)
    (happ : IsAppearance G J H₀ K₀)
    (hdeg : DegenerateAppearance J H₀ →
      Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧ Appears Gᶜ J') :
    Nonempty (G ≃g H₀.lineGraph) ∨
    (¬ Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧ AdmitsProper2Join G) ∨
    AdmitsBalancedSkewPartition G := by
  classical
  by_contra hgoal
  push_neg at hgoal
  obtain ⟨hnotLine, hnotTwoJoin, hnotBalanced⟩ := hgoal
  obtain ⟨S₀, N₀, R₀, hS₀, hS₀K₀, hForms₀, hCover, hNatural, hS₀nondeg⟩ :=
    Workspace.ProofLemmas.NaturalAppearanceStripSystem.naturalAppearanceStripSystem
      G J H₀ K₀ hJ happ
  have hR₀K₀ : ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₀ u v} = K₀ := by
    rw [← hS₀K₀]
    ext x
    rw [Workspace.ProofLemmas.StripSystemBasics.mem_stripSystemVertices_iff]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, huv, hx⟩
      rcases hForms₀.1 u v huv with ⟨-, s, t, hp, hsub, -, -⟩
      exact ⟨u, v, huv, hsub x hx⟩
    · rintro ⟨u, v, huv, hx⟩
      exact ⟨u, v, huv, hCover u v huv x hx⟩
  obtain ⟨S, N, hS, hEnlarges, hMaximal⟩ :=
    Workspace.ProofLemmas.StripSystemMaximal.exists_maximal_enlargement hS₀
  have hOldRungs : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R₀ u v) := by
    intro u v huv
    exact Workspace.ProofLemmas.StripSystemEnlarge.isUVRung_of_enlarges'
      hJ hS₀ hS hEnlarges (hForms₀.1 u v huv)
  have hForms : FormsLineGraph G J S N R₀ H₀ :=
    Workspace.ProofLemmas.StripSystemEnlarge.formsLineGraph_of_enlarges
      hJ hS₀ hS hEnlarges hForms₀
  have hnormalized :=
    Workspace.ProofLemmas.NormalizedMaximalStripSystemLocality.normalizedMaximalStripSystemLocality
      G hG J hJ n H₀ K₀ happ S₀ N₀ R₀ hS₀ hS₀K₀ hForms₀ hCover hS₀nondeg
      S N hS hMaximal hEnlarges hnotBalanced hnoenl hdeg
  simp only at hnormalized
  obtain ⟨hNoOvershadowed, hLocalWithMajor⟩ := hnormalized
  have hNoOvershadowed' :
      (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∨
        Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))) →
      ¬ ∃ (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
          IsAppearance G J H K ∧ IsOvershadowedAppearance G H K φ := by
    intro hK
    rintro ⟨m, H, K, φ, hAppearance, hOvershadowed⟩
    exact hNoOvershadowed hK m H K φ hAppearance hOvershadowed
  let Y : Set V := {y : V | MajorForStripSystem G J S N y}
  have hSaturates : Y.Nonempty → ∀ Y' : Set V,
      IsAnticomponent G Y Y' →
      SaturatesStripSystem J S N ({x : V | VertexComplete G x Y'} ∩ stripSystemVertices J S) := by
    intro hYne Y' hY'
    exact Workspace.ProofLemmas.MajorAnticomponentSaturatesStripSystem.majorAnticomponentSaturatesStripSystem
      G hG J hJ n H₀ K₀ happ S₀ N₀ hS₀ hS₀K₀ R₀ hForms₀ hR₀K₀ S N hS hEnlarges hMaximal
      hOldRungs hnotBalanced hnoenl hdeg hNoOvershadowed' Y rfl hYne Y' hY'
      {x : V | VertexComplete G x Y'} rfl
  have hYempty : Y = ∅ := by
    dsimp [Y]
    exact Workspace.ProofLemmas.NoMajorVerticesOutsideMaximalStripSystem.noMajorVerticesOutsideMaximalStripSystem
      G hG J hJ S N hS hMaximal hnotBalanced (by
        intro F hF
        simpa [Y] using hLocalWithMajor F hF) (by
        intro hYne Y' hY'
        exact hSaturates (by simpa [Y] using hYne) Y' (by simpa [Y] using hY'))
      n H₀ hdeg R₀ hForms
  let Z : Set V := Set.univ \ stripSystemVertices J S
  have hZdisj : Disjoint Z (stripSystemVertices J S) := by
    refine Set.disjoint_left.2 ?_
    intro x hxZ hxS
    exact hxZ.2 hxS
  have hZeq : Z = (stripSystemVertices J S)ᶜ := (Set.compl_eq_univ_diff _).symm
  have hLocal : ∀ F : Set V, IsComponent G Z F →
      LocalForStripSystem J S N (attachments G F (stripSystemVertices J S)) := by
    intro F hF
    apply hLocalWithMajor F
    change IsComponent G (stripSystemVertices J S ∪ Y)ᶜ F
    rw [hYempty, Set.union_empty, Set.compl_eq_univ_diff]
    exact hF
  have hOutside : ∀ F : Set V, IsComponent G Z F →
      ∀ f ∈ F, ∀ x : V, x ∉ F → G.Adj f x → x ∈ stripSystemVertices J S := by
    intro F hF f hf x hxF hfx
    by_contra hxS
    have hxZ : x ∈ Z := by simpa [Z] using hxS
    have hconn : ConnectedSet G (F ∪ {x}) :=
      Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1
        ⟨f, hf, hfx.symm⟩
    have hsub : F ∪ {x} ⊆ Z := Set.union_subset hF.1 (Set.singleton_subset_iff.mpr hxZ)
    have heq : F ∪ {x} = F := hF.2.2 (F ∪ {x}) Set.subset_union_left hsub hconn
    apply hxF
    rw [← heq]
    exact Set.mem_union_right F (Set.mem_singleton x)
  have hLocalUnique : ∀ F : Set V, IsComponent G Z F → F.Nonempty →
      ∃! T : Set V,
        IsStripOfStripSystem J S T ∧
          (attachments G F (stripSystemVertices J S)).Nonempty ∧
          attachments G F (stripSystemVertices J S) ⊆ T ∧
          ∀ v : U, ¬ attachments G F (stripSystemVertices J S) ⊆ N v := by
    intro F hF hFne
    have hnotN : ∀ v : U, ¬ attachments G F (stripSystemVertices J S) ⊆ N v := by
      intro v hattach
      exact hnotBalanced
        (Workspace.ProofLemmas.NoComponentAttachmentInsideStripNeighbourhood.noComponentAttachmentInsideStripNeighbourhood
          G hG J hJ S N hS Z hZdisj hnotBalanced F hF hFne (hOutside F hF) v hattach)
    rcases hLocal F hF with ⟨v, hNv⟩ | ⟨u, v, huv, hstrip⟩
    · exact False.elim (hnotN v hNv)
    · have hattne : (attachments G F (stripSystemVertices J S)).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro heq
        exact hnotN u (by simp [heq])
      refine ⟨S u v, ⟨⟨u, v, huv, rfl⟩, hattne, hstrip, hnotN⟩, ?_⟩
      intro T hT
      rcases hT.1 with ⟨w, x, hwx, rfl⟩
      obtain ⟨a, ha⟩ := hattne
      exact Workspace.ProofLemmas.StripSystemBasics.strip_eq_of_mem_strips hS hwx huv
        (hT.2.2.1 ha) (hstrip ha)
  have hEndgame :=
    Workspace.ProofLemmas.LineGraphOrSelectedEndgameStrip.lineGraphOrSelectedEndgameStrip
      G J H₀ K₀ S₀ S N₀ N R₀ hJ hS₀ hS₀K₀ hForms₀ hCover hS hEnlarges hOldRungs (by
        intro F hF hFne
        rcases hLocal F hF with ⟨v, hNv⟩ | ⟨u, v, huv, hstrip⟩
        · exact False.elim (hnotBalanced
            (Workspace.ProofLemmas.NoComponentAttachmentInsideStripNeighbourhood.noComponentAttachmentInsideStripNeighbourhood
              G hG J hJ S N hS Z hZdisj hnotBalanced F hF hFne (hOutside F hF) v hNv))
        · have hattne : (attachments G F (stripSystemVertices J S)).Nonempty := by
            rw [Set.nonempty_iff_ne_empty]
            intro heq
            exact hnotBalanced
              (Workspace.ProofLemmas.NoComponentAttachmentInsideStripNeighbourhood.noComponentAttachmentInsideStripNeighbourhood
                G hG J hJ S N hS Z hZdisj hnotBalanced F hF hFne (hOutside F hF) u
                (by simp [heq]))
          exact ⟨u, v, huv, hattne, hstrip⟩)
  rcases hEndgame with hline | ⟨⟨b₁, b₂, hb₁b₂, hselected⟩, _⟩
  · exact hnotLine.false hline.some
  · by_cases hEnds : Disjoint (N b₁ ∩ S b₁ b₂) (N b₂ ∩ S b₁ b₂)
    · obtain ⟨hjoin, hnotK33⟩ :=
        Workspace.ProofLemmas.DisjointStripEndsGiveProperTwoJoin.disjointStripEndsGiveProperTwoJoin
          G J hJ S N hS Z hZdisj hZeq hLocalUnique b₁ b₂ hb₁b₂ hselected S₀ N₀ R₀ H₀
          hS₀ hEnlarges hForms₀ (hOldRungs b₁ b₂ hb₁b₂) hEnds
      exact hnotTwoJoin ⟨fun e => hnotK33 ⟨e⟩⟩ ⟨_, _, hjoin⟩
    · have hIntersects : (N b₁ ∩ S b₁ b₂ ∩ (N b₂ ∩ S b₁ b₂)).Nonempty :=
        Set.not_disjoint_iff.mp hEnds
      obtain ⟨hcover, hdisj, hA₁ne, hA₁sub, hA₂ne, hA₂sub,
        hB₁ne, hB₁sub, hB₁card, hB₂ne, hB₂sub, hB₂card,
        hcross, hcompA, hconnB, hmeetB₁, hmeetB₂, hAcard, hBmiddle, hnotpath⟩ :=
        Workspace.ProofLemmas.SelectedStripSeparationData.selectedStripSeparationData
          G J hJ S N hS Z hZdisj hZeq hLocalUnique b₁ b₂ hb₁b₂ hselected
      exact hnotBalanced
        (Workspace.ProofLemmas.IntersectingStripEndsGiveBalancedSkewPartition.intersectingStripEndsGiveBalancedSkewPartition
          G hG _ _ _ _ _ _ ⟨hcover, hdisj⟩ ⟨hA₁ne, hA₁sub⟩ ⟨hA₂ne, hA₂sub⟩
            ⟨hB₁ne, hB₁sub⟩ ⟨hB₂ne, hB₂sub⟩ hcross hAcard hBmiddle (by
            simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hIntersects))

end SPGT

end Workspace.Statements.S08


