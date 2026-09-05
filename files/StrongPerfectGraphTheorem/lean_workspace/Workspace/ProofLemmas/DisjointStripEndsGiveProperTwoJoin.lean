import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.NaturalAppearanceStripSystem
import Workspace.ProofLemmas.StripSystemEnlarge
import Workspace.ProofLemmas.SelectedStripSeparationData
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm86OldRungExcludesK33

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.DisjointStripEndsGiveProperTwoJoin

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.StripSystemMaximal (Enlarges)

/-- **8.6 endgame, B9** (printed p. 46).

When the two end-sets of the selected strip are disjoint, the selected-strip
separation data yields a proper 2-join.  The surviving old rung also excludes
the exceptional `K₃,₃` appearance. -/
theorem disjointStripEndsGiveProperTwoJoin
    {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hS : IsJStripSystem G J S N)
    (Z : Set V) (hZdisj : Disjoint Z (stripSystemVertices J S))
    (hZ : Z = (stripSystemVertices J S)ᶜ)
    (hLocal : ∀ F : Set V, IsComponent G Z F → F.Nonempty →
      ∃! T : Set V,
        IsStripOfStripSystem J S T ∧
          (attachments G F (stripSystemVertices J S)).Nonempty ∧
          attachments G F (stripSystemVertices J S) ⊆ T ∧
          ∀ v : U, ¬ attachments G F (stripSystemVertices J S) ⊆ N v)
    (b₁ b₂ : U) (hb₁b₂ : J.Adj b₁ b₂)
    (hselected :
      (∃ R₁ R₂ : List V,
        IsUVRung G J S N b₁ b₂ R₁ ∧ IsUVRung G J S N b₁ b₂ R₂ ∧
          ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂}) ∨
      ∃ F : Set V, IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty)
    (S₀ : U → U → Set V) (N₀ : U → Set V) (R₀ : U → U → List V)
    (H₀ : SimpleGraph W) (hS₀ : IsJStripSystem G J S₀ N₀)
    (hEnlarges : Enlarges J S₀ N₀ S N)
    (hForms : FormsLineGraph G J S₀ N₀ R₀ H₀)
    (hOldRung : IsUVRung G J S N b₁ b₂ (R₀ b₁ b₂))
    (hEndsDisjoint : Disjoint (N b₁ ∩ S b₁ b₂) (N b₂ ∩ S b₁ b₂)) :
    let A : Set V := S b₁ b₂ ∪
      ⋃ (F : Set V) (_ : IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty), F
    let B : Set V := Set.univ \ A
    let A₁ : Set V := N b₁ ∩ S b₁ b₂
    let A₂ : Set V := N b₂ ∩ S b₁ b₂
    IsProper2Join G A B ∧
      ¬ Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  intro A B A₁ A₂
  -- The separation data of the selected strip (8.6, B8)
  obtain ⟨hunion, hdisj, hA₁ne, hA₁sub, hA₂ne, hA₂sub,
      hB₁ne, hB₁sub, hB₁card, hB₂ne, hB₂sub, hB₂card,
      hcross, hcompA, hBconn, hBB₁, hBB₂, hAcard, hBmid, hpathA⟩ :=
    Workspace.ProofLemmas.SelectedStripSeparationData.selectedStripSeparationData
      G J hJ S N hS Z hZdisj hZ hLocal b₁ b₂ hb₁b₂ hselected
  refine ⟨⟨hunion, hdisj, A₁, A₂, N b₁ \ A₁, N b₂ \ A₂,
    hA₁sub, hA₂sub, hB₁sub, hB₂sub, hA₁ne, hA₂ne, hB₁ne, hB₂ne,
    hEndsDisjoint, ?_, hcross, hcompA, ?_, ?_, ?_⟩, ?_⟩
  · -- `B₁` and `B₂` are disjoint: they live in strips at `b₁`, resp. `b₂`, other than
    -- `S_{b₁b₂}`, and distinct strips are disjoint.
    rw [Set.disjoint_left]
    rintro x ⟨hxN₁, hxA₁⟩ ⟨hxN₂, hxA₂⟩
    have hxS : x ∉ S b₁ b₂ := fun h => hxA₁ ⟨hxN₁, h⟩
    exact hxS
      (Workspace.ProofLemmas.StripSystemBasics.N_inter_N_subset_strip hS hb₁b₂.ne hb₁b₂
        ⟨hxN₁, hxN₂⟩)
  · -- `B` is connected, so it is its own unique component.
    intro C hC
    have hCB : B = C := hC.2.2 B hC.1 (subset_refl B) hBconn
    rw [← hCB]
    exact ⟨hBB₁, hBB₂⟩
  · -- The odd-path bullet on the `A` side is vacuous by `hpathA`.
    intro a b ha hb p hp hpA
    exact absurd ⟨p, hp, hpA⟩ (hpathA a b ha hb)
  · -- The odd-path bullet on the `B` side is vacuous because `|B₁| ≥ 2`.
    intro a b ha hb p hp hpB
    exfalso
    rw [ha, Set.ncard_singleton] at hB₁card
    omega
  · -- `H₀` is not `K₃,₃`: the surviving old rung has two distinct ends.
    exact Workspace.ProofLemmas.Thm86OldRungExcludesK33.thm86OldRungExcludesK33
      G J S N S₀ N₀ R₀ H₀ hS₀ hForms b₁ b₂ hb₁b₂ hOldRung hEndsDisjoint

end Workspace.ProofLemmas.DisjointStripEndsGiveProperTwoJoin
