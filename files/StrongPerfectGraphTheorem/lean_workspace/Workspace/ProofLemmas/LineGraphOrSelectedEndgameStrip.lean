import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.NaturalAppearanceStripSystem
import Workspace.ProofLemmas.StripSystemEnlarge
import Workspace.ProofLemmas.ComponentsOfSetBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.LineGraphOrSelectedEndgameStrip

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.StripSystemMaximal (Enlarges)

theorem lineGraphOrSelectedEndgameStrip
    {V U W : Type*} [Fintype V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (H₀ : SimpleGraph W) (K₀ : Set V)
    (S₀ S : U → U → Set V) (N₀ N : U → Set V) (R₀ : U → U → List V)
    (hJ : IsKConnected J 3)
    (hS₀ : IsJStripSystem G J S₀ N₀)
    (hK₀ : stripSystemVertices J S₀ = K₀)
    (hForms : FormsLineGraph G J S₀ N₀ R₀ H₀)
    (hCover : ∀ u v : U, J.Adj u v → ∀ x ∈ S₀ u v, x ∈ R₀ u v)
    (hS : IsJStripSystem G J S N)
    (hEnlarges : Enlarges J S₀ N₀ S N)
    (hOldRungs : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R₀ u v))
    (hLocal : ∀ F : Set V,
      IsComponent G (Set.univ \ stripSystemVertices J S) F → F.Nonempty →
      ∃ u v : U, J.Adj u v ∧
        (attachments G F (stripSystemVertices J S)).Nonempty ∧
        attachments G F (stripSystemVertices J S) ⊆ S u v) :
    ((Nonempty (G ≃g H₀.lineGraph)) ∨
      (∃ b₁ b₂ : U, J.Adj b₁ b₂ ∧
        ((∃ R₁ R₂ : List V,
            IsUVRung G J S N b₁ b₂ R₁ ∧
            IsUVRung G J S N b₁ b₂ R₂ ∧
            ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂}) ∨
          ∃ F : Set V,
            IsComponent G (Set.univ \ stripSystemVertices J S) F ∧
            (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty)) ∧
      ¬ ((Nonempty (G ≃g H₀.lineGraph)) ∧
        ∃ b₁ b₂ : U, J.Adj b₁ b₂ ∧
          ((∃ R₁ R₂ : List V,
              IsUVRung G J S N b₁ b₂ R₁ ∧
              IsUVRung G J S N b₁ b₂ R₂ ∧
              ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂}) ∨
            ∃ F : Set V,
              IsComponent G (Set.univ \ stripSystemVertices J S) F ∧
              (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty))) := by
  classical
  by_cases hline : Nonempty (G ≃g H₀.lineGraph)
  · exact Or.inl hline
  · right
    have hselected : ∃ b₁ b₂ : U, J.Adj b₁ b₂ ∧
        ((∃ R₁ R₂ : List V,
            IsUVRung G J S N b₁ b₂ R₁ ∧
            IsUVRung G J S N b₁ b₂ R₂ ∧
            ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂}) ∨
          ∃ F : Set V,
            IsComponent G (Set.univ \ stripSystemVertices J S) F ∧
            (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty) := by
      by_contra hnone
      have hnoMulti : ∀ u v : U, J.Adj u v →
          ¬ ∃ R₁ R₂ : List V,
            IsUVRung G J S N u v R₁ ∧ IsUVRung G J S N u v R₂ ∧
              ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂} := by
        intro u v huv hm
        exact hnone ⟨u, v, huv, Or.inl hm⟩
      have hnoComponent : ∀ u v : U, J.Adj u v →
          ¬ ∃ F : Set V, IsComponent G (Set.univ \ stripSystemVertices J S) F ∧
            (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty := by
        intro u v huv hm
        exact hnone ⟨u, v, huv, Or.inr hm⟩
      have hSeq : ∀ u v : U, J.Adj u v → S u v = S₀ u v := by
        intro u v huv
        have hR₀ := hForms.1 u v huv
        have hR₀set : S₀ u v = {x : V | x ∈ R₀ u v} := by
          apply Set.Subset.antisymm
          · exact hCover u v huv
          · intro x hx
            obtain ⟨-, -, -, -, hsub, -, -⟩ := hR₀
            exact hsub x hx
        apply StripSystemEnlarge.strip_eq_of_unique_rung hJ hS₀ hS hEnlarges huv hR₀ hR₀set
        intro R' hR'
        by_contra hne
        exact hnoMulti u v huv ⟨R', R₀ u v, hR', hOldRungs u v huv, hne⟩
      have hvertsEq : stripSystemVertices J S = stripSystemVertices J S₀ := by
        ext x
        simp only [stripSystemVertices, Set.mem_iUnion]
        constructor
        · rintro ⟨u, v, huv, hx⟩
          have hx' := hx
          rw [hSeq u v huv] at hx'
          exact ⟨u, v, huv, hx'⟩
        · rintro ⟨u, v, huv, hx⟩
          have hx' := hx
          rw [← hSeq u v huv] at hx'
          exact ⟨u, v, huv, hx'⟩
      have hvertsUniv : stripSystemVertices J S = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        by_contra hx
        have hxout : x ∈ Set.univ \ stripSystemVertices J S := ⟨Set.mem_univ x, hx⟩
        obtain ⟨F, hFcomp, hxF⟩ :=
          ComponentsOfSetBasics.exists_isComponent_mem G
            (Set.univ \ stripSystemVertices J S) hxout
        have hFne : F.Nonempty := ⟨x, hxF⟩
        obtain ⟨u, v, huv, hattne, hattsub⟩ := hLocal F hFcomp hFne
        obtain ⟨z, hzatt⟩ := hattne
        have hinter :
            (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty :=
          ⟨z, hzatt, hattsub hzatt⟩
        exact hnoComponent u v huv ⟨F, hFcomp, hinter⟩
      have hK₀univ : K₀ = Set.univ := by
        rw [← hK₀, ← hvertsEq]
        exact hvertsUniv
      let L : Set V :=
        ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₀ u v}
      have hLK₀ : L = K₀ := by
        rw [← hK₀]
        ext x
        simp only [L, stripSystemVertices, Set.mem_iUnion]
        constructor
        · rintro ⟨u, v, huv, hx⟩
          obtain ⟨-, -, -, -, hsub, -, -⟩ := hForms.1 u v huv
          exact ⟨u, v, huv, hsub x hx⟩
        · rintro ⟨u, v, huv, hx⟩
          exact ⟨u, v, huv, hCover u v huv x hx⟩
      have hLuniv : L = Set.univ := hLK₀.trans hK₀univ
      obtain ⟨φ⟩ := hForms.2.2
      have φ' : H₀.lineGraph ≃g G.induce L := by exact φ
      rw [hLuniv] at φ'
      exact hline ⟨((SimpleGraph.induceUnivIso G).comp φ').symm⟩
    refine ⟨hselected, ?_⟩
    rintro ⟨h, -⟩
    exact hline h

end Workspace.ProofLemmas.LineGraphOrSelectedEndgameStrip
