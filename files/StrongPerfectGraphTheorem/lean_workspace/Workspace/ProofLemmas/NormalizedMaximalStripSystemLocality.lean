import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.NaturalAppearanceStripSystem
import Workspace.ProofLemmas.StripSystemMaximal
import Workspace.ProofLemmas.StripSystemEnlarge
import Workspace.Statements.S07.Thm_7_5
import Workspace.Statements.S08.Thm_8_5

/-!
# Normalization and locality for the maximal strip system in 8.6

This is the setup consequence used in the proof of 8.6.  The hypotheses retain
the natural strip system of the given appearance, its enlargement to the maximal
system, and the exceptional-degeneracy condition from the frozen theorem.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NormalizedMaximalStripSystemLocality

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.StripSystemMaximal (Enlarges)

/-- **8.6 setup, B4** (printed pp. 45--46).

For a maximal strip system enlarging the natural system of the displayed
appearance, the non-overshadowing normalization and the locality conclusion of
7.5 and 8.5 hold simultaneously. -/
theorem normalizedMaximalStripSystemLocality
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (H₀ : SimpleGraph (Fin n)) (K₀ : Set V)
    (hAppearance : IsAppearance G J H₀ K₀)
    (S₀ : U → U → Set V) (N₀ : U → Set V) (R₀ : U → U → List V)
    (hS₀ : IsJStripSystem G J S₀ N₀)
    (hS₀vertices : stripSystemVertices J S₀ = K₀)
    (hS₀forms : FormsLineGraph G J S₀ N₀ R₀ H₀)
    (hS₀points : ∀ u v : U, J.Adj u v → ∀ x ∈ S₀ u v, x ∈ R₀ u v)
    (hS₀nondeg : NondegenerateAppearance J H₀ → NondegenerateStripSystem G J S₀ N₀)
    (S : U → U → Set V) (N : U → Set V)
    (hSN : IsJStripSystem G J S N) (hmax : MaximalStripSystem G J S N)
    (henlarges : Enlarges J S₀ N₀ S N)
    (hnoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hnoEnlargement : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (hdegenerate : DegenerateAppearance J H₀ →
      Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧ Appears Gᶜ J') :
    let Y : Set V := {y : V | MajorForStripSystem G J S N y}
    let Z : Set V := (stripSystemVertices J S ∪ Y)ᶜ
    ((Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∨
        Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))) →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
        IsAppearance G J H K → ¬ IsOvershadowedAppearance G H K φ) ∧
    ∀ F : Set V, IsComponent G Z F →
      LocalForStripSystem J S N (attachments G F (stripSystemVertices J S)) := by
  classical
  -- **"By 7.5, we may assume that if `J = K₄` or `K₃,₃` then no appearance of `J` in `G` is
  -- overshadowed."**  Indeed 7.5 offers a `J`-enlargement with a nondegenerate appearance or a
  -- balanced skew partition, and both are excluded by hypothesis.
  have hnoOver : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V)
      (φ : H.lineGraph ≃g G.induce K), IsAppearance G J H K →
      ¬ IsOvershadowedAppearance G H K φ := by
    intro m H K φ happ hover
    rcases Workspace.Statements.S07.SPGT.thm_7_5 G hG J hJ H K φ happ hover with h | h
    · exact hnoEnlargement h
    · exact hnoBalanced h
  -- **"If `L(H₀)` is nondegenerate then so is the strip system."**  When `J = K₄` the appearance
  -- `L(H₀)` *is* nondegenerate, because a degenerate one would force `J = K₃,₃`.
  have hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N := by
    intro hK4
    have hND₀ : NondegenerateAppearance J H₀ := by
      intro hdeg
      obtain ⟨-, hJ33, -⟩ := hdegenerate hdeg
      obtain ⟨e4⟩ := hK4
      obtain ⟨e33⟩ := hJ33
      have hcard : Fintype.card (Fin 4) = Fintype.card (Fin 3 ⊕ Fin 3) :=
        Fintype.card_congr (e4.symm.trans e33).toEquiv
      simp at hcard
    exact StripSystemEnlarge.nondegenerateStripSystem_of_enlarges hJ hS₀ hSN henlarges
      (hS₀nondeg hND₀)
  intro Y Z
  refine ⟨fun _ m H K φ happ => hnoOver m H K φ happ, ?_⟩
  intro F hFcomp
  have hFZ : F ⊆ (stripSystemVertices J S ∪ Y)ᶜ := hFcomp.1
  refine Workspace.Statements.S08.SPGT.thm_8_5 G hG J hJ S N hSN hmax hnoEnlargement ?_ F ?_
    hFcomp.2.1 ?_
  · intro hK4
    refine ⟨hnd hK4, ?_⟩
    rintro ⟨m, H, K', φ, happ, hover⟩
    exact hnoOver m H K' φ happ hover
  · intro f hf
    exact fun hfV => hFZ hf (Or.inl hfV)
  · intro f hf hmaj
    exact hFZ hf (Or.inr hmaj)

end Workspace.ProofLemmas.NormalizedMaximalStripSystemLocality
