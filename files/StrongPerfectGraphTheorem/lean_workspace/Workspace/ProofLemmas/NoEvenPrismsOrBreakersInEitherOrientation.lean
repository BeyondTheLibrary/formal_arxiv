import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.NineVertexEvenPrismOrientationsExcluded
import Workspace.ProofLemmas.ClassLemmas
import Workspace.Statements.S10.Thm_10_6
import Workspace.Statements.S11.Thm_11_5
import Workspace.Statements.S12.Thm_12_4
import Workspace.Statements.S13.Thm_13_3

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoEvenPrismsOrBreakersInEitherOrientation

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions.SPGT

theorem noEvenPrismsOrBreakersInEitherOrientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4G : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hK4Gc : ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4)))
    (hprism : ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsLongPrism G s t R₁ R₂ R₃ ∧ IsOddPrism G s t R₁ R₂ R₃)
    (h2join : ¬ AdmitsProper2Join G ∧ ¬ AdmitsProper2Join Gᶜ)
    (hskew : ¬ AdmitsBalancedSkewPartition G) :
    (¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G a b P₁ P₂ P₃) ∧
    (¬ ∃ A C B F Q : Set V, IsOneBreaker G A C B F Q) ∧
    (¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
        IsTwoBreaker G A C B a₀ R₀ b₀ Q) ∧
    (¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ x : V),
        IsThreeBreaker G A C B a₀ R₀ b₀ x) ∧
    (¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism Gᶜ a b P₁ P₂ P₃) ∧
    (¬ ∃ A C B F Q : Set V, IsOneBreaker Gᶜ A C B F Q) ∧
    (¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
        IsTwoBreaker Gᶜ A C B a₀ R₀ b₀ Q) ∧
    (¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ x : V),
        IsThreeBreaker Gᶜ A C B a₀ R₀ b₀ x) := by
  have hGc : Berge Gᶜ :=
    Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  have hskewc : ¬ AdmitsBalancedSkewPartition Gᶜ := by
    intro hs
    exact hskew
      (Workspace.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp hs)
  have hnoNondegG :
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
        IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
          NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K, happ, -⟩
    exact hK4G ⟨n, H, K, happ⟩
  have hnoNondegGc :
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
        IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K ∧
          NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K, happ, -⟩
    exact hK4Gc ⟨n, H, K, happ⟩
  obtain ⟨hnoExceptionalG, hnoExceptionalGc⟩ :=
    Workspace.ProofLemmas.NineVertexEvenPrismOrientationsExcluded.nineVertexEvenPrismOrientationsExcluded
      G hG hprism
  have hevenG :
      ¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G a b P₁ P₂ P₃ := by
    intro heven
    rcases Workspace.Statements.S10.SPGT.thm_10_6 G hG hnoNondegG heven with
      hexception | hjoin | hbalanced
    · exact hnoExceptionalG hexception
    · exact h2join.1 hjoin
    · exact hskew hbalanced
  have hevenGc :
      ¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism Gᶜ a b P₁ P₂ P₃ := by
    intro heven
    rcases Workspace.Statements.S10.SPGT.thm_10_6 Gᶜ hGc hnoNondegGc heven with
      hexception | hjoin | hbalanced
    · exact hnoExceptionalGc hexception
    · exact h2join.2 hjoin
    · exact hskewc hbalanced
  have honeG : ¬ ∃ A C B F Q : Set V, IsOneBreaker G A C B F Q := by
    intro hbreaker
    exact hskew (Workspace.Statements.S11.SPGT.thm_11_5 G hG hK4G hevenG hbreaker)
  have honeGc : ¬ ∃ A C B F Q : Set V, IsOneBreaker Gᶜ A C B F Q := by
    intro hbreaker
    exact hskewc (Workspace.Statements.S11.SPGT.thm_11_5 Gᶜ hGc hK4Gc hevenGc hbreaker)
  have htwoG :
      ¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
        IsTwoBreaker G A C B a₀ R₀ b₀ Q := by
    intro hbreaker
    exact hskew
      (Workspace.Statements.S12.SPGT.thm_12_4 G hG hK4G hevenG honeG hbreaker)
  have htwoGc :
      ¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
        IsTwoBreaker Gᶜ A C B a₀ R₀ b₀ Q := by
    intro hbreaker
    exact hskewc
      (Workspace.Statements.S12.SPGT.thm_12_4 Gᶜ hGc hK4Gc hevenGc honeGc hbreaker)
  have hthreeG :
      ¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ x : V),
        IsThreeBreaker G A C B a₀ R₀ b₀ x := by
    intro hbreaker
    exact hskew
      (Workspace.Statements.S13.SPGT.thm_13_3 G hG hK4G hevenG honeG htwoG hbreaker)
  have hthreeGc :
      ¬ ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ x : V),
        IsThreeBreaker Gᶜ A C B a₀ R₀ b₀ x := by
    intro hbreaker
    exact hskewc
      (Workspace.Statements.S13.SPGT.thm_13_3 Gᶜ hGc hK4Gc hevenGc honeGc htwoGc hbreaker)
  exact ⟨hevenG, honeG, htwoG, hthreeG, hevenGc, honeGc, htwoGc, hthreeGc⟩

end Workspace.ProofLemmas.NoEvenPrismsOrBreakersInEitherOrientation
