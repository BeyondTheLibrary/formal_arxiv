import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmaStatements.HyperprismLocalAttachmentsOrBalancedSkew
import Workspace.ProofLemmas.Thm106Steps

set_option autoImplicit false

namespace Workspace.Statements.S10

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_10_6 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (heven : ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃) :
    ((∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃ ∧
        {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} = Set.univ) ∧
      Fintype.card V = 9) ∨
    AdmitsProper2Join G ∨ AdmitsBalancedSkewPartition G := by
  apply Workspace.ProofLemmas.Thm106Steps.thm_10_6_of_claim2 G hG hK4
  · intro hG' hK4' A B C hH hmax
    exact
      Workspace.ProofLemmaStatements.HyperprismLocalAttachmentsOrBalancedSkew.hyperprismLocalAttachmentsOrBalancedSkew
        G hG' hK4' A B C hH hmax
  · exact heven

end SPGT

end Workspace.Statements.S10
