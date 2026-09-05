import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.HyperprismLocalMinimalBadPath
import Workspace.ProofLemmas.HyperprismLocalEnlargementGaps

set_option autoImplicit false

namespace Workspace.ProofLemmaStatements.HyperprismLocalAttachmentsOrBalancedSkew

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup

theorem hyperprismLocalAttachmentsOrBalancedSkew
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (A B C : Fin 3 → Set V)
    (hH : IsHyperprism G A B C)
    (hmax : ∀ A' B' C' : Fin 3 → Set V, IsHyperprism G A' B' C' →
      ((A' 0 ∪ B' 0 ∪ C' 0) ∪ (A' 1 ∪ B' 1 ∪ C' 1) ∪
        (A' 2 ∪ B' 2 ∪ C' 2)).ncard ≤
      ((A 0 ∪ B 0 ∪ C 0) ∪ (A 1 ∪ B 1 ∪ C 1) ∪
        (A 2 ∪ B 2 ∪ C 2)).ncard) :
    AdmitsBalancedSkewPartition G ∨
      ∀ F : Set V, ConnectedSet G F →
        F ⊆ ((A 0 ∪ B 0 ∪ C 0) ∪ (A 1 ∪ B 1 ∪ C 1) ∪
          (A 2 ∪ B 2 ∪ C 2))ᶜ →
        LocalForHyperprism A B C
          (attachments G F
            ((A 0 ∪ B 0 ∪ C 0) ∪ (A 1 ∪ B 1 ∪ C 1) ∪
              (A 2 ∪ B 2 ∪ C 2))) := by
  have hclaim : Workspace.ProofLemmas.Thm106Assembly.Claim2 G :=
    claim2_of_bigger (G := G) (by
      intro A' B' C' hG' hK4' hNoBalanced hH' F hF
      by_cases hInterior : ∃ (i : Fin 3) (x : V),
          x ∈ attachments G F (hyperVerts A' B' C') ∧ x ∈ C' i
      · exact
          Workspace.ProofLemmas.HyperprismLocalEnlargementGaps.interiorAttachmentYieldsBigger
            G A' B' C' F hG' hK4' hNoBalanced hH' hF hInterior
      have hNoC : ∀ (k : Fin 3) (x : V),
          x ∈ attachments G F (hyperVerts A' B' C') → x ∉ C' k := by
        intro k x hx hxC
        exact hInterior ⟨k, x, hx, hxC⟩
      have hAB : ∀ x ∈ attachments G F (hyperVerts A' B' C'),
          (∃ k : Fin 3, x ∈ A' k) ∨ (∃ k : Fin 3, x ∈ B' k) := by
        intro x hx
        obtain ⟨k, hk⟩ := mem_hyperVerts_iff.mp hx.1
        rcases hk with (hxA | hxB) | hxC
        · exact Or.inl ⟨k, hxA⟩
        · exact Or.inr ⟨k, hxB⟩
        · exact absurd hxC (hNoC k x hx)
      obtain ⟨i, j, xA, xB, hij, hxAatt, hxBatt, hxAA, hxBB⟩ :=
        Workspace.ProofLemmas.HyperprismTwoAttachments.exists_nonlocal_pair hAB hF.1.2.2
      obtain ⟨f, hfne, hfF, hpath, hxAend, hxBend, hFf⟩ :=
        Workspace.ProofLemmas.HyperprismLocalMinimalBadPath.minimalBadAttachmentPath
          G A' B' C' F hH' hF i j hij xA xB hxAatt hxAA hxBatt hxBB
      rcases Nat.even_or_odd f.length with heven | hodd
      · exact
          Workspace.ProofLemmas.HyperprismLocalEnlargementGaps.evenAttachmentPathYieldsBigger
            G A' B' C' F hG' hH' hF (fun x hx k => hNoC k x hx) i j hij xA xB
              hxAatt hxAA hxBatt hxBB
              ⟨f, hfne, hfF, hpath, hxAend, hxBend, hFf, heven⟩
      · exact
          Workspace.ProofLemmas.HyperprismLocalEnlargementGaps.oddAttachmentPathYieldsBigger
            G A' B' C' F hG' hK4' hNoBalanced hH' hF hNoC hij hxAatt hxAA hxBatt hxBB
              ⟨f, hfne, hfF, hpath, hxAend, hxBend, hFf, hodd⟩)
  apply hclaim hG hK4 A B C hH
  intro A' B' C' hH'
  exact hmax A' B' C' hH'

end Workspace.ProofLemmaStatements.HyperprismLocalAttachmentsOrBalancedSkew
