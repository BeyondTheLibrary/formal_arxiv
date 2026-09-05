import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.BranchExternalEdge

/-!
# 7.5 claim (2): `S` is anticomplete to `T`

PAPER (proof of 7.5, printed p. 36):

*"We observe first that no vertex of `S` is adjacent to any vertex in `T`; for such an edge
would join two vertices both in `N_{c_i}` for some `i`, and therefore both not in `X`,
contradicting (1)."*
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2STAnticomplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- The two sides `S` and `T` of the prospective separation are anticomplete. -/
theorem thm75Claim2STAnticomplete {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (X X₁ Rset S T : Set V)
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (hsmall : (NSet G H K φ c₁ \ X).Subsingleton ∧
      (NSet G H K φ c₂ \ X).Subsingleton) :
    Anticomplete G S T := by
  classical
  intro s hsS t htT hst
  have hsS' : s ∈ Rset \ X₁ := by rwa [← hS]
  have htT' : t ∈ (K \ Rset) \ X₁ := by rwa [← hT]
  obtain ⟨eₛ, heₛE, heₛB, hsφ⟩ := by
    rw [hRset] at hsS'
    exact hsS'.1
  have hsK : s ∈ K := by rw [hsφ]; exact Subtype.coe_prop _
  let eₜ : H.edgeSet := φ.symm ⟨t, htT'.1.1⟩
  have heₜφ : (↑(φ eₜ) : V) = t := by
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨t, htT'.1.1⟩)
  have heₜB : (eₜ : Sym2 W) ∉ trackEdges B := by
    intro heB
    apply htT'.1.2
    rw [hRset]
    exact ⟨eₜ, eₜ.2, heB, heₜφ.symm⟩
  have hline : H.lineGraph.Adj ⟨eₛ, heₛE⟩ eₜ := by
    apply φ.map_adj_iff.mp
    change G.Adj (↑(φ ⟨eₛ, heₛE⟩) : V) (↑(φ eₜ) : V)
    rw [← hsφ, heₜφ]
    exact hst
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hline
  obtain ⟨-, w, hweₛ, hweₜ⟩ := hline
  have hwends :=
    Workspace.ProofLemmas.BranchExternalEdge.external_edge_meets_branch_only_at_ends
      hbranch hfrom heₛB eₜ.2 heₜB hweₜ hweₛ
  have hne : s ≠ t := fun h => htT'.1.2 (h ▸ hsS'.1)
  rcases hwends with hw₁ | hw₂
  · subst w
    have hsN : s ∈ NSet G H K φ c₁ := ⟨eₛ, heₛE, ⟨heₛE, hweₛ⟩, hsφ⟩
    have htN : t ∈ NSet G H K φ c₁ := ⟨eₜ, eₜ.2, ⟨eₜ.2, hweₜ⟩, heₜφ.symm⟩
    have hsX : s ∉ X := fun hsx => hsS'.2 (by rw [hX₁]; exact ⟨hsx, Or.inl hsN⟩)
    have htX : t ∉ X := fun htx => htT'.2 (by rw [hX₁]; exact ⟨htx, Or.inl htN⟩)
    exact hne (hsmall.1 ⟨hsN, hsX⟩ ⟨htN, htX⟩)
  · subst w
    have hsN : s ∈ NSet G H K φ c₂ := ⟨eₛ, heₛE, ⟨heₛE, hweₛ⟩, hsφ⟩
    have htN : t ∈ NSet G H K φ c₂ := ⟨eₜ, eₜ.2, ⟨eₜ.2, hweₜ⟩, heₜφ.symm⟩
    have hsX : s ∉ X := fun hsx => hsS'.2 (by rw [hX₁]; exact ⟨hsx, Or.inr hsN⟩)
    have htX : t ∉ X := fun htx => htT'.2 (by rw [hX₁]; exact ⟨htx, Or.inr htN⟩)
    exact hne (hsmall.2 ⟨hsN, hsX⟩ ⟨htN, htX⟩)

end Workspace.ProofLemmas.Thm75Claim2STAnticomplete
