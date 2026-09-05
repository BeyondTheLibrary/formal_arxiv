import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# 7.5 claim (2): the attachments of `F` in `L(H)` are not local

PAPER (proof of 7.5, claim (2), printed p. 36):

*"On the other hand, the set of attachments of `F` in `L(H)` is not local, because it has an
attachment in `Rc₁c₂`, and its attachments are not all contained in any of `V(Rc₁c₂)`, `Nc₁`,
`Nc₂`.  Let us apply 5.8."*

`LocalForLineGraph` (printed p. 25) is *"`X ⊆ δ_H(v)` for some `v ∈ V(J)`, or `X` is a subset of
the edge-set of some branch of `H`"*.  The attachment set has a member in `S ⊆ V(Rc₁c₂)` and a
member in `T ⊆ V(L(H)) \ V(Rc₁c₂)`, which is what rules out both alternatives.

The conclusion is verbatim the hypothesis `hnotlocal` of
`Thm75Claim2Transport.five8W`, so the caller can feed it straight in.

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2AttachmentsNotLocal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- An edge of a branch can contain a branch-vertex only at one of the named ends. -/
private theorem branchVertex_on_branch_edge_is_end {W : Type*} {H : SimpleGraph W}
    {B : List W} {c₁ c₂ v : W} {e : Sym2 W}
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (heB : e ∈ trackEdges B) (hve : v ∈ e) (hv : v ∈ branchVertices H) :
    v = c₁ ∨ v = c₂ := by
  have hvB : v ∈ B := by
    obtain ⟨i, hi, hie⟩ := heB
    rw [hie] at hve
    rcases Sym2.mem_iff.mp hve with h₁ | h₁
    · rw [h₁]
      exact List.getElem_mem _
    · rw [h₁]
      exact List.getElem_mem _
  have hvint : v ∉ trackInterior B := fun hint => hbranch.2.1 v hint hv
  exact Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
    hfrom.2.1 hfrom.2.2 hvB hvint

/-- **The attachments of `F` in `L(H)` are not local** (printed p. 36). -/
theorem thm75Claim2AttachmentsNotLocal {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y X X₀ X₁ Rset S T : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₀ : X₀ = X \ K)
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (hsmall : (NSet G H K φ c₁ \ X).Subsingleton ∧
      (NSet G H K φ c₂ \ X).Subsingleton)
    (F : Set V) (hFconn : ConnectedSet G F) (hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y)
    (hFK : ∀ x ∈ F, x ∉ K)
    (hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f) (hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f) :
    ¬ LocalForLineGraph H
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K} := by
  classical
  let A : Set (Sym2 W) :=
    {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K}
  obtain ⟨s, hsS, fₛ, hfₛF, hsfₛ⟩ := hSF
  have hsS' : s ∈ Rset \ X₁ := by rwa [← hS]
  obtain ⟨eₛ, heₛE, heₛB, hsφ⟩ := by
    rw [hRset] at hsS'
    exact hsS'.1
  have hsK : s ∈ K := by rw [hsφ]; exact Subtype.coe_prop _
  have heₛA : eₛ ∈ A := by
    refine ⟨heₛE, ?_⟩
    rw [← hsφ]
    exact ⟨hsK, fₛ, hfₛF, hsfₛ⟩
  obtain ⟨t, htT, fₜ, hfₜF, htfₜ⟩ := hTF
  have htT' : t ∈ (K \ Rset) \ X₁ := by rwa [← hT]
  let eₜ : H.edgeSet := φ.symm ⟨t, htT'.1.1⟩
  have heₜφ : (↑(φ eₜ) : V) = t := by
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨t, htT'.1.1⟩)
  have heₜB : (eₜ : Sym2 W) ∉ trackEdges B := by
    intro heB
    apply htT'.1.2
    rw [hRset]
    exact ⟨eₜ, eₜ.2, heB, heₜφ.symm⟩
  have heₜA : (eₜ : Sym2 W) ∈ A := by
    refine ⟨eₜ.2, ?_⟩
    change (↑(φ eₜ) : V) ∈ attachments G F K
    rw [heₜφ]
    exact ⟨htT'.1.1, fₜ, hfₜF, htfₜ⟩
  have hst : s ≠ t := by
    intro hst
    apply htT'.1.2
    rw [← hst]
    exact hsS'.1
  intro hlocal
  change LocalForLineGraph H A at hlocal
  rcases hlocal with ⟨v, hv, hAv⟩ | ⟨q, hq, hAq⟩
  · have heₛv := hAv heₛA
    have heₜv := hAv heₜA
    rcases branchVertex_on_branch_edge_is_end hbranch hfrom heₛB heₛv.2 hv with hv₁ | hv₂
    · subst v
      have hsN : s ∈ NSet G H K φ c₁ := ⟨eₛ, heₛE, heₛv, hsφ⟩
      have htN : t ∈ NSet G H K φ c₁ := ⟨eₜ, eₜ.2, heₜv, heₜφ.symm⟩
      have hsX : s ∉ X := fun hsx => hsS'.2 (by rw [hX₁]; exact ⟨hsx, Or.inl hsN⟩)
      have htX : t ∉ X := fun htx => htT'.2 (by rw [hX₁]; exact ⟨htx, Or.inl htN⟩)
      exact hst (hsmall.1 ⟨hsN, hsX⟩ ⟨htN, htX⟩)
    · subst v
      have hsN : s ∈ NSet G H K φ c₂ := ⟨eₛ, heₛE, heₛv, hsφ⟩
      have htN : t ∈ NSet G H K φ c₂ := ⟨eₜ, eₜ.2, heₜv, heₜφ.symm⟩
      have hsX : s ∉ X := fun hsx => hsS'.2 (by rw [hX₁]; exact ⟨hsx, Or.inr hsN⟩)
      have htX : t ∉ X := fun htx => htT'.2 (by rw [hX₁]; exact ⟨htx, Or.inr htN⟩)
      exact hst (hsmall.2 ⟨hsN, hsX⟩ ⟨htN, htX⟩)
  · have hsub := happ.1.1
    obtain ⟨ι, R, hι, htrack, hlenR, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
    have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
    have hBlen : 2 ≤ B.length := by simp only [trackLength] at hlen; omega
    have hqlen : 2 ≤ q.length := by
      obtain ⟨i, hi, -⟩ := hAq heₛA
      omega
    obtain ⟨u, v, huv, hBR⟩ :=
      Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_of_isBranch
        hι htrack hlenR hrev hdisj hnew hcover hedges hdeg hbranch hBlen
    obtain ⟨u', v', hu'v', hqR⟩ :=
      Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_of_isBranch
        hι htrack hlenR hrev hdisj hnew hcover hedges hdeg hq hqlen
    have hpairs : s(u, v) = s(u', v') :=
      Workspace.ProofLemmas.SubdivisionCounting.trackEdges_disjoint hι htrack hlenR hdisj
        u v u' v' huv hu'v' eₛ (hBR ▸ heₛB) (hqR ▸ hAq heₛA)
    have htracks : trackEdges (R u v) = trackEdges (R u' v') := by
      rcases Sym2.eq_iff.mp hpairs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · subst u'
        subst v'
        rfl
      · subst u'
        subst v'
        rw [hrev u v huv, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    have hqB : trackEdges q = trackEdges B :=
      hqR.trans (htracks.symm.trans hBR.symm)
    exact heₜB (hqB ▸ hAq heₜA)

end Workspace.ProofLemmas.Thm75Claim2AttachmentsNotLocal
