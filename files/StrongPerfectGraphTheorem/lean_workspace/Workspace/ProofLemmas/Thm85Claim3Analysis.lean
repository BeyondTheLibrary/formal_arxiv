import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

/-!
# 8.5, claim (3): the local line-graph outcome

The rung family used in claim (3) meets the attachment set on every active strip.  If the
corresponding edge set is local in its line graph, the rung dictionaries turn that locality
back into a common end for all active edges of `J`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm85Claim3Analysis

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- If the attachments on a rung family are local in the resulting line graph, all strips
which meet the original attachment set have a common end in `J`. -/
theorem common_end_of_local_choice
    {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (R : U → U → List V)
    (hmeet : ∀ a b : U, J.Adj a b →
      (attachments G F (stripSystemVertices J S) ∩ S a b).Nonempty →
      ∃ z ∈ attachments G F (stripSystemVertices J S), z ∈ R a b)
    (H : SimpleGraph W) (hForms : FormsLineGraph G J S N R H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
    (hlocal : LocalForLineGraph H
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet,
        (↑(phi ⟨e, he⟩) : V) ∈
          attachments G F (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b})}) :
    ∃ d : U, ∀ a b : U, J.Adj a b →
      (attachments G F (stripSystemVertices J S) ∩ S a b).Nonempty →
      d = a ∨ d = b := by
  classical
  let K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}
  rcases hlocal with ⟨c, hcbranch, hsub⟩ | ⟨q, hqbranch, hsub⟩
  · obtain ⟨iota, E, hiota, hrange, hEedge, hincident, hEinj, hEphi⟩ :=
      Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.rungEndDictionaryAt
        G J hJ S N hSN H R hForms phi
    obtain ⟨d, hd⟩ : c ∈ Set.range iota := by rw [hrange]; exact hcbranch
    refine ⟨d, ?_⟩
    intro a b hab hactive
    obtain ⟨z, hzX, hzR⟩ := hmeet a b hab hactive
    have hzK : z ∈ K := by
      simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨a, b, hab, hzR⟩
    let fe : H.edgeSet := phi.symm ⟨z, hzK⟩
    let f : Sym2 W := fe.1
    have hf : f ∈ H.edgeSet := fe.2
    have hphi : (↑(phi ⟨f, hf⟩) : V) = z := by
      have heq : (⟨f, hf⟩ : H.edgeSet) = fe := rfl
      rw [heq]
      exact congrArg (fun y : ↑K => (y : V)) (phi.apply_symm_apply ⟨z, hzK⟩)
    have hfX : f ∈ {e : Sym2 W | ∃ he : e ∈ H.edgeSet,
        (↑(phi ⟨e, he⟩) : V) ∈ attachments G F K} := by
      refine ⟨hf, ?_⟩
      rw [hphi]
      exact ⟨hzK, hzX.2⟩
    have hfc : f ∈ incidentEdges H c := hsub hfX
    rw [← hd, hincident d] at hfc
    obtain ⟨w, hdw, hfw⟩ := hfc
    obtain ⟨-, s, t, hp, hRsub, -, -⟩ := hForms.1 d w hdw
    have hsR : s ∈ R d w := List.mem_of_mem_head? hp.2.1
    have himg := hEphi d w hdw (hEedge d w hdw) s t hp
    have hedge : (⟨f, hf⟩ : H.edgeSet) = ⟨E d w, hEedge d w hdw⟩ :=
      Subtype.ext hfw
    have hzs : z = s := by
      apply hphi.symm.trans
      rw [hedge]
      exact himg
    have hzSdw : z ∈ S d w := by rw [hzs]; exact hRsub s hsR
    obtain ⟨-, -, -, -, hRab, -, -⟩ := hForms.1 a b hab
    have hzSab : z ∈ S a b := hRab z hzR
    have hedges : s(d, w) = s(a, b) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hdw hab hzSdw hzSab
    rcases Sym2.eq_iff.mp hedges with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · obtain ⟨iota, B, hiota, hrange, hB, hBrung, hsurj⟩ :=
      Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.branchRungDictionaryAt
        G J hJ S N hSN H R hForms phi
    obtain ⟨d, w, hdw, hqB⟩ := hsurj q hqbranch
    refine ⟨d, ?_⟩
    intro a b hab hactive
    obtain ⟨z, hzX, hzR⟩ := hmeet a b hab hactive
    have hzK : z ∈ K := by
      simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨a, b, hab, hzR⟩
    let fe : H.edgeSet := phi.symm ⟨z, hzK⟩
    let f : Sym2 W := fe.1
    have hf : f ∈ H.edgeSet := fe.2
    have hphi : (↑(phi ⟨f, hf⟩) : V) = z := by
      have heq : (⟨f, hf⟩ : H.edgeSet) = fe := rfl
      rw [heq]
      exact congrArg (fun y : ↑K => (y : V)) (phi.apply_symm_apply ⟨z, hzK⟩)
    have hfX : f ∈ {e : Sym2 W | ∃ he : e ∈ H.edgeSet,
        (↑(phi ⟨e, he⟩) : V) ∈ attachments G F K} := by
      refine ⟨hf, ?_⟩
      rw [hphi]
      exact ⟨hzK, hzX.2⟩
    have hfB : f ∈ trackEdges (B d w) := by
      rw [← hqB]
      exact hsub hfX
    have hzRdw : z ∈ R d w := by
      have hzimg : z ∈ {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
          e ∈ trackEdges (B d w) ∧ x = (↑(phi ⟨e, he⟩) : V)} :=
        ⟨f, hf, hfB, hphi.symm⟩
      rw [hBrung d w hdw] at hzimg
      exact hzimg
    obtain ⟨-, -, -, -, hRsub, -, -⟩ := hForms.1 d w hdw
    have hzSdw : z ∈ S d w := hRsub z hzRdw
    obtain ⟨-, -, -, -, hRab, -, -⟩ := hForms.1 a b hab
    have hzSab : z ∈ S a b := hRab z hzR
    have hedges : s(d, w) = s(a, b) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hdw hab hzSdw hzSab
    rcases Sym2.eq_iff.mp hedges with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1

end Workspace.ProofLemmas.Thm85Claim3Analysis
