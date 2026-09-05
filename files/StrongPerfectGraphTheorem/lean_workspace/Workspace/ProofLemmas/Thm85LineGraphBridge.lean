import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

/-!
# 8.5: passing a non-local pair from a strip system to a chosen line graph

The proof of 8.5 repeatedly chooses rungs through prescribed attachments and then applies 5.8
to the line graph formed by those rungs.  `FormsLineGraph` does not state that its isomorphism
matches a rung with a particular branch.  The rung and branch dictionaries recover that fact
for any isomorphism.  This file records the one consequence needed below: two chosen vertices
which are not local in the strip system pull back to two edges which are not local in the line
graph.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm85LineGraphBridge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]

/-- The union of a chosen family of rungs is contained in the strip-system vertex set. -/
theorem rungUnion_subset_stripSystemVertices
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (R : U → U → List V)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v)) :
    (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) ⊆
      stripSystemVertices J S := by
  intro x hx
  simp only [stripSystemVertices, Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨u, v, huv, hxR⟩ := hx
  obtain ⟨-, -, -, -, hsub, -, -⟩ := hR u v huv
  exact ⟨u, v, huv, hsub x hxR⟩

/-- Pulling two prescribed rung vertices back through the appearance isomorphism preserves
non-locality.

This is the formal version of the sentence in claim (2), *"Then `{x,x'}` is not local with
respect to `L(H)`"*.  The branch dictionary handles the branch alternative in
`LocalForLineGraph`; the rung-end dictionary handles the incident-edge alternative. -/
theorem exists_nonlocal_preimage_pair
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
    (u v u' v' : U) (huv : J.Adj u v) (hu'v' : J.Adj u' v')
    (x x' : V) (hxR : x ∈ R u v) (hx'R : x' ∈ R u' v')
    (hpair : ¬ LocalForStripSystem J S N ({x, x'} : Set V)) :
    ∃ (e e' : Sym2 W) (he : e ∈ H.edgeSet) (he' : e' ∈ H.edgeSet),
      (↑(phi ⟨e, he⟩) : V) = x ∧ (↑(phi ⟨e', he'⟩) : V) = x' ∧
      ¬ LocalForLineGraph H ({e, e'} : Set (Sym2 W)) := by
  classical
  let K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}
  have hxK : x ∈ K := by
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, hxR⟩
  have hx'K : x' ∈ K := by
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u', v', hu'v', hx'R⟩
  let ee : H.edgeSet := phi.symm ⟨x, hxK⟩
  let ee' : H.edgeSet := phi.symm ⟨x', hx'K⟩
  let e : Sym2 W := ee.1
  let e' : Sym2 W := ee'.1
  have he : e ∈ H.edgeSet := ee.2
  have he' : e' ∈ H.edgeSet := ee'.2
  have hphi : (↑(phi ⟨e, he⟩) : V) = x := by
    have hsub : (⟨e, he⟩ : H.edgeSet) = ee := rfl
    rw [hsub]
    exact congrArg (fun z : ↑K => (z : V)) (phi.apply_symm_apply ⟨x, hxK⟩)
  have hphi' : (↑(phi ⟨e', he'⟩) : V) = x' := by
    have hsub : (⟨e', he'⟩ : H.edgeSet) = ee' := rfl
    rw [hsub]
    exact congrArg (fun z : ↑K => (z : V)) (phi.apply_symm_apply ⟨x', hx'K⟩)
  refine ⟨e, e', he, he', hphi, hphi', ?_⟩
  intro hlocal
  rcases hlocal with ⟨w, hwbranch, hsub⟩ | ⟨q, hqbranch, hsub⟩
  · obtain ⟨iota, E, hiota, hrange, hEedge, hincident, hEinj, hEphi⟩ :=
      Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.rungEndDictionaryAt
        G J hJ S N hSN H R hForms phi
    obtain ⟨a, ha⟩ : w ∈ Set.range iota := by
      rw [hrange]
      exact hwbranch
    have hew : e ∈ incidentEdges H w := hsub (by simp)
    have he'w : e' ∈ incidentEdges H w := hsub (by simp)
    rw [← ha, hincident a] at hew he'w
    obtain ⟨b, hab, heb⟩ := hew
    obtain ⟨b', hab', heb'⟩ := he'w
    have hxN : x ∈ N a := by
      obtain ⟨-, s, t, hp, -, hs, -⟩ := hForms.1 a b hab
      have hsR : s ∈ R a b := List.mem_of_mem_head? hp.2.1
      have hsN : s ∈ N a := (hs s hsR).mpr rfl
      have himg := hEphi a b hab (hEedge a b hab) s t hp
      have hedge : (⟨e, he⟩ : H.edgeSet) = ⟨E a b, hEedge a b hab⟩ :=
        Subtype.ext heb
      have himg' : (↑(phi ⟨e, he⟩) : V) = s := by
        rw [hedge]
        exact himg
      have hxs : x = s := hphi.symm.trans himg'
      rwa [hxs]
    have hx'N : x' ∈ N a := by
      obtain ⟨-, s, t, hp, -, hs, -⟩ := hForms.1 a b' hab'
      have hsR : s ∈ R a b' := List.mem_of_mem_head? hp.2.1
      have hsN : s ∈ N a := (hs s hsR).mpr rfl
      have himg := hEphi a b' hab' (hEedge a b' hab') s t hp
      have hedge : (⟨e', he'⟩ : H.edgeSet) = ⟨E a b', hEedge a b' hab'⟩ :=
        Subtype.ext heb'
      have himg' : (↑(phi ⟨e', he'⟩) : V) = s := by
        rw [hedge]
        exact himg
      have hxs : x' = s := hphi'.symm.trans himg'
      rwa [hxs]
    apply hpair
    refine Or.inl ⟨a, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · rwa [hz]
    · have hzx' : z = x' := hz
      rwa [hzx']
  · obtain ⟨iota, B, hiota, hrange, hB, hBrung, hsurj⟩ :=
      Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.branchRungDictionaryAt
        G J hJ S N hSN H R hForms phi
    obtain ⟨a, b, hab, hqB⟩ := hsurj q hqbranch
    have heB : e ∈ trackEdges (B a b) := by
      rw [← hqB]
      exact hsub (by simp)
    have he'B : e' ∈ trackEdges (B a b) := by
      rw [← hqB]
      exact hsub (by simp)
    have hxRab : x ∈ R a b := by
      have hximg : x ∈ {z : V | ∃ (f : Sym2 W) (hf : f ∈ H.edgeSet),
          f ∈ trackEdges (B a b) ∧ z = (↑(phi ⟨f, hf⟩) : V)} :=
        ⟨e, he, heB, hphi.symm⟩
      rw [hBrung a b hab] at hximg
      exact hximg
    have hx'Rab : x' ∈ R a b := by
      have hximg : x' ∈ {z : V | ∃ (f : Sym2 W) (hf : f ∈ H.edgeSet),
          f ∈ trackEdges (B a b) ∧ z = (↑(phi ⟨f, hf⟩) : V)} :=
        ⟨e', he', he'B, hphi'.symm⟩
      rw [hBrung a b hab] at hximg
      exact hximg
    obtain ⟨-, -, -, -, hRS, -, -⟩ := hForms.1 a b hab
    apply hpair
    refine Or.inr ⟨a, b, hab, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      exact hRS x hxRab
    · have hzx' : z = x' := hz
      rw [hzx']
      exact hRS x' hx'Rab

/-- A non-local pair contained in the attachment-edge set makes that whole set non-local. -/
theorem attachmentEdges_not_local_of_pair
    (G : SimpleGraph V) (H : SimpleGraph W) (K F : Set V)
    (phi : H.lineGraph ≃g G.induce K)
    (e e' : Sym2 W) (he : e ∈ H.edgeSet) (he' : e' ∈ H.edgeSet)
    (heF : (↑(phi ⟨e, he⟩) : V) ∈ attachments G F K)
    (he'F : (↑(phi ⟨e', he'⟩) : V) ∈ attachments G F K)
    (hpair : ¬ LocalForLineGraph H ({e, e'} : Set (Sym2 W))) :
    ¬ LocalForLineGraph H
      {f : Sym2 W | ∃ hf : f ∈ H.edgeSet,
        (↑(phi ⟨f, hf⟩) : V) ∈ attachments G F K} := by
  intro hlocal
  apply hpair
  rcases hlocal with ⟨w, hw, hsub⟩ | ⟨q, hq, hsub⟩
  · exact Or.inl ⟨w, hw, fun f hf => hsub (by
      rcases hf with rfl | rfl
      · exact ⟨he, heF⟩
      · exact ⟨he', he'F⟩)⟩
  · exact Or.inr ⟨q, hq, fun f hf => hsub (by
      rcases hf with rfl | rfl
      · exact ⟨he, heF⟩
      · exact ⟨he', he'F⟩)⟩

end Workspace.ProofLemmas.Thm85LineGraphBridge
