import Workspace.Types.Tracks
import Workspace.ProofLemmas.TwoVertexMengerForNonadjacentVertices

/-!
# Two internally vertex-disjoint tracks in a 2-connected graph

This is the common-cycle consequence of finite 2-connectivity used in the proof of
result 7.1.  The conclusion is phrased directly with the project's track lists:
the two lists have the prescribed distinct endpoints, are themselves distinct, and
share no vertex other than those endpoints.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.TwoInternallyDisjointTracksInTwoConnectedGraph

open Workspace.Types.Tracks.SPGT

private theorem isTrackFrom_support_of_isPath
    {U : Type*} {G : SimpleGraph U} {u v : U} (p : G.Walk u v) (hp : p.IsPath) :
    IsTrackFrom G p.support u v := by
  refine ⟨⟨p.support_ne_nil, hp.support_nodup, ?_⟩, ?_, ?_⟩
  · intro i hi
    rw [p.support_getElem_eq_getVert, p.support_getElem_eq_getVert]
    exact p.adj_getVert_succ (by simpa [p.length_support] using hi)
  · simp [List.head?_eq_some_head, p.head_support]
  · simp [List.getLast?_eq_some_getLast, p.getLast_support]

/-- Distinct vertices in a finite 2-connected graph are joined by two distinct
internally vertex-disjoint tracks. -/
theorem twoInternallyDisjointTracksInTwoConnectedGraph
    {U : Type*} [Fintype U] (G : SimpleGraph U) (u v : U)
    (huv : u ≠ v) (hG : IsKConnected G 2) :
    ∃ P Q : List U,
      P ≠ Q ∧
      IsTrackFrom G P u v ∧
      IsTrackFrom G Q u v ∧
      ∀ w ∈ P, w ∈ Q → w = u ∨ w = v := by
  classical
  by_cases hadj : G.Adj u v
  · have hpair : ({u, v} : Finset U).card = 2 := Finset.card_pair huv
    have hlt : ({u, v} : Finset U).card < (Finset.univ : Finset U).card := by
      simpa [hpair] using hG.1
    obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hru : r ≠ u := by
      intro h
      apply hr
      simp [h]
    have hrv : r ≠ v := by
      intro h
      apply hr
      simp [h]

    have hdelv := hG.2 ({v} : Set U) (by simp)
    let uV : ↑(({v} : Set U)ᶜ) := ⟨u, by simp [huv]⟩
    let rV : ↑(({v} : Set U)ᶜ) := ⟨r, by simp [hrv]⟩
    obtain ⟨p, hp⟩ := hdelv.exists_isPath uV rV
    have huVrV : uV ≠ rV := by
      intro h
      apply hru
      exact (congrArg Subtype.val h).symm
    obtain ⟨xV, huxV, p', hp'⟩ := p.exists_eq_cons_of_ne huVrV
    let x : U := xV.1
    have hux : G.Adj u x := by
      simpa [uV, x] using huxV
    have hxu : x ≠ u := hux.ne.symm
    have hxv : x ≠ v := by
      have hxnotmem : (xV : U) ∉ ({v} : Set U) := xV.property
      intro h
      apply hxnotmem
      rw [Set.mem_singleton_iff]
      simpa [x] using h

    have hdelu := hG.2 ({u} : Set U) (by simp)
    let xU : ↑(({u} : Set U)ᶜ) := ⟨x, by simp [hxu]⟩
    let vU : ↑(({u} : Set U)ᶜ) := ⟨v, by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact huv.symm⟩
    obtain ⟨q0, hq0⟩ := hdelu.exists_isPath xU vU
    let f : G.induce ({u} : Set U)ᶜ →g G :=
      { toFun := fun y ↦ y.1
        map_rel' := fun h ↦ h }
    have hf : Function.Injective f := Subtype.val_injective
    let qBase : G.Walk x v := q0.map f
    have hqBase : qBase.IsPath := by
      exact (q0.map_isPath_iff_of_injective hf).2 hq0
    have huqBase : u ∉ qBase.support := by
      intro hu
      change u ∈ (q0.map f).support at hu
      rw [SimpleGraph.Walk.support_map] at hu
      obtain ⟨y, -, hyu⟩ := List.mem_map.mp hu
      have hyne : (y : U) ≠ u := by
        have hynotmem : (y : U) ∉ ({u} : Set U) := y.property
        intro h
        apply hynotmem
        simpa only [Set.mem_singleton_iff] using h
      exact hyne hyu
    let q : G.Walk u v := SimpleGraph.Walk.cons hux qBase
    have hq : q.IsPath := by
      exact hqBase.cons huqBase
    have hxq : x ∈ q.support := by
      change x ∈ (SimpleGraph.Walk.cons hux qBase).support
      exact SimpleGraph.Walk.support_subset_support_cons qBase hux qBase.start_mem_support
    have hP : IsTrackFrom G [u, v] u v := by
      refine ⟨⟨by simp, by simp [huv], ?_⟩, by simp, by simp⟩
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have hi0 : i = 0 := by omega
      subst i
      simpa using hadj
    have hQ : IsTrackFrom G q.support u v :=
      isTrackFrom_support_of_isPath q hq
    refine ⟨[u, v], q.support, ?_, hP, hQ, ?_⟩
    · intro heq
      have hxP : x ∈ [u, v] := by simpa [heq] using hxq
      simp [hxu, hxv] at hxP
    · intro w hwP _
      simpa using hwP
  · obtain ⟨p, q, hp, hq, hpq, hinter⟩ :=
      Workspace.ProofLemmas.TwoVertexMengerForNonadjacentVertices.twoVertexMengerForNonadjacentVertices
        G u v huv hadj hG
    exact ⟨p.support, q.support, hpq,
      isTrackFrom_support_of_isPath p hp,
      isTrackFrom_support_of_isPath q hq, hinter⟩

end Workspace.ProofLemmas.TwoInternallyDisjointTracksInTwoConnectedGraph
