import Workspace.ProofLemmas.Thm84K4CaseRungs
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.Thm84ForkCountForcesK4
import Workspace.ProofLemmas.Thm83MixedRungs

/-! # Reading the short-branch attachment equality on the rungs -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm84K4CaseDictionary

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems.SPGT Workspace.Types.Appearances.SPGT
open Thm84K4CaseRungs

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
  {R : U → U → List V} {r : U → U → V} {H : SimpleGraph W}

/-- Under the rung-end dictionary, incidence with a branch vertex means membership
in its set `N_u`, for every vertex of the chosen line graph. -/
theorem incidence_dictionary (hJ : IsKConnected J 3) (hSN : IsJStripSystem G J S N)
    (hForms : FormsLineGraph G J S N R H) (h : Ends G J S N R r)
    (hsym : ∀ u v, J.Adj u v → R v u = (R u v).reverse)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x | x ∈ R u v})) :
    ∃ ι : U → W, Function.Injective ι ∧ Set.range ι = branchVertices H ∧
      ∀ u (e : H.edgeSet), ι u ∈ (e : Sym2 W) ↔ (phi e : V) ∈ N u := by
  obtain ⟨ι, E, hinj, hrange, hEedge, hinc, -, hmap⟩ :=
    Thm84BranchRungDictionaryAt.rungEndDictionaryAt G J hJ S N hSN H R hForms phi
  have hmap' : ∀ u v (huv : J.Adj u v), (phi ⟨E u v, hEedge u v huv⟩ : V) = r u v :=
    fun u v huv => hmap u v huv _ _ _ (h.path u v huv)
  refine ⟨ι, hinj, hrange, ?_⟩
  intro u e
  constructor
  · intro hue
    have hem : (e : Sym2 W) ∈ incidentEdges H (ι u) := ⟨e.2, hue⟩
    rw [hinc u] at hem
    obtain ⟨v, huv, heq⟩ := hem
    have he : e = ⟨E u v, hEedge u v huv⟩ := Subtype.ext heq
    rw [he, hmap' u v huv]
    exact h.head_N huv
  · intro hxN
    have step : ∀ v, J.Adj u v → (phi e : V) ∈ R u v → ι u ∈ (e : Sym2 W) := by
      intro v huv hx
      have hxhead := (h.first u v huv _ hx).mp hxN
      have heq : e = ⟨E u v, hEedge u v huv⟩ :=
        phi.injective (Subtype.ext (hxhead.trans (hmap' u v huv).symm))
      have heinc : E u v ∈ incidentEdges H (ι u) := by
        rw [hinc u]; exact ⟨v, huv, rfl⟩
      rw [heq]
      exact heinc.2
    have hxK := (phi e).2
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hxK
    obtain ⟨v, w, hvw, hx⟩ := hxK
    by_cases huv : u = v
    · subst v
      exact step w hvw hx
    have huw : u = w := by
      by_contra huw
      have hem : (phi e : V) ∈ S v w ∩ N u := ⟨h.sub v w hvw _ hx, hxN⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hvw huv huw] at hem
      exact hem
    subst w
    exact step v hvw.symm (by simpa [hsym v u hvw] using hx)

/-- Two selected rung ends in `X` give two incident `X`-edges at the corresponding
branch vertex. This form uses the incidence dictionary without naming each end-edge. -/
theorem fork_incident_nontrivial (hSN : IsJStripSystem G J S N)
    (h : Ends G J S N R r)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x | x ∈ R u v}))
    (ι : U → W)
    (hinc : ∀ u (e : H.edgeSet), ι u ∈ (e : Sym2 W) ↔ (phi e : V) ∈ N u)
    {X : Set V} {u : U} (hf : Thm84ForkCountForcesK4.ForkAt J R X u) :
    (incidentEdges H (ι u) ∩
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (phi ⟨e, he⟩ : V) ∈ X}).Nontrivial := by
  obtain ⟨v, w, huv, huw, hvw, ⟨s, hs, hsX⟩, ⟨t, ht, htX⟩⟩ := hf
  have hsEq : s = r u v := Option.some_injective _ (hs.symm.trans (h.path u v huv).2.1)
  have htEq : t = r u w := Option.some_injective _ (ht.symm.trans (h.path u w huw).2.1)
  have hsK : s ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), {x | x ∈ R a b} := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, hsEq.symm ▸ h.head_mem huv⟩
  have htK : t ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), {x | x ∈ R a b} := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, w, huw, htEq.symm ▸ h.head_mem huw⟩
  let e := phi.symm ⟨s, hsK⟩
  let f := phi.symm ⟨t, htK⟩
  have he : (phi e : V) = s := by simp [e]
  have hf' : (phi f : V) = t := by simp [f]
  refine ⟨e, ⟨⟨e.2, (hinc u e).mpr ?_⟩, e.2, ?_⟩,
    f, ⟨⟨f.2, (hinc u f).mpr ?_⟩, f.2, ?_⟩, ?_⟩
  · rw [he, hsEq]; exact h.head_N huv
  · rwa [he]
  · rw [hf', htEq]; exact h.head_N huw
  · rwa [hf']
  · intro hef
    have heq : e = f := Subtype.ext hef
    have hst : s = t := he.symm.trans ((congrArg (fun e => (phi e : V)) heq).trans hf')
    have hstrips := StripSystemBasics.edge_eq_of_mem_strips hSN huv huw
      (h.head_strip huv) ((hsEq.symm.trans (hst.trans htEq)).symm ▸ h.head_strip huw)
    rcases Sym2.eq_iff.mp hstrips with ⟨-, h⟩ | ⟨-, h⟩
    · exact hvw h
    · exact huv.ne h.symm

end Workspace.ProofLemmas.Thm84K4CaseDictionary
