import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.Thm84RungEndDictionary

/-!
# The rung/branch dictionary used by the printed proof of 8.2

PAPER (printed p. 40, proof of 8.2): *"Let `B` be the branch of `H` between `u` and `v`, so
`E(B) = V(R_uv)`.  Then `B` is odd and has length `≥ 3` and `y` is nonadjacent in `G` to at most
one vertex of `G` in `δ_H(u)` and at most one in `δ_H(v)`."*

The proof below is the bookkeeping under the word *"so"*.  The identification `φ` and the
branch-vertex dictionary `ι`, `E` are the ones produced by
`ProofLemmas.Thm84RungEndDictionary.rungEndDictionary`; the branch `B` is read off from the rung
`R_uv` through `φ⁻¹` (an edge-list of `H`, i.e. `E(B) = V(R_uv)` literally), and the two
`δ`-clauses are the dictionary clause *"every edge of `δ_H(u)` is the `u`-end of the rung on some
edge `uw` of `J`"* combined with the disjointness of the strips.

**Status: proof attempt 1.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm82BranchDelta

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas

section Aux

variable {W : Type*}

theorem otherEnd_ex (e : Sym2 W) (a : W) : ∃ b : W, a ∈ e → e = s(a, b) := by
  by_cases h : a ∈ e
  · obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp h
    exact ⟨b, fun _ => hb⟩
  · exact ⟨a, fun hc => absurd hc h⟩

/-- The end of the edge `e` other than `a` (junk if `a ∉ e`). -/
noncomputable def otherEnd (e : Sym2 W) (a : W) : W := Classical.choose (otherEnd_ex e a)

theorem otherEnd_spec {e : Sym2 W} {a : W} (h : a ∈ e) : e = s(a, otherEnd e a) :=
  Classical.choose_spec (otherEnd_ex e a) h

/-- Two tracks with the same first vertex, the edges of the first among the edges of the
second, agree index by index as far as the first one goes. -/
theorem getElem?_eq_of_trackEdges_subset {p p' : List W} {x : W}
    (hnd : p.Nodup) (hnd' : p'.Nodup)
    (hh : p.head? = some x) (hh' : p'.head? = some x)
    (hsub : trackEdges p ⊆ trackEdges p') :
    ∀ i, i < p.length → p[i]? = p'[i]? := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi
    match i with
    | 0 =>
      rw [List.head?_eq_getElem?] at hh hh'
      rw [hh, hh']
    | (j + 1) =>
      have hj : j < p.length := by omega
      have hIHj : p[j]? = p'[j]? := IH j (by omega) hj
      have hpj : p[j]? = some (p[j]'hj) := List.getElem?_eq_getElem hj
      have hp'j : p'[j]? = some (p[j]'hj) := by rw [← hIHj, hpj]
      have hjlt' : j < p'.length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by omega)] at hp'j
        simp at hp'j
      have hval : p'[j]'hjlt' = p[j]'hj := by
        have h0 := List.getElem?_eq_getElem hjlt'
        rw [h0] at hp'j
        exact Option.some_injective _ hp'j
      have hmem : s(p[j]'hj, p[j + 1]'hi) ∈ trackEdges p := ⟨j, hi, rfl⟩
      obtain ⟨k, hk, heq⟩ := hsub hmem
      rcases Sym2.eq_iff.mp heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hjk : j = k := by
          have hv : p'[j]'hjlt' = p'[k]'(by omega) := by rw [hval, e1]
          exact hnd'.getElem_inj_iff.mp hv
        subst hjk
        rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hk, e2]
      · exfalso
        have hjk : j = k + 1 := by
          have hv : p'[j]'hjlt' = p'[k + 1]'hk := by rw [hval, e1]
          exact hnd'.getElem_inj_iff.mp hv
        have hIHk : p[k]? = p'[k]? := IH k (by omega) (by omega)
        have h1 : p'[k]'(by omega) = p[k]'(by omega) := by
          have ha := List.getElem?_eq_getElem (show k < p.length by omega)
          have hb := List.getElem?_eq_getElem (show k < p'.length by omega)
          rw [ha, hb] at hIHk
          exact (Option.some_injective _ hIHk).symm
        have hcc : p[j + 1]'hi = p[k]'(show k < p.length by omega) := by rw [e2, h1]
        have := hnd.getElem_inj_iff.mp hcc
        omega

theorem eq_of_trackEdges_subset {p p' : List W} {x y : W}
    (hnd : p.Nodup) (hnd' : p'.Nodup)
    (hh : p.head? = some x) (hh' : p'.head? = some x)
    (hl : p.getLast? = some y) (hl' : p'.getLast? = some y)
    (hsub : trackEdges p ⊆ trackEdges p') : p = p' := by
  have key := getElem?_eq_of_trackEdges_subset hnd hnd' hh hh' hsub
  have hpne : p ≠ [] := by
    intro hcon
    rw [hcon] at hh
    simp at hh
  have hp'ne : p' ≠ [] := by
    intro hcon
    rw [hcon] at hh'
    simp at hh'
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hp'len : 0 < p'.length := List.length_pos_of_ne_nil hp'ne
  set m := p.length - 1 with hm
  set m' := p'.length - 1 with hm'
  have hpm : p[m]? = some y := by
    rw [List.getLast?_eq_getElem?] at hl
    exact hl
  have hp'm' : p'[m']? = some y := by
    rw [List.getLast?_eq_getElem?] at hl'
    exact hl'
  have hkm : p[m]? = p'[m]? := key m (by omega)
  have hp'm : p'[m]? = some y := by rw [← hkm, hpm]
  have hmlt' : m < p'.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hp'm
    simp at hp'm
  have hmm' : m = m' := by
    have e1 := List.getElem?_eq_getElem hmlt'
    have e2 := List.getElem?_eq_getElem (show m' < p'.length by omega)
    rw [e1] at hp'm
    rw [e2] at hp'm'
    have hval : p'[m]'hmlt' = p'[m']'(show m' < p'.length by omega) :=
      (Option.some_injective _ hp'm).trans (Option.some_injective _ hp'm').symm
    exact hnd'.getElem_inj_iff.mp hval
  have hlen : p.length = p'.length := by omega
  refine List.ext_getElem? ?_
  intro i
  by_cases hi : i < p.length
  · exact key i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **A track whose two ends are branch-vertices and whose interior contains none is a
branch.**  (Maximality: any larger such track would have a branch-vertex in its interior.) -/
theorem isBranch_of_ends_branch {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (hab : a ≠ b)
    (hint : ∀ w ∈ trackInterior q, w ∉ branchVertices H)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H) :
    IsBranch H q := by
  refine ⟨hq.1, hint, ?_⟩
  intro q' hq' hint' hsub hverts
  have haq' : a ∈ q' := hverts a (List.mem_of_mem_head? hq.2.1)
  have hbq' : b ∈ q' := hverts b (List.mem_of_getLast? hq.2.2)
  have hq'ne : q' ≠ [] := hq'.1
  obtain ⟨x', hx'⟩ : ∃ x', q'.head? = some x' := by
    cases hc : q' with
    | nil => exact absurd hc hq'ne
    | cons c l => exact ⟨c, by simp⟩
  obtain ⟨y', hy'⟩ : ∃ y', q'.getLast? = some y' :=
    ⟨q'.getLast hq'ne, List.getLast?_eq_some_getLast hq'ne⟩
  have hane : a ∉ trackInterior q' := fun hmem => hint' a hmem ha
  have hbne : b ∉ trackInterior q' := fun hmem => hint' b hmem hb
  have ha' := SubdivisionCompose.mem_ends_of_mem hx' hy' haq' hane
  have hb' := SubdivisionCompose.mem_ends_of_mem hx' hy' hbq' hbne
  rcases ha' with rfl | rfl
  · have hby : b = y' := by
      rcases hb' with h | h
      · exact absurd h.symm hab
      · exact h
    subst hby
    have := eq_of_trackEdges_subset hq.1.2.1 hq'.2.1 hq.2.1 hx' hq.2.2 hy' hsub
    rw [this]
  · have hbx : b = x' := by
      rcases hb' with h | h
      · exact h
      · exact absurd h.symm hab
    subst hbx
    have hrevnd : q'.reverse.Nodup := by simpa using hq'.2.1
    have hrevh : q'.reverse.head? = some a := by
      rw [List.head?_reverse]; exact hy'
    have hrevl : q'.reverse.getLast? = some b := by
      rw [List.getLast?_reverse]; exact hx'
    have hsub' : trackEdges q ⊆ trackEdges q'.reverse := by
      rw [SubdivisionCounting.trackEdges_reverse]; exact hsub
    have := eq_of_trackEdges_subset hq.1.2.1 hrevnd hq.2.1 hrevh hq.2.2 hrevl hsub'
    rw [this, SubdivisionCounting.trackEdges_reverse]

end Aux

/-- **"Let `B` be the branch of `H` between `u` and `v`, so `E(B) = V(R_uv)`."** -/
theorem thm82BranchDelta {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (u v : U) (huv : J.Adj u v) :
    ∃ (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
      (B : List W) (b₁ b₂ : W),
      IsBranch H B ∧ IsTrackFrom H B b₁ b₂ ∧
      trackLength B = pathLength (R u v) + 1 ∧
      (∀ e ∈ incidentEdges H b₁, ∀ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ N u) ∧
      (∀ e ∈ incidentEdges H b₂, ∀ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ N v) ∧
      {e ∈ incidentEdges H b₁ | ∀ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ S u v}.Subsingleton ∧
      {e ∈ incidentEdges H b₂ | ∀ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ S u v}.Subsingleton := by
  classical
  ---------------------------------------------------------------------------
  -- 0.  `H` has a finite vertex type, so the dictionary of 8.4 is available.
  ---------------------------------------------------------------------------
  have hbip : H.IsBipartite := hForms.2.1.2
  obtain ⟨ι₀, T, hι₀inj, htrack0, hlen0, hrev0, hdisj0, hnew0, hcover0, hedges0⟩ := hForms.2.1.1
  haveI : Finite W := by
    have hsubset : (Set.univ : Set W) ⊆
        Set.range ι₀ ∪ ⋃ (a : U) (b : U), {w : W | w ∈ T a b} := by
      intro w _
      rcases hcover0 w with ⟨a, rfl⟩ | ⟨a, b, hab, hw⟩
      · exact Or.inl ⟨a, rfl⟩
      · refine Or.inr ?_
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨a, b, SubdivisionCompose.mem_of_mem_trackInterior hw⟩
    have hfin : (Set.univ : Set W).Finite :=
      Set.Finite.subset (Set.Finite.union (Set.finite_range _)
        (Set.finite_iUnion fun a => Set.finite_iUnion fun b => (T a b).finite_toSet)) hsubset
    exact Set.finite_univ_iff.mp hfin
  haveI : Fintype W := Fintype.ofFinite W
  obtain ⟨φ, ι, E, hιinj, hrange, hEedge, hincid, hEinj, hEφ⟩ :=
    Thm84RungEndDictionary.rungEndDictionary G J hJ S N hSN H R hForms
  ---------------------------------------------------------------------------
  -- 1.  The `a`-end of the rung on the edge `ab`, and its `φ`-preimage `E a b`.
  ---------------------------------------------------------------------------
  have hheadData : ∀ a b : U, J.Adj a b → ∃ s : V,
      (R a b).head? = some s ∧ s ∈ R a b ∧ s ∈ S a b ∧ s ∈ N a ∧
      (∀ he : E a b ∈ H.edgeSet, (↑(φ ⟨E a b, he⟩) : V) = s) := by
    intro a b hab
    obtain ⟨-, s, t, hp, hsubs, hs, -⟩ := hForms.1 a b hab
    have hsR : s ∈ R a b := List.mem_of_mem_head? hp.2.1
    exact ⟨s, hp.2.1, hsR, hsubs s hsR, (hs s hsR).mpr rfl, fun he => hEφ a b hab he s t hp⟩
  choose! sf hsfHead hsfMem hsfStrip hsfN hsfφ using hheadData
  have hincidMem : ∀ (a : U) (e : Sym2 W), e ∈ H.edgeSet → ι a ∈ e →
      ∃ b : U, J.Adj a b ∧ e = E a b := by
    intro a e he hae
    have hmem : e ∈ incidentEdges H (ι a) := ⟨he, hae⟩
    rw [hincid a] at hmem
    exact hmem
  have hEmemIncid : ∀ a b : U, J.Adj a b → ι a ∈ E a b := by
    intro a b hab
    have hmem : E a b ∈ incidentEdges H (ι a) := by rw [hincid a]; exact ⟨b, hab, rfl⟩
    exact hmem.2
  ---------------------------------------------------------------------------
  -- 2.  The rung `R_uv`, indexed by a total function.
  ---------------------------------------------------------------------------
  obtain ⟨-, s₀, t₀, hpath, hstrip, hNu, hNv⟩ := hForms.1 u v huv
  have hLne : R u v ≠ [] := hpath.1.1
  have hn1 : 1 ≤ (R u v).length := List.length_pos_of_ne_nil hLne
  have hLnodup : (R u v).Nodup := hpath.1.2.1
  have hHead : (R u v)[0]'(by omega) = s₀ := by
    have h1 := hpath.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some_injective _ h1
  have hLast : (R u v)[(R u v).length - 1]'(by omega) = t₀ := by
    have h1 := hpath.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some_injective _ h1
  obtain ⟨idx, hidxlt, hidxMem⟩ :
      ∃ f : ℕ → V, (∀ (i : ℕ) (hi : i < (R u v).length), f i = (R u v)[i]'hi) ∧
        (∀ i : ℕ, f i ∈ R u v) := by
    refine ⟨fun i => ((R u v)[i]?).getD ((R u v)[0]'(by omega)), ?_, ?_⟩
    · intro i hi
      simp [List.getElem?_eq_getElem hi]
    · intro i
      by_cases hi : i < (R u v).length
      · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem hi
      · simp only [List.getElem?_eq_none (show (R u v).length ≤ i by omega), Option.getD_none]
        exact List.getElem_mem _
  have hidxK : ∀ i : ℕ,
      idx i ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}) := by
    intro i
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, hidxMem i⟩
  have hkeyNu : ∀ i : ℕ, i < (R u v).length → idx i ∈ N u → i = 0 := by
    intro i hi hmem
    have h1 : idx i = s₀ := (hNu (idx i) (hidxMem i)).mp hmem
    rw [hidxlt i hi] at h1
    have h2 : (R u v)[i]'hi = (R u v)[0]'(show 0 < (R u v).length by omega) := by
      rw [h1, hHead]
    exact hLnodup.getElem_inj_iff.mp h2
  have hkeyNv : ∀ i : ℕ, i < (R u v).length → idx i ∈ N v → i = (R u v).length - 1 := by
    intro i hi hmem
    have h1 : idx i = t₀ := (hNv (idx i) (hidxMem i)).mp hmem
    rw [hidxlt i hi] at h1
    have h2 : (R u v)[i]'hi
        = (R u v)[(R u v).length - 1]'(show (R u v).length - 1 < (R u v).length by omega) := by
      rw [h1, hLast]
    exact hLnodup.getElem_inj_iff.mp h2
  ---------------------------------------------------------------------------
  -- 3.  `E(B) = V(R_uv)`: the edges of `H` corresponding to the rung.
  ---------------------------------------------------------------------------
  obtain ⟨ef, hefφ⟩ : ∃ f : ℕ → H.edgeSet, ∀ i : ℕ, (↑(φ (f i)) : V) = idx i :=
    ⟨fun i => φ.symm ⟨idx i, hidxK i⟩, fun i => by rw [RelIso.apply_symm_apply]⟩
  obtain ⟨ee, heedef⟩ : ∃ g : ℕ → Sym2 W, ∀ i : ℕ, g i = ((ef i : H.edgeSet) : Sym2 W) :=
    ⟨fun i => ((ef i : H.edgeSet) : Sym2 W), fun _ => rfl⟩
  have heeEdge : ∀ i : ℕ, ee i ∈ H.edgeSet := by
    intro i; rw [heedef i]; exact (ef i).2
  have hefNe : ∀ i j : ℕ, i < (R u v).length → j < (R u v).length → i ≠ j → ef i ≠ ef j := by
    intro i j hi hj hij hcon
    have h1 : idx i = idx j := by rw [← hefφ i, ← hefφ j, hcon]
    rw [hidxlt i hi, hidxlt j hj] at h1
    exact hij (hLnodup.getElem_inj_iff.mp h1)
  have hefAdj : ∀ i j : ℕ, i < (R u v).length → j < (R u v).length →
      (H.lineGraph.Adj (ef i) (ef j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    have key : H.lineGraph.Adj (ef i) (ef j) ↔ G.Adj (idx i) (idx j) := by
      constructor
      · intro h
        have h3 : G.Adj (↑(φ (ef i))) (↑(φ (ef j))) := φ.map_rel_iff.mpr h
        rwa [hefφ i, hefφ j] at h3
      · intro h
        have h3 : G.Adj (↑(φ (ef i))) (↑(φ (ef j))) := by rw [hefφ i, hefφ j]; exact h
        exact φ.map_rel_iff.mp h3
    rw [key, hidxlt i hi, hidxlt j hj]
    exact hpath.1.2.2 i j hi hj
  have hMeet : ∀ i : ℕ, i + 1 < (R u v).length → ∃ w : W, w ∈ ee i ∧ w ∈ ee (i + 1) := by
    intro i hi
    have hadj : H.lineGraph.Adj (ef i) (ef (i + 1)) :=
      (hefAdj i (i + 1) (by omega) hi).mpr (Or.inl rfl)
    obtain ⟨-, w, hw1, hw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
    exact ⟨w, by rw [heedef i]; exact hw1, by rw [heedef (i + 1)]; exact hw2⟩
  have hDisj : ∀ i j : ℕ, i < (R u v).length → j < (R u v).length →
      ¬ (i + 1 = j ∨ j + 1 = i) → i ≠ j → ∀ w : W, w ∈ ee i → w ∈ ee j → False := by
    intro i j hi hj hcons hne w hw1 hw2
    rw [heedef i] at hw1
    rw [heedef j] at hw2
    have hadj : H.lineGraph.Adj (ef i) (ef j) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hefNe i j hi hj hne, w, hw1, hw2⟩
    exact hcons ((hefAdj i j hi hj).mp hadj)
  -- the first of these edges is `E u v`
  have hee0 : ee 0 = E u v := by
    have h1 : idx 0 = sf u v huv := by
      have h2 : (R u v)[0]? = some (sf u v huv) := by
        rw [← List.head?_eq_getElem?]; exact hsfHead u v huv
      rw [hidxlt 0 (by omega)]
      have h3 := List.getElem?_eq_getElem (show 0 < (R u v).length by omega)
      rw [h3] at h2
      exact Option.some_injective _ h2
    have h4 : φ (ef 0) = φ ⟨E u v, hEedge u v huv⟩ :=
      Subtype.ext (by rw [hefφ 0, h1, hsfφ u v huv (hEedge u v huv)])
    have h5 : ef 0 = ⟨E u v, hEedge u v huv⟩ := φ.injective h4
    rw [heedef 0, h5]
  -- "the edge of `H` at `ι a` is the `a`-end of some rung at `a`"
  have hstepN : ∀ (a : U) (m : ℕ), m < (R u v).length → ι a ∈ ee m → idx m ∈ N a := by
    intro a m hm hmem
    obtain ⟨b, hb, hEq⟩ := hincidMem a (ee m) (heeEdge m) hmem
    have h5 : ef m = ⟨E a b, hEedge a b hb⟩ :=
      Subtype.ext (by rw [← heedef m]; exact hEq)
    have h6 : idx m = sf a b hb := by
      rw [← hefφ m, h5]; exact hsfφ a b hb (hEedge a b hb)
    rw [h6]; exact hsfN a b hb
  have hstepUV : ∀ (a : U) (m : ℕ), m < (R u v).length → ι a ∈ ee m → a = u ∨ a = v := by
    intro a m hm hmem
    have hNa := hstepN a m hm hmem
    by_contra hc
    push_neg at hc
    have hempty := StripSystemBasics.strip_inter_N_eq_empty hSN huv hc.1 hc.2
    have : idx m ∈ S u v ∩ N a := ⟨hstrip (idx m) (hidxMem m), hNa⟩
    rw [hempty] at this
    exact this
  ---------------------------------------------------------------------------
  -- 4.  Walking the edge list back into a track of `H`.
  ---------------------------------------------------------------------------
  obtain ⟨wf, hwf0, hwfs⟩ :
      ∃ f : ℕ → W, f 0 = ι u ∧ ∀ k : ℕ, f (k + 1) = otherEnd (ee k) (f k) :=
    ⟨fun i => Nat.rec (motive := fun _ => W) (ι u) (fun k acc => otherEnd (ee k) acc) i,
      rfl, fun _ => rfl⟩
  have hIotaU1 : 1 < (R u v).length → ι u ∉ ee 1 := by
    intro h1n hcon
    have := hkeyNu 1 h1n (hstepN u 1 h1n hcon)
    omega
  have hinv : ∀ i : ℕ, i < (R u v).length →
      (wf i ∈ ee i ∧ (i + 1 < (R u v).length → wf i ∉ ee (i + 1))) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [hwf0, hee0]; exact hEmemIncid u v huv
      · intro h1n; rw [hwf0]; exact hIotaU1 h1n
    | succ k IH =>
      intro hk1
      obtain ⟨hmem, hnot⟩ := IH (by omega)
      have hnotk : wf k ∉ ee (k + 1) := hnot hk1
      have hedgek : ee k = s(wf k, wf (k + 1)) := by
        rw [hwfs k]; exact otherEnd_spec hmem
      obtain ⟨c, hc1, hc2⟩ := hMeet k hk1
      have hcw : c = wf (k + 1) := by
        rw [hedgek] at hc1
        rcases Sym2.mem_iff.mp hc1 with h | h
        · exact absurd (by rw [← h]; exact hc2) hnotk
        · exact h
      subst hcw
      refine ⟨hc2, ?_⟩
      intro hk2 hcon
      have hmemk : wf (k + 1) ∈ ee k := by rw [hedgek]; exact Sym2.mem_mk_right _ _
      exact hDisj k (k + 2) (by omega) hk2 (by omega) (by omega) _ hmemk hcon
  have hedge : ∀ i : ℕ, i < (R u v).length → ee i = s(wf i, wf (i + 1)) := by
    intro i hi
    rw [hwfs i]; exact otherEnd_spec (hinv i hi).1
  have hadjW : ∀ i : ℕ, i < (R u v).length → H.Adj (wf i) (wf (i + 1)) := by
    intro i hi
    have h := heeEdge i
    rw [hedge i hi] at h
    exact h
  have hwfNe : ∀ i : ℕ, i < (R u v).length → wf i ≠ wf (i + 1) := fun i hi => (hadjW i hi).ne
  have hwfMemPrev : ∀ i : ℕ, i < (R u v).length → wf (i + 1) ∈ ee i := by
    intro i hi; rw [hedge i hi]; exact Sym2.mem_mk_right _ _
  have hwfInj : ∀ i j : ℕ, i ≤ (R u v).length → j ≤ (R u v).length → i < j → wf i ≠ wf j := by
    intro i j hi hj hij hcon
    have hi' : i < (R u v).length := by omega
    have hjm : j - 1 < (R u v).length := by omega
    have hmem1 : wf i ∈ ee i := (hinv i hi').1
    have hmem2 : wf j ∈ ee (j - 1) := by
      have h := hwfMemPrev (j - 1) hjm
      rwa [show j - 1 + 1 = j from by omega] at h
    rw [hcon] at hmem1
    rcases Nat.lt_or_ge (i + 1) j with hlt | hge
    · by_cases hcase : j - 1 = i + 1
      · have h1 : wf j ∈ ee (i + 1) := by rwa [hcase] at hmem2
        have h2 : wf (i + 1) ∈ ee i := hwfMemPrev i hi'
        have h3 : wf (i + 1) ∈ ee (i + 1) := (hinv (i + 1) (by omega)).1
        have hneEE : ee i ≠ ee (i + 1) := by
          intro hc
          refine hefNe i (i + 1) hi' (by omega) (by omega) (Subtype.ext ?_)
          rw [← heedef i, ← heedef (i + 1), hc]
        have h4 := Thm84RungEndDictionary.subsingleton_inter_of_ne hneEE hmem1 h1 h2 h3
        exact hwfNe i hi' (hcon.trans h4)
      · exact hDisj i (j - 1) hi' hjm (by omega) (by omega) _ hmem1 hmem2
    · have hji : j = i + 1 := by omega
      subst hji
      exact hwfNe i hi' hcon
  ---------------------------------------------------------------------------
  -- 5.  The track `B`.
  ---------------------------------------------------------------------------
  obtain ⟨B, hBlen, hBget⟩ :
      ∃ l : List W, l.length = (R u v).length + 1 ∧
        ∀ (i : ℕ) (hi : i < l.length), l[i]'hi = wf i := by
    refine ⟨List.ofFn (fun i : Fin ((R u v).length + 1) => wf (i : ℕ)), by simp, ?_⟩
    intro i hi
    simp only [List.getElem_ofFn]
  have hBnodup : B.Nodup := by
    rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj
    intro hcon
    have hi : i < B.length := by omega
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hcon
    have h1 := Option.some_injective _ hcon
    rw [hBget i hi, hBget j hj] at h1
    exact hwfInj i j (by omega) (by omega) hij h1
  have hBtrack : IsTrackList H B := by
    refine ⟨?_, hBnodup, ?_⟩
    · intro hcon
      rw [hcon] at hBlen
      simp at hBlen
    · intro i hi
      rw [hBget i (by omega), hBget (i + 1) hi]
      exact hadjW i (by omega)
  have hBhead : B.head? = some (ι u) := by
    have h0 : 0 < B.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, hBget 0 h0, hwf0]
  have hBlast : B.getLast? = some (wf ((R u v).length)) := by
    have h0 : (R u v).length < B.length := by omega
    rw [List.getLast?_eq_getElem?, show B.length - 1 = (R u v).length from by omega,
      List.getElem?_eq_getElem h0, hBget _ h0]
  ---------------------------------------------------------------------------
  -- 6.  The far end of `B` is the branch-vertex `ι v`.
  ---------------------------------------------------------------------------
  have hdegv : 3 ≤ (J.neighborSet v).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ v
  obtain ⟨w₁, w₂, hw₁, hw₂, hw12⟩ :=
    Thm84RungEndDictionary.exists_two_mem
      (Thm84RungEndDictionary.two_le_ncard_diff (s := J.neighborSet v) (a := u) hdegv)
  have hvw₁ : J.Adj v w₁ := hw₁.1
  have hvw₂ : J.Adj v w₂ := hw₂.1
  have hw₁u : u ≠ w₁ := fun h => hw₁.2 (by simp [h])
  have hw₂u : u ≠ w₂ := fun h => hw₂.2 (by simp [h])
  have hMeetEnd : ∀ w : U, J.Adj v w → u ≠ w →
      ∃ z : W, z ∈ ee ((R u v).length - 1) ∧ z ∈ E v w := by
    intro w hvw hwu
    have hidxNv : idx ((R u v).length - 1) ∈ N v := by
      rw [hidxlt _ (by omega), hLast]
      have := hNv t₀ (List.mem_of_getLast? hpath.2.2)
      exact this.mpr rfl
    have hidxSvu : idx ((R u v).length - 1) ∈ S v u := by
      rw [← StripSystemBasics.strip_symm hSN huv]
      exact hstrip _ (hidxMem _)
    have hadjG : G.Adj (idx ((R u v).length - 1)) (sf v w hvw) :=
      StripSystemBasics.Nuv_complete hSN huv.symm hvw hwu
        (idx ((R u v).length - 1)) ⟨hidxNv, hidxSvu⟩
        (sf v w hvw) ⟨hsfN v w hvw, hsfStrip v w hvw⟩
    have hadjI : G.Adj (↑(φ (ef ((R u v).length - 1))))
        (↑(φ (⟨E v w, hEedge v w hvw⟩ : H.edgeSet))) := by
      rw [hefφ _, hsfφ v w hvw (hEedge v w hvw)]
      exact hadjG
    have hadjL : H.lineGraph.Adj (ef ((R u v).length - 1)) ⟨E v w, hEedge v w hvw⟩ :=
      φ.map_rel_iff.mp hadjI
    obtain ⟨-, z, hz1, hz2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjL
    exact ⟨z, by rw [heedef _]; exact hz1, hz2⟩
  have hIotaVmem : ι v ∈ ee ((R u v).length - 1) := by
    by_contra hcon
    obtain ⟨z₁, hz₁a, hz₁b⟩ := hMeetEnd w₁ hvw₁ hw₁u
    obtain ⟨z₂, hz₂a, hz₂b⟩ := hMeetEnd w₂ hvw₂ hw₂u
    obtain ⟨x₁, hx₁⟩ := Sym2.mem_iff_exists.mp (hEmemIncid v w₁ hvw₁)
    obtain ⟨x₂, hx₂⟩ := Sym2.mem_iff_exists.mp (hEmemIncid v w₂ hvw₂)
    have hz₁x : z₁ = x₁ := by
      rw [hx₁] at hz₁b
      rcases Sym2.mem_iff.mp hz₁b with h | h
      · exact absurd (by rw [← h]; exact hz₁a) hcon
      · exact h
    have hz₂x : z₂ = x₂ := by
      rw [hx₂] at hz₂b
      rcases Sym2.mem_iff.mp hz₂b with h | h
      · exact absurd (by rw [← h]; exact hz₂a) hcon
      · exact h
    have hx12 : x₁ ≠ x₂ := by
      intro hc
      have hEE : E v w₁ = E v w₂ := by rw [hx₁, hx₂, hc]
      exact hw12 (hEinj v w₁ w₂ hvw₁ hvw₂ hEE)
    have hx₁mem : x₁ ∈ ee ((R u v).length - 1) := by rw [← hz₁x]; exact hz₁a
    have hx₂mem : x₂ ∈ ee ((R u v).length - 1) := by rw [← hz₂x]; exact hz₂a
    have heeeq : ee ((R u v).length - 1) = s(x₁, x₂) :=
      Thm84RungEndDictionary.eq_sym2_of_mem_mem hx12 hx₁mem hx₂mem
    have hadj12 : H.Adj x₁ x₂ := by
      have h := heeEdge ((R u v).length - 1)
      rw [heeeq] at h
      exact h
    have hadjv1 : H.Adj (ι v) x₁ := by
      have h := hEedge v w₁ hvw₁
      rw [hx₁] at h
      exact h
    have hadjv2 : H.Adj (ι v) x₂ := by
      have h := hEedge v w₂ hvw₂
      rw [hx₂] at h
      exact h
    exact Thm84RungEndDictionary.no_triangle_of_bipartite hbip hadjv1 hadj12 hadjv2
  have hιuv : ι u ≠ ι v := fun h => huv.ne (hιinj h)
  have hwfEnd : wf ((R u v).length) = ι v := by
    have hedgeE : ee ((R u v).length - 1)
        = s(wf ((R u v).length - 1), wf ((R u v).length)) := by
      have h := hedge ((R u v).length - 1) (by omega)
      rwa [show (R u v).length - 1 + 1 = (R u v).length from by omega] at h
    have hmem := hIotaVmem
    rw [hedgeE] at hmem
    rcases Sym2.mem_iff.mp hmem with h | h
    · exfalso
      by_cases hnn : (R u v).length = 1
      · rw [hnn] at h
        simp only [Nat.sub_self] at h
        rw [hwf0] at h
        exact hιuv h.symm
      · have hprev : wf ((R u v).length - 1) ∈ ee ((R u v).length - 2) := by
          have h2 := hwfMemPrev ((R u v).length - 2) (by omega)
          rwa [show (R u v).length - 2 + 1 = (R u v).length - 1 from by omega] at h2
        have h3 : ι v ∈ ee ((R u v).length - 2) := by rw [h]; exact hprev
        have h4 := hkeyNv ((R u v).length - 2) (by omega)
          (hstepN v ((R u v).length - 2) (by omega) h3)
        omega
    · exact h.symm
  ---------------------------------------------------------------------------
  -- 7.  `B` is a branch: its interior avoids the branch-vertices.
  ---------------------------------------------------------------------------
  have hBint : ∀ w ∈ trackInterior B, w ∉ branchVertices H := by
    intro w hw hbr
    rw [SubdivisionCounting.mem_trackInterior_iff] at hw
    obtain ⟨j, hj, hjw⟩ := hw
    have hi1 : 1 ≤ j + 1 := by omega
    have hin : j + 1 < (R u v).length := by omega
    have hwi : w = wf (j + 1) := by rw [← hjw]; exact hBget _ _
    rw [← hrange] at hbr
    obtain ⟨a, ha⟩ := hbr
    have haw : ι a = wf (j + 1) := ha.trans hwi
    have hmemA : wf (j + 1) ∈ ee j := hwfMemPrev j (by omega)
    have hmemB : wf (j + 1) ∈ ee (j + 1) := (hinv (j + 1) hin).1
    have hau : a = u ∨ a = v := hstepUV a (j + 1) hin (by rw [haw]; exact hmemB)
    rcases hau with hau1 | hau1
    · have hNa := hstepN a (j + 1) hin (by rw [haw]; exact hmemB)
      rw [hau1] at hNa
      have := hkeyNu (j + 1) hin hNa
      omega
    · have hNa := hstepN a j (by omega) (by rw [haw]; exact hmemA)
      rw [hau1] at hNa
      have := hkeyNv j (by omega) hNa
      omega
  have hBbranch : IsBranch H B := by
    refine isBranch_of_ends_branch ⟨hBtrack, hBhead, ?_⟩ hιuv hBint ?_ ?_
    · rw [hBlast, hwfEnd]
    · rw [← hrange]; exact ⟨u, rfl⟩
    · rw [← hrange]; exact ⟨v, rfl⟩
  ---------------------------------------------------------------------------
  -- 8.  The two `δ`-clauses.
  ---------------------------------------------------------------------------
  refine ⟨φ, B, ι u, ι v, hBbranch, ⟨hBtrack, hBhead, by rw [hBlast, hwfEnd]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show B.length - 1 = (R u v).length - 1 + 1
    omega
  · intro e he' he
    rw [hincid u] at he'
    obtain ⟨b, hb, rfl⟩ := he'
    rw [hsfφ u b hb he]
    exact hsfN u b hb
  · intro e he' he
    rw [hincid v] at he'
    obtain ⟨b, hb, rfl⟩ := he'
    rw [hsfφ v b hb he]
    exact hsfN v b hb
  · rintro e₁ ⟨h₁a, h₁b⟩ e₂ ⟨h₂a, h₂b⟩
    rw [hincid u] at h₁a h₂a
    obtain ⟨b₁, hb₁, rfl⟩ := h₁a
    obtain ⟨b₂, hb₂, rfl⟩ := h₂a
    have key : ∀ b : U, J.Adj u b →
        (∀ he : E u b ∈ H.edgeSet, (↑(φ ⟨E u b, he⟩) : V) ∈ S u v) → b = v := by
      intro b hb hS
      have hmem : sf u b hb ∈ S u v := by
        rw [← hsfφ u b hb (hEedge u b hb)]
        exact hS (hEedge u b hb)
      have heq := StripSystemBasics.edge_eq_of_mem_strips hSN hb huv (hsfStrip u b hb) hmem
      rcases Sym2.eq_iff.mp heq with ⟨-, h⟩ | ⟨h1, -⟩
      · exact h
      · exact absurd h1 huv.ne
    rw [key b₁ hb₁ h₁b, key b₂ hb₂ h₂b]
  · rintro e₁ ⟨h₁a, h₁b⟩ e₂ ⟨h₂a, h₂b⟩
    rw [hincid v] at h₁a h₂a
    obtain ⟨b₁, hb₁, rfl⟩ := h₁a
    obtain ⟨b₂, hb₂, rfl⟩ := h₂a
    have key : ∀ b : U, J.Adj v b →
        (∀ he : E v b ∈ H.edgeSet, (↑(φ ⟨E v b, he⟩) : V) ∈ S u v) → b = u := by
      intro b hb hS
      have hmem : sf v b hb ∈ S u v := by
        rw [← hsfφ v b hb (hEedge v b hb)]
        exact hS (hEedge v b hb)
      have heq := StripSystemBasics.edge_eq_of_mem_strips hSN hb huv (hsfStrip v b hb) hmem
      rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1.symm huv.ne
      · exact h2
    rw [key b₁ hb₁ h₁b, key b₂ hb₂ h₂b]

end Workspace.ProofLemmas.Thm82BranchDelta
