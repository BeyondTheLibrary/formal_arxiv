import Workspace.ProofLemmas.Thm84K4CaseDictionary

/-! # The short alternative-5 branch is opposite the changed strip -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.Thm84K4CaseShortAttachment

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems.SPGT Workspace.Types.Appearances.SPGT
open Thm84K4CaseRungs Thm84K4CaseDictionary

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
  {R : U → U → List V} {r : U → U → V} {H : SimpleGraph W}

/-- A vertex of the chosen line graph that lies in `S_uv` lies on the chosen `uv`-rung. -/
theorem mem_rung_of_mem_strip (hSN : IsJStripSystem G J S N) (h : Ends G J S N R r)
    (hsym : ∀ u v, J.Adj u v → R v u = (R u v).reverse)
    {x : V} (hxK : x ∈ ⋃ (u : U) (v : U) (_ : J.Adj u v), {x | x ∈ R u v})
    {u v : U} (huv : J.Adj u v) (hxS : x ∈ S u v) : x ∈ R u v := by
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hxK
  obtain ⟨w, z, hwz, hx⟩ := hxK
  have heq := StripSystemBasics.edge_eq_of_mem_strips hSN hwz huv (h.sub w z hwz _ hx) hxS
  rcases Sym2.eq_iff.mp heq with ⟨hwu, hzv⟩ | ⟨hwv, hzu⟩
  · subst w; subst z; exact hx
  · subst w; subst z
    simpa [hsym u v huv] using hx

/-- PAPER (8.4, printed p. 41): "So `i = 4`, and hence ...
`(X ∩ V(L(H'))) \ V(R_{3,4}) = {r_{3,1}, r_{4,1}, r_{3,2}, r_{4,2}}`."

When the branch has one edge, bipartiteness identifies its ends directly: no other
vertex forks, whereas the unchanged vertices `c,d` both fork. -/
theorem short_attachment_data (hJ : IsKConnected J 3) (hSN : IsJStripSystem G J S N)
    (hForms : FormsLineGraph G J S N R H) (h : Ends G J S N R r)
    (hsym : ∀ u v, J.Adj u v → R v u = (R u v).reverse)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x | x ∈ R u v}))
    {a b c d : U} (hab : J.Adj a b) (hac : J.Adj a c) (had : J.Adj a d)
    (hbc : J.Adj b c) (hbd : J.Adj b d) (hcd : J.Adj c d)
    {y : V} {X : Set V} (hX : X = G.neighborSet y)
    (hfc : Thm84ForkCountForcesK4.ForkAt J R X c)
    (hfd : Thm84ForkCountForcesK4.ForkAt J R X d)
    {q : List W} {s t : W} (hq : IsTrackFrom H q s t) (hlen : trackLength q = 1)
    (hEq : {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (phi ⟨e, he⟩ : V) ∈ X} \ trackEdges q =
      (incidentEdges H s ∪ incidentEdges H t) \ trackEdges q) :
    pathLength (R c d) = 0 ∧
    (∀ x ∈ R a b, ¬ G.Adj y x) ∧
    (∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d →
      ∀ x ∈ R u v, G.Adj y x ↔ x = r v u) := by
  classical
  have hqlen : q.length = 2 := by simp only [trackLength] at hlen; omega
  have hpair := Thm83MixedRungs.eq_pair_of_length_two hq hqlen
  have hst : H.Adj s t := by
    have hh := hq.1
    rw [hpair] at hh
    exact hh.2.2 0 (by simp)
  rw [hpair, Thm83MixedRungs.trackEdges_pair] at hEq
  obtain ⟨ι, hinj, -, hinc⟩ := incidence_dictionary hJ hSN hForms h hsym phi
  have hcfork := fork_incident_nontrivial hSN h phi ι hinc hfc
  have hdfork := fork_incident_nontrivial hSN h phi ι hinc hfd
  have hcs : ι c = s ∨ ι c = t := by
    by_contra hh
    push Not at hh
    exact hcfork.not_subsingleton
      (Thm84K4CaseGeometry.outside_stars_subsingleton hForms.2.1.2 hst hh.1 hh.2 hEq)
  have hds : ι d = s ∨ ι d = t := by
    by_contra hh
    push Not at hh
    exact hdfork.not_subsingleton
      (Thm84K4CaseGeometry.outside_stars_subsingleton hForms.2.1.2 hst hh.1 hh.2 hEq)
  have hicd : ι c ≠ ι d := fun hh => hcd.ne (hinj hh)
  have hcdH : H.Adj (ι c) (ι d) := by
    rcases hcs with hc | hc <;> rcases hds with hd | hd
    · exact (hicd (hc.trans hd.symm)).elim
    · rwa [hc, hd]
    · rw [hc, hd]; exact hst.symm
    · exact (hicd (hc.trans hd.symm)).elim
  have hEq' : {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (phi ⟨e, he⟩ : V) ∈ X} \ {s(ι c, ι d)} =
      (incidentEdges H (ι c) ∪ incidentEdges H (ι d)) \ {s(ι c, ι d)} := by
    rcases hcs with hc | hc <;> rcases hds with hd | hd
    · exact (hicd (hc.trans hd.symm)).elim
    · rwa [hc, hd]
    · rw [hc, hd, (show s(t, s) = s(s, t) from Sym2.eq_swap), Set.union_comm]
      exact hEq
    · exact (hicd (hc.trans hd.symm)).elim
  let e₀ : H.edgeSet := ⟨s(ι c, ι d), hcdH⟩
  have hec : (phi e₀ : V) ∈ N c := (hinc c e₀).mp (by simp [e₀])
  have hed : (phi e₀ : V) ∈ N d := (hinc d e₀).mp (by simp [e₀])
  have heS : (phi e₀ : V) ∈ S c d :=
    StripSystemBasics.N_inter_N_subset_strip hSN hcd.ne hcd ⟨hec, hed⟩
  have heR : (phi e₀ : V) ∈ R c d := mem_rung_of_mem_strip hSN h hsym (phi e₀).2 hcd heS
  have hzero : pathLength (R c d) = 0 :=
    (h.zero_iff hcd).mpr
      (((h.first c d hcd _ heR).mp hec).symm.trans ((h.last c d hcd _ heR).mp hed))
  have hattach : ∀ u v, J.Adj u v → s(u, v) ≠ s(c, d) →
      ∀ x ∈ R u v, G.Adj y x ↔ x ∈ N c ∨ x ∈ N d := by
    intro u v huv hne x hx
    have hxK : x ∈ ⋃ (u : U) (v : U) (_ : J.Adj u v), {x | x ∈ R u v} := by
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨u, v, huv, hx⟩
    let e := phi.symm ⟨x, hxK⟩
    have hex : (phi e : V) = x := by simp [e]
    have hene : (e : Sym2 W) ≠ s(ι c, ι d) := by
      intro he
      have he' : e = e₀ := Subtype.ext he
      have hxS : x ∈ S c d := by rw [← hex, he']; exact heS
      exact hne (StripSystemBasics.edge_eq_of_mem_strips hSN huv hcd (h.sub u v huv x hx) hxS)
    have hiff := Set.ext_iff.mp hEq' (e : Sym2 W)
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, hene, not_false_eq_true,
      and_true, Set.mem_union] at hiff
    have hxmem : (∃ he : (e : Sym2 W) ∈ H.edgeSet, (phi ⟨e, he⟩ : V) ∈ X) ↔ G.Adj y x := by
      constructor
      · rintro ⟨he, hx⟩
        rwa [hX, hex] at hx
      · intro hx
        exact ⟨e.2, by rw [hX, hex]; exact hx⟩
    rw [hxmem] at hiff
    rw [hiff]
    constructor
    · rintro (hc | hd)
      · exact Or.inl (hex ▸ (hinc c e).mp hc.2)
      · exact Or.inr (hex ▸ (hinc d e).mp hd.2)
    · rintro (hc | hd)
      · exact Or.inl ⟨e.2, (hinc c e).mpr (hex.symm ▸ hc)⟩
      · exact Or.inr ⟨e.2, (hinc d e).mpr (hex.symm ▸ hd)⟩
  have hnotN : ∀ u v w, J.Adj u v → w ≠ u → w ≠ v → ∀ x ∈ R u v, x ∉ N w := by
    intro u v w huv hwu hwv x hx hxN
    have hem : x ∈ S u v ∩ N w := ⟨h.sub u v huv x hx, hxN⟩
    rwa [StripSystemBasics.strip_inter_N_eq_empty hSN huv hwu hwv] at hem
  refine ⟨hzero, ?_, ?_⟩
  · intro x hx hyx
    have hne : s(a, b) ≠ s(c, d) := by simp [Sym2.eq_iff, hac.ne, had.ne]
    rcases (hattach a b hab hne x hx).mp hyx with hc | hd
    · exact hnotN a b c hab hac.ne' hbc.ne' x hx hc
    · exact hnotN a b d hab had.ne' hbd.ne' x hx hd
  · intro u hu v hv x hx
    have huv : J.Adj u v := by
      rcases hu with hu | hu <;> rcases hv with hv | hv <;> subst u <;> subst v <;> assumption
    have huc : u ≠ c := by rcases hu with h | h <;> subst u; exact hac.ne; exact hbc.ne
    have hud : u ≠ d := by rcases hu with h | h <;> subst u; exact had.ne; exact hbd.ne
    have hne : s(u, v) ≠ s(c, d) := by simp [Sym2.eq_iff, huc, hud]
    rw [hattach u v huv hne x hx]
    rcases hv with hv | hv
    · subst v
      have hn := hnotN u c d huv hud.symm hcd.ne' x hx
      simpa only [hn, or_false] using h.last u c huv x hx
    · subst v
      have hn := hnotN u d c huv huc.symm hcd.ne x hx
      simpa only [hn, false_or] using h.last u d huv x hx

end Workspace.ProofLemmas.Thm84K4CaseShortAttachment
