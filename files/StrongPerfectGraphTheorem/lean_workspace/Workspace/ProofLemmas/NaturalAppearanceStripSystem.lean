import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.NaturalAppearanceStripSystemCore
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.NaturalAppearanceStripSystem

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.BipartiteClosedWalkEven
open Workspace.ProofLemmas.NaturalAppearanceStripSystemCore

theorem naturalAppearanceStripSystem
    {V U W : Type*} [Fintype V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (H : SimpleGraph W) (K : Set V)
    (hJ : IsKConnected J 3) (hAppearance : IsAppearance G J H K) :
    ∃ (S : U → U → Set V) (N : U → Set V) (R : U → U → List V),
      IsJStripSystem G J S N ∧
      stripSystemVertices J S = K ∧
      FormsLineGraph G J S N R H ∧
      (∀ u v : U, J.Adj u v → ∀ x ∈ S u v, x ∈ R u v) ∧
      (∃ (φ : H.lineGraph ≃g G.induce K) (ι : U → W) (T : U → U → List W),
        Function.Injective ι ∧
        (∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v)) ∧
        (∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v)) ∧
        (∀ u v : U, J.Adj u v → T v u = (T u v).reverse) ∧
        (∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
          ∀ w ∈ trackInterior (T u v), w ∉ T u' v') ∧
        (∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι) ∧
        (∀ w : W, (∃ u : U, w = ι u) ∨
          ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v)) ∧
        H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v) ∧
        (∀ u v : U, J.Adj u v → ∀ x : V,
          x ∈ R u v ↔ ∃ e : H.edgeSet, e.1 ∈ trackEdges (T u v) ∧ x = (φ e : V))) ∧
      (NondegenerateAppearance J H → NondegenerateStripSystem G J S N) := by
  classical
  rcases hAppearance with ⟨⟨⟨iota, T, hiota, htrack, hlen, hrev, hdisj,
      hnew, hcover, hedges⟩, hbip⟩, ⟨phi⟩⟩
  let R : U → U → List V := fun u v =>
    if huv : J.Adj u v then trackRung phi (T u v) (htrack u v huv).1 else []
  let S : U → U → Set V := fun u v => {x | x ∈ R u v}
  let N : U → Set V := fun u =>
    {x | ∃ e : H.edgeSet, iota u ∈ e.1 ∧ x = (phi e : V)}
  have hmem : ∀ u v (huv : J.Adj u v) (x : V),
      x ∈ R u v ↔ ∃ e : H.edgeSet, e.1 ∈ trackEdges (T u v) ∧ x = (phi e : V) := by
    intro u v huv x
    simp only [R, huv, dite_true]
    constructor
    · intro hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      change e ∈ trackEdgeVerts H (T u v) (htrack u v huv).1 at he
      simp only [trackEdgeVerts, List.mem_ofFn] at he
      obtain ⟨j, hj⟩ := he
      refine ⟨e, ⟨j.1, by have := j.2; simp at this ⊢; omega, ?_⟩, rfl⟩
      exact congrArg Subtype.val hj.symm
    · rintro ⟨e, ⟨i, hi, hie⟩, rfl⟩
      apply List.mem_map.mpr
      have hidx : i < (trackEdgeVerts H (T u v) (htrack u v huv).1).length := by
        simp [trackLength]
        omega
      let f : H.edgeSet := (trackEdgeVerts H (T u v) (htrack u v huv).1)[i]'hidx
      have hfe : f = e := by
        apply Subtype.ext
        simpa [f, trackEdgeVerts] using hie.symm
      exact ⟨f, List.getElem_mem _, by rw [hfe]⟩
  have hSK : stripSystemVertices J S = K := by
    ext x
    constructor
    · intro hx
      simp only [stripSystemVertices, Set.mem_iUnion] at hx
      obtain ⟨u, v, huv, hx⟩ := hx
      exact trackRung_subset_K phi (T u v) (htrack u v huv).1 x (by simpa [S, R, huv] using hx)
    · intro hx
      let e : H.edgeSet := phi.symm ⟨x, hx⟩
      have he : e.1 ∈ H.edgeSet := e.2
      have he' : e.1 ∈ ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v) := by
        simpa only [← hedges] using he
      simp only [Set.mem_iUnion] at he'
      obtain ⟨u, v, huv, heT⟩ := he'
      simp only [stripSystemVertices, Set.mem_iUnion]
      refine ⟨u, v, huv, ?_⟩
      have hphi : (phi e : V) = x := congrArg Subtype.val (phi.apply_symm_apply ⟨x, hx⟩)
      exact (show x ∈ S u v from (hmem u v huv x).2 ⟨e, heT, hphi.symm⟩)
  refine ⟨S, N, R, ?_, hSK, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u v huv
      ext z
      rw [show z ∈ S u v ↔ z ∈ R u v by rfl,
        show z ∈ S v u ↔ z ∈ R v u by rfl,
        hmem u v huv z, hmem v u huv.symm z, hrev u v huv,
        Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    · intro u v p q huv hpq hne
      refine Set.disjoint_left.mpr ?_
      intro z hzuv hzpq
      obtain ⟨e, heuv, hze⟩ := (hmem u v huv z).mp hzuv
      obtain ⟨f, hefpq, hzf⟩ := (hmem p q hpq z).mp hzpq
      have hef : e = f := by
        apply phi.injective
        apply Subtype.ext
        exact hze.symm.trans hzf
      apply hne
      exact Workspace.ProofLemmas.SubdivisionCounting.trackEdges_disjoint
        hiota htrack hlen hdisj u v p q huv hpq e.1 heuv (by simpa [hef] using hefpq)
    · intro u z hzN
      change ∃ e : H.edgeSet, iota u ∈ e.1 ∧ z = (phi e : V) at hzN
      obtain ⟨e, hue, rfl⟩ := hzN
      have heAll : e.1 ∈ ⋃ (p : U) (q : U) (_ : J.Adj p q), trackEdges (T p q) := by
        simpa only [← hedges] using e.2
      simp only [Set.mem_iUnion] at heAll
      obtain ⟨p, q, hpq, hepq⟩ := heAll
      have huiT : iota u ∈ T p q := endpoints_mem_of_mem_trackEdges hepq hue
      rcases range_mem_track_iff_end hiota htrack hnew hpq huiT with hup | huq
      · subst p
        simp only [Set.mem_iUnion]
        exact ⟨q, hpq, (hmem u q hpq (phi e : V)).mpr ⟨e, hepq, rfl⟩⟩
      · subst q
        have heqp : e.1 ∈ trackEdges (T u p) := by
          rw [hrev p u hpq, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
          exact hepq
        simp only [Set.mem_iUnion]
        exact ⟨p, hpq.symm, (hmem u p hpq.symm (phi e : V)).mpr ⟨e, heqp, rfl⟩⟩
    · intro u v huv z hz
      refine ⟨R u v, ?_, hz⟩
      simpa [R, huv] using
        (trackRung_isUVRung phi iota T htrack hlen S N huv
          (fun x => by simp [S, R, huv]) (fun _ _ => Iff.rfl))
    · intro u v p q huv hpq hnodup
      intro a ha b hb hab
      obtain ⟨e, heuv, hae⟩ := (hmem u v huv a).mp ha
      obtain ⟨f, hefpq, hbf⟩ := (hmem p q hpq b).mp hb
      have habInd : (G.induce K).Adj (phi e) (phi f) := by
        change G.Adj (phi e : V) (phi f : V)
        simpa only [hae, hbf] using hab
      have hline : H.lineGraph.Adj e f := phi.map_rel_iff.mp habInd
      obtain ⟨-, z, hze, hzf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hline
      have hzuv : z ∈ T u v := endpoints_mem_of_mem_trackEdges heuv hze
      have hzpq : z ∈ T p q := endpoints_mem_of_mem_trackEdges hefpq hzf
      have hne : s(u, v) ≠ s(p, q) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨hup, hvq⟩ | ⟨huq, hvp⟩ <;>
          subst_vars <;> simp at hnodup
      rcases common_vertex_of_distinct_tracks hiota htrack hdisj huv hpq hne hzuv hzpq with
        ⟨hup, -⟩ | ⟨huq, -⟩ | ⟨hvp, -⟩ | ⟨hvq, -⟩ <;>
          subst_vars <;> simp at hnodup
    · intro u v w huv huw hvw
      have hedgeNe : s(u, v) ≠ s(u, w) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨-, hvw'⟩ | ⟨huw', hvu⟩
        · exact hvw hvw'
        · exact huv.ne hvu.symm
      constructor
      · intro a ha b hb
        obtain ⟨e, heuv, hae⟩ := (hmem u v huv a).mp ha.2
        obtain ⟨f, heuw, hbf⟩ := (hmem u w huw b).mp hb.2
        have heu : iota u ∈ e.1 := by
          have haN : a ∈ N u := ha.1
          change ∃ d : H.edgeSet, iota u ∈ d.1 ∧ a = (phi d : V) at haN
          obtain ⟨d, hdu, had⟩ := haN
          have hde : d = e := by
            apply phi.injective
            apply Subtype.ext
            exact had.symm.trans hae
          simpa [hde] using hdu
        have hfu : iota u ∈ f.1 := by
          have hbN : b ∈ N u := hb.1
          change ∃ d : H.edgeSet, iota u ∈ d.1 ∧ b = (phi d : V) at hbN
          obtain ⟨d, hdu, hbd⟩ := hbN
          have hdf : d = f := by
            apply phi.injective
            apply Subtype.ext
            exact hbd.symm.trans hbf
          simpa [hdf] using hdu
        have hef : e ≠ f := by
          intro heq
          exact hedgeNe (Workspace.ProofLemmas.SubdivisionCounting.trackEdges_disjoint
            hiota htrack hlen hdisj u v u w huv huw e.1 heuv (by simpa [heq] using heuw))
        have hline : H.lineGraph.Adj e f :=
          SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef, iota u, heu, hfu⟩
        have hind : (G.induce K).Adj (phi e) (phi f) := phi.map_rel_iff.mpr hline
        change G.Adj (phi e : V) (phi f : V) at hind
        simpa only [← hae, ← hbf] using hind
      · intro a ha b hb hab
        obtain ⟨e, heuv, hae⟩ := (hmem u v huv a).mp ha
        obtain ⟨f, heuw, hbf⟩ := (hmem u w huw b).mp hb
        have habInd : (G.induce K).Adj (phi e) (phi f) := by
          change G.Adj (phi e : V) (phi f : V)
          simpa only [hae, hbf] using hab
        have hline : H.lineGraph.Adj e f := phi.map_rel_iff.mp habInd
        obtain ⟨-, z, hze, hzf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hline
        have hzuv : z ∈ T u v := endpoints_mem_of_mem_trackEdges heuv hze
        have hzuw : z ∈ T u w := endpoints_mem_of_mem_trackEdges heuw hzf
        have hzu : z = iota u := by
          rcases common_vertex_of_distinct_tracks hiota htrack hdisj huv huw hedgeNe hzuv hzuw with
            ⟨-, hz⟩ | ⟨huw', -⟩ | ⟨hvu, -⟩ | ⟨hvw', -⟩
          · exact hz
          · exact False.elim (huw.ne huw')
          · exact False.elim (huv.ne hvu.symm)
          · exact False.elim (hvw hvw')
        constructor
        · change ∃ d : H.edgeSet, iota u ∈ d.1 ∧ a = (phi d : V)
          exact ⟨e, hzu ▸ hze, hae⟩
        · change ∃ d : H.edgeSet, iota u ∈ d.1 ∧ b = (phi d : V)
          exact ⟨f, hzu ▸ hzf, hbf⟩
    · refine ⟨R, ?_, ?_⟩
      · intro u v huv
        simpa [R, huv] using
          (trackRung_isUVRung phi iota T htrack hlen S N huv
            (fun x => by simp [S, R, huv]) (fun _ _ => Iff.rfl))
      · intro c hc3 hcnd hadj
        have hpar := sum_trackLength_pred_modEq hbip htrack hlen c hadj
        have hmaps :
            (c.zip (c.rotate 1)).map (fun p => pathLength (R p.1 p.2)) =
              (c.zip (c.rotate 1)).map (fun p => trackLength (T p.1 p.2) - 1) := by
          apply List.map_congr_left
          intro p hp
          have hpAdj := hadj p hp
          simp [R, hpAdj, trackRung_pathLength]
        rw [hmaps]
        exact hpar
  · refine ⟨?_, ?_⟩
    · intro u v huv
      have hRdef : R u v = trackRung phi (T u v) (htrack u v huv).1 := by
        simp [R, huv]
      rw [hRdef]
      obtain ⟨s, t, hpath⟩ :=
        trackRung_exists_isPathFrom phi (T u v) (htrack u v huv).1 (hlen u v huv)
      refine ⟨huv, s, t, hpath, ?_, ?_, ?_⟩
      · intro x hx
        simpa [S, R, huv] using hx
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
        have hjT : j + 1 < (T u v).length := by
          rw [trackRung_length] at hj
          simp only [trackLength] at hj
          omega
        have hedge : s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) ∈ H.edgeSet :=
          trackEdge_mem_edgeSet (htrack u v huv).1 j hjT
        have hvalue :
            (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
              (phi ⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : V) :=
          trackRung_getElem phi (T u v) (htrack u v huv).1 j hj hjT hedge
        have hRpos : 0 < (trackRung phi (T u v) (htrack u v huv).1).length := by
          rw [trackRung_length]
          exact hlen u v huv
        have hRzero :
            (trackRung phi (T u v) (htrack u v huv).1)[0]'hRpos = s :=
          Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hpath.2.1 hRpos
        constructor
        · intro hxN
          change ∃ e : H.edgeSet, iota u ∈ e.1 ∧
            (trackRung phi (T u v) (htrack u v huv).1)[j]'hj = (phi e : V) at hxN
          obtain ⟨e, heu, heval⟩ := hxN
          have heq : e =
              (⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : H.edgeSet) := by
            apply phi.injective
            apply Subtype.ext
            exact heval.symm.trans hvalue
          have hinc : iota u ∈
              s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) := by
            change iota u ∈ e.1 at heu
            rw [heq] at heu
            exact heu
          have hjzero : j = 0 :=
            (left_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mp hinc
          have hget :
              (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
                (trackRung phi (T u v) (htrack u v huv).1)[0]'hRpos :=
            Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _ hjzero _ _
          exact hget.trans hRzero
        · intro hxs
          have hget :
              (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
                (trackRung phi (T u v) (htrack u v huv).1)[0]'hRpos :=
            hxs.trans hRzero.symm
          have hjzero : j = 0 :=
            (hpath.1.2.1.getElem_inj_iff).mp hget
          refine ⟨⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩,
            (left_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mpr hjzero,
            hvalue⟩
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
        have hjT : j + 1 < (T u v).length := by
          rw [trackRung_length] at hj
          simp only [trackLength] at hj
          omega
        have hedge : s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) ∈ H.edgeSet :=
          trackEdge_mem_edgeSet (htrack u v huv).1 j hjT
        have hvalue :
            (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
              (phi ⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : V) :=
          trackRung_getElem phi (T u v) (htrack u v huv).1 j hj hjT hedge
        have hRpos : 0 < (trackRung phi (T u v) (htrack u v huv).1).length := by
          rw [trackRung_length]
          exact hlen u v huv
        have hRlast :
            (trackRung phi (T u v) (htrack u v huv).1)[
                (trackRung phi (T u v) (htrack u v huv).1).length - 1]'(by omega) = t :=
          Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hpath.2.2 hRpos
        constructor
        · intro hxN
          change ∃ e : H.edgeSet, iota v ∈ e.1 ∧
            (trackRung phi (T u v) (htrack u v huv).1)[j]'hj = (phi e : V) at hxN
          obtain ⟨e, hev, heval⟩ := hxN
          have heq : e =
              (⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩ : H.edgeSet) := by
            apply phi.injective
            apply Subtype.ext
            exact heval.symm.trans hvalue
          have hinc : iota v ∈
              s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT) := by
            change iota v ∈ e.1 at hev
            rw [heq] at hev
            exact hev
          have hjlastT : j + 2 = (T u v).length :=
            (right_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mp hinc
          have hjlastR : j =
              (trackRung phi (T u v) (htrack u v huv).1).length - 1 := by
            rw [trackRung_length]
            simp only [trackLength]
            omega
          have hget :
              (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
                (trackRung phi (T u v) (htrack u v huv).1)[
                  (trackRung phi (T u v) (htrack u v huv).1).length - 1]'(by omega) :=
            Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _ hjlastR _ _
          exact hget.trans hRlast
        · intro hxt
          have hget :
              (trackRung phi (T u v) (htrack u v huv).1)[j]'hj =
                (trackRung phi (T u v) (htrack u v huv).1)[
                  (trackRung phi (T u v) (htrack u v huv).1).length - 1]'(by omega) :=
            hxt.trans hRlast.symm
          have hjlastR : j =
              (trackRung phi (T u v) (htrack u v huv).1).length - 1 :=
            (hpath.1.2.1.getElem_inj_iff).mp hget
          have hjlastT : j + 2 = (T u v).length := by
            rw [trackRung_length, trackLength] at hjlastR
            omega
          refine ⟨⟨s((T u v)[j]'(by omega), (T u v)[j + 1]'hjT), hedge⟩,
            (right_endpoint_mem_edge_iff (htrack u v huv) (hlen u v huv) j hjT).mpr hjlastT,
            hvalue⟩
    · have hUnion : (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) = K := by
        change stripSystemVertices J S = K
        exact hSK
      rw [hUnion]
      exact ⟨⟨⟨iota, T, hiota, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩, hbip⟩, ⟨phi⟩⟩
  · intro u v huv x hx
    exact hx
  · exact ⟨phi, iota, T, hiota, htrack, hlen, hrev, hdisj, hnew, hcover, hedges, hmem⟩
  · intro hnondeg
    let Hfin : SimpleGraph (Fin (Fintype.card W)) := H.overFin rfl
    let psi : H ≃g Hfin := H.overFinIso rfl
    have hsub : IsSubdivision J H :=
      ⟨iota, T, hiota, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩
    have happFin : IsAppearance G J Hfin K := by
      exact ⟨⟨Workspace.ProofLemmas.SubdivisionCounting.isSubdivision_of_iso psi hsub,
        SimpleGraph.Colorable.of_hom psi.symm.toHom hbip⟩,
        ⟨psi.lineGraph.symm.trans phi⟩⟩
    have hnondegFin : NondegenerateAppearance J Hfin := by
      intro hdegFin
      apply hnondeg
      rcases hdegFin with ⟨hK4, hdegK4⟩ | ⟨hnotK4, hK33, ⟨hiso⟩⟩
      · exact Or.inl ⟨hK4,
          Workspace.ProofLemmas.SubdivisionCounting.degenerateK4Appearance_of_iso
            psi.symm hdegK4⟩
      · exact Or.inr ⟨hnotK4, hK33, ⟨psi.trans hiso⟩⟩
    refine ⟨Fintype.card W, Hfin, R, ?_, hnondegFin⟩
    refine ⟨?_, ?_⟩
    · intro u v huv
      simpa [R, huv] using
        (trackRung_isUVRung phi iota T htrack hlen S N huv
          (fun x => by simp [S, R, huv]) (fun _ _ => Iff.rfl))
    · have hUnion :
          (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) = K := by
        change stripSystemVertices J S = K
        exact hSK
      rw [hUnion]
      exact happFin

end Workspace.ProofLemmas.NaturalAppearanceStripSystem
