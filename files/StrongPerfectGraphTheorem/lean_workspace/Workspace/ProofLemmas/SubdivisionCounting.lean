import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.IsoTransport

/-!
# Counting the edges of a subdivision, and line graphs of subgraphs

Section 5 of *The Strong Perfect Graph Theorem* keeps saying things like *"choose a
3-connected graph `J` maximal (under `J`-enlargement)"* (proof of 5.1) and *"no
`K₃,₃`-enlargement appears in either `G, Ḡ`"* (proof of 5.2).  Both are edge-counting
arguments about subdivisions, and this module collects the counting machinery.

The chain that makes *"maximal under `J`-enlargement"* into *"maximal number of edges"* is

```
|E(J)|  ≤  |E(D)|  =  |E(S)|  <  |E(J')|
```

for a `J`-enlargement `J'` carrying a proper subgraph `S ≠ ⊤` isomorphic to a subdivision `D`
of `J`.  The first inequality is `edgeSet_ncard_le_of_isSubdivision`, the last one
`edgeSet_ncard_lt_of_ne_top`.

The final section records the fact that makes a *subgraph* of the host graph produce a genuine
*appearance*: for `H' ⊆ H` (a subgraph, not necessarily induced), `L(H')` is an **induced**
subgraph of `L(H)`, because line-graph adjacency ("these two edges share an end") does not
depend on the ambient graph.  Mathlib already knows this as
`SimpleGraph.Copy.toLineGraphEmbedding`; `exists_lineGraph_iso_induce_of_subgraph` packages it
in the form §5 uses.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.SubdivisionCounting

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-! ### Positions along a track -/

/-- An entry of a track at a position which is neither the first nor the last is an internal
vertex of the track. -/
theorem mem_trackInterior_getElem {W : Type*} (q : List W) (j : ℕ)
    (h : j + 2 < q.length) : q[j + 1]'(by omega) ∈ trackInterior q := by
  have hlen : j < q.tail.dropLast.length := by
    simp only [List.length_dropLast, List.length_tail]
    omega
  have hmem := List.getElem_mem hlen
  simp only [List.getElem_dropLast, List.getElem_tail] at hmem
  exact hmem

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
theorem getElem_eq_of_index_eq {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- A track and its reverse are the same subgraph, so they have the same edges. -/
theorem trackEdges_reverse {W : Type*} (q : List W) : trackEdges q.reverse = trackEdges q := by
  have key : ∀ l : List W, trackEdges l.reverse ⊆ trackEdges l := by
    intro l e he
    obtain ⟨i, hi, rfl⟩ := he
    have hlen : i + 1 < l.length := by
      have h' : i + 1 < l.reverse.length := hi
      rw [List.length_reverse] at h'
      exact h'
    refine ⟨l.length - 2 - i, by omega, ?_⟩
    have e1 : l.reverse[i]'(by rw [List.length_reverse]; omega)
        = l[l.length - 2 - i + 1]'(by omega) := by
      rw [List.getElem_reverse]
      exact getElem_eq_of_index_eq l (by omega) _ _
    have e2 : l.reverse[i + 1]'(by rw [List.length_reverse]; omega)
        = l[l.length - 2 - i]'(by omega) := by
      rw [List.getElem_reverse]
      exact getElem_eq_of_index_eq l (by omega) _ _
    rw [e1, e2, Sym2.eq_swap]
  refine Set.Subset.antisymm (key q) fun e he => ?_
  have h2 := key q.reverse
  rw [List.reverse_reverse] at h2
  exact h2 he

/-- Internal vertices of a track, by index. -/
theorem mem_trackInterior_iff {W : Type*} (q : List W) (w : W) :
    w ∈ trackInterior q ↔ ∃ (j : ℕ) (h : j + 2 < q.length), q[j + 1]'(by omega) = w := by
  constructor
  · intro hw
    have hw' : w ∈ q.tail.dropLast := hw
    obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hw'
    have hj2 : j + 2 < q.length := by
      have h' : j < q.tail.dropLast.length := hj
      simp only [List.length_dropLast, List.length_tail] at h'
      omega
    refine ⟨j, hj2, ?_⟩
    rw [List.getElem_dropLast, List.getElem_tail] at hjw
    exact hjw
  · rintro ⟨j, hj, rfl⟩
    exact mem_trackInterior_getElem q j hj

/-- If neither end of an edge of a track is an internal vertex of that track, then the track
has exactly two vertices. -/
theorem track_edge_len_two {W : Type*} (q : List W) (i : ℕ) (hi : i + 1 < q.length)
    (h1 : q[i]'(by omega) ∉ trackInterior q)
    (h2 : q[i + 1]'hi ∉ trackInterior q) : q.length = 2 := by
  by_contra hne
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact h2 (mem_trackInterior_getElem q 0 (by omega))
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact h1 (mem_trackInterior_getElem q j (by omega))

/-- The first vertex of a track named by `IsTrackFrom`. -/
theorem track_head {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom D q a b) (hlen : 0 < q.length) : q[0]'hlen = a := by
  have h' := h.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h'
  exact Option.some_injective _ h'

/-- The last vertex of a two-vertex track named by `IsTrackFrom`. -/
theorem track_last {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom D q a b) (hlen : q.length = 2) : q[1]'(by omega) = b := by
  have h' := h.2.2
  rw [List.getLast?_eq_getElem?, show q.length - 1 = 1 from by omega,
    List.getElem?_eq_getElem (by omega)] at h'
  exact Option.some_injective _ h'

/-! ### Subdivisions do not lose edges -/

/-- The tracks that a subdivision attaches to two **distinct** edges of `J` have disjoint edge
sets.  (Stated contrapositively: a common edge forces the two edges of `J` to be equal.)

The argument: a common edge has both of its ends on the other track, so neither end is an
internal vertex of its own track; hence *both* tracks have exactly two vertices, so each is
the pair of its ends, and injectivity of `ι` finishes. -/
theorem trackEdges_disjoint {U W : Type*} {J : SimpleGraph U} {D : SimpleGraph W}
    {ι : U → W} {T : U → U → List W} (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom D (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (u v u' v' : U) (huv : J.Adj u v) (hu'v' : J.Adj u' v')
    (f : Sym2 W) (hf1 : f ∈ trackEdges (T u v)) (hf2 : f ∈ trackEdges (T u' v')) :
    s(u, v) = s(u', v') := by
  by_contra hne
  obtain ⟨i, hi, hfi⟩ := hf1
  obtain ⟨j, hj, hfj⟩ := hf2
  have hq2 : 2 ≤ (T u v).length := by
    have := hlen u v huv
    simp only [trackLength] at this
    omega
  have hr2 : 2 ≤ (T u' v').length := by
    have := hlen u' v' hu'v'
    simp only [trackLength] at this
    omega
  have heq : s((T u v)[i]'(by omega), (T u v)[i + 1]'hi)
      = s((T u' v')[j]'(by omega), (T u' v')[j + 1]'hj) := by rw [← hfi, ← hfj]
  have hmemr : ((T u v)[i]'(by omega) ∈ T u' v') ∧ ((T u v)[i + 1]'hi ∈ T u' v') := by
    rcases Sym2.eq_iff.mp heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
  have hmemq : ((T u' v')[j]'(by omega) ∈ T u v) ∧ ((T u' v')[j + 1]'hj ∈ T u v) := by
    rcases Sym2.eq_iff.mp heq.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
  have hqlen : (T u v).length = 2 :=
    track_edge_len_two (T u v) i hi
      (fun hmem => hdisjint u v u' v' huv hu'v' hne _ hmem hmemr.1)
      (fun hmem => hdisjint u v u' v' huv hu'v' hne _ hmem hmemr.2)
  have hrlen : (T u' v').length = 2 :=
    track_edge_len_two (T u' v') j hj
      (fun hmem => hdisjint u' v' u v hu'v' huv (Ne.symm hne) _ hmem hmemq.1)
      (fun hmem => hdisjint u' v' u v hu'v' huv (Ne.symm hne) _ hmem hmemq.2)
  obtain rfl : i = 0 := by omega
  obtain rfl : j = 0 := by omega
  have e1 : (T u v)[0]'(by omega) = ι u := track_head (htrack u v huv) (by omega)
  have e2 : (T u v)[1]'(by omega) = ι v := track_last (htrack u v huv) hqlen
  have e3 : (T u' v')[0]'(by omega) = ι u' := track_head (htrack u' v' hu'v') (by omega)
  have e4 : (T u' v')[1]'(by omega) = ι v' := track_last (htrack u' v' hu'v') hrlen
  rw [e1, e2, e3, e4] at heq
  rcases Sym2.eq_iff.mp heq with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · exact hne (by rw [hι p1, hι p2])
  · exact hne (by rw [Sym2.eq_swap, hι p1, hι p2])

/-- Subdividing cannot decrease the number of edges: `|E(J)| ≤ |E(D)|` whenever `D` is a
subdivision of `J`. -/
theorem edgeSet_ncard_le_of_isSubdivision {U W : Type*} [Finite W]
    (J : SimpleGraph U) (D : SimpleGraph W) (hsub : IsSubdivision J D) :
    J.edgeSet.ncard ≤ D.edgeSet.ncard := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have key : ∀ e : Sym2 U, e ∈ J.edgeSet →
      ∃ f : Sym2 W, (∃ u v : U, J.Adj u v ∧ e = s(u, v) ∧ f ∈ trackEdges (T u v)) ∧
        f ∈ D.edgeSet := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      have huv : J.Adj u v := (SimpleGraph.mem_edgeSet _).mp he
      have ht := htrack u v huv
      have h2 : 2 ≤ (T u v).length := by
        have := hlen u v huv
        simp only [trackLength] at this
        omega
      refine ⟨s((T u v)[0]'(by omega), (T u v)[1]'(by omega)), ⟨u, v, huv, rfl, ?_⟩, ?_⟩
      · exact ⟨0, by omega, rfl⟩
      · exact (SimpleGraph.mem_edgeSet _).mpr (ht.1.2.2 0 (by omega))
  choose Φ₀ hΦ₀ using key
  have hinj : Function.Injective
      (fun e : ↥J.edgeSet => (⟨Φ₀ e.1 e.2, (hΦ₀ e.1 e.2).2⟩ : ↥D.edgeSet)) := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ heq
    have heq' : Φ₀ e₁ he₁ = Φ₀ e₂ he₂ := congrArg Subtype.val heq
    obtain ⟨u, v, huv, rfl, hm1⟩ := (hΦ₀ e₁ he₁).1
    obtain ⟨u', v', hu'v', rfl, hm2⟩ := (hΦ₀ e₂ he₂).1
    rw [heq'] at hm1
    exact Subtype.ext (trackEdges_disjoint hι htrack hlen hdisjint u v u' v' huv hu'v' _ hm1 hm2)
  have := Nat.card_le_card_of_injective _ hinj
  simpa only [Nat.card_coe_set_eq] using this

/-! ### 3-connected graphs have no isolated vertex -/

/-- Two distinct reachable vertices: the first one has a neighbour. -/
theorem exists_adj_of_reachable {X : Type*} {K : SimpleGraph X} {a b : X}
    (h : K.Reachable a b) (hab : a ≠ b) : ∃ c, K.Adj a c := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hab
  | cons hadj q => exact ⟨_, hadj⟩

/-- A 3-connected graph has no isolated vertex. -/
theorem exists_adj_of_three_connected {U' : Type*} [Fintype U'] (J' : SimpleGraph U')
    (hJ' : IsKConnected J' 3) (v : U') : ∃ w, J'.Adj v w := by
  obtain ⟨hcard, hconn⟩ := hJ'
  have hc := hconn ∅ (by simp)
  rw [Set.compl_empty] at hc
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  have hne : (⟨v, Set.mem_univ v⟩ : ↥(Set.univ : Set U')) ≠ ⟨w, Set.mem_univ w⟩ := by
    intro h
    exact hw (congrArg Subtype.val h).symm
  obtain ⟨c, hcadj⟩ :=
    exists_adj_of_reachable (hc.preconnected ⟨v, Set.mem_univ v⟩ ⟨w, Set.mem_univ w⟩) hne
  exact ⟨(c : U'), hcadj⟩

/-- A **proper** subgraph of a 3-connected graph has strictly fewer edges — stated for any
graph `Dg` isomorphic to that subgraph, which is the shape `IsJEnlargement` delivers. -/
theorem edgeSet_ncard_lt_of_ne_top {U' : Type*} [Fintype U'] (J' : SimpleGraph U')
    (hJ' : IsKConnected J' 3) (S : J'.Subgraph) (hSne : S ≠ ⊤)
    {W : Type*} (Dg : SimpleGraph W) (φ : S.coe ≃g Dg) :
    Dg.edgeSet.ncard < J'.edgeSet.ncard := by
  classical
  have hcard : Dg.edgeSet.ncard = S.coe.edgeSet.ncard := by
    simpa only [Nat.card_coe_set_eq] using (Nat.card_congr φ.symm.mapEdgeSet)
  have hmapinj : Function.Injective (Sym2.map (Subtype.val : ↥S.verts → U')) :=
    Sym2.map.injective Subtype.val_injective
  have himg : Sym2.map (Subtype.val : ↥S.verts → U') '' S.coe.edgeSet ⊆ J'.edgeSet := by
    rintro x ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [Sym2.map_mk]
      exact (SimpleGraph.mem_edgeSet _).mpr (S.adj_sub ((SimpleGraph.mem_edgeSet _).mp he))
  have hmiss : ∃ x ∈ J'.edgeSet, x ∉ Sym2.map (Subtype.val : ↥S.verts → U') '' S.coe.edgeSet := by
    by_cases hverts : S.verts = Set.univ
    · have hadj : ∃ a b, J'.Adj a b ∧ ¬ S.Adj a b := by
        by_contra hcon
        refine hSne ?_
        ext a b
        · rw [hverts]; simp
        · constructor
          · intro h; exact SimpleGraph.Subgraph.top_adj.mpr (S.adj_sub h)
          · intro h
            by_contra hc
            exact hcon ⟨a, b, SimpleGraph.Subgraph.top_adj.mp h, hc⟩
      obtain ⟨a, b, hab, hnab⟩ := hadj
      refine ⟨s(a, b), (SimpleGraph.mem_edgeSet _).mpr hab, ?_⟩
      rintro ⟨e, he, hee⟩
      induction e using Sym2.ind with
      | _ x y =>
        rw [Sym2.map_mk] at hee
        have hxy : S.Adj (x : U') (y : U') := S.coe_adj x y ▸ (SimpleGraph.mem_edgeSet _).mp he
        rcases Sym2.eq_iff.mp hee with ⟨p1, p2⟩ | ⟨p1, p2⟩
        · exact hnab (p1 ▸ p2 ▸ hxy)
        · exact hnab (p1 ▸ p2 ▸ S.symm hxy)
    · obtain ⟨v₀, hv₀⟩ : ∃ v₀ : U', v₀ ∉ S.verts := by
        by_contra hcon
        exact hverts (Set.eq_univ_of_forall (by simpa using hcon))
      obtain ⟨w, hw⟩ := exists_adj_of_three_connected J' hJ' v₀
      refine ⟨s(v₀, w), (SimpleGraph.mem_edgeSet _).mpr hw, ?_⟩
      rintro ⟨e, he, hee⟩
      induction e using Sym2.ind with
      | _ x y =>
        rw [Sym2.map_mk] at hee
        rcases Sym2.eq_iff.mp hee with ⟨p1, -⟩ | ⟨-, p2⟩
        · exact hv₀ (p1 ▸ x.2)
        · exact hv₀ (p2 ▸ y.2)
  obtain ⟨x₀, hx₀, hx₀'⟩ := hmiss
  have hss : Sym2.map (Subtype.val : ↥S.verts → U') '' S.coe.edgeSet ⊂ J'.edgeSet :=
    ⟨himg, fun hcon => hx₀' (hcon hx₀)⟩
  have := Set.ncard_lt_ncard hss (Set.toFinite _)
  rwa [Set.ncard_image_of_injective _ hmapinj, ← hcard] at this

/-- `K₄` is 3-connected. -/
theorem k4_three_connected : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 := by
  refine ⟨by simp, fun S hS => ?_⟩
  have hne : (Sᶜ : Set (Fin 4)).Nonempty := by
    rcases Set.eq_empty_or_nonempty (Sᶜ : Set (Fin 4)) with h | h
    · exfalso
      have hu : S = Set.univ := by rwa [Set.compl_empty_iff] at h
      rw [hu, Set.ncard_univ] at hS
      simp [Nat.card_eq_fintype_card] at hS
    · exact h
  obtain ⟨x, hx⟩ := hne
  haveI : Nonempty (↥(Sᶜ : Set (Fin 4))) := ⟨⟨x, hx⟩⟩
  refine ⟨fun a b => ?_⟩
  by_cases hab : a = b
  · exact hab ▸ SimpleGraph.Reachable.refl a
  · refine SimpleGraph.Adj.reachable ?_
    show (⊤ : SimpleGraph (Fin 4)).Adj (a : Fin 4) (b : Fin 4)
    exact fun h => hab (Subtype.ext h)

/-- In a 3-connected graph every vertex has degree at least `3`. -/
theorem three_le_degree_of_three_connected {U' : Type*} [Fintype U'] (J' : SimpleGraph U')
    (hJ' : IsKConnected J' 3) (v : U') : 3 ≤ (J'.neighborSet v).ncard := by
  by_contra hcon
  obtain ⟨hcard, hconn⟩ := hJ'
  have hc := hconn (J'.neighborSet v) (by omega)
  have hvmem : v ∈ (J'.neighborSet v)ᶜ := by
    simp only [Set.mem_compl_iff, SimpleGraph.mem_neighborSet]
    exact J'.irrefl
  have hcompl : 1 < ((J'.neighborSet v)ᶜ : Set U').ncard := by
    have h1 := Set.ncard_add_ncard_compl (J'.neighborSet v)
    rw [Nat.card_eq_fintype_card] at h1
    omega
  obtain ⟨w, hw, hwv⟩ := Set.exists_ne_of_one_lt_ncard hcompl v
  have hne : (⟨v, hvmem⟩ : ↥((J'.neighborSet v)ᶜ : Set U')) ≠ ⟨w, hw⟩ := by
    intro h
    exact hwv (congrArg Subtype.val h).symm
  obtain ⟨c, hcadj⟩ := exists_adj_of_reachable (hc.preconnected ⟨v, hvmem⟩ ⟨w, hw⟩) hne
  exact c.2 hcadj

/-- `K₃,₃` is bipartite. -/
theorem k33_bipartite : (completeBipartiteGraph (Fin 3) (Fin 3)).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)))
    (by intro u v hadj; cases u <;> cases v <;> simp_all [_root_.completeBipartiteGraph_adj])⟩

/-- `K₃,₃` is 3-connected: it has `6 > 3` vertices, and after deleting fewer than three
vertices each side still has a vertex left, so any two remaining vertices are joined by a path
of length at most two. -/
theorem k33_three_connected : IsKConnected (completeBipartiteGraph (Fin 3) (Fin 3)) 3 := by
  refine ⟨by simp, fun S hS => ?_⟩
  have hleft : ∃ i : Fin 3, (Sum.inl i : Fin 3 ⊕ Fin 3) ∈ Sᶜ := by
    by_contra hcon
    simp only [not_exists, Set.mem_compl_iff, not_not] at hcon
    have hsub : Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3) ⊆ S := by
      rintro x ⟨i, rfl⟩
      exact hcon i
    have h3 : (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3)).ncard = 3 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ]
      simp
    have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hright : ∃ i : Fin 3, (Sum.inr i : Fin 3 ⊕ Fin 3) ∈ Sᶜ := by
    by_contra hcon
    simp only [not_exists, Set.mem_compl_iff, not_not] at hcon
    have hsub : Set.range (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3) ⊆ S := by
      rintro x ⟨i, rfl⟩
      exact hcon i
    have h3 : (Set.range (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3)).ncard = 3 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ]
      simp
    have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨i0, hi0⟩ := hleft
  obtain ⟨j0, hj0⟩ := hright
  haveI : Nonempty ↥(Sᶜ : Set (Fin 3 ⊕ Fin 3)) := ⟨⟨Sum.inl i0, hi0⟩⟩
  refine ⟨fun a b => ?_⟩
  have step : ∀ x y : ↥(Sᶜ : Set (Fin 3 ⊕ Fin 3)),
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (x : Fin 3 ⊕ Fin 3) (y : Fin 3 ⊕ Fin 3) →
      ((completeBipartiteGraph (Fin 3) (Fin 3)).induce (Sᶜ)).Reachable x y :=
    fun _ _ h => SimpleGraph.Adj.reachable h
  rcases ha : (a : Fin 3 ⊕ Fin 3) with ia | ia <;> rcases hb : (b : Fin 3 ⊕ Fin 3) with ib | ib
  · exact (step a ⟨Sum.inr j0, hj0⟩ (by simp [ha, _root_.completeBipartiteGraph_adj])).trans
      (step ⟨Sum.inr j0, hj0⟩ b (by simp [hb, _root_.completeBipartiteGraph_adj]))
  · exact step a b (by simp [ha, hb, _root_.completeBipartiteGraph_adj])
  · exact step a b (by simp [ha, hb, _root_.completeBipartiteGraph_adj])
  · exact (step a ⟨Sum.inl i0, hi0⟩ (by simp [ha, _root_.completeBipartiteGraph_adj])).trans
      (step ⟨Sum.inl i0, hi0⟩ b (by simp [hb, _root_.completeBipartiteGraph_adj]))

/-! ### Recovering `J` from a subdivision: the branch vertices

If `H` is a subdivision of `J` then the branch-vertices of `H` (degree `≥ 3`) are exactly the
images of the vertices of `J`, provided `J` itself has minimum degree `≥ 3` — which is the case
for every 3-connected `J`.  This is the fact that lets one read `V(J)` off `H`, and hence off
`L(H)`; the paper states it in passing on printed p. 20 (*"If `H` is a subdivision of `J` then
`V(J)` is the set of branch-vertices of `H`"*) and uses it silently, e.g. in the proof of 5.2
at *"By 5.3, no `K₃,₃`-enlargement appears in either `G, Ḡ`"*. -/

/-- Every vertex of `J` becomes a branch-vertex of the subdivision, when `J` has minimum
degree `≥ 3`.  (The `3` neighbours of `u` in `J` give `3` distinct neighbours of `ι u` in `H`,
namely the second vertices of their tracks.) -/
theorem range_subset_branchVertices {U W : Type*} [Finite W] {J : SimpleGraph U}
    {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard) :
    Set.range ι ⊆ branchVertices H := by
  rintro w ⟨u, rfl⟩
  show 3 ≤ (H.neighborSet (ι u)).ncard
  have hlen2 : ∀ v : U, J.Adj u v → 2 ≤ (T u v).length := by
    intro v hv
    have h := hlen u v hv
    simp only [trackLength] at h
    omega
  have hgv : ∀ v : U, ∀ hv : J.Adj u v,
      (T u v).getD 1 (ι u) = (T u v)[1]'(by have := hlen2 v hv; omega) := by
    intro v hv
    exact List.getD_eq_getElem _ _ (by have := hlen2 v hv; omega)
  have hmaps : ∀ v ∈ J.neighborSet u, (T u v).getD 1 (ι u) ∈ H.neighborSet (ι u) := by
    intro v hv
    have hv' : J.Adj u v := hv
    have hadj := (htrack u v hv').1.2.2 0 (by have := hlen2 v hv'; omega)
    rw [track_head (htrack u v hv') (by have := hlen2 v hv'; omega)] at hadj
    show H.Adj (ι u) ((T u v).getD 1 (ι u))
    rw [hgv v hv']
    exact hadj
  have hinj : Set.InjOn (fun v => (T u v).getD 1 (ι u)) (J.neighborSet u) := by
    intro v₁ h₁ v₂ h₂ heq
    have hv₁ : J.Adj u v₁ := h₁
    have hv₂ : J.Adj u v₂ := h₂
    by_contra hne12
    have hs : s(u, v₁) ≠ s(u, v₂) := by
      intro hcon
      rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hne12 h2
      · exact absurd hv₁ (by rw [h2]; exact J.loopless.irrefl u)
    have heq' : (T u v₁)[1]'(by have := hlen2 v₁ hv₁; omega)
        = (T u v₂)[1]'(by have := hlen2 v₂ hv₂; omega) := by
      rw [← hgv v₁ hv₁, ← hgv v₂ hv₂]
      exact heq
    by_cases hl1 : 3 ≤ (T u v₁).length
    · have hmem : (T u v₁)[1]'(by omega) ∈ trackInterior (T u v₁) :=
        mem_trackInterior_getElem _ 0 (by omega)
      exact hdisjint u v₁ u v₂ hv₁ hv₂ hs _ hmem
        (by rw [heq']; exact List.getElem_mem _)
    · have hl1' : (T u v₁).length = 2 := by have := hlen2 v₁ hv₁; omega
      have hx1 : (T u v₁)[1]'(by omega) = ι v₁ := track_last (htrack u v₁ hv₁) hl1'
      by_cases hl2 : 3 ≤ (T u v₂).length
      · have hmem : (T u v₂)[1]'(by omega) ∈ trackInterior (T u v₂) :=
          mem_trackInterior_getElem _ 0 (by omega)
        exact hnew u v₂ hv₂ _ hmem ⟨v₁, by rw [← heq', hx1]⟩
      · have hl2' : (T u v₂).length = 2 := by have := hlen2 v₂ hv₂; omega
        have hx2 : (T u v₂)[1]'(by omega) = ι v₂ := track_last (htrack u v₂ hv₂) hl2'
        exact hne12 (hι (by rw [← hx1, ← hx2]; exact heq'))
  calc (3 : ℕ) ≤ (J.neighborSet u).ncard := hdeg u
    _ ≤ (H.neighborSet (ι u)).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)

/-- Conversely, every branch-vertex of a subdivision is a vertex of the graph subdivided:
an internal vertex of a track has exactly the two neighbours it has on that track. -/
theorem branchVertices_subset_range {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hcover : ∀ w : W, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v)) :
    branchVertices H ⊆ Set.range ι := by
  intro w hw
  by_contra hwr
  rcases hcover w with ⟨u, rfl⟩ | ⟨u, v, huv, hwint⟩
  · exact hwr ⟨u, rfl⟩
  obtain ⟨j, hj, rfl⟩ := (mem_trackInterior_iff _ _).mp hwint
  have hnd : (T u v).Nodup := (htrack u v huv).1.2.1
  have hnb : H.neighborSet ((T u v)[j + 1]'(by omega)) ⊆
      {(T u v)[j]'(by omega), (T u v)[j + 2]'(by omega)} := by
    intro x hx
    have hxe : s((T u v)[j + 1]'(by omega), x) ∈ H.edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr hx
    rw [hedges] at hxe
    simp only [Set.mem_iUnion] at hxe
    obtain ⟨u', v', hu'v', hmem⟩ := hxe
    have hin : s((T u v)[j + 1]'(by omega), x) ∈ trackEdges (T u v) := by
      by_cases hsame : s(u, v) = s(u', v')
      · rcases Sym2.eq_iff.mp hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hmem
        · rw [hrev _ _ hu'v'.symm, trackEdges_reverse] at hmem
          exact hmem
      · exfalso
        obtain ⟨i, hi, hie⟩ := hmem
        refine hdisjint u v u' v' huv hu'v' hsame _ hwint ?_
        rcases Sym2.eq_iff.mp hie with ⟨e1, -⟩ | ⟨e1, -⟩
        · exact e1 ▸ List.getElem_mem _
        · exact e1 ▸ List.getElem_mem _
    obtain ⟨i, hi, hie⟩ := hin
    rcases Sym2.eq_iff.mp hie with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have : j + 1 = i := (hnd.getElem_inj_iff).mp e1
      subst this
      exact Or.inr (by rw [e2]; exact getElem_eq_of_index_eq _ (by omega) _ _)
    · have : j + 1 = i + 1 := (hnd.getElem_inj_iff).mp e1
      have hij : j = i := by omega
      subst hij
      exact Or.inl (by rw [e2])
  have hcard : (H.neighborSet ((T u v)[j + 1]'(by omega))).ncard ≤ 2 := by
    refine le_trans (Set.ncard_le_ncard hnb ((Set.finite_singleton _).insert _)) ?_
    refine le_trans (Set.ncard_insert_le _ _) ?_
    simp
  have h3 : 3 ≤ (H.neighborSet ((T u v)[j + 1]'(by omega))).ncard := hw
  omega

/-! ### Two general facts used to set §5's citations up -/

/-- Every graph is a subdivision of itself (no edge subdivided). -/
theorem isSubdivision_self {U : Type*} (J : SimpleGraph U) : IsSubdivision J J := by
  refine ⟨id, fun u v => [u, v], Function.injective_id, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    refine ⟨⟨by simp, by simp [huv.ne], ?_⟩, by simp, by simp⟩
    intro i hi
    have hi2 : i + 1 < ([u, v] : List U).length := hi
    simp only [List.length_cons, List.length_nil] at hi2
    obtain rfl : i = 0 := by omega
    simpa using huv
  · intro u v _
    simp [trackLength]
  · intro u v _
    simp
  · intro u v u' v' _ _ _ w hw
    simp [trackInterior] at hw
  · intro u v _ w hw
    simp [trackInterior] at hw
  · intro w
    exact Or.inl ⟨w, rfl⟩
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · intro he
      induction e using Sym2.ind with
      | _ a b => exact ⟨a, b, (SimpleGraph.mem_edgeSet _).mp he, 0, by simp, rfl⟩
    · rintro ⟨a, b, hab, i, hi, rfl⟩
      have hi2 : i + 1 < ([a, b] : List U).length := hi
      simp only [List.length_cons, List.length_nil] at hi2
      obtain rfl : i = 0 := by omega
      exact (SimpleGraph.mem_edgeSet _).mpr hab

/-- `k`-connectivity transports along an isomorphism. -/
theorem isKConnected_of_iso {α β : Type*} [Fintype α] [Fintype β] {A : SimpleGraph α}
    {B : SimpleGraph β} (e : A ≃g B) {k : ℕ} (h : IsKConnected A k) : IsKConnected B k := by
  obtain ⟨hcard, hconn⟩ := h
  refine ⟨by rwa [← Fintype.card_congr e.toEquiv], fun S hS => ?_⟩
  have h1 : ⇑e '' (⇑e ⁻¹' S) = S := Set.image_preimage_eq _ (EquivLike.surjective e)
  have h2 : (⇑e ⁻¹' S).ncard = S.ncard := by
    conv_rhs => rw [← h1]
    rw [Set.ncard_image_of_injective _ (EquivLike.injective e)]
  have h3 := hconn (⇑e ⁻¹' S) (by omega)
  have h4 : ⇑e '' ((⇑e ⁻¹' S)ᶜ) = Sᶜ := by
    rw [Set.image_compl_eq (EquivLike.bijective e), h1]
  have h5 := Workspace.ProofLemmas.IsoTransport.induceIso e ((⇑e ⁻¹' S)ᶜ)
  rw [h4] at h5
  exact (SimpleGraph.Iso.connected_iff h5).mp h3

/-! ### Transporting a subdivision along an isomorphism

`IsSubdivision` and `DegenerateK4Appearance` are stated with explicit lists of vertices, so
moving them along an isomorphism is mechanical but not free.  These are what let a subgraph
`S ⊆ H` (living on the subtype `↥S.verts`) be presented as a graph on `Fin n`, which is the
shape every `∃ (n : ℕ) (H : SimpleGraph (Fin n))` in §5 asks for. -/

theorem edgeSet_image_of_iso {Vx Wx : Type*} {A : SimpleGraph Vx} {B : SimpleGraph Wx}
    (ψ : A ≃g B) : Sym2.map ψ '' A.edgeSet = B.edgeSet := by
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩
    induction f using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact ψ.map_adj_iff.mpr ((SimpleGraph.mem_edgeSet _).mp hf)
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      refine ⟨s(ψ.symm x, ψ.symm y), ?_, by simp⟩
      rw [SimpleGraph.mem_edgeSet]
      exact ψ.symm.map_adj_iff.mpr ((SimpleGraph.mem_edgeSet _).mp he)

theorem trackEdges_map {Vx Wx : Type*} (f : Vx → Wx) (q : List Vx) :
    trackEdges (q.map f) = Sym2.map f '' trackEdges q := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i + 1 < q.length := by simpa using hi
    exact ⟨s(q[i]'(by omega), q[i + 1]'hi'), ⟨i, hi', rfl⟩, by simp [List.getElem_map]⟩
  · rintro ⟨g, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, by simpa using hi, by simp [List.getElem_map]⟩

theorem trackInterior_map {Vx Wx : Type*} (f : Vx → Wx) (q : List Vx) :
    trackInterior (q.map f) = (trackInterior q).map f := by
  simp [trackInterior, List.map_tail, List.map_dropLast]

theorem isTrackFrom_map {Vx Wx : Type*} {A : SimpleGraph Vx} {B : SimpleGraph Wx} (ψ : A ≃g B)
    {q : List Vx} {a b : Vx} (h : IsTrackFrom A q a b) :
    IsTrackFrom B (q.map ψ) (ψ a) (ψ b) := by
  obtain ⟨⟨hne, hnd, hadj⟩, hh, hl⟩ := h
  refine ⟨⟨by simpa using hne, hnd.map (EquivLike.injective ψ), ?_⟩, ?_, ?_⟩
  · intro i hi
    have hi' : i + 1 < q.length := by simpa using hi
    simp only [List.getElem_map]
    exact ψ.map_adj_iff.mpr (hadj i hi')
  · rw [List.head?_map, hh]; rfl
  · rw [List.getLast?_map, hl]; rfl

theorem isSubdivision_of_iso {U Vx Wx : Type*} {J : SimpleGraph U} {A : SimpleGraph Vx}
    {B : SimpleGraph Wx} (ψ : A ≃g B) (h : IsSubdivision J A) : IsSubdivision J B := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := h
  refine ⟨fun u => ψ (ι u), fun u v => (T u v).map ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (EquivLike.injective ψ).comp hι
  · intro u v huv
    exact isTrackFrom_map ψ (htrack u v huv)
  · intro u v huv
    have := hlen u v huv
    simp only [trackLength, List.length_map] at *
    omega
  · intro u v huv
    show (T v u).map ⇑ψ = ((T u v).map ⇑ψ).reverse
    rw [hrev u v huv]
    simp
  · intro u v u' v' huv hu'v' hs w hw hmem
    rw [trackInterior_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem
    exact hdisjint u v u' v' huv hu'v' hs w0 hw0
      (by rwa [(EquivLike.injective ψ) hzeq] at hz)
  · intro u v huv w hw
    rw [trackInterior_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    rintro ⟨u0, hu0⟩
    exact hnew u v huv w0 hw0 ⟨u0, (EquivLike.injective ψ) hu0⟩
  · intro w
    rcases hcover (ψ.symm w) with ⟨u, hu⟩ | ⟨u, v, huv, hint⟩
    · refine Or.inl ⟨u, ?_⟩
      show w = ψ (ι u)
      rw [← hu]
      simp
    · refine Or.inr ⟨u, v, huv, ?_⟩
      rw [trackInterior_map]
      exact List.mem_map.mpr ⟨ψ.symm w, hint, by simp⟩
  · ext e
    rw [← edgeSet_image_of_iso ψ]
    simp only [Set.mem_image, Set.mem_iUnion, trackEdges_map]
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [hedges] at hf
      simp only [Set.mem_iUnion] at hf
      obtain ⟨u, v, huv, hfm⟩ := hf
      exact ⟨u, v, huv, f, hfm, rfl⟩
    · rintro ⟨u, v, huv, f, hfm, rfl⟩
      refine ⟨f, ?_, rfl⟩
      rw [hedges]
      simp only [Set.mem_iUnion]
      exact ⟨u, v, huv, hfm⟩

theorem neighborSet_image_of_iso {Vx Wx : Type*} {A : SimpleGraph Vx} {B : SimpleGraph Wx}
    (ψ : A ≃g B) (x : Vx) : B.neighborSet (ψ x) = ψ '' A.neighborSet x := by
  ext y
  constructor
  · intro hy
    refine ⟨ψ.symm y, ?_, by simp⟩
    have hy' : B.Adj (ψ x) (ψ (ψ.symm y)) := by simpa using hy
    exact ψ.map_adj_iff.mp hy'
  · rintro ⟨z, hz, rfl⟩
    exact ψ.map_adj_iff.mpr hz

theorem branchVertices_image_of_iso {Vx Wx : Type*} {A : SimpleGraph Vx} {B : SimpleGraph Wx}
    (ψ : A ≃g B) : branchVertices B = ψ '' branchVertices A := by
  ext w
  constructor
  · intro hw
    refine ⟨ψ.symm w, ?_, by simp⟩
    show 3 ≤ (A.neighborSet (ψ.symm w)).ncard
    have h1 : B.neighborSet (ψ (ψ.symm w)) = ψ '' A.neighborSet (ψ.symm w) :=
      neighborSet_image_of_iso ψ _
    rw [show ψ (ψ.symm w) = w from by simp] at h1
    have h2 : 3 ≤ (B.neighborSet w).ncard := hw
    rwa [h1, Set.ncard_image_of_injective _ (EquivLike.injective ψ)] at h2
  · rintro ⟨z, hz, rfl⟩
    show 3 ≤ (B.neighborSet (ψ z)).ncard
    rw [neighborSet_image_of_iso ψ z, Set.ncard_image_of_injective _ (EquivLike.injective ψ)]
    exact hz

theorem degenerateK4Appearance_of_iso {Vx Wx : Type*} {A : SimpleGraph Vx} {B : SimpleGraph Wx}
    (ψ : A ≃g B) (h : DegenerateK4Appearance A) : DegenerateK4Appearance B := by
  obtain ⟨a, b, c, d, hnd, h1, h2, h3, h4, hbr⟩ := h
  refine ⟨ψ a, ψ b, ψ c, ψ d, ?_, ψ.map_adj_iff.mpr h1, ψ.map_adj_iff.mpr h2,
    ψ.map_adj_iff.mpr h3, ψ.map_adj_iff.mpr h4, ?_⟩
  · have hm : (([a, b, c, d] : List Vx).map ψ).Nodup := hnd.map (EquivLike.injective ψ)
    simpa using hm
  · rw [branchVertices_image_of_iso ψ]
    rintro x ⟨y, hy, rfl⟩
    have hy' := hbr hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy' ⊢
    rcases hy' with rfl | rfl | rfl | rfl <;> simp

/-! ### Line graphs of subgraphs

`L(H')` for a subgraph `H' ⊆ H` is the **induced** subgraph of `L(H)` on `E(H')`: two edges of
`H'` share an end in `H'` exactly when they share an end in `H`.  This is what turns a
subgraph of the host graph of an appearance into an appearance in its own right. -/

/-- An induced embedding is an isomorphism onto the subgraph induced on its range. -/
noncomputable def isoRange {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (f : A ↪g B) :
    A ≃g B.induce (Set.range (f : α → β)) :=
  { Equiv.ofInjective (f : α → β) f.injective with
    map_rel_iff' := by
      intro a b
      show B.Adj (f a) (f b) ↔ A.Adj a b
      exact f.map_rel_iff }

/-- A subgraph of `H`, viewed as a graph in its own right, sits inside `H` as a (not
necessarily induced) copy. -/
def subgraphCopy {W : Type*} {H : SimpleGraph W} (S : H.Subgraph) :
    SimpleGraph.Copy S.coe H :=
  ⟨⟨fun x => (x : W), fun {_ _} h => S.adj_sub h⟩, Subtype.val_injective⟩

/-- `L(S)` embeds in `L(H)` as an **induced** subgraph, for any subgraph `S` of `H`. -/
def lineGraphEmbeddingOfSubgraph {W : Type*} {H : SimpleGraph W} (S : H.Subgraph) :
    S.coe.lineGraph ↪g H.lineGraph :=
  (subgraphCopy S).toLineGraphEmbedding

/-- `L(S)` for a subgraph `S ⊆ H`, embedded (inducingly) into `G` through an appearance
`φ : L(H) ≃g G|K`. -/
noncomputable def lineGraphEmbeddingOfAppearance {Vx W : Type*} {G : SimpleGraph Vx}
    {H : SimpleGraph W} {K : Set Vx} (φ : H.lineGraph ≃g G.induce K) (S : H.Subgraph) :
    S.coe.lineGraph ↪g G :=
  ((lineGraphEmbeddingOfSubgraph S).trans φ.toEmbedding).trans
    (SimpleGraph.Embedding.induce (G := G) K)

/-- **The fact §5 needs.**  If `L(H)` is (isomorphic to) the induced subgraph of `G` on `K`,
then for every subgraph `S` of `H` the line graph `L(S)` is (isomorphic to) the induced
subgraph of `G` on some `K' ⊆ K`.  In the vocabulary of §5: a subgraph of the host graph of an
appearance yields an appearance again, on a smaller vertex set. -/
theorem exists_lineGraph_iso_induce_of_subgraph {Vx W : Type*} {G : SimpleGraph Vx}
    {H : SimpleGraph W} {K : Set Vx} (φ : H.lineGraph ≃g G.induce K) (S : H.Subgraph) :
    ∃ K' : Set Vx, K' ⊆ K ∧ Nonempty (S.coe.lineGraph ≃g G.induce K') := by
  classical
  refine ⟨Set.range ((lineGraphEmbeddingOfAppearance φ S : _ → Vx)), ?_,
    ⟨isoRange (lineGraphEmbeddingOfAppearance φ S)⟩⟩
  rintro x ⟨e, rfl⟩
  exact (φ (lineGraphEmbeddingOfSubgraph S e)).2

end Workspace.ProofLemmas.SubdivisionCounting
