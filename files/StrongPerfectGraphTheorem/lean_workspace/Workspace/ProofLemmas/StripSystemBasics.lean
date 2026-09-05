import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems

/-!
# Elementary consequences of the `J`-strip system axioms

`Workspace.Types.StripSystems` transcribes the definition of a `J`-strip system `(S,N)` in `G`
(printed p. 39) and deliberately leaves out the sentence the authors flag as a *consequence*:

PAPER (printed p. 39, immediately after the definition): *"It follows that for distinct
`u,v ∈ V(J)`, `N_u ∩ N_v` is empty if `u,v` are nonadjacent, and otherwise `N_u ∩ N_v ⊆ S_{uv}`;
and for `uv ∈ E(J)` and `w ∈ V(J)`, if `w ≠ u,v` then `S_{uv} ∩ N_w = ∅`."*

and the sentence (printed p. 40, in the paragraph introducing `N_{uv}`):

PAPER: *"So every vertex of `N_u` belongs to `N_{uv}` for exactly one `v`."*

This module supplies those, together with named accessors for the seven axioms and the small
"a vertex lies in only one strip" facts that §8 uses constantly (e.g. in the proof of 8.6:
*"`n₁,n₂` belong to strips `S_{u₁w}`, `S_{vu₂}`, where `u₁w`, `vu₂` are disjoint edges of `J`;
and so `n₁,n₂` are not adjacent in `G`"*, and *"`n₂` is not in `K` since it is in only one
strip"*).

Nothing here needs `G` to be Berge or `J` to be 3-connected: every statement is a direct
consequence of the seven axioms of `IsJStripSystem`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.StripSystemBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}
  {S : U → U → Set V} {N : U → Set V} {u v : U} {R : List V}

/-! ## Named accessors for the seven axioms -/

/-- Axiom 1: `S_{uv} = S_{vu}` for every edge `uv` of `J`. -/
theorem strip_symm (h : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v) :
    S u v = S v u := h.1 u v huv

/-- Axiom 2: the strips are pairwise disjoint. -/
theorem strip_disjoint (h : IsJStripSystem G J S N) {u v w x : U}
    (huv : J.Adj u v) (hwx : J.Adj w x) (hne : s(u, v) ≠ s(w, x)) :
    Disjoint (S u v) (S w x) := h.2.1 u v w x huv hwx hne

/-- Axiom 3: `N_u` is covered by the strips at `u`. -/
theorem N_subset_iUnion (h : IsJStripSystem G J S N) (u : U) :
    N u ⊆ ⋃ (v : U) (_ : J.Adj u v), S u v := h.2.2.1 u

/-- Axiom 4: every vertex of a strip lies on a rung of that strip. -/
theorem exists_rung (h : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v) {x : V}
    (hx : x ∈ S u v) : ∃ R : List V, IsUVRung G J S N u v R ∧ x ∈ R :=
  h.2.2.2.1 u v huv x hx

/-- Axiom 5: strips on disjoint edges of `J` are anticomplete. -/
theorem strip_anticomplete (h : IsJStripSystem G J S N) {u v w x : U}
    (huv : J.Adj u v) (hwx : J.Adj w x) (hnd : [u, v, w, x].Nodup) :
    Anticomplete G (S u v) (S w x) := h.2.2.2.2.1 u v w x huv hwx hnd

/-- Axiom 6, first half: `N_{uv}` is complete to `N_{uw}` for `v ≠ w`. -/
theorem Nuv_complete (h : IsJStripSystem G J S N) {u v w : U}
    (huv : J.Adj u v) (huw : J.Adj u w) (hvw : v ≠ w) :
    Complete G (N u ∩ S u v) (N u ∩ S u w) := (h.2.2.2.2.2.1 u v w huv huw hvw).1

/-- Axiom 6, second half: there are no other edges between `S_{uv}` and `S_{uw}`. -/
theorem mem_N_of_adj (h : IsJStripSystem G J S N) {u v w : U}
    (huv : J.Adj u v) (huw : J.Adj u w) (hvw : v ≠ w) {a b : V}
    (ha : a ∈ S u v) (hb : b ∈ S u w) (hab : G.Adj a b) : a ∈ N u ∧ b ∈ N u :=
  (h.2.2.2.2.2.1 u v w huv huw hvw).2 a ha b hb hab

/-- Axiom 7: the family of special rungs. -/
theorem exists_special_rungs (h : IsJStripSystem G J S N) :
    ∃ R : U → U → List V,
      (∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v)) ∧
      ∀ c : List U, 3 ≤ c.length → c.Nodup →
        (∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) →
        ((c.zip (c.rotate 1)).map (fun p => pathLength (R p.1 p.2))).sum
          ≡ c.length [MOD 2] := h.2.2.2.2.2.2

/-! ## `V(S,N)` -/

theorem mem_stripSystemVertices_iff {x : V} :
    x ∈ stripSystemVertices J S ↔ ∃ u v : U, J.Adj u v ∧ x ∈ S u v := by
  simp only [stripSystemVertices, Set.mem_iUnion, exists_prop]

theorem strip_subset_vertices {u v : U} (huv : J.Adj u v) :
    S u v ⊆ stripSystemVertices J S := fun _ hx =>
  mem_stripSystemVertices_iff.mpr ⟨u, v, huv, hx⟩

/-- PAPER: *"Hence every `N_v ⊆ V(S,N)`."* (printed p. 40). -/
theorem N_subset_vertices (h : IsJStripSystem G J S N) (u : U) :
    N u ⊆ stripSystemVertices J S := by
  intro x hx
  have := N_subset_iUnion h u hx
  simp only [Set.mem_iUnion] at this
  obtain ⟨v, huv, hxv⟩ := this
  exact strip_subset_vertices huv hxv

theorem Nuv_subset_strip {u v : U} : stripSystemNuv S N u v ⊆ S u v := fun _ hx => hx.2

theorem Nuv_subset_N {u v : U} : stripSystemNuv S N u v ⊆ N u := fun _ hx => hx.1

/-! ## A vertex lies in only one strip -/

/-- The strips are indexed by the *edges* of `J`: a vertex of `G` lies in at most one of
them. -/
theorem edge_eq_of_mem_strips (h : IsJStripSystem G J S N) {u v w x : U} {z : V}
    (huv : J.Adj u v) (hwx : J.Adj w x) (hzuv : z ∈ S u v) (hzwx : z ∈ S w x) :
    s(u, v) = s(w, x) := by
  by_contra hne
  exact (Set.disjoint_left.mp (strip_disjoint h huv hwx hne) hzuv) hzwx

/-- The version of `edge_eq_of_mem_strips` that is convenient at the call sites: two strips
sharing a vertex are the *same set*. -/
theorem strip_eq_of_mem_strips (h : IsJStripSystem G J S N) {u v w x : U} {z : V}
    (huv : J.Adj u v) (hwx : J.Adj w x) (hzuv : z ∈ S u v) (hzwx : z ∈ S w x) :
    S u v = S w x := by
  have := edge_eq_of_mem_strips h huv hwx hzuv hzwx
  rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact strip_symm h huv

/-- PAPER: *"So every vertex of `N_u` belongs to `N_{uv}` for exactly one `v`."*
(printed p. 40). -/
theorem existsUnique_Nuv (h : IsJStripSystem G J S N) {u : U} {x : V} (hx : x ∈ N u) :
    ∃! v : U, J.Adj u v ∧ x ∈ stripSystemNuv S N u v := by
  have hcov := N_subset_iUnion h u hx
  simp only [Set.mem_iUnion] at hcov
  obtain ⟨v, huv, hxv⟩ := hcov
  refine ⟨v, ⟨huv, hx, hxv⟩, ?_⟩
  rintro w ⟨huw, -, hxw⟩
  have := edge_eq_of_mem_strips h huw huv hxw hxv
  rcases Sym2.eq_iff.mp this with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd rfl huv.ne'

/-! ## `N_u ∩ N_v` -/

/-- PAPER: *"It follows that for distinct `u,v ∈ V(J)` … `N_u ∩ N_v ⊆ S_{uv}`"* when `u,v` are
adjacent (printed p. 39). -/
theorem N_inter_N_subset_strip (h : IsJStripSystem G J S N) {u v : U} (hne : u ≠ v)
    (huv : J.Adj u v) : N u ∩ N v ⊆ S u v := by
  rintro z ⟨hzu, hzv⟩
  have h1 := N_subset_iUnion h u hzu
  have h2 := N_subset_iUnion h v hzv
  simp only [Set.mem_iUnion] at h1 h2
  obtain ⟨a, hua, hza⟩ := h1
  obtain ⟨b, hvb, hzb⟩ := h2
  have := edge_eq_of_mem_strips h hua hvb hza hzb
  rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd rfl hne
  · exact hza

/-- PAPER: *"`N_u ∩ N_v` is empty if `u,v` are nonadjacent"* (printed p. 39). -/
theorem N_inter_N_eq_empty (h : IsJStripSystem G J S N) {u v : U} (hne : u ≠ v)
    (huv : ¬ J.Adj u v) : N u ∩ N v = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzu, hzv⟩
  have h1 := N_subset_iUnion h u hzu
  have h2 := N_subset_iUnion h v hzv
  simp only [Set.mem_iUnion] at h1 h2
  obtain ⟨a, hua, hza⟩ := h1
  obtain ⟨b, hvb, hzb⟩ := h2
  have := edge_eq_of_mem_strips h hua hvb hza hzb
  rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne rfl
  · exact huv hua

/-- PAPER: *"and for `uv ∈ E(J)` and `w ∈ V(J)`, if `w ≠ u,v` then `S_{uv} ∩ N_w = ∅`."*
(printed p. 39). -/
theorem strip_inter_N_eq_empty (h : IsJStripSystem G J S N) {u v w : U} (huv : J.Adj u v)
    (hwu : w ≠ u) (hwv : w ≠ v) : S u v ∩ N w = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzs, hzw⟩
  have h1 := N_subset_iUnion h w hzw
  simp only [Set.mem_iUnion] at h1
  obtain ⟨a, hwa, hza⟩ := h1
  have := edge_eq_of_mem_strips h huv hwa hzs hza
  rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hwu rfl
  · exact hwv rfl

/-! ## Rungs -/

theorem rung_adj (hR : IsUVRung G J S N u v R) : J.Adj u v := hR.1

theorem rung_subset_strip (hR : IsUVRung G J S N u v R) : ∀ x ∈ R, x ∈ S u v := by
  obtain ⟨-, s, t, -, hsub, -, -⟩ := hR; exact hsub

theorem rung_isPath (hR : IsUVRung G J S N u v R) :
    ∃ s t : V, IsPathFrom G R s t ∧ (∀ x ∈ R, (x ∈ N u ↔ x = s)) ∧
      (∀ x ∈ R, (x ∈ N v ↔ x = t)) := by
  obtain ⟨-, s, t, hp, -, hs, ht⟩ := hR; exact ⟨s, t, hp, hs, ht⟩

/-- A rung meets `N_u` in exactly one vertex, namely its first end. -/
theorem rung_head_mem_N (hR : IsUVRung G J S N u v R) :
    ∃ s : V, s ∈ R ∧ s ∈ N u ∧ ∀ x ∈ R, x ∈ N u → x = s := by
  obtain ⟨-, s, t, hp, -, hs, -⟩ := hR
  have hsR : s ∈ R := by
    have := hp.2.1
    exact List.mem_of_mem_head? this
  exact ⟨s, hsR, (hs s hsR).mpr rfl, fun x hx hxN => (hs x hx).mp hxN⟩

/-! ## Non-adjacency across disjoint edges of `J` -/

/-- PAPER (proof of 8.6, claim (2)): *"`n₁,n₂` belong to strips `S_{u₁w}`, `S_{vu₂}`, where
`u₁w`, `vu₂` are disjoint edges of `J`; and so `n₁,n₂` are not adjacent in `G`."* -/
theorem not_adj_of_disjoint_edges (h : IsJStripSystem G J S N) {u v w x : U} {a b : V}
    (huv : J.Adj u v) (hwx : J.Adj w x) (hnd : [u, v, w, x].Nodup)
    (ha : a ∈ S u v) (hb : b ∈ S w x) : ¬ G.Adj a b :=
  strip_anticomplete h huv hwx hnd a ha b hb

/-! ## Every strip is nonempty

The last axiom of a `J`-strip system designates a *special* `uv`-rung for **every** edge `uv` of
`J`, and a rung is a path, hence a nonempty list of vertices of `S_{uv}`.  So no strip — and no
`N_{uv}` — is empty.  The paper uses this silently throughout §8 (e.g. in claim (2) of the proof
of 8.6, *"choose `n₁ ∈ N_{u₁w}`, and choose `n₂ ∈ N_{vu₂}`"*, which presupposes that those sets
have members). -/

/-- The head of a rung, packaged: a `uv`-rung has a first vertex, it lies in `N_{uv}`, and it is
the only vertex of the rung in `N_u`. -/
theorem exists_rung_head (hR : IsUVRung G J S N u v R) :
    ∃ s : V, s ∈ R ∧ s ∈ S u v ∧ s ∈ N u ∧ ∀ x ∈ R, x ∈ N u → x = s := by
  obtain ⟨-, s, t, hp, hsub, hs, -⟩ := hR
  have hsR : s ∈ R := List.mem_of_mem_head? hp.2.1
  exact ⟨s, hsR, hsub s hsR, (hs s hsR).mpr rfl, fun x hx hxN => (hs x hx).mp hxN⟩

/-- Dually, the last vertex of a `uv`-rung is its unique vertex in `N_v`. -/
theorem exists_rung_last (hR : IsUVRung G J S N u v R) :
    ∃ t : V, t ∈ R ∧ t ∈ S u v ∧ t ∈ N v ∧ ∀ x ∈ R, x ∈ N v → x = t := by
  obtain ⟨-, s, t, hp, hsub, -, ht⟩ := hR
  have htR : t ∈ R := List.mem_of_getLast? hp.2.2
  exact ⟨t, htR, hsub t htR, (ht t htR).mpr rfl, fun x hx hxN => (ht x hx).mp hxN⟩

/-- The *special* `uv`-rung supplied by the last axiom, for a single edge. -/
theorem exists_uvRung (h : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v) :
    ∃ R : List V, IsUVRung G J S N u v R := by
  obtain ⟨R, hR, -⟩ := exists_special_rungs h
  exact ⟨R u v, hR u v huv⟩

/-- Every strip of a `J`-strip system is nonempty. -/
theorem strip_nonempty (h : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v) :
    (S u v).Nonempty := by
  obtain ⟨R, hR⟩ := exists_uvRung h huv
  obtain ⟨s, -, hsS, -, -⟩ := exists_rung_head hR
  exact ⟨s, hsS⟩

/-- Every `N_{uv}` of a `J`-strip system is nonempty: the `u`-end of any `uv`-rung lies in it. -/
theorem Nuv_nonempty (h : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v) :
    (stripSystemNuv S N u v).Nonempty := by
  obtain ⟨R, hR⟩ := exists_uvRung h huv
  obtain ⟨s, -, hsS, hsN, -⟩ := exists_rung_head hR
  exact ⟨s, hsN, hsS⟩

/-- Every `N_u` is nonempty, provided `u` has a neighbour in `J`. -/
theorem N_nonempty (h : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v) : (N u).Nonempty := by
  obtain ⟨s, hs⟩ := Nuv_nonempty h huv
  exact ⟨s, hs.1⟩

/-! ## `N_u` is the union of the `N_{uv}` -/

/-- PAPER (printed p. 40): *"So every vertex of `N_u` belongs to `N_{uv}` for exactly one `v`."*
The existence half, in the form used at the call sites. -/
theorem mem_Nuv_of_mem_N (h : IsJStripSystem G J S N) {u : U} {x : V} (hx : x ∈ N u) :
    ∃ v : U, J.Adj u v ∧ x ∈ stripSystemNuv S N u v := by
  obtain ⟨v, hv, -⟩ := existsUnique_Nuv h hx
  exact ⟨v, hv.1, hv.2⟩

/-- The uniqueness half: `x ∈ N_u` lies in `N_{uv}` for only one neighbour `v` of `u`. -/
theorem Nuv_eq_of_mem (h : IsJStripSystem G J S N) {u v w : U} {x : V}
    (huv : J.Adj u v) (huw : J.Adj u w) (hv : x ∈ stripSystemNuv S N u v)
    (hw : x ∈ stripSystemNuv S N u w) : v = w := by
  obtain ⟨v₀, -, huniq⟩ := existsUnique_Nuv h hv.1
  rw [huniq v ⟨huv, hv⟩, huniq w ⟨huw, hw⟩]

end Workspace.ProofLemmas.StripSystemBasics
