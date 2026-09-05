import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# A degenerate `K₄`-subdivision is two disjoint odd tracks plus four cross edges

This module supplies the second sentence of the proof of 5.3 (printed p. 19):

> *"… and we may assume that it does not satisfy the theorem.  **Hence there are tracks
> `p₁-⋯-p_m` (`= P` say) and `q₁-⋯-q_n` (`= Q` say) of `H`, vertex-disjoint, such that `p₁q₁`,
> `p₁q_n`, `p_mq₁`, `p_mq_n` are edges, and `m, n ≥ 3` are odd.**"*

The mathematics.  Let `D` be a bipartite subdivision of `K₄`, with branch-vertex embedding
`ι : Fin 4 → V(D)` and tracks `T u v`.  `DegenerateK4Appearance D` gives a four-cycle
`a-b-c-d-a` of `D` containing every branch-vertex.  Since `branchVertices D = Set.range ι`
(`SubdivisionCounting.range_subset_branchVertices` and the degenerate cycle's own inclusion,
both sides having `ncard` 4), the four cycle vertices *are* the four branch-vertices, say
`a = ι α`, `b = ι β`, `c = ι γ`, `d = ι δ` with `α, β, γ, δ` pairwise distinct.  The two
**diagonal** tracks

```
P := T α γ        Q := T β δ
```

are then the paper's `P` and `Q`.

* **Vertex-disjoint.**  A common vertex is not interior to `P` (the tracks of a subdivision are
  disjoint except at their ends, and `s(α,γ) ≠ s(β,δ)`), so it is an end of `P`, hence lies in
  `Set.range ι`; but the interior of `Q` misses `Set.range ι`, so it is an end of `Q` too — and
  `{α,γ}` is disjoint from `{β,δ}`.
* **`m` odd.**  The four cycle edges are edges of `D`, so `a-P-c` closed up through `b` is a
  cycle of length `|P| + 1`; as `D` is bipartite, `|P|` is odd.  Together with `|P| ≥ 2` (a
  track of a subdivision has at least one edge) this gives `m = |P| ≥ 3`.

**Note.**  The four cycle edges are *not* needed as length-one tracks: it is tempting (and the
picture suggests) to first prove that each of `T α β`, `T β γ`, `T γ δ`, `T δ α` has exactly two
vertices, but nothing downstream uses it.  The cross edges of the conclusion are literally the
four edges `hab`, `hbc`, `hcd`, `hda` of the degenerate cycle, read through `ι`, and the parity
argument only needs two of them per track.  Dropping that step removes the whole
`D.edgeSet = ⋃ trackEdges` analysis from this module.

Bipartiteness is used through a **2-colouring**, not through walks: `track_color` says the
colour along a track alternates, so `col q[i] ≡ col q[0] + i (mod 2)`.  That avoids having to
turn a track into a `SimpleGraph.Walk` (Mathlib's `two_colorable_iff_forall_loop_even` would
otherwise be the entry point, and building the walk from a list is more work than the whole
alternation lemma).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.DegenerateK4Tracks

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {X : Type*}

/-! ### Small facts about tracks -/

/-- The last vertex of a track named by `IsTrackFrom`, at arbitrary length.
(`SubdivisionCounting.track_last` is the special case of a two-vertex track.) -/
theorem track_getLast {D : SimpleGraph X} {q : List X} {a b : X}
    (h : IsTrackFrom D q a b) (hlen : 0 < q.length) :
    q[q.length - 1]'(by omega) = b := by
  have h' := h.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
  exact Option.some_injective _ h'

/-- A vertex of a track which is not an internal vertex is one of the two ends. -/
theorem mem_ends_of_notMem_interior {q : List X} {x : X} (hx : x ∈ q)
    (hnot : x ∉ trackInterior q) (h0 : 0 < q.length) :
    x = q[0]'h0 ∨ x = q[q.length - 1]'(by omega) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  by_contra hc
  push Not at hc
  have hk0 : k ≠ 0 := by rintro rfl; exact hc.1 rfl
  have hkl : k ≠ q.length - 1 := fun h =>
    hc.2 (getElem_eq_of_index_eq q h hk (by omega))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hnot (mem_trackInterior_getElem q j (by omega))

/-- **Colours alternate along a track.**  In a proper 2-colouring, the colour of the `i`-th
vertex of a track differs from the colour of its first vertex exactly by the parity of `i`. -/
theorem track_color {D : SimpleGraph X} (col : D.Coloring (Fin 2))
    {q : List X} (hq : IsTrackList D q) :
    ∀ (i : ℕ) (hi : i < q.length) (h0 : 0 < q.length),
      ((col (q[i]'hi) : ℕ) + i) % 2 = ((col (q[0]'h0) : ℕ)) % 2 := by
  intro i
  induction i with
  | zero => intro hi h0; simp
  | succ k ih =>
      intro hi h0
      have hk : k < q.length := by omega
      have hadj : D.Adj (q[k]'hk) (q[k + 1]'hi) := hq.2.2 k (by omega)
      have hne : col (q[k]'hk) ≠ col (q[k + 1]'hi) := col.valid hadj
      have hne' : ((col (q[k]'hk) : ℕ)) ≠ ((col (q[k + 1]'hi) : ℕ)) := fun h =>
        hne (Fin.val_injective h)
      have h1 := (col (q[k]'hk)).isLt
      have h2 := (col (q[k + 1]'hi)).isLt
      have h3 := ih hk h0
      omega

/-! ### The main extraction -/

/-- **5.3, second sentence.**  A *degenerate* bipartite subdivision `D` of `K₄` consists of two
vertex-disjoint tracks `P`, `Q`, both of odd order at least `3`, whose four ends are joined by
the four edges `p₁q₁`, `p₁q_n`, `p_mq₁`, `p_mq_n`.

The order of the conclusion's four adjacencies matches the paper's `p₁q₁`, `p₁q_n`, `p_mq₁`,
`p_mq_n`.  The paper's `m` and `n` are the *vertex counts* `P.length`, `Q.length` (a track
`p₁-⋯-p_m` has `m` vertices and length `m - 1`), so it is those that are odd. -/
theorem exists_two_tracks_of_degenerate [Finite X] {D : SimpleGraph X}
    (hbip : D.IsBipartite)
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) D)
    (hdegen : DegenerateK4Appearance D) :
    ∃ (P Q : List X) (_hP : 3 ≤ P.length) (_hQ : 3 ≤ Q.length),
      IsTrackList D P ∧ IsTrackList D Q ∧
      (∀ x ∈ P, x ∉ Q) ∧
      Odd P.length ∧ Odd Q.length ∧
      D.Adj P[0] Q[0] ∧
      D.Adj P[0] Q[Q.length - 1] ∧
      D.Adj P[P.length - 1] Q[0] ∧
      D.Adj P[P.length - 1] Q[Q.length - 1] := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, -, hdisjint, hnew, -, -⟩ := hsub
  obtain ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hbr⟩ := hdegen
  obtain ⟨col⟩ := hbip
  -- The four cycle vertices are pairwise distinct.
  have dab : a ≠ b := by rintro rfl; simp at hnd
  have dac : a ≠ c := by rintro rfl; simp at hnd
  have dad : a ≠ d := by rintro rfl; simp at hnd
  have dbc : b ≠ c := by rintro rfl; simp at hnd
  have dbd : b ≠ d := by rintro rfl; simp at hnd
  have dcd : c ≠ d := by rintro rfl; simp at hnd
  -- `Set.range ι = branchVertices D = {a, b, c, d}` : both sides have four elements.
  have hdeg4 : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    three_le_degree_of_three_connected (⊤ : SimpleGraph (Fin 4)) k4_three_connected
  have hA : Set.range ι ⊆ branchVertices D :=
    range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg4
  have hcard1 : (Set.range ι).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hι, Set.ncard_univ]
    simp
  have hcard2 : ({a, b, c, d} : Set X).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [dab, dac, dad]),
      Set.ncard_insert_of_notMem (by simp [dbc, dbd]),
      Set.ncard_insert_of_notMem (by simp [dcd]), Set.ncard_singleton]
  have hrange : Set.range ι = ({a, b, c, d} : Set X) :=
    Set.eq_of_subset_of_ncard_le (hA.trans hbr) (by omega) (Set.toFinite _)
  obtain ⟨α, hα⟩ : a ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨β, hβ⟩ : b ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨γ, hγ⟩ : c ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨δ, hδ⟩ : d ∈ Set.range ι := by rw [hrange]; simp
  -- and so the four indices are pairwise distinct.
  have iαβ : α ≠ β := fun h => dab (by rw [← hα, ← hβ, h])
  have iαγ : α ≠ γ := fun h => dac (by rw [← hα, ← hγ, h])
  have iαδ : α ≠ δ := fun h => dad (by rw [← hα, ← hδ, h])
  have iβγ : β ≠ γ := fun h => dbc (by rw [← hβ, ← hγ, h])
  have iβδ : β ≠ δ := fun h => dbd (by rw [← hβ, ← hδ, h])
  have iγδ : γ ≠ δ := fun h => dcd (by rw [← hγ, ← hδ, h])
  have eαγ : (⊤ : SimpleGraph (Fin 4)).Adj α γ := by rw [SimpleGraph.top_adj]; exact iαγ
  have eβδ : (⊤ : SimpleGraph (Fin 4)).Adj β δ := by rw [SimpleGraph.top_adj]; exact iβδ
  -- The two diagonal tracks.
  have hPlen : 2 ≤ (T α γ).length := by
    have := hlen α γ eαγ; simp only [trackLength] at this; omega
  have hQlen : 2 ≤ (T β δ).length := by
    have := hlen β δ eβδ; simp only [trackLength] at this; omega
  have hPfirst : (T α γ)[0]'(by omega) = a := by
    rw [track_head (htrack α γ eαγ) (by omega)]; exact hα
  have hPlast : (T α γ)[(T α γ).length - 1]'(by omega) = c := by
    rw [track_getLast (htrack α γ eαγ) (by omega)]; exact hγ
  have hQfirst : (T β δ)[0]'(by omega) = b := by
    rw [track_head (htrack β δ eβδ) (by omega)]; exact hβ
  have hQlast : (T β δ)[(T β δ).length - 1]'(by omega) = d := by
    rw [track_getLast (htrack β δ eβδ) (by omega)]; exact hδ
  -- Parity of the two tracks, from the 2-colouring.
  have vala := (col a).isLt
  have valb := (col b).isLt
  have valc := (col c).isLt
  have vald := (col d).isLt
  have nab : ((col a : ℕ)) ≠ ((col b : ℕ)) := fun h => col.valid hab (Fin.val_injective h)
  have nbc : ((col b : ℕ)) ≠ ((col c : ℕ)) := fun h => col.valid hbc (Fin.val_injective h)
  have ncd : ((col c : ℕ)) ≠ ((col d : ℕ)) := fun h => col.valid hcd (Fin.val_injective h)
  have hcolP := track_color col (htrack α γ eαγ).1 ((T α γ).length - 1) (by omega) (by omega)
  have hcolQ := track_color col (htrack β δ eβδ).1 ((T β δ).length - 1) (by omega) (by omega)
  rw [hPfirst, hPlast] at hcolP
  rw [hQfirst, hQlast] at hcolQ
  have hoddP : Odd (T α γ).length := by rw [Nat.odd_iff]; omega
  have hoddQ : Odd (T β δ).length := by rw [Nat.odd_iff]; omega
  -- Vertex-disjointness of the two diagonal tracks.
  have hsne : s(α, γ) ≠ s(β, δ) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact iαβ h1
    · exact iαδ h1
  have hdisjPQ : ∀ x ∈ T α γ, x ∉ T β δ := by
    intro x hxP hxQ
    have hnotP : x ∉ trackInterior (T α γ) := fun hc =>
      hdisjint α γ β δ eαγ eβδ hsne _ hc hxQ
    have hrng : x ∈ Set.range ι := by
      rcases mem_ends_of_notMem_interior hxP hnotP (by omega) with h | h
      · exact ⟨α, by rw [hα]; rw [h, hPfirst]⟩
      · exact ⟨γ, by rw [hγ]; rw [h, hPlast]⟩
    have hnotQ : x ∉ trackInterior (T β δ) := fun hc => hnew β δ eβδ _ hc hrng
    rcases mem_ends_of_notMem_interior hxQ hnotQ (by omega) with h | h
    · rw [hQfirst] at h
      rcases mem_ends_of_notMem_interior hxP hnotP (by omega) with h' | h'
      · rw [hPfirst] at h'; exact dab (h'.symm.trans h)
      · rw [hPlast] at h'; exact dbc (h.symm.trans h')
    · rw [hQlast] at h
      rcases mem_ends_of_notMem_interior hxP hnotP (by omega) with h' | h'
      · rw [hPfirst] at h'; exact dad (h'.symm.trans h)
      · rw [hPlast] at h'; exact dcd (h'.symm.trans h)
  refine ⟨T α γ, T β δ, by omega, by omega, (htrack α γ eαγ).1, (htrack β δ eβδ).1,
    hdisjPQ, hoddP, hoddQ, ?_, ?_, ?_, ?_⟩
  · rw [hPfirst, hQfirst]; exact hab
  · rw [hPfirst, hQlast]; exact hda.symm
  · rw [hPlast, hQfirst]; exact hbc.symm
  · rw [hPlast, hQlast]; exact hcd

/-! ### The form 5.3 consumes: a subgraph of the host graph -/

/-- A track of a subgraph `S` of `H` is a track of `H`, read along `Subtype.val`. -/
theorem isTrackList_val {W : Type*} {H : SimpleGraph W} {S : H.Subgraph} {q : List ↥S.verts}
    (hq : IsTrackList S.coe q) : IsTrackList H (q.map Subtype.val) := by
  have hne : q.map Subtype.val ≠ [] := by
    cases q with
    | nil => exact absurd rfl hq.1
    | cons x t => exact List.cons_ne_nil _ _
  refine ⟨hne, hq.2.1.map Subtype.val_injective, ?_⟩
  intro i hi
  have hi' : i + 1 < q.length := by simpa using hi
  simpa using S.adj_sub (hq.2.2 i hi')

/-- **5.3, second sentence, as 5.3 uses it.**  In a bipartite `H`, a *degenerate*
`K₄`-subdivision subgraph `S` yields the paper's two vertex-disjoint tracks `P`, `Q` **of `H`**,
of odd order at least `3`, with the four cross edges `p₁q₁`, `p₁q_n`, `p_mq₁`, `p_mq_n`. -/
theorem exists_two_tracks_of_degenerate_subgraph {W : Type*} [Finite W] {H : SimpleGraph W}
    (hbip : H.IsBipartite) (S : H.Subgraph)
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe)
    (hdegen : DegenerateK4Appearance S.coe) :
    ∃ (P Q : List W) (_hP : 3 ≤ P.length) (_hQ : 3 ≤ Q.length),
      IsTrackList H P ∧ IsTrackList H Q ∧
      (∀ x ∈ P, x ∉ Q) ∧
      Odd P.length ∧ Odd Q.length ∧
      H.Adj P[0] Q[0] ∧
      H.Adj P[0] Q[Q.length - 1] ∧
      H.Adj P[P.length - 1] Q[0] ∧
      H.Adj P[P.length - 1] Q[Q.length - 1] := by
  have hbip' : S.coe.IsBipartite :=
    SimpleGraph.Colorable.of_hom (subgraphCopy S).toHom hbip
  obtain ⟨P, Q, hP, hQ, htP, htQ, hdisj, hoP, hoQ, e1, e2, e3, e4⟩ :=
    exists_two_tracks_of_degenerate hbip' hsub hdegen
  refine ⟨P.map Subtype.val, Q.map Subtype.val, by simpa using hP, by simpa using hQ,
    isTrackList_val htP, isTrackList_val htQ, ?_, by simpa using hoP, by simpa using hoQ,
    ?_, ?_, ?_, ?_⟩
  · rintro x hx hxQ
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, hvu⟩ := List.mem_map.mp hxQ
    exact hdisj u hu (by rw [← Subtype.val_injective hvu]; exact hv)
  · simpa using S.adj_sub e1
  · simpa using S.adj_sub e2
  · simpa using S.adj_sub e3
  · simpa using S.adj_sub e4

end Workspace.ProofLemmas.DegenerateK4Tracks
