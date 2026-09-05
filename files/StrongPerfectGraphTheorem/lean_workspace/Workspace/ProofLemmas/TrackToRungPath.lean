import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# The track ↔ path correspondence

Printed p. 19 of *The Strong Perfect Graph Theorem*:

> *"the edge-set of a track becomes the vertex-set of a path"*

and, in the §5/§8 vocabulary, the rung of an appearance `φ : L(H) ≃g G|K` belonging to a track
`T u v` of the subdivision `H` is the `φ`-image of the list of consecutive edges of that track.

The whole content is a triviality that the paper never bothers to state: **two edges of a track
meet exactly when they are consecutive**.  A track carries `Nodup` (no repeated vertex), so the
edge `q[i]q[i+1]` and the edge `q[j]q[j+1]` share an end iff `{i,i+1} ∩ {j,j+1} ≠ ∅`, and they
are distinct iff `i ≠ j`; combining, `L(H)` makes them adjacent iff `|i - j| = 1`.  That is
literally the definition of the list `[e₀, e₁, …]` being an **induced** path of `L(H)`, hence —
transported through `φ`, whose adjacency is `G`-adjacency on the nose — an induced path of `G`
in the sense of `Core.IsPathList`.

The two exports the §8 lane needs are

* `trackRung_exists_isPathFrom` — the `φ`-image of the consecutive-edge list of a track is a
  path of `G` with named ends, i.e. exactly the first conjunct of `StripSystems.IsUVRung`;
* `trackRung_pathLength` — `pathLength (R u v) = trackLength (T u v) - 1`, the length identity
  that turns the parity axiom of a `J`-strip system into a statement about the tracks of `H`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.TrackToRungPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V W : Type*}

/-! ### The list of consecutive edges of a track -/

/-- The `i`-th edge of a track is an edge of the host graph. -/
theorem trackEdge_mem_edgeSet {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (i : ℕ) (hi : i + 1 < q.length) :
    s(q[i]'(by omega), q[i + 1]'hi) ∈ H.edgeSet :=
  (SimpleGraph.mem_edgeSet _).mpr (hq.2.2 i hi)

/-- **The edge-set of a track, as a list of vertices of `L(H)`** (printed p. 19, *"the edge-set
of a track becomes the vertex-set of a path"*).

The consecutive edges `q[0]q[1], q[1]q[2], …` of the track `q`, in order; a track on
`q.length` vertices has `q.length - 1 = trackLength q` of them. -/
def trackEdgeVerts (H : SimpleGraph W) (q : List W) (hq : IsTrackList H q) :
    List ↥H.edgeSet :=
  List.ofFn (n := q.length - 1) fun i =>
    ⟨s(q[i.1]'(by have := i.2; omega), q[i.1 + 1]'(by have := i.2; omega)),
      trackEdge_mem_edgeSet hq i.1 (by have := i.2; omega)⟩

@[simp] theorem trackEdgeVerts_length {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q) :
    (trackEdgeVerts H q hq).length = trackLength q := by
  simp [trackEdgeVerts, trackLength]

theorem trackEdgeVerts_getElem {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (i : ℕ) (hi : i < (trackEdgeVerts H q hq).length) (hi' : i + 1 < q.length)
    (he : s(q[i]'(by omega), q[i + 1]'hi') ∈ H.edgeSet) :
    (trackEdgeVerts H q hq)[i]'hi = ⟨s(q[i]'(by omega), q[i + 1]'hi'), he⟩ := by
  simp only [trackEdgeVerts, List.getElem_ofFn]

/-! ### Two edges of a track meet iff they are consecutive -/

/-- **The whole content of the correspondence.**  For a track `q` of `H`, the `i`-th and `j`-th
edges of `q` are adjacent in the line graph `L(H)` — i.e. they are distinct and share an end —
exactly when `i` and `j` are consecutive.  (`Nodup` of the track is what rules out any other
coincidence: a *chord* of `q` that happens to be an edge of `H` is not an edge of the track.) -/
theorem lineGraph_adj_trackEdge {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (i j : ℕ) (hi : i + 1 < q.length) (hj : j + 1 < q.length)
    (hei : s(q[i]'(by omega), q[i + 1]'hi) ∈ H.edgeSet)
    (hej : s(q[j]'(by omega), q[j + 1]'hj) ∈ H.edgeSet) :
    H.lineGraph.Adj ⟨_, hei⟩ ⟨_, hej⟩ ↔ (i + 1 = j ∨ j + 1 = i) := by
  have hnd : q.Nodup := hq.2.1
  have key : ∀ (a b : ℕ) (ha : a < q.length) (hb : b < q.length),
      (q[a]'ha = q[b]'hb ↔ a = b) := by
    intro a b ha hb
    exact hnd.getElem_inj_iff
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hv1, hv2⟩
    have hij : i ≠ j := by
      rintro rfl
      exact hne rfl
    have h1 : v = q[i]'(by omega) ∨ v = q[i + 1]'hi := by
      simpa using hv1
    have h2 : v = q[j]'(by omega) ∨ v = q[j + 1]'hj := by
      simpa using hv2
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
    · exact absurd ((key _ _ _ _).mp h2) hij
    · exact Or.inr ((key _ _ _ _).mp h2).symm
    · exact Or.inl ((key _ _ _ _).mp h2)
    · exact absurd (Nat.succ_injective ((key _ _ _ _).mp h2)) hij
  · intro h
    have hne : (⟨_, hei⟩ : ↥H.edgeSet) ≠ ⟨_, hej⟩ := by
      intro hcon
      have hcon' : s(q[i]'(by omega), q[i + 1]'hi) = s(q[j]'(by omega), q[j + 1]'hj) :=
        congrArg Subtype.val hcon
      rcases Sym2.eq_iff.mp hcon' with ⟨e1, -⟩ | ⟨e1, e2⟩
      · have : i = j := (key _ _ _ _).mp e1
        omega
      · have p1 : i = j + 1 := (key _ _ _ _).mp e1
        have p2 : i + 1 = j := (key _ _ _ _).mp e2
        omega
    refine ⟨hne, ?_⟩
    rcases h with h | h
    · refine ⟨q[i + 1]'hi, by simp, ?_⟩
      have : q[i + 1]'hi = q[j]'(by omega) := (key _ _ _ _).mpr h
      simp [this]
    · refine ⟨q[j + 1]'hj, ?_, by simp⟩
      have : q[j + 1]'hj = q[i]'(by omega) := (key _ _ _ _).mpr h
      simp [this]

/-! ### The rung: the `φ`-image of the edge list -/

/-- **The rung belonging to a track** (printed p. 19 and, in the §8 vocabulary, p. 40).

Given an appearance `φ : L(H) ≃g G|K` and a track `q` of `H`, this is the list of vertices of
`G` corresponding to the consecutive edges of `q`. -/
def trackRung {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q) : List V :=
  (trackEdgeVerts H q hq).map fun e => (φ e : V)

@[simp] theorem trackRung_length {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q) :
    (trackRung φ q hq).length = trackLength q := by
  simp [trackRung]

/-- **The length identity** the parity axiom of a `J`-strip system needs:
`pathLength (R u v) = trackLength (T u v) - 1`. -/
theorem trackRung_pathLength {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q) :
    pathLength (trackRung φ q hq) = trackLength q - 1 := by
  simp [pathLength, trackRung_length]

/-- Every vertex of the rung lies in `K = V(L(H))`. -/
theorem trackRung_subset_K {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q) :
    ∀ x ∈ trackRung φ q hq, x ∈ K := by
  intro x hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
  exact Subtype.coe_prop _

theorem trackRung_getElem {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q)
    (i : ℕ) (hi : i < (trackRung φ q hq).length) (hi' : i + 1 < q.length)
    (he : s(q[i]'(by omega), q[i + 1]'hi') ∈ H.edgeSet) :
    (trackRung φ q hq)[i]'hi = (φ ⟨s(q[i]'(by omega), q[i + 1]'hi'), he⟩ : V) := by
  have hlen : i < (trackEdgeVerts H q hq).length := by
    simpa [trackRung] using hi
  simp only [trackRung, List.getElem_map]
  rw [trackEdgeVerts_getElem hq i hlen hi' he]

/-! ### The headline theorem -/

/-- **The `φ`-image of the consecutive-edge list of a track is an induced path of `G`**
(printed p. 19, *"the edge-set of a track becomes the vertex-set of a path"*).

`Core.IsPathList` is the paper's *induced* path: non-null, no repeated vertex, and two entries
adjacent in `G` **iff** consecutive in the list.  All three come straight from
`lineGraph_adj_trackEdge`, because the appearance isomorphism `φ` turns `L(H)`-adjacency into
`G`-adjacency on the nose. -/
theorem trackRung_isPathList {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q)
    (hlen : 1 ≤ trackLength q) :
    IsPathList G (trackRung φ q hq) := by
  have hq2 : 2 ≤ q.length := by
    simp only [trackLength] at hlen; omega
  have hL : (trackRung φ q hq).length = q.length - 1 := by
    simp [trackLength]
  -- the value of the `i`-th entry
  have hval : ∀ (i : ℕ) (hi : i < (trackRung φ q hq).length),
      (trackRung φ q hq)[i]'hi
        = (φ ⟨s(q[i]'(by omega), q[i + 1]'(by rw [hL] at hi; omega)),
            trackEdge_mem_edgeSet hq i (by rw [hL] at hi; omega)⟩ : V) := by
    intro i hi
    exact trackRung_getElem φ q hq i hi (by rw [hL] at hi; omega) _
  refine ⟨?_, ?_, ?_⟩
  · -- non-null
    intro hnil
    have : (trackRung φ q hq).length = 0 := by rw [hnil]; rfl
    omega
  · -- no repeated vertex
    refine List.nodup_iff_injective_get.mpr ?_
    intro a b hab
    obtain ⟨i, hi⟩ := a
    obtain ⟨j, hj⟩ := b
    refine Fin.ext ?_
    show i = j
    by_contra hij
    have hcon : (trackRung φ q hq)[i]'hi = (trackRung φ q hq)[j]'hj := hab
    rw [hval i hi, hval j hj] at hcon
    have hcon' : (⟨s(q[i]'(by omega), q[i + 1]'(by rw [hL] at hi; omega)),
        trackEdge_mem_edgeSet hq i (by rw [hL] at hi; omega)⟩ : ↥H.edgeSet)
        = ⟨s(q[j]'(by omega), q[j + 1]'(by rw [hL] at hj; omega)),
            trackEdge_mem_edgeSet hq j (by rw [hL] at hj; omega)⟩ :=
      (EquivLike.injective φ) (Subtype.ext hcon)
    have hsym : s(q[i]'(by omega), q[i + 1]'(by rw [hL] at hi; omega))
        = s(q[j]'(by omega), q[j + 1]'(by rw [hL] at hj; omega)) := congrArg Subtype.val hcon'
    have hnd : q.Nodup := hq.2.1
    rcases Sym2.eq_iff.mp hsym with ⟨e1, -⟩ | ⟨e1, e2⟩
    · exact hij (hnd.getElem_inj_iff.mp e1)
    · have p1 : i = j + 1 := hnd.getElem_inj_iff.mp e1
      have p2 : i + 1 = j := hnd.getElem_inj_iff.mp e2
      omega
  · -- adjacency is exactly consecutiveness
    intro i j hi hj
    rw [hval i hi, hval j hj]
    have hadj : G.Adj
        (φ ⟨s(q[i]'(by omega), q[i + 1]'(by rw [hL] at hi; omega)),
          trackEdge_mem_edgeSet hq i (by rw [hL] at hi; omega)⟩ : V)
        (φ ⟨s(q[j]'(by omega), q[j + 1]'(by rw [hL] at hj; omega)),
          trackEdge_mem_edgeSet hq j (by rw [hL] at hj; omega)⟩ : V)
        ↔ H.lineGraph.Adj
            ⟨s(q[i]'(by omega), q[i + 1]'(by rw [hL] at hi; omega)),
              trackEdge_mem_edgeSet hq i (by rw [hL] at hi; omega)⟩
            ⟨s(q[j]'(by omega), q[j + 1]'(by rw [hL] at hj; omega)),
              trackEdge_mem_edgeSet hq j (by rw [hL] at hj; omega)⟩ :=
      φ.map_rel_iff
    rw [hadj]
    exact lineGraph_adj_trackEdge hq i j (by rw [hL] at hi; omega) (by rw [hL] at hj; omega) _ _

/-- **The form `StripSystems.IsUVRung` asks for**: the rung is a path of `G` with named ends. -/
theorem trackRung_exists_isPathFrom {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q)
    (hlen : 1 ≤ trackLength q) :
    ∃ s t : V, IsPathFrom G (trackRung φ q hq) s t := by
  have hpath := trackRung_isPathList φ q hq hlen
  have hne : trackRung φ q hq ≠ [] := hpath.1
  obtain ⟨s, hs⟩ : ∃ s, (trackRung φ q hq).head? = some s := by
    cases h : trackRung φ q hq with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, by simp⟩
  obtain ⟨t, ht⟩ : ∃ t, (trackRung φ q hq).getLast? = some t :=
    ⟨(trackRung φ q hq).getLast hne, List.getLast?_eq_some_getLast hne⟩
  exact ⟨s, t, hpath, hs, ht⟩

end Workspace.ProofLemmas.TrackToRungPath
