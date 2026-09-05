import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.RungReplacementLabelled

/-!
# A rung has as many vertices as its track has edges

PAPER (printed p. 19): *"the edge-set of a track becomes the vertex-set of a path"*.

`Workspace.ProofLemmas.TrackToRungPath` builds, from a track `q` of `H`, the *ordered* rung
`trackRung φ q`, and proves that it is an induced path of `G` with `trackLength q` vertices.
The §7 statements instead name an unordered rung: a path `R` of `G` together with the equation
`{x | x ∈ R} = rungSet G H K φ q`.  This module connects the two.

The only content is that both lists have no repeated vertex, so a common vertex *set* forces a
common length.  That gives the length dictionary

> `R.length = trackLength q`,  equivalently  `pathLength R + 1 = trackLength q`,

which is what turns the paper's *"`Bc₁c₂` is odd"* into *"`Rc₁c₂` is even"*.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementRungLength

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.RungReplacementLabelled

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- A path with two distinct ends has at least two vertices. -/
theorem two_le_length_of_ends_ne {V : Type*} {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (huv : u ≠ v) : 2 ≤ p.length := by
  have hpos : 0 < p.length := Workspace.ProofLemmas.PathBasics.path_length_pos hp.1
  by_contra hcon
  have h1 : p.length = 1 := by omega
  have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  exact huv (((gidx p (show (0 : ℕ) = p.length - 1 by omega) hpos (by omega)).symm.trans
    h0).symm.trans hl)

/-- The vertex set of a list without repeats has as many elements as the list. -/
theorem ncard_setOf_mem {α : Type*} (l : List α) (h : l.Nodup) :
    {x : α | x ∈ l}.ncard = l.length := by
  classical
  have hset : {x : α | x ∈ l} = (↑l.toFinset : Set α) := by ext x; simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup h]

/-- The unordered rung of a track is the vertex set of its ordered rung. -/
theorem rungSet_eq_trackRung {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q) :
    rungSet G H K φ q = {x : V | x ∈ TrackToRungPath.trackRung φ q hq} := by
  have hlen : (TrackToRungPath.trackRung φ q hq).length = q.length - 1 := by
    rw [TrackToRungPath.trackRung_length]; rfl
  ext x
  constructor
  · rintro ⟨e, he, ⟨i, hi, rfl⟩, rfl⟩
    have hidx : i < (TrackToRungPath.trackRung φ q hq).length := by rw [hlen]; omega
    have hget := TrackToRungPath.trackRung_getElem φ q hq i hidx hi he
    rw [← hget]
    exact List.getElem_mem _
  · intro hx
    obtain ⟨i, hidx, hxi⟩ := List.mem_iff_getElem.mp hx
    have hi : i + 1 < q.length := by rw [hlen] at hidx; omega
    have he : s(q[i]'(by omega), q[i + 1]'hi) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hq i hi
    refine ⟨s(q[i]'(by omega), q[i + 1]'hi), he, ⟨i, hi, rfl⟩, ?_⟩
    rw [← hxi]
    exact TrackToRungPath.trackRung_getElem φ q hq i hidx hi he

/-- **The length dictionary.**  A path of `G` whose vertex set is the rung of a track `q` has
exactly `trackLength q` vertices. -/
theorem rung_length_eq_trackLength {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    (q : List W) (hq : IsTrackList H q) (hlen : 1 ≤ trackLength q)
    (R : List V) (hR : IsPathList G R) (hRset : {x : V | x ∈ R} = rungSet G H K φ q) :
    R.length = trackLength q := by
  have h1 : {x : V | x ∈ R} = {x : V | x ∈ TrackToRungPath.trackRung φ q hq} :=
    hRset.trans (rungSet_eq_trackRung φ q hq)
  have hnd : (TrackToRungPath.trackRung φ q hq).Nodup :=
    (TrackToRungPath.trackRung_isPathList φ q hq hlen).2.1
  have hcard := congrArg Set.ncard h1
  rw [ncard_setOf_mem R hR.2.1, ncard_setOf_mem _ hnd,
    TrackToRungPath.trackRung_length] at hcard
  exact hcard

/-- The same statement as a parity dictionary: an odd branch has an even rung. -/
theorem even_pathLength_of_odd_trackLength {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    (q : List W) (hq : IsTrackList H q) (hodd : Odd (trackLength q))
    (R : List V) (hR : IsPathList G R) (hRset : {x : V | x ∈ R} = rungSet G H K φ q) :
    Even (pathLength R) := by
  have h1 : 1 ≤ trackLength q := by
    rcases hodd with ⟨k, hk⟩; omega
  have hL := rung_length_eq_trackLength φ q hq h1 R hR hRset
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  simp only [pathLength, hL, hk]
  omega

end Workspace.ProofLemmas.RungReplacementRungLength
