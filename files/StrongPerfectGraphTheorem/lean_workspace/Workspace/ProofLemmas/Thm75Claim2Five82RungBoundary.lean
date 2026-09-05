import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The boundary of a rung inside its appearance

PAPER (proof of 7.5, claim (2), printed p. 37): *"we replace `Rb₁b₂` by `R′`"*, and (printed
p. 22) *"for each `v ∈ V(J)` let `Nv` be the clique of `L(H)` with vertex set `δ_H(v)`"*.

Deleting a branch and gluing in a new rung needs one dictionary: **which vertices of the old
appearance are adjacent to which vertices of the old rung.**  The answer is that a rung vertex
that is neither of the two rung ends has no neighbour at all outside the rung, and the two rung
ends see exactly the two endpoint cliques.  The reason is entirely local: an internal vertex of
a branch is not a branch-vertex, so it has degree two and both of its edges are branch edges,
and therefore an edge of `H` outside the branch can meet a branch edge only at one of the two
branch ends.

This module proves that dictionary.  It is used to build the case-1 replacement path of 5.8.2,
which reuses a terminal segment of the old rung and therefore has to know the old rung's
attachments in `K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism

variable {V W : Type*}

/-- An internal vertex of a repetition-free list sits at a position strictly between the two
extreme positions.  This is `PathBasics.exists_getElem_of_mem_interior` for tracks, where only
`Nodup` is available. -/
theorem exists_getElem_of_mem_trackInterior {t : List W} (hnd : t.Nodup) {x : W}
    (hx : x ∈ trackInterior t) :
    ∃ (k : ℕ) (hk : k < t.length), 1 ≤ k ∧ k + 2 ≤ t.length ∧ t[k]'hk = x := by
  have hx' : x ∈ SPGT.interior t := hx
  rw [Workspace.ProofLemmas.PathBasics.mem_interior_iff hnd] at hx'
  obtain ⟨hxp, hhd, hlt⟩ := hx'
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hxp
  have hpos : 0 < t.length := by omega
  refine ⟨k, hk, ?_, ?_, hkx⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos, hkx]) hhd
    · exact hk0
  · by_contra hcon
    have hke : k = t.length - 1 := by omega
    subst hke
    refine hlt ?_
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show t.length - 1 < t.length by omega)]
    exact congrArg some hkx

/-- **Every edge of `H` at an internal vertex of a branch is an edge of that branch.**

PAPER (printed p. 19): *"a branch of `H` means a maximal track `P` in `H` such that no internal
vertex of `P` is a branch-vertex"*.  An internal vertex therefore has degree at most two, and
its two track neighbours already use up that degree. -/
theorem incident_mem_trackEdges_of_mem_trackInterior [Finite W] {H : SimpleGraph W}
    {t : List W} (ht : IsBranch H t) {v : W} (hv : v ∈ trackInterior t)
    {e : Sym2 W} (he : e ∈ H.edgeSet) (hve : v ∈ e) : e ∈ trackEdges t := by
  classical
  obtain ⟨k, hk, hk1, hk2, hkv⟩ := exists_getElem_of_mem_trackInterior ht.1.2.1 hv
  have hk1' : k - 1 + 1 < t.length := by omega
  have hk2' : k + 1 < t.length := by omega
  have hidx : k - 1 + 1 = k := by omega
  -- the two track neighbours of `v`
  have hadjL : H.Adj v (t[k - 1]'(by omega)) := by
    have hraw := ht.1.2.2 (k - 1) hk1'
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq t hidx hk1' hk] at hraw
    exact hkv ▸ hraw.symm
  have hadjR : H.Adj v (t[k + 1]'hk2') := by
    have hraw := ht.1.2.2 k hk2'
    exact hkv ▸ hraw
  have hne : (t[k - 1]'(by omega)) ≠ (t[k + 1]'hk2') := by
    intro hcon
    have := ht.1.2.1.getElem_inj_iff.mp hcon
    omega
  -- `v` is not a branch-vertex, so it has no third neighbour
  have hdeg : ¬ (3 ≤ (H.neighborSet v).ncard) := ht.2.1 v hv
  have hsub : ({t[k - 1]'(by omega), t[k + 1]'hk2'} : Set W) ⊆ H.neighborSet v := by
    rintro z (rfl | rfl)
    · exact hadjL
    · exact hadjR
  have hpair : ({t[k - 1]'(by omega), t[k + 1]'hk2'} : Set W).ncard = 2 := Set.ncard_pair hne
  have heq : ({t[k - 1]'(by omega), t[k + 1]'hk2'} : Set W) = H.neighborSet v :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  -- so the other end of `e` is one of them
  have hspec : e = s(v, Workspace.ProofLemmas.Thm82BranchDelta.otherEnd e v) :=
    Workspace.ProofLemmas.Thm82BranchDelta.otherEnd_spec hve
  have hadj : H.Adj v (Workspace.ProofLemmas.Thm82BranchDelta.otherEnd e v) := by
    have : s(v, Workspace.ProofLemmas.Thm82BranchDelta.otherEnd e v) ∈ H.edgeSet := hspec ▸ he
    simpa using this
  have hmem : Workspace.ProofLemmas.Thm82BranchDelta.otherEnd e v ∈
      ({t[k - 1]'(by omega), t[k + 1]'hk2'} : Set W) := by
    rw [heq]; exact hadj
  rcases hmem with hcase | hcase
  · refine ⟨k - 1, hk1', ?_⟩
    rw [hspec, hcase,
      Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq t hidx hk1' hk, ← hkv]
    exact Sym2.eq_swap
  · refine ⟨k, hk2', ?_⟩
    rw [hspec, hcase, ← hkv]

/-- Every vertex of `K` is the label of an edge of `H`. -/
theorem exists_edge_of_mem_K {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {y : V} (hy : y ∈ K) :
    ∃ (f : Sym2 W) (hf : f ∈ H.edgeSet), y = (↑(φ ⟨f, hf⟩) : V) := by
  refine ⟨(φ.symm ⟨y, hy⟩ : H.edgeSet).1, (φ.symm ⟨y, hy⟩ : H.edgeSet).2, ?_⟩
  have : (⟨(φ.symm ⟨y, hy⟩ : H.edgeSet).1, (φ.symm ⟨y, hy⟩ : H.edgeSet).2⟩ : H.edgeSet)
      = φ.symm ⟨y, hy⟩ := rfl
  rw [this]
  simp

/-- **The attachments of a rung inside its own appearance.**

For a branch `t` with ends `b₁, b₂`, a vertex `y` of `K` off the rung of `t` is adjacent to a
rung vertex `x` exactly when `x` is one of the two rung ends and `y` lies in the corresponding
endpoint clique.  In particular no internal rung vertex has a neighbour in `K` off the rung. -/
theorem rung_boundary [Finite W] {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {t : List W} {b₁ b₂ : W}
    (ht : IsBranch H t) (htf : IsTrackFrom H t b₁ b₂) (h2 : 2 ≤ t.length)
    {x y : V} (hx : x ∈ trackRung φ t ht.1) (hyK : y ∈ K) (hy : y ∉ trackRung φ t ht.1) :
    (G.Adj x y ↔
      (x = firstRungVertex φ t ht.1 h2 ∧ y ∈ NSet G H K φ b₁) ∨
      (x = lastRungVertex φ t ht.1 h2 ∧ y ∈ NSet G H K φ b₂)) := by
  classical
  obtain ⟨e, he, het, rfl⟩ := (mem_trackRung_iff φ ht.1).mp hx
  obtain ⟨f, hf, rfl⟩ := exists_edge_of_mem_K φ hyK
  have hfnot : f ∉ trackEdges t := by
    intro hcon
    exact hy ((mem_trackRung_iff φ ht.1).mpr ⟨f, hf, hcon, rfl⟩)
  have hef : (⟨e, he⟩ : H.edgeSet) ≠ ⟨f, hf⟩ := by
    intro hcon
    have hEF : e = f := congrArg Subtype.val hcon
    exact hfnot (hEF ▸ het)
  have hmap : G.Adj (↑(φ ⟨e, he⟩) : V) (↑(φ ⟨f, hf⟩) : V) ↔
      H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff
  rw [hmap, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨-, z, hze, hzf⟩
    -- `z` lies on the branch, and it cannot be an internal vertex, because `f` is not a
    -- branch edge
    have hzt : z ∈ t := by
      obtain ⟨i, hi, hie⟩ := het
      have : z ∈ s(t[i]'(by omega), t[i + 1]'hi) := hie ▸ hze
      rcases Sym2.mem_iff.mp this with rfl | rfl
      · exact List.getElem_mem _
      · exact List.getElem_mem _
    have hznotint : z ∉ trackInterior t := fun hcon =>
      hfnot (incident_mem_trackEdges_of_mem_trackInterior ht hcon hf hzf)
    have hzend : z = b₁ ∨ z = b₂ := by
      by_contra hcon
      push Not at hcon
      refine hznotint ?_
      have : z ∈ SPGT.interior t :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff ht.1.2.1).mpr
          ⟨hzt, by rw [htf.2.1]; simpa using fun h => hcon.1 h.symm,
            by rw [htf.2.2]; simpa using fun h => hcon.2 h.symm⟩
      exact this
    rcases hzend with rfl | rfl
    · left
      refine ⟨congrArg (fun s : H.edgeSet => (↑(φ s) : V))
        (Subtype.ext (edge_eq_firstTrackEdge htf h2 het hze)), ?_⟩
      exact ⟨f, hf, ⟨hf, hzf⟩, rfl⟩
    · right
      refine ⟨congrArg (fun s : H.edgeSet => (↑(φ s) : V))
        (Subtype.ext (edge_eq_lastTrackEdge htf h2 het hze)), ?_⟩
      exact ⟨f, hf, ⟨hf, hzf⟩, rfl⟩
  · rintro (⟨hxe, hyN⟩ | ⟨hxe, hyN⟩)
    · obtain ⟨g, hg, hginc, hgy⟩ := hyN
      have hgf : f = g := congrArg Subtype.val (φ.injective (Subtype.ext hgy))
      have hb₁f : b₁ ∈ f := by rw [hgf]; exact hginc.2
      have hee : e = firstTrackEdge t h2 :=
        congrArg Subtype.val (φ.injective (Subtype.ext hxe))
      have hb₁e : b₁ ∈ e := hee ▸ firstTrackEdge_contains htf h2
      exact ⟨hef, b₁, hb₁e, hb₁f⟩
    · obtain ⟨g, hg, hginc, hgy⟩ := hyN
      have hgf : f = g := congrArg Subtype.val (φ.injective (Subtype.ext hgy))
      have hb₂f : b₂ ∈ f := by rw [hgf]; exact hginc.2
      have hee : e = lastTrackEdge t h2 :=
        congrArg Subtype.val (φ.injective (Subtype.ext hxe))
      have hb₂e : b₂ ∈ e := hee ▸ lastTrackEdge_contains htf h2
      exact ⟨hef, b₂, hb₂e, hb₂f⟩

end Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary
