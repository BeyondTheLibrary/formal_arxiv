import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCompose

/-!
# Expanding tracks through a subdivision

The basic expansion operations live in `SubdivisionCompose`.  This module records the two
forms needed by 7.5: an expanded track is a track with the corresponding ends, and two tracks
which meet only in their common ends still meet only in those ends after expansion (provided
at least one of them does not use the common-end edge).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.SubdivisionTrackExpansion

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCompose

variable {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
  {ι : U → W} {T : U → U → List W}

theorem expandTracks_isTrackFrom (hS : SubdivWitness J H ι T)
    {p : List U} {a b : U} (hp : IsTrackFrom J p a b) :
    IsTrackFrom H (expandTracks ι T p) (ι a) (ι b) := by
  have hch : List.IsChain J.Adj p := List.isChain_iff_getElem.mpr hp.1.2.2
  refine ⟨⟨expandTracks_ne_nil hS hch hp.1.1,
    expandTracks_nodup hS p hch hp.1.2.1, ?_⟩, ?_, ?_⟩
  · exact List.isChain_iff_getElem.mp (expandTracks_isChain hS p hch)
  · rw [expandTracks_head? hS p hch, hp.2.1]
    rfl
  · rw [expandTracks_getLast? hS p hch, hp.2.2]
    rfl

private theorem mem_expandTracks_strong (hS : SubdivWitness J H ι T) :
    ∀ (p : List U), List.IsChain J.Adj p → ∀ w : W, w ∈ expandTracks ι T p →
      (∃ x ∈ p, w = ι x) ∨
      (∃ x y : U, s(x, y) ∈ trackEdges p ∧ J.Adj x y ∧
        w ∈ trackInterior (T x y)) := by
  intro p
  induction p with
  | nil => intro _ w hw; simp at hw
  | cons x tail ih =>
    cases tail with
    | nil =>
      intro _ w hw
      rw [expandTracks_singleton] at hw
      exact Or.inl ⟨x, by simp, by simpa using hw⟩
    | cons y rest =>
      intro hch w hw
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      rw [expandTracks_cons_cons] at hw
      rcases List.mem_append.mp hw with hw | hw
      · have hwT : w ∈ T x y := List.dropLast_subset _ hw
        by_cases hint : w ∈ trackInterior (T x y)
        · exact Or.inr ⟨x, y, ⟨0, by simp, rfl⟩, hxy, hint⟩
        · rcases mem_ends_of_mem (track_head? hS hxy) (track_getLast? hS hxy) hwT hint with h | h
          · exact Or.inl ⟨x, by simp, h⟩
          · exact Or.inl ⟨y, by simp, h⟩
      · rcases ih htail w hw with ⟨z, hz, heq⟩ | ⟨z, z', he, hzz', hint⟩
        · exact Or.inl ⟨z, by simp [hz], heq⟩
        · right
          refine ⟨z, z', ?_, hzz', hint⟩
          obtain ⟨i, hi, hEq⟩ := he
          refine ⟨i + 1, by simp only [List.length_cons] at hi ⊢; omega, ?_⟩
          simp only [List.getElem_cons_succ]
          exact hEq

theorem expandTracks_cons_cons_full (hS : SubdivWitness J H ι T)
    (x y : U) (rest : List U) (hxy : J.Adj x y)
    (hch : List.IsChain J.Adj (y :: rest)) :
    expandTracks ι T (x :: y :: rest) =
      T x y ++ (expandTracks ι T (y :: rest)).tail := by
  have hlast : (T x y).dropLast ++ [ι y] = T x y :=
    List.dropLast_append_getLast? (ι y) (track_getLast? hS hxy)
  have hhead : (expandTracks ι T (y :: rest)).head? = some (ι y) := by
    rw [expandTracks_head? hS (y :: rest) hch]
    rfl
  have hsplit : expandTracks ι T (y :: rest) =
      ι y :: (expandTracks ι T (y :: rest)).tail :=
    (List.cons_head?_tail hhead).symm
  calc
    expandTracks ι T (x :: y :: rest)
        = (T x y).dropLast ++ expandTracks ι T (y :: rest) := rfl
    _ = (T x y).dropLast ++ (ι y :: (expandTracks ι T (y :: rest)).tail) := by rw [← hsplit]
    _ = ((T x y).dropLast ++ [ι y]) ++ (expandTracks ι T (y :: rest)).tail := by simp
    _ = T x y ++ (expandTracks ι T (y :: rest)).tail := by rw [hlast]

theorem trackEdges_expandTracks_prefix (hS : SubdivWitness J H ι T)
    {x y : U} {rest : List U} (hxy : J.Adj x y)
    (hch : List.IsChain J.Adj (y :: rest)) :
    trackEdges (T x y) ⊆ trackEdges (expandTracks ι T (x :: y :: rest)) := by
  rw [expandTracks_cons_cons_full hS x y rest hxy hch]
  rintro e ⟨i, hi, rfl⟩
  refine ⟨i, by simp only [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]

/-- Every edge of the subdivision incident with an embedded old vertex belongs to the
subdividing track of an edge incident with the corresponding original vertex. -/
theorem edge_at_embedded_vertex (hS : SubdivWitness J H ι T)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    {x : U} {e : Sym2 W} (he : e ∈ H.edgeSet) (hxe : ι x ∈ e) :
    ∃ y : U, J.Adj x y ∧ e ∈ trackEdges (T x y) := by
  rw [hedges] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨p, q, hpq, heT⟩ := he
  have hxT : ι x ∈ T p q := by
    obtain ⟨i, hi, hEq⟩ := heT
    rw [hEq] at hxe
    rcases Sym2.mem_iff.mp hxe with h | h <;> rw [h] <;> exact List.getElem_mem _
  have hxnot : ι x ∉ trackInterior (T p q) := fun hint =>
    hS.new p q hpq (ι x) hint ⟨x, rfl⟩
  rcases mem_ends_of_mem (track_head? hS hpq) (track_getLast? hS hpq) hxT hxnot with h | h
  · have hxp : x = p := hS.inj h
    subst p
    exact ⟨q, hpq, heT⟩
  · have hxq : x = q := hS.inj h
    subst q
    refine ⟨p, hpq.symm, ?_⟩
    rw [hS.rev p x hpq, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    exact heT

private theorem mem_of_mem_trackEdges {l : List U} {e : Sym2 U}
    (he : e ∈ trackEdges l) {x : U} (hx : x ∈ e) : x ∈ l := by
  obtain ⟨i, hi, hEq⟩ := he
  rw [hEq] at hx
  rcases Sym2.mem_iff.mp hx with hx | hx <;> rw [hx] <;> exact List.getElem_mem _

/-- Expansion preserves the assertion that two common-end tracks otherwise have no common
vertices.  The extra condition excludes the only exceptional subdivision track: the edge
joining the two common ends themselves. -/
theorem expandTracks_meet_only_ends (hS : SubdivWitness J H ι T)
    {p q : List U} {a b : U}
    (hp : IsTrackFrom J p a b) (hq : IsTrackFrom J q a b)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a ∨ z = b)
    (havoid : s(a, b) ∉ trackEdges p ∨ s(a, b) ∉ trackEdges q) :
    ∀ w ∈ expandTracks ι T p, w ∈ expandTracks ι T q → w = ι a ∨ w = ι b := by
  have hpch : List.IsChain J.Adj p := List.isChain_iff_getElem.mpr hp.1.2.2
  have hqch : List.IsChain J.Adj q := List.isChain_iff_getElem.mpr hq.1.2.2
  intro w hwp hwq
  rcases mem_expandTracks_strong hS p hpch w hwp with
      ⟨x, hxp, hwx⟩ | ⟨x, y, hxyP, hxy, hwint⟩
  · rcases mem_expandTracks_strong hS q hqch w hwq with
        ⟨x', hxq, hwx'⟩ | ⟨x', y', hx'y'Q, hx'y', hwint'⟩
    · have hxx' : x = x' := hS.inj (hwx.symm.trans hwx')
      rcases hmeet x hxp (hxx' ▸ hxq) with rfl | rfl
      · exact Or.inl hwx
      · exact Or.inr hwx
    · exact False.elim (hS.new x' y' hx'y' w hwint' ⟨x, hwx.symm⟩)
  · rcases mem_expandTracks_strong hS q hqch w hwq with
        ⟨x', hxq, hwx'⟩ | ⟨x', y', hx'y'Q, hx'y', hwint'⟩
    · exact False.elim (hS.new x y hxy w hwint ⟨x', hwx'.symm⟩)
    · by_cases hedges : s(x, y) = s(x', y')
      · have hxP : x ∈ p := mem_of_mem_trackEdges hxyP (by simp)
        have hyP : y ∈ p := mem_of_mem_trackEdges hxyP (by simp)
        have hxq : x ∈ q := mem_of_mem_trackEdges hx'y'Q (by rw [← hedges]; simp)
        have hyq : y ∈ q := mem_of_mem_trackEdges hx'y'Q (by rw [← hedges]; simp)
        have hxend := hmeet x hxP hxq
        have hyend := hmeet y hyP hyq
        have habedge : s(x, y) = s(a, b) := by
          rcases hxend with rfl | rfl <;> rcases hyend with rfl | rfl
          · exact False.elim (hxy.ne rfl)
          · rfl
          · exact Sym2.eq_swap
          · exact False.elim (hxy.ne rfl)
        rcases havoid with havoid | havoid
        · exact False.elim (havoid (habedge ▸ hxyP))
        · exact False.elim (havoid (by rw [← habedge, hedges]; exact hx'y'Q))
      · exact False.elim (hS.disj x y x' y' hxy hx'y' hedges w hwint
          (mem_of_mem_trackInterior hwint'))

end Workspace.ProofLemmas.SubdivisionTrackExpansion
