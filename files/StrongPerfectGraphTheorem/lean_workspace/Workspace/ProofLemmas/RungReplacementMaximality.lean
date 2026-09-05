import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.RungReplacementBranchFacts

/-!
# When a track is a branch

PAPER (printed p. 19): *"a branch of `H` means a maximal track `P` in `H` such that no internal
vertex of `P` is a branch-vertex."*

Checking that a concrete track is a branch means checking maximality, which is the only clause
of `Workspace.Types.Tracks.IsBranch` that quantifies over all other tracks.  This module proves
the criterion that every use in the paper actually needs:

> a track whose internal vertices are not branch-vertices and whose **two ends are**
> branch-vertices is a branch.

The reason is that a competing track `P'` containing `P` cannot have an end of `P` in its
interior, so `P` and `P'` have the same ends, and then a step-by-step comparison shows they are
the same list.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementMaximality

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {Z : Type*} {D : SimpleGraph Z}

/-- A track whose edges are all edges of a second track, and which starts at the same vertex,
agrees with it position by position. -/
theorem getElem_eq_of_trackEdges_subset {t t' : List Z} (hnd : t.Nodup) (hnd' : t'.Nodup)
    (hpos : 0 < t.length) (hpos' : 0 < t'.length)
    (h0 : t[0]'hpos = t'[0]'hpos')
    (hsub : trackEdges t ⊆ trackEdges t') :
    ∀ (i : ℕ) (hi : i < t.length), ∃ hi' : i < t'.length, t[i]'hi = t'[i]'hi' := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i with
    | 0 => exact ⟨hpos', h0⟩
    | (k + 1) =>
      obtain ⟨hk', hk⟩ := ih k (by omega) (by omega)
      obtain ⟨m, hm, hme⟩ := hsub ⟨k, hi, rfl⟩
      rcases Sym2.eq_iff.mp hme with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hkm : k = m := hnd'.getElem_inj_iff.mp (by rw [← hk, h1])
        subst hkm
        exact ⟨hm, h2⟩
      · exfalso
        have hkm : k = m + 1 := hnd'.getElem_inj_iff.mp (by rw [← hk, h1])
        have hmpos : 0 < k := by omega
        obtain ⟨hm', hmv⟩ := ih (k - 1) (by omega) (by omega)
        have hme' : t[k - 1]'(by omega) = t[k + 1]'hi := by
          rw [hmv, h2]
          exact getElem_eq_of_index_eq t' (by omega) hm' (by omega)
        have := hnd.getElem_inj_iff.mp hme'
        omega

/-- Two tracks with the same ends, one of whose edge sets contains the other's, are equal. -/
theorem eq_of_trackEdges_subset {t t' : List Z} {u v : Z}
    (ht : IsTrackFrom D t u v) (ht' : IsTrackFrom D t' u v)
    (hsub : trackEdges t ⊆ trackEdges t') : t = t' := by
  have hpos : 0 < t.length := List.length_pos_of_ne_nil ht.1.1
  have hpos' : 0 < t'.length := List.length_pos_of_ne_nil ht'.1.1
  have h0 : t[0]'hpos = t'[0]'hpos' := by
    rw [track_head ht hpos, track_head ht' hpos']
  have hL : t[t.length - 1]'(by omega) = v := by
    have h' := ht.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  have hL' : t'[t'.length - 1]'(by omega) = v := by
    have h' := ht'.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  have hkey := getElem_eq_of_trackEdges_subset ht.1.2.1 ht'.1.2.1 hpos hpos' h0 hsub
  obtain ⟨hlt, hval⟩ := hkey (t.length - 1) (by omega)
  have hlen : t.length = t'.length := by
    have : t'[t.length - 1]'hlt = t'[t'.length - 1]'(by omega) := by rw [← hval, hL, hL']
    have := ht'.1.2.1.getElem_inj_iff.mp this
    omega
  refine List.ext_getElem hlen ?_
  intro i hi hi'
  obtain ⟨hh, h⟩ := hkey i hi
  exact h

/-- **A track with branch-vertex ends and no branch-vertex inside is a branch.** -/
theorem isBranch_of_ends {t : List Z} {u v : Z} (ht : IsTrackFrom D t u v)
    (h2 : 2 ≤ t.length) (hint : ∀ x ∈ trackInterior t, x ∉ branchVertices D)
    (hu : u ∈ branchVertices D) (hv : v ∈ branchVertices D) : IsBranch D t := by
  refine ⟨ht.1, hint, ?_⟩
  intro t' ht' hint' hsub hmem
  have hpos' : 0 < t'.length := List.length_pos_of_ne_nil ht'.1
  have hu' : u ∈ t' := hmem u (List.mem_of_mem_head? ht.2.1)
  have hv' : v ∈ t' := hmem v (List.mem_of_mem_getLast? ht.2.2)
  have huv : u ≠ v := by
    intro hcon
    have hpos : 0 < t.length := by omega
    have h0 : t[0]'hpos = u := track_head ht hpos
    have hL : t[t.length - 1]'(by omega) = v := by
      have h' := ht.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
      exact Option.some_injective _ h'
    have := ht.1.2.1.getElem_inj_iff.mp (show t[0]'hpos = t[t.length - 1]'(by omega) by
      rw [h0, hL, hcon])
    omega
  -- `t'` has at least two vertices, since it contains the two distinct vertices `u` and `v`
  have h2' : 2 ≤ t'.length := by
    by_contra hcon
    have hlen1 : t'.length = 1 := by omega
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen1
    simp only [List.mem_singleton] at hu' hv'
    exact huv (hu'.trans hv'.symm)
  have h0' : t'[0]'hpos' = u ∨ t'[0]'hpos' = v := by
    have hb0 : ∀ w : Z, w ∈ t' → w ∈ branchVertices D →
        w = t'[0]'hpos' ∨ w = t'[t'.length - 1]'(by omega) := by
      intro w hw hwb
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact Or.inl rfl
      · rcases Nat.lt_or_ge j (t'.length - 1) with hlt | hge
        · exfalso
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          exact hint' _ (mem_trackInterior_getElem t' k (by omega)) hwb
        · exact Or.inr (getElem_eq_of_index_eq t' (by omega) hj (by omega))
    rcases hb0 u hu' hu with h | h
    · exact Or.inl h.symm
    · rcases hb0 v hv' hv with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) huv
  have hlast' : ∀ (h : t'[0]'hpos' = u), t'[t'.length - 1]'(by omega) = v := by
    intro h
    have hb0 : v = t'[0]'hpos' ∨ v = t'[t'.length - 1]'(by omega) := by
      obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv'
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact Or.inl hjv.symm
      · rcases Nat.lt_or_ge j (t'.length - 1) with hlt | hge
        · exfalso
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          exact hint' _ (mem_trackInterior_getElem t' k (by omega)) (hjv ▸ hv)
        · exact Or.inr (by rw [← hjv]; exact getElem_eq_of_index_eq t' (by omega) hj (by omega))
    rcases hb0 with hc | hc
    · exact absurd (h.symm.trans hc.symm) huv
    · exact hc.symm
  rcases h0' with hstart | hstart
  · have ht'f : IsTrackFrom D t' u v := by
      refine ⟨ht', ?_, ?_⟩
      · rw [List.head?_eq_getElem? , List.getElem?_eq_getElem hpos', hstart]
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), hlast' hstart]
    rw [eq_of_trackEdges_subset ht ht'f hsub]
  · -- `t'` runs the other way; compare with its reverse
    have hrevpos : 0 < t'.reverse.length := by simpa using hpos'
    have hrev0 : t'.reverse[0]'hrevpos = t'[t'.length - 1]'(by omega) := by
      rw [List.getElem_reverse]
      exact getElem_eq_of_index_eq t' (by omega) (by omega) (by omega)
    have hrevL : t'.reverse[t'.reverse.length - 1]'(by omega) = t'[0]'hpos' := by
      rw [List.getElem_reverse]
      exact getElem_eq_of_index_eq t' (by simp) (by omega) (by omega)
    have hrevu : t'[t'.length - 1]'(by omega) = u := by
      have hb0 : u = t'[0]'hpos' ∨ u = t'[t'.length - 1]'(by omega) := by
        obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu'
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact Or.inl hju.symm
        · rcases Nat.lt_or_ge j (t'.length - 1) with hlt | hge
          · exfalso
            obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
            exact hint' _ (mem_trackInterior_getElem t' k (by omega)) (hju ▸ hu)
          · exact Or.inr (by rw [← hju]; exact getElem_eq_of_index_eq t' (by omega) hj (by omega))
      rcases hb0 with hc | hc
      · exact absurd (hc.trans hstart) huv
      · exact hc.symm
    have htrev : IsTrackList D t'.reverse := by
      refine ⟨by simpa using ht'.1, by simpa using ht'.2.1, ?_⟩
      intro i hi
      have hi2 : i + 1 < t'.length := by simpa using hi
      rw [List.getElem_reverse, List.getElem_reverse]
      have hadj := ht'.2.2 (t'.length - 1 - (i + 1)) (by omega)
      rw [getElem_eq_of_index_eq t'
        (show t'.length - 1 - i = t'.length - 1 - (i + 1) + 1 by omega)
        (by omega) (by omega)]
      exact D.adj_symm hadj
    have ht'f : IsTrackFrom D t'.reverse u v := by
      refine ⟨htrev, ?_, ?_⟩
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hrevpos, hrev0, hrevu]
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), hrevL, hstart]
    have hsubrev : trackEdges t ⊆ trackEdges t'.reverse := by
      rw [trackEdges_reverse]; exact hsub
    rw [← trackEdges_reverse t', eq_of_trackEdges_subset ht ht'f hsubrev]

end Workspace.ProofLemmas.RungReplacementMaximality
