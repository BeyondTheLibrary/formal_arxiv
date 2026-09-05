import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.BranchClassification

/-!
# What the rest of a subdivision looks like from one branch

These are Lemmas 1–2 of the rung-replacement plan for 7.5, in the only form the surgery needs:

* an edge of `H` that is not an edge of the branch `q` has **both ends outside the interior of
  `q`** — an internal vertex of a branch has degree two, and both of its edges are branch edges;
* a **different** branch of `H` avoids the interior of `q` altogether.

Both follow from the same two facts about a subdivision: every branch is one of the
subdividing tracks (`Workspace.ProofLemmas.BranchClassification`), and two different
subdividing tracks share no edge and no internal vertex.

The bridge between "same edge set" and "same internal vertices" is
`mem_trackInterior_of_two_edges`: an internal vertex of a track is exactly a vertex lying on
two different edges of it.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementBranchFacts

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {U W : Type*}

/-- Both ends of an edge of a track lie on that track. -/
theorem mem_list_of_mem_trackEdges {t : List W} {e : Sym2 W} (he : e ∈ trackEdges t)
    {w : W} (hw : w ∈ e) : w ∈ t := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with rfl | rfl <;> exact List.getElem_mem _

/-- A vertex lying on two different edges of a track is an internal vertex of it. -/
theorem mem_trackInterior_of_two_edges {t : List W} (hnd : t.Nodup) {e f : Sym2 W}
    (he : e ∈ trackEdges t) (hf : f ∈ trackEdges t) (hef : e ≠ f) {w : W}
    (hwe : w ∈ e) (hwf : w ∈ f) : w ∈ trackInterior t := by
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  have hij : i ≠ j := by rintro rfl; exact hef rfl
  rw [mem_trackInterior_iff]
  rcases Sym2.mem_iff.mp hwe with h1 | h1 <;> rcases Sym2.mem_iff.mp hwf with h2 | h2
  · exact absurd (hnd.getElem_inj_iff.mp (h1.symm.trans h2)) hij
  · have hidx : i = j + 1 := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    exact ⟨j, by omega, h2.symm⟩
  · have hidx : i + 1 = j := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    exact ⟨i, by omega, h1.symm⟩
  · have hidx : i + 1 = j + 1 := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    exact absurd (by omega : i = j) hij

/-- Two tracks with the same edges have the same internal vertices. -/
theorem trackInterior_subset_of_trackEdges_eq {t t' : List W} (hnd : t.Nodup) (hnd' : t'.Nodup)
    (hE : trackEdges t = trackEdges t') {w : W} (hw : w ∈ trackInterior t) :
    w ∈ trackInterior t' := by
  obtain ⟨j, hj, rfl⟩ := (mem_trackInterior_iff t w).mp hw
  have he₁ : s(t[j]'(by omega), t[j + 1]'(by omega)) ∈ trackEdges t := ⟨j, by omega, rfl⟩
  have he₂ : s(t[j + 1]'(by omega), t[j + 2]'(by omega)) ∈ trackEdges t := ⟨j + 1, by omega, rfl⟩
  refine mem_trackInterior_of_two_edges hnd' (hE ▸ he₁) (hE ▸ he₂) ?_ (by simp) (by simp)
  intro hcon
  rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (hnd.getElem_inj_iff.mp h1) (by omega)
  · exact absurd (hnd.getElem_inj_iff.mp h1) (by omega)


section Subdivision

variable [Finite W] [Fintype U] {J : SimpleGraph U} {H : SimpleGraph W}

/-- **An edge off the branch avoids the branch's interior.**

An internal vertex of a branch of a subdivision has degree two and both of its edges lie on the
branch, so an edge of `H` that is not an edge of `q` has both ends outside the interior of `q`.
This is what makes deleting the edges of `q` and deleting its internal vertices agree. -/
theorem edges_off_branch_avoid_interior (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) :
    ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have hdeg := three_le_degree_of_three_connected J hJ
  obtain ⟨u, v, huv, hEq⟩ :=
    BranchClassification.exists_trackEdges_eq_of_isBranch hι htrack hlen hrev hdisjint hnew
      hcover hedges hdeg hq hq2
  intro e he hne w hw hwint
  have hwint' : w ∈ trackInterior (T u v) :=
    trackInterior_subset_of_trackEdges_eq hq.1.2.1 (htrack u v huv).1.2.1 hEq hwint
  rw [hedges] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨u', v', hu'v', he'⟩ := he
  have hne2 : s(u, v) ≠ s(u', v') := by
    intro hcon
    refine hne ?_
    rw [hEq]
    rcases Sym2.eq_iff.mp hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he'
    · have hTr : T u v = (T u' v').reverse := by rw [h1, h2]; exact hrev u' v' hu'v'
      rw [hTr, trackEdges_reverse]; exact he'
  exact hdisjint u v u' v' huv hu'v' hne2 w hwint' (mem_list_of_mem_trackEdges he' hw)

/-- Two different branches of a subdivision share no edge. -/
theorem trackEdges_disjoint_of_ne (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q p : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length)
    (hp : IsBranch H p) (hp2 : 2 ≤ p.length) (hne : trackEdges p ≠ trackEdges q) :
    ∀ e ∈ trackEdges p, e ∉ trackEdges q := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have hdeg := three_le_degree_of_three_connected J hJ
  obtain ⟨u, v, huv, hEq⟩ :=
    BranchClassification.exists_trackEdges_eq_of_isBranch hι htrack hlen hrev hdisjint hnew
      hcover hedges hdeg hq hq2
  obtain ⟨u', v', hu'v', hEq'⟩ :=
    BranchClassification.exists_trackEdges_eq_of_isBranch hι htrack hlen hrev hdisjint hnew
      hcover hedges hdeg hp hp2
  intro e hep heq
  have h1 : e ∈ trackEdges (T u v) := hEq ▸ heq
  have h2 : e ∈ trackEdges (T u' v') := hEq' ▸ hep
  have hsame : s(u, v) = s(u', v') :=
    trackEdges_disjoint hι htrack hlen hdisjint u v u' v' huv hu'v' e h1 h2
  refine hne ?_
  rw [hEq, hEq']
  rcases Sym2.eq_iff.mp hsame with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h3, h4]
  · have hTr : T u v = (T u' v').reverse := by rw [h3, h4]; exact hrev u' v' hu'v'
    rw [hTr, trackEdges_reverse]

/-- A different branch of `H` avoids the interior of `q` altogether, so all of its vertices
survive the deletion of `q`. -/
theorem other_branch_avoids_interior (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q p : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length)
    (hp : IsBranch H p) (hp2 : 2 ≤ p.length) (hne : trackEdges p ≠ trackEdges q) :
    ∀ w ∈ p, w ∉ trackInterior q := by
  intro w hw
  obtain ⟨i, hi, hcase⟩ := BranchClassification.exists_edge_of_mem hp2 hw
  have hepE : s(p[i]'(by omega), p[i + 1]'hi) ∈ H.edgeSet := hp.1.2.2 i hi
  have hep : s(p[i]'(by omega), p[i + 1]'hi) ∈ trackEdges p := ⟨i, hi, rfl⟩
  refine edges_off_branch_avoid_interior hJ hsub hq hq2 _ hepE
    (trackEdges_disjoint_of_ne hJ hsub hq hq2 hp hp2 hne _ hep) w ?_
  rcases hcase with rfl | rfl <;> simp


/-- A subdivision of a graph of minimum degree at least three has no isolated vertex. -/
theorem exists_adj_of_isSubdivision (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    (w : W) : ∃ x, H.Adj w x := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have hdeg := three_le_degree_of_three_connected J hJ
  rcases hcover w with ⟨u, rfl⟩ | ⟨u, v, huv, hint⟩
  · have hne : (J.neighborSet u).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hcon
      have := hdeg u
      rw [hcon] at this
      simp at this
    obtain ⟨v, hv⟩ := hne
    have huv : J.Adj u v := hv
    have hL : 2 ≤ (T u v).length := by
      have := hlen u v huv
      simp only [trackLength] at this
      omega
    have hadj := (htrack u v huv).1.2.2 0 (by omega)
    have h0 : (T u v)[0]'(by omega) = ι u :=
      track_head (htrack u v huv) (by omega)
    exact ⟨(T u v)[1]'(by omega), by rw [← h0]; exact hadj⟩
  · obtain ⟨j, hj, rfl⟩ := (mem_trackInterior_iff (T u v) w).mp hint
    exact ⟨(T u v)[j + 2]'(by omega), (htrack u v huv).1.2.2 (j + 1) (by omega)⟩

/-- Every branch of a subdivision has at least two vertices: a one-vertex track is maximal only
at an isolated vertex. -/
theorem two_le_length_of_isBranch (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {p : List W} (hp : IsBranch H p) : 2 ≤ p.length := by
  rcases Nat.lt_or_ge p.length 2 with hlt | hge
  · exfalso
    have hpos : 0 < p.length := List.length_pos_of_ne_nil hp.1.1
    have h1 : p.length = 1 := by omega
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨x, hx⟩ := exists_adj_of_isSubdivision hJ hsub w
    have htl : IsTrackList H [w, x] := by
      refine ⟨by simp, by simp [hx.ne], ?_⟩
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst this
      simpa using hx
    have hE : trackEdges ([w] : List W) = ∅ := by
      ext e
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, hi, -⟩
      simp at hi
    have hmax := hp.2.2 [w, x] htl (by intro v hv; simp [trackInterior] at hv)
      (by rw [hE]; exact Set.empty_subset _) (by intro v hv; simp at hv; simp [hv])
    have : s(w, x) ∈ trackEdges ([w, x] : List W) := ⟨0, by simp, rfl⟩
    rw [hmax, hE] at this
    exact this
  · exact hge

end Subdivision

end Workspace.ProofLemmas.RungReplacementBranchFacts
