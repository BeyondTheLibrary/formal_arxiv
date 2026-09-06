import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm58StarBranchMixedHoleExpand
import Workspace.ProofLemmas.SplitVertexTwoPaths
import Workspace.ProofLemmas.Thm58StarBranchParityTrack
import Workspace.ProofLemmas.Connectivity58Concat
import Workspace.ProofLemmas.Connectivity58CycleAvoid
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.LineGraphDegree
import Workspace.ProofLemmas.TrackSlice

/-!
# The cycle `C₂` of 5.8 (6) in the host graph

PAPER (proof of 5.8 (6), printed p. 28): *"Let `A` be the neighbours of `p₁` in `N_u` and
`B = N_u \ A`.  In `H` there is a cycle `C₂` using the branch between `v₁` and `v₂`, and using
an edge in `A` and an edge in `B`.  (To see this, divide `u` into two adjacent vertices, one
incident with the edges in `A` and the other with those in `B`, and use Menger's theorem to
deduce that there are two vertex-disjoint paths between these two vertices and `{v₁,v₂}`.)"*

The division of `u` is carried out in `H` itself by `SplitVertexTwoPaths.exists_split_paths`,
which is the printed parenthesis verbatim: it divides the star vertex `u` into two adjacent
vertices, one carrying the edges into `A` and one those into `B`, and returns the two
vertex-disjoint paths of Menger's theorem, read back in `H` as two tracks out of `u` meeting
only at `u`, one leaving along an edge into `A` and one along an edge into `B`, ending at the
two ends `v₁`, `v₂` of the branch in one order or the other.

Gluing those two tracks at `u` gives the track `D` from `v₁` to `v₂` through `u`; together with
the branch `Q` it is the cycle `C₂`, since neither of the two paths can enter the interior of
the branch (it would then have to run along the branch to its far end, which lies on the other
path).  `Connectivity58CycleBuild.baseCycle` glues `Q` and `D` into the cycle, and
`Thm58StarBranchMixedHoleCycle.exists_hole` reads its rung in `G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchMixedHoleTrack

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.Thm58StarBranchMixedHoleExpand

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- **The cycle `C₂` of 5.8 (6).**  PAPER, proof of 5.8 (6), printed p. 28: *"In `H` there is a
cycle `C₂` using the branch between `v₁` and `v₂`, and using an edge in `A` and an edge in `B`.
(To see this, divide `u` into two adjacent vertices, one incident with the edges in `A` and the
other with those in `B`, and use Menger's theorem to deduce that there are two vertex-disjoint
paths between these two vertices and `{v₁,v₂}`.)"*

Here `u` is the star vertex `c` and `Av` is the set `A`; `v₁`, `v₂` are the two ends of the
branch `q`.  The cycle `C₂` is returned as the branch `Q` (that is `q`, read in whichever
direction makes the `A`-edge the one on the `w₁` side) together with the complementary track
`D`, which runs from `w₁` to `w₂` through `c`, arriving along an edge `c xA` into `A` and
leaving along an edge `c xB` into `B`, and which meets the branch only at `w₁` and `w₂`. -/
theorem exists_mixed_track (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (Av : Set (Fin n))
    (hAne : ∃ x, H.Adj c x ∧ x ∈ Av) (hBne : ∃ x, H.Adj c x ∧ x ∉ Av) :
    ∃ (Q D : List (Fin n)) (w₁ w₂ xA xB : Fin n) (j : ℕ),
      s(c, xA) ∈ H.edgeSet ∧ xA ∈ Av ∧ s(c, xB) ∈ H.edgeSet ∧ xB ∉ Av ∧
      IsTrackFrom H Q w₁ w₂ ∧ 2 ≤ Q.length ∧ trackEdges Q = trackEdges q ∧
      IsTrackFrom H D w₁ w₂ ∧ 3 ≤ D.length ∧ (∀ z ∈ trackInterior D, z ∉ Q) ∧
      1 ≤ j ∧ j + 1 < D.length ∧
      D[j]? = some c ∧ D[j - 1]? = some xA ∧ D[j + 1]? = some xB := by
  classical
  have hJ3 : IsKConnected J 3 := h.ready.2.1
  have hsubd : IsSubdivision J H := h.ready.2.2.1.1
  have hc3 : CyclicallyThreeConnected H := ⟨m, J, hJ3, hsubd⟩
  have hcut : ∀ z : Fin n, ConnectedSet H ({z}ᶜ : Set (Fin n)) :=
    Workspace.ProofLemmas.CyclicThreeConnectedAttachments.no_cutvertex_of_cyclicallyThreeConnected
      hc3
  have hdeg2 : ∀ z : Fin n, 2 ≤ (H.neighborSet z).ncard :=
    Workspace.ProofLemmas.LineGraphDegree.two_le_degree_of_isSubdivision hJ3 hsubd
  -- the branch and its two ends
  have hq2 : 2 ≤ q.length := branch_two_le_length h
  have hqbr : IsBranch H q := h.branch
  have hqt : IsTrackList H q := hqbr.1
  have hqfrom : IsTrackFrom H q (q[0]'(by omega)) (q[q.length - 1]'(by omega)) := by
    refine ⟨hqt, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < q.length)]
    · rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : q.length - 1 < q.length)]
  have hvne : (q[0]'(by omega)) ≠ (q[q.length - 1]'(by omega)) := by
    intro hc
    have := (hqt.2.1.getElem_inj_iff (hi := (by omega : 0 < q.length))
      (hj := (by omega : q.length - 1 < q.length))).mp hc
    omega
  have hcv1 : c ≠ q[0]'(by omega) := by
    intro hc; exact hcq (hc ▸ List.getElem_mem _)
  have hcv2 : c ≠ q[q.length - 1]'(by omega) := by
    intro hc; exact hcq (hc ▸ List.getElem_mem _)
  -- PAPER: "divide `u` into two adjacent vertices, one incident with the edges in `A` and the
  -- other with those in `B`, and use Menger's theorem to deduce that there are two
  -- vertex-disjoint paths between these two vertices and `{v₁,v₂}`."
  obtain ⟨tA, tB, xA, xB, w₁, w₂, htA, htB, hlA, hlB, hxAget, hxBget, hxAadj, hxAmem,
      hxBadj, hxBmem, hmeet, hends⟩ :=
    Workspace.ProofLemmas.SplitVertexTwoPaths.exists_split_paths hcut hdeg2 hvne hcv1 hcv2
      hAne hBne
  have hAedge : s(c, xA) ∈ H.edgeSet := hxAadj
  have hBedge : s(c, xB) ∈ H.edgeSet := hxBadj
  have hA1 : tA[1]'(by omega) = xA := by
    rw [List.getElem?_eq_getElem (by omega : 1 < tA.length)] at hxAget
    exact Option.some_injective _ hxAget
  have hB1 : tB[1]'(by omega) = xB := by
    rw [List.getElem?_eq_getElem (by omega : 1 < tB.length)] at hxBget
    exact Option.some_injective _ hxBget
  -- glue the two paths at the star vertex
  have hAr : IsTrackFrom H tA.reverse w₁ c :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse htA
  have hmeetRev : ∀ z ∈ tA.reverse, z ∈ tB → z = c := fun z hz hz' =>
    hmeet z (List.mem_reverse.mp hz) hz'
  have hD : IsTrackFrom H (tA.reverse ++ tB.tail) w₁ w₂ :=
    Workspace.ProofLemmas.Connectivity58Concat.isTrackFrom_append hAr htB hmeetRev
  have hDlen : (tA.reverse ++ tB.tail).length = tA.length + (tB.length - 1) := by
    rw [Workspace.ProofLemmas.Connectivity58Concat.length_append, List.length_reverse]
  have hAmemA : w₁ ∈ tA :=
    List.mem_of_mem_getLast? (by rw [htA.2.2]; rfl)
  have hBmemB : w₂ ∈ tB :=
    List.mem_of_mem_getLast? (by rw [htB.2.2]; rfl)
  have hcA : c ∈ tA := List.mem_of_mem_head? (by rw [htA.2.1]; rfl)
  have hcB : c ∈ tB := List.mem_of_mem_head? (by rw [htB.2.1]; rfl)
  -- the branch, oriented from `w₁` to `w₂`
  have build : ∀ Q : List (Fin n), IsBranch H Q → IsTrackFrom H Q w₁ w₂ → 2 ≤ Q.length →
      trackEdges Q = trackEdges q → c ∉ Q →
      (∃ (Q' D : List (Fin n)) (w₁' w₂' xA' xB' : Fin n) (j : ℕ),
        s(c, xA') ∈ H.edgeSet ∧ xA' ∈ Av ∧ s(c, xB') ∈ H.edgeSet ∧ xB' ∉ Av ∧
        IsTrackFrom H Q' w₁' w₂' ∧ 2 ≤ Q'.length ∧ trackEdges Q' = trackEdges q ∧
        IsTrackFrom H D w₁' w₂' ∧ 3 ≤ D.length ∧ (∀ z ∈ trackInterior D, z ∉ Q') ∧
        1 ≤ j ∧ j + 1 < D.length ∧
        D[j]? = some c ∧ D[j - 1]? = some xA' ∧ D[j + 1]? = some xB') := by
    intro Q hQbr hQfrom hQ2 hQedges hcQ
    have hQ0 : Q[0]'(by omega) = w₁ := track_head hQfrom (by omega)
    have hQl : Q[Q.length - 1]'(by omega) = w₂ := by
      have h' := hQfrom.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : Q.length - 1 < Q.length)] at h'
      exact Option.some_injective _ h'
    have hQrev : IsBranch H Q.reverse :=
      Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse hQbr
    have hQrevFrom : IsTrackFrom H Q.reverse w₂ w₁ :=
      Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hQfrom
    have hQrevl : Q.reverse[Q.reverse.length - 1]'(by rw [List.length_reverse]; omega) = w₁ := by
      have h' := hQrevFrom.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem
          (by rw [List.length_reverse]; omega : Q.reverse.length - 1 < Q.reverse.length)] at h'
      exact Option.some_injective _ h'
    -- neither end of the branch is an internal vertex of it
    have hQends : ∀ x : Fin n, (x = w₁ ∨ x = w₂) → x ∉ trackInterior Q := by
      intro x hx hmem
      obtain ⟨j, hj, hjx⟩ := (mem_trackInterior_iff Q x).mp hmem
      rcases hx with rfl | rfl
      · have := (hQfrom.1.2.1.getElem_inj_iff (hi := (by omega : j + 1 < Q.length))
          (hj := (by omega : 0 < Q.length))).mp (by rw [hjx, hQ0])
        omega
      · have := (hQfrom.1.2.1.getElem_inj_iff (hi := (by omega : j + 1 < Q.length))
          (hj := (by omega : Q.length - 1 < Q.length))).mp (by rw [hjx, hQl])
        omega
    have hw₁w₂ : w₁ ≠ w₂ := by
      intro hc
      have := (hQfrom.1.2.1.getElem_inj_iff (hi := (by omega : 0 < Q.length))
        (hj := (by omega : Q.length - 1 < Q.length))).mp (by rw [hQ0, hQl, hc])
      omega
    have hw₂A : w₂ ∉ tA := by
      intro hc
      exact hcQ (hmeet w₂ hc hBmemB ▸ (by rw [← hQl]; exact List.getElem_mem _))
    have hw₁B : w₁ ∉ tB := by
      intro hc
      exact hcQ ((hmeet w₁ hAmemA hc) ▸ (by rw [← hQ0]; exact List.getElem_mem _))
    -- neither path enters the interior of the branch
    have hAint : ∀ x ∈ trackInterior Q, x ∉ tA := by
      refine Workspace.ProofLemmas.Connectivity58CycleAvoid.interior_disjoint_of_last_not_mem
        hdeg2 hQbr hQ2 htA.1 ?_ ?_
      · intro x hx hend
        rcases hend with hh | hh
        · rw [htA.2.1] at hh
          have : x = c := (Option.some_injective _ hh).symm
          subst this
          exact fun hc => hcQ
            (Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hc)
        · rw [htA.2.2] at hh
          have : x = w₁ := (Option.some_injective _ hh).symm
          subst this
          exact hQends _ (Or.inl rfl)
      · rw [hQl]; exact hw₂A
    have hBint : ∀ x ∈ trackInterior Q, x ∉ tB := by
      have hkey := Workspace.ProofLemmas.Connectivity58CycleAvoid.interior_disjoint_of_last_not_mem
        hdeg2 hQrev (by rw [List.length_reverse]; omega) htB.1 ?_ ?_
      · intro x hx
        exact hkey x (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse.mpr hx)
      · intro x hx hend
        rcases hend with hh | hh
        · rw [htB.2.1] at hh
          have : x = c := (Option.some_injective _ hh).symm
          subst this
          intro hc
          exact hcQ (Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior
            (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse.mp hc))
        · rw [htB.2.2] at hh
          have : x = w₂ := (Option.some_injective _ hh).symm
          subst this
          intro hc
          exact hQends _ (Or.inr rfl)
            (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse.mp hc)
      · rw [hQrevl]; exact hw₁B
    -- so the two tracks meet only at the two ends
    have hdisjD : ∀ z ∈ trackInterior (tA.reverse ++ tB.tail), z ∉ Q := by
      intro z hz hzQ
      have hzD : z ∈ tA.reverse ++ tB.tail :=
        Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hz
      have hz1 : z ≠ w₁ :=
        Workspace.ProofLemmas.SubdivisionCompose.ne_head_of_mem_trackInterior hD.1.2.1 hD.2.1 hz
      have hz2 : z ≠ w₂ :=
        Workspace.ProofLemmas.SubdivisionCompose.ne_getLast_of_mem_trackInterior
          hD.1.2.1 hD.2.2 hz
      have hzint : z ∉ trackInterior Q := by
        rcases List.mem_append.mp hzD with hh | hh
        · exact fun hc => hAint z hc (List.mem_reverse.mp hh)
        · exact fun hc => hBint z hc (List.mem_of_mem_tail hh)
      rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
        hQfrom.2.1 hQfrom.2.2 hzQ hzint with hh | hh
      · exact hz1 hh
      · exact hz2 hh
    refine ⟨Q, tA.reverse ++ tB.tail, w₁, w₂, xA, xB, tA.length - 1, hAedge, hxAmem, hBedge,
      hxBmem, hQfrom, hQ2, hQedges, hD, by omega, hdisjD, by omega, by omega, ?_, ?_, ?_⟩
    · have hb : tA.length - 1 < (tA.reverse ++ tB.tail).length := by omega
      rw [List.getElem?_eq_getElem hb,
        Workspace.ProofLemmas.Connectivity58Concat.append_getElem_left _ _ _
          (by rw [List.length_reverse]; omega) hb,
        List.getElem_reverse,
        getElem_eq_of_index_eq tA
          (show tA.length - 1 - (tA.length - 1) = 0 by omega) (by omega) (by omega),
        track_head htA (by omega)]
    · have hb : tA.length - 1 - 1 < (tA.reverse ++ tB.tail).length := by omega
      rw [List.getElem?_eq_getElem hb,
        Workspace.ProofLemmas.Connectivity58Concat.append_getElem_left _ _ _
          (by rw [List.length_reverse]; omega) hb,
        List.getElem_reverse,
        getElem_eq_of_index_eq tA
          (show tA.length - 1 - (tA.length - 1 - 1) = 1 by omega) (by omega) (by omega),
        hA1]
    · have hb : tA.length - 1 + 1 < (tA.reverse ++ tB.tail).length := by omega
      have hidx : tA.reverse.length - 1 + 1 = tA.length - 1 + 1 := by
        rw [List.length_reverse]
      rw [List.getElem?_eq_getElem hb,
        ← getElem_eq_of_index_eq (tA.reverse ++ tB.tail) hidx (by omega) hb,
        Workspace.ProofLemmas.Connectivity58Concat.append_getElem_right hAr htB 1
          (by omega) (by omega),
        hB1]
  -- orient the branch so that it runs from `w₁` to `w₂`
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact build q hqbr hqfrom hq2 rfl hcq
  · refine build q.reverse
      (Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse hqbr)
      (Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hqfrom)
      (by rw [List.length_reverse]; omega) (trackEdges_reverse q) ?_
    rw [List.mem_reverse]; exact hcq

end Workspace.ProofLemmas.Thm58StarBranchMixedHoleTrack
