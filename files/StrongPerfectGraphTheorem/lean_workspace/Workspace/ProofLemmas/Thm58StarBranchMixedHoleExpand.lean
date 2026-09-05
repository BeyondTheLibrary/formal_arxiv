import Workspace.ProofLemmas.Thm58StarStarGapCross

/-!
# Where two expanded tracks of a subdivision can meet

Two tracks of the skeleton `J` that share no edge expand, in the subdivision `H`, to two tracks
that meet only at the images of their common skeleton vertices: an internal vertex of a
subdividing track belongs to no other subdividing track and is not the image of a skeleton
vertex.  This is the form of `SubdivisionTrackExpansion.expandTracks_meet_only_ends` that
5.8 (6) needs, where the two tracks share one end rather than two.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarBranchMixedHoleExpand

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCompose

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
variable {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

/-- **Two edge-disjoint skeleton tracks expand to tracks meeting only over common vertices.** -/
theorem expandTracks_meet (hS : SubdivWitness J H ι T) {p r : List U}
    (hpch : List.IsChain J.Adj p) (hrch : List.IsChain J.Adj r)
    (hnoedge : ∀ e ∈ trackEdges p, e ∉ trackEdges r) :
    ∀ w ∈ expandTracks ι T p, w ∈ expandTracks ι T r →
      ∃ z : U, z ∈ p ∧ z ∈ r ∧ w = ι z := by
  intro w hwp hwr
  rcases Thm58StarStarGapCross.mem_expandTracks_edge hS p hpch w hwp with
      ⟨z, hzp, hwz⟩ | ⟨x, y, hxyP, hxy, hint⟩
  · rcases Thm58StarStarGapCross.mem_expandTracks_edge hS r hrch w hwr with
        ⟨z', hz'r, hwz'⟩ | ⟨x', y', hx'y'R, hx'y', hint'⟩
    · exact ⟨z, hzp, (hS.inj (hwz.symm.trans hwz')) ▸ hz'r, hwz⟩
    · exact absurd (hS.new x' y' hx'y' w hint' ⟨z, hwz.symm⟩) (fun h => h)
  · rcases Thm58StarStarGapCross.mem_expandTracks_edge hS r hrch w hwr with
        ⟨z', hz'r, hwz'⟩ | ⟨x', y', hx'y'R, hx'y', hint'⟩
    · exact absurd (hS.new x y hxy w hint ⟨z', hwz'.symm⟩) (fun h => h)
    · by_cases hsame : s(x, y) = s(x', y')
      · exact absurd (hsame ▸ hx'y'R) (hnoedge _ hxyP)
      · exact absurd (hS.disj x y x' y' hxy hx'y' hsame w hint
          (mem_of_mem_trackInterior hint')) (fun h => h)

/-- Both ends of an edge of a track lie on the track. -/
theorem mem_of_mem_trackEdges {l : List U} {e : Sym2 U} (he : e ∈ trackEdges l)
    {z : U} (hz : z ∈ e) : z ∈ l := by
  obtain ⟨i, hi, hEq⟩ := he
  rw [hEq] at hz
  rcases Sym2.mem_iff.mp hz with h | h <;> rw [h] <;> exact List.getElem_mem _

/-- The only edge of a track containing its first vertex is its first edge. -/
theorem edge_at_head {K : SimpleGraph U} {R : List U} (hR : IsTrackList K R) {e : Sym2 U}
    (he : e ∈ trackEdges R) (h2 : 2 ≤ R.length) (hc : (R[0]'(by omega)) ∈ e) :
    e = s(R[0]'(by omega), R[1]'(by omega)) := by
  obtain ⟨i, hi, hEq⟩ := he
  rw [hEq] at hc ⊢
  have hi0 : i = 0 := by
    rcases Sym2.mem_iff.mp hc with hh | hh
    · have := (hR.2.1.getElem_inj_iff (hi := (by omega : (0:ℕ) < R.length))
        (hj := (by omega : i < R.length))).mp hh
      omega
    · have := (hR.2.1.getElem_inj_iff (hi := (by omega : (0:ℕ) < R.length))
        (hj := hi)).mp hh
      omega
  subst hi0
  rfl

/-- The second vertex of an expanded track is the second vertex of the first subdividing
track. -/
theorem expandTracks_second (hS : SubdivWitness J H ι T) {x y : U} {rest : List U}
    (hxy : J.Adj x y) (hch : List.IsChain J.Adj (y :: rest)) :
    (expandTracks ι T (x :: y :: rest))[1]? = (T x y)[1]? := by
  rw [Workspace.ProofLemmas.SubdivisionTrackExpansion.expandTracks_cons_cons_full
      hS x y rest hxy hch,
    List.getElem?_append_left (by have := two_le_track_length hS hxy; omega)]

/-- Expanding the two ends of a skeleton edge gives back its subdividing track. -/
theorem expandTracks_pair (hS : SubdivWitness J H ι T) {x y : U} (hxy : J.Adj x y) :
    expandTracks ι T [x, y] = T x y := by
  show (T x y).dropLast ++ expandTracks ι T [y] = T x y
  rw [expandTracks_singleton]
  exact List.dropLast_append_getLast? (ι y) (track_getLast? hS hxy)

end Workspace.ProofLemmas.Thm58StarBranchMixedHoleExpand
