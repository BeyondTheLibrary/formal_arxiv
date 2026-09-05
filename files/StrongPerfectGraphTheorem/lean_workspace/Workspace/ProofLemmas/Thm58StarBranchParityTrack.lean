import Workspace.ProofLemmas.Thm58StarStarGapCross
import Workspace.ProofLemmas.Connectivity58Skeleton

/-!
# The two host tracks of 5.8 (2)

PAPER (proof of 5.8 (2), printed p. 26): *"Now `H` is a subdivision of a 3-connected graph, so
if we delete all edges of `H` incident with `u` except `s₁`, the graph we produce is still
connected.  Consequently there is a track of `H` from `u` to `v` with first edge `s₁` ...
Indeed, if we delete from `H` both the vertex `w` and all edges incident with `u` except `s₂`,
the graph remains connected."*

`exists_side_track` below is both sentences at once.  Given a branch `q` of `H` from `c` to `v`
and two distinct edges `e`, `f` of `H` at `c`, neither of them an edge of `q`, it produces a
track of `H` from `c` to `v` whose first edge is `e`, which uses no edge of `q`, and no edge of
which — except the first one — meets `f`.  Taking `(e, f) = (s₁, s₂)` gives the first track and
`(e, f) = (s₂, s₁)` the second; in the second case the extra clause is the paper's *"delete the
vertex `w`"*, `w` being the far end of the branch carrying `s₁`.

The proof is the skeleton statement `Connectivity58Skeleton.exists_avoiding_track_first`
(a track of the 3-connected graph `J` between the ends of an edge, with a prescribed first
edge, avoiding a prescribed third vertex and not using the edge itself) expanded through the
subdivision.  The three clauses then read off the expansion: the first branch of the expansion
is the branch carrying `e`, no branch of the expansion is the branch of `q`, and the branch
carrying `f` is missed altogether because the skeleton track avoids its far end.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchParityTrack

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCompose
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- The second vertex of a subdividing track is either an internal vertex of it or the image
of the far end. -/
theorem second_vertex_cases {t : List W} (h2 : 2 ≤ t.length) :
    t[1]'(by omega) ∈ trackInterior t ∨ t[1]'(by omega) = t[t.length - 1]'(by omega) := by
  by_cases hlen : 3 ≤ t.length
  · exact Or.inl ((SubdivisionCounting.mem_trackInterior_iff t _).mpr ⟨0, by omega, rfl⟩)
  · right
    congr 1
    omega


/-- A vertex of an edge of a track is a vertex of the track. -/
theorem mem_of_mem_edge {t : List W} {g : Sym2 W} (hg : g ∈ trackEdges t) {w : W}
    (hw : w ∈ g) : w ∈ t := by
  obtain ⟨i, hi, rfl⟩ := hg
  rcases Sym2.mem_iff.mp hw with hh | hh <;> rw [hh] <;> exact List.getElem_mem _


/-- An edge of `H` at one end of a branch, which is not an edge of that branch, does not
contain the other end.  (In a subdivision, two branch-vertices are joined by at most one
branch, because `J` is simple.) -/
theorem end_not_mem_edge {J : SimpleGraph U} {H : SimpleGraph W}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {c v : W} {q : List W} (hq : IsBranch H q) (hqfrom : IsTrackFrom H q c v)
    (hq2 : 2 ≤ q.length) (hbc : c ∈ branchVertices H) (hbv : v ∈ branchVertices H)
    {e : Sym2 W} (he : e ∈ H.edgeSet) (hce : c ∈ e) (heq : e ∉ trackEdges q) : v ∉ e := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlen, hrev, hdisj, hnew⟩
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  obtain ⟨u₀, v₀, hu₀v₀, hEq0, hcase⟩ :=
    BranchClassification.exists_trackEdges_eq_and_ends hι htrack hlen hrev hdisj hnew hcover
      hedges hdeg hq hq2 hqfrom hbc hbv
  obtain ⟨α, β, hαβ, hEq, hcα, hvβ⟩ :
      ∃ a b : U, J.Adj a b ∧ trackEdges q = trackEdges (T a b) ∧ c = ι a ∧ v = ι b := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨u₀, v₀, hu₀v₀, hEq0, h1, h2⟩
    · refine ⟨v₀, u₀, hu₀v₀.symm, ?_, h1, h2⟩
      rw [hrev u₀ v₀ hu₀v₀, SubdivisionCounting.trackEdges_reverse]
      exact hEq0
  subst hcα
  subst hvβ
  obtain ⟨ξ, hαξ, heT⟩ :=
    SubdivisionTrackExpansion.edge_at_embedded_vertex hS hedges he hce
  intro hve
  have hvT : ι β ∈ T α ξ := mem_of_mem_edge heT hve
  have hvint : ι β ∉ trackInterior (T α ξ) := fun hh => hnew α ξ hαξ _ hh ⟨β, rfl⟩
  rcases mem_ends_of_mem (track_head? hS hαξ) (track_getLast? hS hαξ) hvT hvint with hh | hh
  · exact hαβ.ne' (hι hh)
  · have : ξ = β := hι hh.symm
    subst this
    exact heq (hEq ▸ heT)

/-- **The two tracks of 5.8 (2).**  A track of `H` from `c` to `v` with prescribed first edge
`e` at `c`, using no edge of the branch `q` from `c` to `v`, and meeting the other prescribed
edge `f` at `c` only in `c` itself. -/
theorem exists_side_track {J : SimpleGraph U} {H : SimpleGraph W}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {c v : W} {q : List W} (hq : IsBranch H q) (hqfrom : IsTrackFrom H q c v)
    (hq2 : 2 ≤ q.length) (hbc : c ∈ branchVertices H) (hbv : v ∈ branchVertices H)
    {e f : Sym2 W} (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet)
    (hce : c ∈ e) (hcf : c ∈ f) (hef : e ≠ f)
    (heq : e ∉ trackEdges q) (hfq : f ∉ trackEdges q) :
    ∃ (t : List W) (h2 : 2 ≤ t.length),
      IsTrackFrom H t c v ∧ firstTrackEdge t h2 = e ∧
      (∀ g ∈ trackEdges t, g ∉ trackEdges q) ∧
      (∀ g ∈ trackEdges t, g ≠ e → ∀ w : W, w ∈ g → w ∉ f) := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlen, hrev, hdisj, hnew⟩
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  -- name the edge of `J` carrying the branch `q`
  obtain ⟨u₀, v₀, hu₀v₀, hEq0, hcase⟩ :=
    BranchClassification.exists_trackEdges_eq_and_ends hι htrack hlen hrev hdisj hnew hcover
      hedges hdeg hq hq2 hqfrom hbc hbv
  obtain ⟨α, β, hαβ, hEq, hcα, hvβ⟩ :
      ∃ a b : U, J.Adj a b ∧ trackEdges q = trackEdges (T a b) ∧ c = ι a ∧ v = ι b := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨u₀, v₀, hu₀v₀, hEq0, h1, h2⟩
    · refine ⟨v₀, u₀, hu₀v₀.symm, ?_, h1, h2⟩
      rw [hrev u₀ v₀ hu₀v₀, SubdivisionCounting.trackEdges_reverse]
      exact hEq0
  subst hcα
  subst hvβ
  -- name the two branches carrying `e` and `f`
  obtain ⟨ξe, hαξe, heT⟩ :=
    SubdivisionTrackExpansion.edge_at_embedded_vertex hS hedges he hce
  obtain ⟨ξf, hαξf, hfT⟩ :=
    SubdivisionTrackExpansion.edge_at_embedded_vertex hS hedges hf hcf
  -- the first edge of a branch at its first end is determined
  have hfirst : ∀ (x : U) (hx : J.Adj α x) (g : Sym2 W), g ∈ trackEdges (T α x) → ι α ∈ g →
      g = firstTrackEdge (T α x) (two_le_track_length hS hx) :=
    fun x hx g hg hmem => edge_eq_firstTrackEdge (htrack α x hx) _ hg hmem
  have hξeβ : ξe ≠ β := by
    rintro rfl
    exact heq (hEq ▸ heT)
  have hξfβ : ξf ≠ β := by
    rintro rfl
    exact hfq (hEq ▸ hfT)
  have hξeξf : ξe ≠ ξf := by
    rintro rfl
    exact hef ((hfirst ξe hαξe e heT hce).trans (hfirst ξe hαξf f hfT hcf).symm)
  have hξfα : ξf ≠ α := fun hh => hαξf.ne' hh
  -- the skeleton track
  obtain ⟨p, hp, hpξf, hpedge, hp3, hp1⟩ :=
    Connectivity58Skeleton.exists_avoiding_track_first hJ hαβ hαξe hξeβ hξeξf hξfα hξfβ
  have hpch : List.IsChain J.Adj p := List.isChain_iff_getElem.mpr hp.1.2.2
  set t : List W := expandTracks ι T p with ht
  have htfrom : IsTrackFrom H t (ι α) (ι β) :=
    SubdivisionTrackExpansion.expandTracks_isTrackFrom hS hp
  have ht3 : 3 ≤ t.length :=
    le_trans hp3 (Thm58StarStarGapCross.length_le_expandTracks hS p hpch)
  have ht2 : 2 ≤ t.length := by omega
  -- the first edge of the expansion is `e`
  have hfe : firstTrackEdge t ht2 = e := by
    have hp0 : p.head? = some α := hp.2.1
    obtain ⟨tail, hptail⟩ : ∃ tail, p = α :: tail := by
      cases p with
      | nil => simp at hp0
      | cons a l => exact ⟨l, by simp only [List.head?_cons, Option.some.injEq] at hp0; rw [hp0]⟩
    obtain ⟨rest, hrest⟩ : ∃ rest, tail = ξe :: rest := by
      cases tail with
      | nil => rw [hptail] at hp3; simp at hp3
      | cons b l =>
        refine ⟨l, ?_⟩
        rw [hptail] at hp1
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp1
        rw [hp1]
    have hpeq : p = α :: ξe :: rest := by rw [hptail, hrest]
    have hchtail : List.IsChain J.Adj (ξe :: rest) := by
      rw [hpeq] at hpch; exact hpch.tail
    have hsplit : t = T α ξe ++ (expandTracks ι T (ξe :: rest)).tail := by
      rw [ht, hpeq]
      exact SubdivisionTrackExpansion.expandTracks_cons_cons_full hS α ξe rest hαξe hchtail
    have hTe2 : 2 ≤ (T α ξe).length := two_le_track_length hS hαξe
    have hq0 : t[0]? = (T α ξe)[0]? := by
      conv_lhs => rw [hsplit]
      exact List.getElem?_append_left (by omega)
    have hq1 : t[1]? = (T α ξe)[1]? := by
      conv_lhs => rw [hsplit]
      exact List.getElem?_append_left (by omega)
    rw [List.getElem?_eq_getElem (show 0 < t.length by omega),
      List.getElem?_eq_getElem (show 0 < (T α ξe).length by omega)] at hq0
    rw [List.getElem?_eq_getElem (show 1 < t.length by omega),
      List.getElem?_eq_getElem (show 1 < (T α ξe).length by omega)] at hq1
    have hg0 : t[0]'(by omega) = (T α ξe)[0]'(by omega) := Option.some_injective _ hq0
    have hg1 : t[1]'(by omega) = (T α ξe)[1]'(by omega) := Option.some_injective _ hq1
    have hstep : firstTrackEdge t ht2 = firstTrackEdge (T α ξe) hTe2 := by
      simp only [firstTrackEdge]
      rw [hg0, hg1]
    rw [hstep]
    exact (hfirst ξe hαξe e heT hce).symm
  refine ⟨t, ht2, htfrom, hfe, ?_, ?_⟩
  · -- no edge of the expansion is an edge of the branch `q`
    have key : ∀ z ∈ t, z ∉ trackInterior (T α β) := by
      intro z hz hint
      rcases Thm58StarStarGapCross.mem_expandTracks_edge hS p hpch z hz with
        ⟨x, hx, rfl⟩ | ⟨x, y, hxy, hadjxy, hzint⟩
      · exact hnew α β hαβ (ι x) hint ⟨x, rfl⟩
      · have hne : s(x, y) ≠ s(α, β) := fun hc => hpedge (hc ▸ hxy)
        exact hdisj x y α β hadjxy hαβ hne z hzint
          (SubdivisionCompose.mem_of_mem_trackInterior hint)
    have hTlen : 0 < (T α β).length := by
      have := hlen α β hαβ
      simp only [trackLength] at this
      omega
    have hhead : (T α β)[0]'hTlen = ι α :=
      SubdivisionCounting.track_head (htrack α β hαβ) hTlen
    have hlast : (T α β)[(T α β).length - 1]'(by omega) = ι β :=
      DegenerateK4Tracks.track_getLast (htrack α β hαβ) hTlen
    intro g hgt hgq
    rw [hEq] at hgq
    obtain ⟨i, hi, rfl⟩ := hgq
    have hmemQ := BranchClassification.mem_of_mem_trackEdges hgt
    have hends : ∀ j : ℕ, ∀ hj : j < (T α β).length,
        (T α β)[j]'hj ∈ t → (T α β)[j]'hj = ι α ∨ (T α β)[j]'hj = ι β := by
      intro j hj hjQ
      rcases DegenerateK4Tracks.mem_ends_of_notMem_interior (List.getElem_mem hj)
        (key _ hjQ) hTlen with hh | hh
      · exact Or.inl (hh.trans hhead)
      · exact Or.inr (hh.trans hlast)
    have hne : (T α β)[i]'(by omega) ≠ (T α β)[i + 1]'hi := by
      intro hc
      have := (htrack α β hαβ).1.2.1.getElem_inj_iff.mp hc
      omega
    have hi1 := hends i (by omega) hmemQ.1
    have hi2 := hends (i + 1) hi hmemQ.2
    have habs : s((T α β)[i]'(by omega), (T α β)[i + 1]'hi) = s(ι α, ι β) := by
      rcases hi1 with h1 | h1 <;> rcases hi2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]
      · rw [h1, h2, Sym2.eq_swap]
      · exact absurd (h1.trans h2.symm) hne
    exact Thm58StarStarGapTracks.ends_edge_not_mem htfrom (by omega) (habs ▸ hgt)
  · -- no edge of the expansion except the first one meets `f`
    have hTf2 : 2 ≤ (T α ξf).length := two_le_track_length hS hαξf
    have hffirst : f = firstTrackEdge (T α ξf) hTf2 := hfirst ξf hαξf f hfT hcf
    have hfz : f = s(ι α, (T α ξf)[1]'(by omega)) := by
      rw [hffirst]
      simp only [firstTrackEdge]
      congr 1
      exact SubdivisionCounting.track_head (htrack α ξf hαξf) (by omega)
    have hlastf : (T α ξf)[(T α ξf).length - 1]'(by omega) = ι ξf :=
      DegenerateK4Tracks.track_getLast (htrack α ξf hαξf) (by omega)
    have hznot : (T α ξf)[1]'(by omega) ∉ t := by
      intro hzt
      have hzcases := second_vertex_cases (t := T α ξf) hTf2
      rcases Thm58StarStarGapCross.mem_expandTracks_edge hS p hpch _ hzt with
        ⟨x, hx, hxz⟩ | ⟨x, y, hxy, hadjxy, hzint⟩
      · rcases hzcases with hint | hlz
        · exact hnew α ξf hαξf _ hint ⟨x, hxz.symm⟩
        · have hzf : (T α ξf)[1]'(by omega) = ι ξf := by rw [hlz, hlastf]
          have hxf : x = ξf := hι (hxz.symm.trans hzf)
          exact hpξf (hxf ▸ hx)
      · rcases hzcases with hint | hlz
        · have hxp : x ∈ p := (BranchClassification.mem_of_mem_trackEdges hxy).1
          have hyp : y ∈ p := (BranchClassification.mem_of_mem_trackEdges hxy).2
          have hne : s(x, y) ≠ s(α, ξf) := by
            intro hc
            rcases Sym2.eq_iff.mp hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hpξf hyp
            · exact hpξf hxp
          exact hdisj x y α ξf hadjxy hαξf hne _ hzint
            (SubdivisionCompose.mem_of_mem_trackInterior hint)
        · have hzf : (T α ξf)[1]'(by omega) = ι ξf := by rw [hlz, hlastf]
          exact hnew x y hadjxy _ hzint ⟨ξf, hzf.symm⟩
    intro g hgt hge w hwg hwf
    rw [hfz] at hwf
    have hwt : w ∈ t := mem_of_mem_edge hgt hwg
    have hwα : w = ι α := by
      rcases Sym2.mem_iff.mp hwf with hh | hh
      · exact hh
      · exact absurd (hh ▸ hwt) hznot
    subst hwα
    apply hge
    obtain ⟨i, hi, rfl⟩ := hgt
    have h0 : t[0]'(by omega) = ι α :=
      SubdivisionCounting.track_head htfrom (by omega)
    have hnd := htfrom.1.2.1
    have hi0 : i = 0 := by
      rcases Sym2.mem_iff.mp hwg with hh | hh
      · have := hnd.getElem_inj_iff.mp (h0.trans hh)
        omega
      · have := hnd.getElem_inj_iff.mp (h0.trans hh)
        omega
    subst hi0
    exact hfe

end Workspace.ProofLemmas.Thm58StarBranchParityTrack
