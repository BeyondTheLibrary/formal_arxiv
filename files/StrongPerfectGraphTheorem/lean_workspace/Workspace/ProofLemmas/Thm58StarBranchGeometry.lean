import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm57Claim2Structure

/-! The branch and star dictionaries used in 5.8 (2) and (6). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchGeometry

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}
  (h : Context G m J n H K φ N F P p₁ p₂ c q)

include h

/-- A branch through the star can be oriented to start at the star vertex. -/
theorem orient_incident (hcq : c ∈ q) :
    ∃ b Q, IsBranch H Q ∧ IsTrackFrom H Q c b ∧
      trackEdges Q = trackEdges q ∧ b ∈ branchVertices H := by
  have h2 := branch_two_le_length h
  have hfrom := Thm57Claim2Structure.branch_from_ends h.branch h2
  have hcint : c ∉ trackInterior q := fun hi => h.branch.2.1 c hi h.star
  rcases SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 hcq hcint with hc | hc
  · have hfc : IsTrackFrom H q c q[q.length - 1] := by rw [hc]; exact hfrom
    have hb := Thm75BranchEnds.branchEnds_mem_branchVertices J h.ready.2.1 H
      h.ready.2.2.1.1 q c _ h.branch hfc (by simp only [trackLength]; omega)
    exact ⟨_, q, h.branch, hfc, rfl, hb.2⟩
  · have hfc : IsTrackFrom H q.reverse c q[0] := by
      refine ⟨Thm57Claim2Structure.isBranch_reverse h.branch |>.1, ?_, ?_⟩
      · rw [List.head?_reverse, hc]; exact hfrom.2.2
      · rw [List.getLast?_reverse]; exact hfrom.2.1
    have hb := Thm75BranchEnds.branchEnds_mem_branchVertices J h.ready.2.1 H
      h.ready.2.2.1.1 q.reverse c _ (Thm57Claim2Structure.isBranch_reverse h.branch)
      hfc (by simp only [trackLength, List.length_reverse]; omega)
    exact ⟨_, q.reverse, Thm57Claim2Structure.isBranch_reverse h.branch, hfc,
      SubdivisionCounting.trackEdges_reverse q, hb.2⟩

/-- The first and last edges of a track give the two singleton star intersections. -/
theorem rung_intersections {Q : List (Fin n)} {a b : Fin n}
    (hfrom : IsTrackFrom H Q a b) (h2 : 2 ≤ Q.length) :
    ∃ (R : List V) (r s : V), IsPathFrom G R r s ∧
      {x : V | x ∈ R} = edgeImage φ (trackEdges Q) ∧
      N a ∩ {x : V | x ∈ R} = {r} ∧ N b ∩ {x : V | x ∈ R} = {s} := by
  let r := firstRungVertex φ Q hfrom.1 h2
  let s := lastRungVertex φ Q hfrom.1 h2
  have hRset : {x : V | x ∈ trackRung φ Q hfrom.1} = edgeImage φ (trackEdges Q) :=
    Set.ext (fun _ => mem_trackRung_iff φ hfrom.1)
  refine ⟨trackRung φ Q hfrom.1, r, s, trackRung_isPathFrom_ends φ hfrom h2,
    hRset, ?_, ?_⟩
  · rw [star_eq h a, hRset]
    ext x
    constructor
    · rintro ⟨⟨e, he, hea, rfl⟩, heR⟩
      have heQ := (image_mem_iff he).mp heR
      exact congrArg (fun e : H.edgeSet => (φ e : V))
        (Subtype.ext (edge_eq_firstTrackEdge hfrom h2 heQ hea.2))
    · rintro rfl
      exact ⟨⟨_, firstTrackEdge_mem hfrom.1 h2,
        ⟨firstTrackEdge_mem hfrom.1 h2, firstTrackEdge_contains hfrom h2⟩, rfl⟩,
        ⟨_, firstTrackEdge_mem hfrom.1 h2, firstTrackEdge_mem_trackEdges h2, rfl⟩⟩
  · rw [star_eq h b, hRset]
    ext x
    constructor
    · rintro ⟨⟨e, he, heb, rfl⟩, heR⟩
      have heQ := (image_mem_iff he).mp heR
      exact congrArg (fun e : H.edgeSet => (φ e : V))
        (Subtype.ext (edge_eq_lastTrackEdge hfrom h2 heQ heb.2))
    · rintro rfl
      exact ⟨⟨_, lastTrackEdge_mem hfrom.1 h2,
        ⟨lastTrackEdge_mem hfrom.1 h2, lastTrackEdge_contains hfrom h2⟩, rfl⟩,
        ⟨_, lastTrackEdge_mem hfrom.1 h2, lastTrackEdge_mem_trackEdges h2, rfl⟩⟩

omit h in
/-- Two distinct track edges sharing a vertex put that vertex in the track's interior. -/
theorem internal_of_two_edges {Q : List (Fin n)} (hnd : Q.Nodup)
    {e f : Sym2 (Fin n)} (he : e ∈ trackEdges Q) (hf : f ∈ trackEdges Q)
    (hef : e ≠ f) {d : Fin n} (hde : d ∈ e) (hdf : d ∈ f) :
    d ∈ trackInterior Q := by
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  rw [SubdivisionCounting.mem_trackInterior_iff]
  rcases Sym2.mem_iff.mp hde with h1 | h1 <;> rcases Sym2.mem_iff.mp hdf with h2 | h2
  · have hij : i = j := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    subst j
    exact (hef rfl).elim
  · have hij : i = j + 1 := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    exact ⟨j, by omega, h2.symm⟩
  · have hij : i + 1 = j := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    exact ⟨i, by omega, h1.symm⟩
  · have hij : i + 1 = j + 1 := hnd.getElem_inj_iff.mp (h1.symm.trans h2)
    have : i = j := by omega
    subst j
    exact (hef rfl).elim

/-- Two adjacent vertices of a branch rung are exactly the star at their common internal
vertex. This is the star used in conclusion 1 of claim (6). -/
theorem adjacent_pair_star {a b : V}
    (ha : a ∈ edgeImage φ (trackEdges q)) (hb : b ∈ edgeImage φ (trackEdges q))
    (hab : G.Adj a b) : ∃ d ∈ trackInterior q, N d = {a, b} := by
  obtain ⟨e, he, heq, rfl⟩ := ha
  obtain ⟨f, hf, hfq, rfl⟩ := hb
  have hL : H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff.mp hab
  obtain ⟨hne, d, hde, hdf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hL
  have hef : e ≠ f := fun hh => hne (Subtype.ext hh)
  have hdint := internal_of_two_edges h.branch.1.2.1 heq hfq hef hde hdf
  refine ⟨d, hdint, ?_⟩
  have hinc : incidentEdges H d = {e, f} := by
    apply Set.Subset.antisymm
    · intro g hg
      by_contra hg'
      have hge : g ≠ e := fun hh => hg' (Or.inl hh)
      have hgf : g ≠ f := fun hh => hg' (Or.inr hh)
      apply h.branch.2.1 d hdint
      have hsub : ({e, f, g} : Set (Sym2 (Fin n))) ⊆ incidentEdges H d := by
        rintro t (rfl | rfl | rfl)
        · exact ⟨he, hde⟩
        · exact ⟨hf, hdf⟩
        · exact hg
      have hcard : ({e, f, g} : Set (Sym2 (Fin n))).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨e, f, g, hef, hge.symm, hgf.symm, rfl⟩
      have hle := Set.ncard_le_ncard hsub
      rw [hcard, Thm84RungEndDictionary.incidentEdges_ncard] at hle
      exact hle
    · rintro g (rfl | rfl)
      · exact ⟨he, hde⟩
      · exact ⟨hf, hdf⟩
  rw [star_eq h d, hinc]
  ext x
  constructor
  · rintro ⟨g, hg, rfl | rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨e, he, Or.inl rfl, rfl⟩
    · exact ⟨f, hf, Or.inr rfl, rfl⟩

/-- An internal vertex of this branch cannot share another branch with a vertex outside it. -/
theorem no_common_branch (hcq : c ∉ q) {d : Fin n} (hd : d ∈ trackInterior q) :
    ¬ ∃ Q : List (Fin n), IsBranch H Q ∧ c ∈ Q ∧ d ∈ Q := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := h.ready.2.2.1.1
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J h.ready.2.1
  have hrange := SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdeg
  have hbv := SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  have hdnot : d ∉ Set.range ι := fun hm => h.branch.2.1 d hd (hrange hm)
  have h2 := branch_two_le_length h
  obtain ⟨u, v, huv, hqT⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
    hι htrack hlen hrev hdisj hnew hcover hedges hdeg h.branch h2
  have hvertices : ∀ (A B : List (Fin n)), 2 ≤ A.length →
      trackEdges A ⊆ trackEdges B → ∀ x ∈ A, x ∈ B := by
    intro A B hA hAB x hx
    obtain ⟨i, hi, hxi⟩ := BranchClassification.exists_edge_of_mem hA hx
    have hmem := BranchClassification.mem_of_mem_trackEdges
      (hAB (show s(A[i], A[i + 1]) ∈ trackEdges A from ⟨i, hi, rfl⟩))
    rcases hxi with hh | hh
    · exact hh ▸ hmem.1
    · exact hh ▸ hmem.2
  have hdT : d ∈ T u v := hvertices q (T u v) h2 hqT.subset d
    (by exact List.mem_of_mem_tail (List.mem_of_mem_dropLast hd))
  have hdTint : d ∈ trackInterior (T u v) := by
    by_contra hni
    rcases SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1
      (htrack u v huv).2.2 hdT hni with hh | hh
    · exact hdnot ⟨u, hh.symm⟩
    · exact hdnot ⟨v, hh.symm⟩
  rintro ⟨Q, hQ, hcQ, hdQ⟩
  have hQ2 : 2 ≤ Q.length := by
    have hpos := List.length_pos_of_ne_nil hQ.1.1
    by_contra hn
    have hQ1 : Q.length = 1 := by omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hQ1
    have hcz : c = z := by simpa using hcQ
    have hdz : d = z := by simpa using hdQ
    exact h.branch.2.1 d hd (hdz.symm ▸ hcz ▸ h.star)
  obtain ⟨u', v', huv', hQT⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
    hι htrack hlen hrev hdisj hnew hcover hedges hdeg hQ hQ2
  have hdT' := hvertices Q (T u' v') hQ2 hQT.subset d hdQ
  have heq : s(u, v) = s(u', v') := by
    by_contra hn
    exact hdisj u v u' v' huv huv' hn d hdTint hdT'
  have hT : trackEdges (T u v) = trackEdges (T u' v') := by
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [hrev _ _ huv, SubdivisionCounting.trackEdges_reverse]
  have hQq : trackEdges Q ⊆ trackEdges q := by rw [hQT, hqT, hT]
  exact hcq (hvertices Q q hQ2 hQq c hcQ)

/-- A vertex outside a rung cannot see both vertices of an adjacent pair in that rung.
Three such edges would meet at an internal branch vertex, which has degree at most two. -/
theorem no_outside_triangle {a r s : V} (haK : a ∈ K)
    (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : G.Adj r s) : ¬ G.Adj a r ∨ ¬ G.Adj a s := by
  classical
  by_contra hn
  have har : G.Adj a r := by tauto
  have has : G.Adj a s := by tauto
  obtain ⟨e, he, rfl⟩ := exists_edge (φ := φ) haK
  obtain ⟨f, hf, hfq, rfl⟩ := hr
  obtain ⟨g, hg, hgq, rfl⟩ := hs
  have hefL : H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff.mp har
  have hegL : H.lineGraph.Adj ⟨e, he⟩ ⟨g, hg⟩ := φ.map_rel_iff.mp has
  have hfgL : H.lineGraph.Adj ⟨f, hf⟩ ⟨g, hg⟩ := φ.map_rel_iff.mp hrs
  obtain ⟨hef', hefm⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hefL
  obtain ⟨heg', hegm⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hegL
  obtain ⟨hfg', hfgm⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hfgL
  have hef : e ≠ f := fun hh => hef' (Subtype.ext hh)
  have heg : e ≠ g := fun hh => heg' (Subtype.ext hh)
  have hfg : f ≠ g := fun hh => hfg' (Subtype.ext hh)
  obtain ⟨d, hde, hdf, hdg⟩ := Thm84RungEndDictionary.exists_common_of_three
    h.ready.2.2.1.2 he hf hg hef heg hfg hefm hegm hfgm
  have hdint := internal_of_two_edges h.branch.1.2.1 hfq hgq hfg hdf hdg
  apply h.branch.2.1 d hdint
  have hsub : ({e, f, g} : Set (Sym2 (Fin n))) ⊆ incidentEdges H d := by
    rintro t (rfl | rfl | rfl)
    · exact ⟨he, hde⟩
    · exact ⟨hf, hdf⟩
    · exact ⟨hg, hdg⟩
  have hcard : ({e, f, g} : Set (Sym2 (Fin n))).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨e, f, g, hef, heg, hfg, rfl⟩
  have hle := Set.ncard_le_ncard hsub
  rw [hcard, Thm84RungEndDictionary.incidentEdges_ncard] at hle
  exact hle

end Workspace.ProofLemmas.Thm58StarBranchGeometry
