import Workspace.ProofLemmas.Thm58StarStarGapCoveredSetup
import Workspace.ProofLemmas.Thm58StarStarGapOffBranch
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack

/-!
# The path `T` of the last paragraph of 5.8 (4)

PAPER: *"If we delete the vertex `v₂` and the edge `a₁` from `H`, what remains is still
connected, and so contains a track from `w` to `v₁`.  Hence there is a path `T` in `L(H)` from
some `a₃ ∈ N(w)` to `r₁`, disjoint from `N_{v₂} ∪ a₁`."*

The track is built the other way round, from `v₁` to `w`: `v₁` has a third neighbour `a`,
besides the first vertex of the branch and `w`, and `a` lies off the branch; the complement of
the branch is connected, so it contains a track from `a` to `w`, and hanging `v₁` on the front
of it gives a track `W` of `H` from `v₁` to `w` whose only vertex on the branch is `v₁` and
whose first edge is `v₁a ≠ a₁`.  The path `T` is the rung of `W`, with `r₁` — the vertex of
`L(H)` given by the first edge of the branch — glued on at the `v₁` end.

Besides the two properties the paper states, the construction also gives what its last sentence
silently uses: `T` meets the rung `R_{v₁v₂}` only in `r₁`, and meets the star of `w` only in
its end `a₃`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapCoveredTrack

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles
open ThreeTracksLineGraphPrism TrackToRungPath Thm58StarStarGapCoveredSetup
open Thm58StarStarTracks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ w : Fin n}
  {q : List (Fin n)} {R : List V} {r₁ r₂ : V}

variable (hc : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂)

include hc

/-- The first vertex of the branch after `v₁`. -/
theorem head_branch_edge :
    ∃ (z : Fin n) (hz : H.Adj c₁ z), z ≠ w ∧ z ∈ q ∧ s(c₁, z) ∈ trackEdges q ∧
      (∀ e ∈ trackEdges q, c₁ ∈ e → e = s(c₁, z)) ∧ r₁ = (φ ⟨s(c₁, z), hz⟩ : V) := by
  have h3 := three_le_q hc
  have h2 : 2 ≤ q.length := hc.len2
  have hq0 : q[0]'(by omega) = c₁ := PathBasics.getElem_zero_of_head? hc.from'.2.1 (by omega)
  have hadj : H.Adj c₁ (q[1]'(by omega)) := by
    have := hc.from'.1.2.2 0 (by omega)
    rwa [hq0] at this
  have hfe : firstTrackEdge q h2 = s(c₁, q[1]'(by omega)) := by
    simp only [firstTrackEdge]
    rw [hq0]
  refine ⟨q[1]'(by omega), hadj, ?_, List.getElem_mem _, ?_, ?_, ?_⟩
  · intro hcon
    apply hc.off₁
    rw [← hcon, ← hfe]
    exact firstTrackEdge_mem_trackEdges h2
  · rw [← hfe]; exact firstTrackEdge_mem_trackEdges h2
  · intro e he hce
    rw [← hfe]
    exact edge_eq_firstTrackEdge hc.from' h2 he hce
  · -- `r₁` is the vertex of `L(H)` given by the first edge of the branch
    have hr₁K : r₁ ∈ K := star_subset hc.ctx c₁ (r₁_mem_star₁ hc)
    obtain ⟨e, he, hre⟩ := exists_edge (φ := φ) hr₁K
    have heq : e ∈ trackEdges q := by
      rw [← mem_R_iff hc he, ← hre]; exact r₁_mem_R hc
    have hce : c₁ ∈ e := by
      apply (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) he).mp
      rw [← hre]; exact r₁_mem_star₁ hc
    have : e = s(c₁, q[1]'(by omega)) := by
      rw [← hfe]; exact edge_eq_firstTrackEdge hc.from' h2 heq hce
    subst this
    exact hre

/-- The common neighbour `w` is off the branch. -/
theorem w_not_mem_branch : w ∉ q := by
  intro hmem
  have hint : w ∉ trackInterior q := by
    intro hw
    obtain ⟨j, hj, hjw⟩ := (SubdivisionCounting.mem_trackInterior_iff q w).mp hw
    have hsub : incidentEdges H (q[j + 1]'(by omega)) ⊆ trackEdges q :=
      Thm57Claim2Structure.incidentEdges_internal_subset hc.branch (by omega) (by omega)
    rw [hjw] at hsub
    exact hc.off₁ (hsub ⟨hc.adjw₁, Sym2.mem_mk_right _ _⟩)
  rcases SubdivisionCompose.mem_ends_of_mem hc.from'.2.1 hc.from'.2.2 hmem hint with h | h
  · exact w_ne₁ hc h
  · exact w_ne₂ hc h

/-- PAPER, implicit in *"there is a track from `w` to `v₁`"*: `v₁` is a branch-vertex, so
besides `w` and the branch it has a third neighbour, and that neighbour is off the branch. -/
theorem exists_third_neighbour {z : Fin n} (hzedge : s(c₁, z) ∈ trackEdges q) :
    ∃ a : Fin n, H.Adj c₁ a ∧ a ≠ z ∧ a ≠ w ∧ a ∉ q := by
  classical
  have h3 := three_le_q hc
  have h2 : 2 ≤ q.length := hc.len2
  have hdeg : 3 ≤ (H.neighborSet c₁).ncard := hc.ctx.star₁
  have hex : ∃ a : Fin n, H.Adj c₁ a ∧ a ≠ z ∧ a ≠ w := by
    by_contra hcon
    push_neg at hcon
    have hsub : H.neighborSet c₁ ⊆ {z, w} := by
      intro y hy
      rcases eq_or_ne y z with h | h
      · exact Or.inl h
      · exact Or.inr (hcon y hy h)
    have h1 : (H.neighborSet c₁).ncard ≤ ({z, w} : Set (Fin n)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2' : ({z, w} : Set (Fin n)).ncard ≤ 2 := by
      refine le_trans (Set.ncard_insert_le _ _) ?_
      simp
    omega
  obtain ⟨a, ha, haz, haw⟩ := hex
  refine ⟨a, ha, haz, haw, ?_⟩
  intro haq
  have hnotint : a ∉ trackInterior q := by
    intro hai
    obtain ⟨j, hj, hja⟩ := (SubdivisionCounting.mem_trackInterior_iff q a).mp hai
    have hsub : incidentEdges H (q[j + 1]'(by omega)) ⊆ trackEdges q :=
      Thm57Claim2Structure.incidentEdges_internal_subset hc.branch (by omega) (by omega)
    rw [hja] at hsub
    have hmem : s(c₁, a) ∈ trackEdges q := hsub ⟨ha, Sym2.mem_mk_right _ _⟩
    obtain ⟨z', hz', -, -, -, hall, -⟩ := head_branch_edge hc
    have e1 : s(c₁, a) = s(c₁, z') := hall _ hmem (Sym2.mem_mk_left _ _)
    have e2 : s(c₁, z) = s(c₁, z') := hall _ hzedge (Sym2.mem_mk_left _ _)
    have hfe : s(c₁, a) = s(c₁, z) := e1.trans e2.symm
    have : a = z := by
      rcases Sym2.eq_iff.mp hfe with ⟨-, h⟩ | ⟨-, h'⟩
      · exact h
      · exact absurd h'.symm ha.ne
    exact haz this
  rcases SubdivisionCompose.mem_ends_of_mem hc.from'.2.1 hc.from'.2.2 haq hnotint with h | h
  · exact ha.ne' h
  · -- `a = v₂` would make `v₁v₂` an edge of `H`, hence an edge of the branch, impossible
    have hadj12 : H.Adj c₁ c₂ := h ▸ ha
    have hmem : (φ ⟨s(c₁, c₂), hadj12⟩ : V) ∈ N c₁ ∩ N c₂ := by
      constructor
      · exact (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hadj12).mpr
          (Sym2.mem_mk_left _ _)
      · exact (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hadj12).mpr
          (Sym2.mem_mk_right _ _)
    have hsub := Thm58StarStarGeometry.stars_inter_subset_rung hc.ctx hc.branch hc.from' h2 hmem
    have hin : s(c₁, c₂) ∈ trackEdges q := (image_mem_iff hadj12).mp hsub
    exact Thm58StarStarGapTracks.ends_edge_not_mem hc.from' h3 hin


/-- PAPER: *"If we delete the vertex `v₂` and the edge `a₁` from `H`, what remains is still
connected, and so contains a track from `w` to `v₁`."*  Read from `v₁` to `w`: a track of `H`
that meets the branch only at `v₁` and whose first edge is not `a₁`. -/
theorem exists_track_to_w :
    ∃ (W : List (Fin n)) (h2 : 2 ≤ W.length) (hW : IsTrackFrom H W c₁ w),
      (∀ e ∈ trackEdges W, e ∉ trackEdges q) ∧
      (∀ y ∈ W, y ≠ c₁ → y ∉ q) ∧ s(c₁, w) ∉ trackEdges W := by
  classical
  have h3 := three_le_q hc
  have h2q : 2 ≤ q.length := hc.len2
  obtain ⟨z, hz, hzw, hzq, hzedge, hall, hr₁eq⟩ := head_branch_edge hc
  obtain ⟨a, ha, haz, haw, haq⟩ := exists_third_neighbour hc hzedge
  have hc3 : CyclicallyThreeConnected H := ⟨m, J, hc.ctx.ready.2.1, hc.ctx.ready.2.2.1.1⟩
  have hS : ConnectedSet H ({x : Fin n | x ∈ q}ᶜ) :=
    Thm58StarStarGapOffBranch.branch_complement_connected hc3 hc.branch h2q
  have hwq : w ∉ q := w_not_mem_branch hc
  obtain ⟨a', ha', w', hw', Pt, hPt, hPtS, -, -⟩ :=
    ConnectedSetHasEndpointCleanTrack H ({x : Fin n | x ∈ q}ᶜ) {a} {w} hS ⟨a, rfl⟩ ⟨w, rfl⟩
      (by simpa using haq) (by simpa using hwq)
  have haa : a' = a := by simpa using ha'
  have hww : w' = w := by simpa using hw'
  rw [haa, hww] at hPt
  have hc₁q : c₁ ∈ q := List.mem_of_head? hc.from'.2.1
  have hcPt : c₁ ∉ Pt := fun hmem => (hPtS c₁ hmem) hc₁q
  have hPtpos : 0 < Pt.length := List.length_pos_of_ne_nil hPt.1.1
  have hPt0 : Pt[0]'hPtpos = a := PathBasics.getElem_zero_of_head? hPt.2.1 hPtpos
  have hW : IsTrackFrom H (c₁ :: Pt) c₁ w := Thm61Claim1Helpers.isTrackFrom_cons hPt ha hcPt
  have h2 : 2 ≤ (c₁ :: Pt).length := by simp only [List.length_cons]; omega
  have hoff : ∀ y ∈ (c₁ :: Pt), y ≠ c₁ → y ∉ q := by
    intro y hy hyne
    rcases List.mem_cons.mp hy with rfl | hy
    · exact absurd rfl hyne
    · exact hPtS y hy
  have hmemq : ∀ e : Sym2 (Fin n), e ∈ trackEdges q → ∀ y ∈ e, y ∈ q := by
    rintro e ⟨i, hi, rfl⟩ y hy
    rcases Sym2.mem_iff.mp hy with h | h <;> rw [h] <;> exact List.getElem_mem _
  have hdisj : ∀ e ∈ trackEdges (c₁ :: Pt), e ∉ trackEdges q := by
    rintro e ⟨i, hi, rfl⟩ hq'
    have hA : (c₁ :: Pt)[i]'(by omega) ∈ q := hmemq _ hq' _ (Sym2.mem_mk_left _ _)
    have hB : (c₁ :: Pt)[i + 1]'hi ∈ q := hmemq _ hq' _ (Sym2.mem_mk_right _ _)
    have e1 : (c₁ :: Pt)[i]'(by omega) = c₁ := by
      by_contra hcon
      exact hoff _ (List.getElem_mem _) hcon hA
    have e2 : (c₁ :: Pt)[i + 1]'hi = c₁ := by
      by_contra hcon
      exact hoff _ (List.getElem_mem _) hcon hB
    have := hW.1.2.1.getElem_inj_iff.mp (e1.trans e2.symm)
    omega
  have hfirst : firstTrackEdge (c₁ :: Pt) h2 = s(c₁, a) := by
    simp only [firstTrackEdge, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hPt0]
  refine ⟨c₁ :: Pt, h2, hW, hdisj, hoff, ?_⟩
  intro hin
  have hEq := edge_eq_firstTrackEdge hW h2 hin (Sym2.mem_mk_left _ _)
  rw [hfirst] at hEq
  rcases Sym2.eq_iff.mp hEq with ⟨-, h⟩ | ⟨h1, -⟩
  · exact haw h.symm
  · exact ha.ne h1

/-- PAPER: *"Hence there is a path `T` in `L(H)` from some `a₃ ∈ N(w)` to `r₁`, disjoint from
`N_{v₂} ∪ a₁`."*  The last two conclusions are what the closing sentence of the paragraph also
needs: `T` meets the rung `R_{v₁v₂}` only in `r₁`, and meets the star of `w` only in `a₃`. -/
theorem exists_T :
    ∃ (T : List V) (a₃ : V),
      IsPathFrom G T a₃ r₁ ∧ 2 ≤ T.length ∧ (∀ x ∈ T, x ∈ K) ∧ a₃ ∈ N w ∧
      (∀ x ∈ T, x ∉ N c₂) ∧ hc.a₁ ∉ T ∧
      (∀ x ∈ T, x ∈ R → x = r₁) ∧ (∀ x ∈ T, x ∈ N w → x = a₃) := by
  classical
  have h3 := three_le_q hc
  obtain ⟨z, hz, hzw, hzq, hzedge, hall, hr₁eq⟩ := head_branch_edge hc
  obtain ⟨W, h2, hW, hdisj, hoff, hnot⟩ := exists_track_to_w hc
  have hmemW : ∀ e : Sym2 (Fin n), e ∈ trackEdges W → ∀ y ∈ e, y ∈ W := by
    rintro e ⟨i, hi, rfl⟩ y hy
    rcases Sym2.mem_iff.mp hy with h | h <;> rw [h] <;> exact List.getElem_mem _
  have hzW : z ∉ W := fun hmem => hoff z hmem hz.ne' hzq
  have hc₂W : c₂ ∉ W := fun hmem =>
    hoff c₂ hmem (stars_ne' hc).symm (List.mem_of_getLast? hc.from'.2.2)
  have hRwPath : IsPathFrom G (trackRung φ W hW.1) (firstRungVertex φ W hW.1 h2)
      (lastRungVertex φ W hW.1 h2) := trackRung_isPathFrom_ends φ hW h2
  have hr₁notRw : r₁ ∉ trackRung φ W hW.1 := by
    intro hmem
    obtain ⟨f, hf, hfW, hfeq⟩ := (mem_trackRung_iff φ hW.1).mp hmem
    have hEq : s(c₁, z) = f :=
      congrArg Subtype.val (φ.injective (Subtype.ext (hr₁eq.symm.trans hfeq)))
    exact hdisj f hfW (hEq ▸ hzedge)
  have hcross : ∀ y ∈ trackRung φ W hW.1,
      (G.Adj r₁ y ↔ y = firstRungVertex φ W hW.1 h2) := by
    intro y hy
    obtain ⟨f, hf, hfW, rfl⟩ := (mem_trackRung_iff φ hW.1).mp hy
    constructor
    · intro hadj
      rw [hr₁eq] at hadj
      have hL : H.lineGraph.Adj ⟨s(c₁, z), hz⟩ ⟨f, hf⟩ := φ.map_rel_iff.mp hadj
      obtain ⟨-, v, hv1, hv2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hL
      have hvc : v = c₁ := by
        rcases Sym2.mem_iff.mp hv1 with h | h
        · exact h
        · exact absurd (h ▸ hmemW f hfW v hv2) hzW
      rw [hvc] at hv2
      have hEq := edge_eq_firstTrackEdge hW h2 hfW hv2
      exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext hEq)
    · intro hEq
      rw [hEq]
      refine star_adj (star_eq hc.ctx) c₁ (r₁_mem_star₁ hc)
        (firstRungVertex_mem_star (star_eq hc.ctx) hW h2) ?_
      intro hcon
      exact hr₁notRw (hcon ▸ firstRungVertex_mem φ hW.1 h2)
  have hT0 : IsPathFrom G ([r₁] ++ trackRung φ W hW.1) r₁ (lastRungVertex φ W hW.1 h2) := by
    refine PathGlue.glue_path ⟨PathBasics.isPathList_singleton G r₁, rfl, rfl⟩ hRwPath ?_ ?_
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hr₁notRw
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst hx
      simpa using hcross y hy
  refine ⟨([r₁] ++ trackRung φ W hW.1).reverse, lastRungVertex φ W hW.1 h2,
    PathBasics.isPathFrom_reverse hT0, ?_, ?_, lastRungVertex_mem_star (star_eq hc.ctx) hW h2,
    ?_, ?_, ?_, ?_⟩
  · have hlen : (trackRung φ W hW.1).length = trackLength W := trackRung_length φ W hW.1
    simp only [List.length_reverse, List.length_append, List.length_singleton, hlen, trackLength]
    omega
  · intro x hx
    rw [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact star_subset hc.ctx c₁ (r₁_mem_star₁ hc)
    · exact trackRung_subset_K φ W hW.1 x hx
  · intro x hx hmem
    rw [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact r₁_not_mem_star₂ hc hmem
    · obtain ⟨f, hf, hfW, rfl⟩ := (mem_trackRung_iff φ hW.1).mp hx
      have hin := (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hf).mp hmem
      exact hc₂W (hmemW f hfW c₂ hin)
  · intro hx
    rw [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact (r₁_ne_a₁ hc) hx.symm
    · obtain ⟨f, hf, hfW, hfeq⟩ := (mem_trackRung_iff φ hW.1).mp hx
      have hEq : s(c₁, w) = f := congrArg Subtype.val (φ.injective (Subtype.ext hfeq))
      exact hnot (hEq ▸ hfW)
  · intro x hx hxR
    rw [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx
    · rfl
    · obtain ⟨f, hf, hfW, rfl⟩ := (mem_trackRung_iff φ hW.1).mp hx
      exact absurd ((mem_R_iff hc hf).mp hxR) (hdisj f hfW)
  · intro x hx hxw
    rw [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx
    · exfalso
      rw [hr₁eq] at hxw
      have hin := (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hz).mp hxw
      rcases Sym2.mem_iff.mp hin with h | h
      · exact w_ne₁ hc h
      · exact hzw h.symm
    · obtain ⟨f, hf, hfW, rfl⟩ := (mem_trackRung_iff φ hW.1).mp hx
      have hwf := (Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) hf).mp hxw
      have hEq := edge_eq_lastTrackEdge hW h2 hfW hwf
      exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext hEq)

end Workspace.ProofLemmas.Thm58StarStarGapCoveredTrack
