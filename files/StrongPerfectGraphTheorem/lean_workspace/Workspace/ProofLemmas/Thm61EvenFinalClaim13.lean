import Workspace.ProofLemmas.Thm61EvenFinalFourth
import Workspace.ProofLemmas.Thm61EvenFinalK4

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenFinalClaim13

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.Thm61EvenFinalTracks Workspace.ProofLemmas.Thm61EvenFinalBridge
open Workspace.ProofLemmas.Thm61EvenFinalFourth Workspace.ProofLemmas.Thm61EvenFinalK4

/-- "By (10) (applied to three tracks with common end `b₂`), each of them meets either
`b₁b₂` or `e₃`." The three arms are `B₄` extended through the complete edge,
the edge `b₂b₁`, and the two-edge track through `b` and `e₃`. -/
theorem complete_at_fourth_meets
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (hshort : trackLength B₂ = 1)
    (e₄ : Sym2 (Fin n)) (B₄ : List (Fin n)) (b₄ : Fin n)
    (h4 : FourthBranch G H K φ Y y₁ b b₁ b₂ e₄ B₄ b₄)
    (g : Sym2 (Fin n)) (hg : g ∈ incidentEdges H b₄)
    (hgX : g ∈ completeEdges G H K φ Y) : MeetEdges g s(b₁, b₂) ∨ MeetEdges g e₃ := by
  classical
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₃X := other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
    he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hshort] at he₂B₂
    exact he₂B₂
  have h02 : H.Adj b b₂ := H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)
  obtain ⟨z, hP₃, he₃eq⟩ := edge_track_from_incident he₃inc
  have hb₁not : b₁ ∉ e₃ := branch_edge_avoids_other_branchVertex hB₃ hfrom₃ he₃B₃
    hb₁V hbb₁.symm hb₁b₃
  have hb₂not : b₂ ∉ e₃ := branch_edge_avoids_other_branchVertex hB₃ hfrom₃ he₃B₃
    hb₂V hbb₂.symm hb₂b₃
  by_contra hn
  have hgp : DisjointEdges g s(b₁, b₂) := Classical.byContradiction (fun h => hn (Or.inl h))
  have hge : DisjointEdges g e₃ := Classical.byContradiction (fun h => hn (Or.inr h))
  have hb₂g : b₂ ∉ g := fun h => hgp b₂ ⟨h, by simp⟩
  have hB₄pos := one_le_trackLength_of_mem h4.edge
  have hB₄2 : 2 ≤ B₄.length := by simp only [trackLength] at hB₄pos; omega
  have hbB₄ : b ∉ B₄ := by
    intro hm
    rcases SubdivisionCompose.mem_ends_of_mem h4.track.2.1 h4.track.2.2 hm
      (fun hi => h4.branch.2.1 b hi hbV) with h | h
    · exact hbb₂ h
    · exact h4.ne_b h.symm
  have hb₁B₄ : b₁ ∉ B₄ := by
    intro hm
    rcases SubdivisionCompose.mem_ends_of_mem h4.track.2.1 h4.track.2.2 hm
      (fun hi => h4.branch.2.1 b₁ hi hb₁V) with h | h
    · exact hb₁b₂ h
    · exact h4.ne_b1 h.symm
  have he₃out : e₃ ∉ trackEdges B₄ := fun he =>
    branch_edge_avoids_other_branchVertex h4.branch h4.track he hbV hbb₂ h4.ne_b.symm he₃inc.2
  have hzB₄ : z ∉ B₄ := by
    intro hz
    have hze : z ∈ e₃ := by rw [he₃eq]; simp
    rcases external_edge_inter_branch_only_at_ends h4.branch h4.track hB₄pos
      he₃inc.1 he₃out hz hze with h | h
    · exact hb₂not (h ▸ hze)
    · exact hge b₄ ⟨hg.2, h ▸ hze⟩
  have hb₂z : b₂ ≠ z := by intro h; exact hb₂not (by rw [he₃eq, h]; simp)
  have hb₁z : b₁ ≠ z := by intro h; exact hb₁not (by rw [he₃eq, h]; simp)
  obtain ⟨P, v, hP, hP2, hgP, hPmem, hPfirst⟩ :=
    extend_branch_through_incident_edge h4.branch h4.track hB₄pos hg hb₂g
  have hpair : IsTrackFrom H [b₂, b₁] b₂ b₁ := HPrimeTracks.isTrackFrom_pair hadj.symm
  have hlong : IsTrackFrom H [b₂, b, z] b₂ z := isTrackFrom_cons hP₃ h02.symm
    (by simp [hbb₂.symm, hb₂z])
  have h12 : ∀ w ∈ P, w ∈ [b₂, b₁] → w = b₂ := by
    intro w hw hw'
    rcases hPmem w hw with hm | hm
    · rcases List.mem_cons.mp hw' with h | h
      · exact h
      · exact False.elim (hb₁B₄ ((List.eq_of_mem_singleton h) ▸ hm))
    · exact False.elim (hgp w ⟨hm, by simpa [Sym2.mem_iff, or_comm] using hw'⟩)
  have h13 : ∀ w ∈ P, w ∈ [b₂, b, z] → w = b₂ := by
    intro w hw hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with h | h | h
    · exact h
    · rcases hPmem w hw with hm | hm
      · exact False.elim (hbB₄ (h ▸ hm))
      · exact False.elim (hge b ⟨h ▸ hm, he₃inc.2⟩)
    · rcases hPmem w hw with hm | hm
      · exact False.elim (hzB₄ (h ▸ hm))
      · exact False.elim (hge z ⟨h ▸ hm, by rw [he₃eq]; simp⟩)
  have h23 : ∀ w ∈ [b₂, b₁], w ∈ [b₂, b, z] → w = b₂ := by
    intro w hw hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
    rcases hw with rfl | rfl
    · rfl
    · rcases hw' with h | h | h
      · exact h
      · exact False.elim (hbb₁ h.symm)
      · exact False.elim (hb₁z h)
  have hpfirst : s(P[0]'(by omega), P[1]'(by omega)) ∉ completeEdges G H K φ Y := by
    have heP := trackEdge_at_head h4.track hB₄2 (hPfirst hP2)
      (by rw [head_getElem hP.2.1 (by omega)]; simp)
    have he₄ := trackEdge_at_head h4.track hB₄2 h4.edge h4.incident.2
    exact fun hx => h4.extra.2 ((heP.trans he₄.symm) ▸ hx)
  have hlongfirst : s(([b₂, b, z] : List (Fin n))[0], [b₂, b, z][1]) ∉
      completeEdges G H K φ Y := by
    simpa only [List.getElem_cons_zero, List.getElem_cons_succ, Sym2.eq_swap, ← he₂eq] using he₂X₂.2
  have h := h10 b₂ v b₁ z P [b₂, b₁] [b₂, b, z] hP hpair hlong hP2 (by simp) (by simp)
    h12 h13 h23 ⟨g, hgP, hgX⟩ ⟨s(b₁, b₂), ⟨0, by simp, by simp [Sym2.eq_swap]⟩, hXb⟩
    ⟨e₃, ⟨1, by simp, he₃eq⟩, he₃X⟩
  rcases h with h | h | h
  · exact hpfirst h.1
  · exact hpfirst h.1
  · exact hlongfirst h.2

/-- The middle of (13): "So `b₄` is incident with `e₃`, that is, `b₄ = b₃` and `B₃`
has length 1." If `b₄` misses `e₃`, its complete edges force two adjacent degree-three
vertices with the same remaining neighbors. Cyclic 3-connectivity then excludes `b₃`. -/
theorem fourth_end_incident
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (heven : Even (trackLength B₁)) (hshort : trackLength B₂ = 1)
    (e₄ : Sym2 (Fin n)) (B₄ : List (Fin n)) (b₄ : Fin n)
    (h4 : FourthBranch G H K φ Y y₁ b b₁ b₂ e₄ B₄ b₄) : b₄ ∈ e₃ := by
  classical
  have htriad := b2_triad G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h9 hadj hXb heven
  have hgMeet := complete_at_fourth_meets G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc hadj hXb hshort e₄ B₄ b₄ h4
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  have hbcCopy := hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hshort] at he₂B₂
    exact he₂B₂
  have h02 : H.Adj b b₂ := H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)
  have hno₂ := no_extra2_away G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbcCopy h8 heven he₂eq b₄
    h4.vertex h4.ne_b h4.ne_b1 h4.ne_b2
  have hB₄pos := one_le_trackLength_of_mem h4.edge
  have hb₂miss : ∀ g ∈ incidentEdges H b₄, g ∈ completeEdges G H K φ Y → b₂ ∉ g := by
    intro g hg hgX hm
    have hgeq := eq_sym2_of_mem_mem h4.ne_b2.symm hm hg.2
    have h24 : H.Adj b₂ b₄ := H.mem_edgeSet.mp (hgeq ▸ hg.1)
    have hshort₄ := branch_length_one_of_adj J hJ H hsub.1 h4.branch h4.track hB₄pos h24
    have heq : e₄ = s(b₂, b₄) := by
      have he := h4.edge
      rw [trackEdges_eq_singleton_of_length_one h4.track hshort₄] at he
      exact he
    exact h4.extra.2 ((hgeq.trans heq.symm) ▸ hgX)
  have hmeet : ∀ g ∈ incidentEdges H b₄, g ∈ completeEdges G H K φ Y →
      b₁ ∈ g ∨ MeetEdges g e₃ := by
    intro g hg hgX
    rcases hgMeet g hg hgX with hp | he
    · obtain ⟨w, hwg, hwp⟩ := exists_common_end hp
      rcases Sym2.mem_iff.mp hwp with h | h
      · exact Or.inl (h ▸ hwg)
      · exact False.elim (hb₂miss g hg hgX (h ▸ hwg))
    · exact Or.inr he
  have hnt : ¬ (incidentEdges H b₄ ∩ completeEdges G H K φ Y).Subsingleton :=
    fun h => h4.nontriad ⟨h4.vertex, h⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, hgg⟩ := Set.not_subsingleton_iff.mp hnt
  by_contra hmiss
  have hex1 : ∃ g ∈ incidentEdges H b₄, g ∈ completeEdges G H K φ Y ∧ b₁ ∈ g := by
    rcases hmeet g₁ hg₁.1 hg₁.2 with h1 | h1
    · exact ⟨g₁, hg₁.1, hg₁.2, h1⟩
    rcases hmeet g₂ hg₂.1 hg₂.2 with h2 | h2
    · exact ⟨g₂, hg₂.1, hg₂.2, h2⟩
    exact False.elim (hgg (meeting_edges_at_vertex_subsingleton hsub.2 he₃inc.1 hmiss
      ⟨hg₁.1, h1⟩ ⟨hg₂.1, h2⟩))
  obtain ⟨g, hg, hgX, hb₁g⟩ := hex1
  have hg1 : g = s(b₄, b₁) := eq_sym2_of_mem_mem h4.ne_b1 hg.2 hb₁g
  have h41 : H.Adj b₄ b₁ := H.mem_edgeSet.mp (hg1 ▸ hg.1)
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
  have h01 := (BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mp heven
  have hc40 : col b₄ ≠ col b := h01.symm ▸ col.valid h41
  have meeting_at_b : ∀ f ∈ incidentEdges H b₄, MeetEdges f e₃ → b ∈ f := by
    intro f hf hm
    obtain ⟨w, hwf, hwe⟩ := exists_common_end hm
    by_cases hw : w = b
    · exact hw ▸ hwf
    have hw4 : w ≠ b₄ := fun h => hmiss (h ▸ hwe)
    have heq := eq_sym2_of_mem_mem (Ne.symm hw) he₃inc.2 hwe
    have hfq := eq_sym2_of_mem_mem hw4.symm hf.2 hwf
    have hbw : H.Adj b w := H.mem_edgeSet.mp (heq ▸ he₃inc.1)
    have h4w : H.Adj b₄ w := H.mem_edgeSet.mp (hfq ▸ hf.1)
    exact False.elim (hc40 (bool_eq_of_ne_ne (col w) (col b₄) (col b)
      (col.valid h4w).symm (col.valid hbw).symm))
  have hXsub : incidentEdges H b₄ ∩ completeEdges G H K φ Y ⊆ {s(b₄, b₁), s(b₄, b)} := by
    intro f hf
    rcases hmeet f hf.1 hf.2 with h1 | hm
    · exact Or.inl (eq_sym2_of_mem_mem h4.ne_b1 hf.1.2 h1)
    · exact Or.inr (eq_sym2_of_mem_mem h4.ne_b hf.1.2 (meeting_at_b f hf.1 hm))
  have hex0 : ∃ f ∈ incidentEdges H b₄, f = s(b₄, b) := by
    rcases hXsub hg₁ with h1 | h1
    · rcases hXsub hg₂ with h2 | h2
      · exact False.elim (hgg (h1.trans h2.symm))
      · exact ⟨g₂, hg₂.1, h2⟩
    · exact ⟨g₁, hg₁.1, h1⟩
  obtain ⟨f, hf, hfeq⟩ := hex0
  have h40 : H.Adj b₄ b := H.mem_edgeSet.mp (hfeq ▸ hf.1)
  obtain ⟨-, -, -, -, -, -, -, hsat₂⟩ := X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hnotXsub : (incidentEdges H b₄ \ completeEdges G H K φ Y).Subsingleton := by
    intro f hf g hg
    exact hsat₂ b₄ h4.vertex ⟨hf.1, fun h => h.elim hf.2 (hno₂ f hf.1)⟩
      ⟨hg.1, fun h => h.elim hg.2 (hno₂ g hg.1)⟩
  have hn1 : (incidentEdges H b₄ \ completeEdges G H K φ Y).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr hnotXsub
  have hn2 : (incidentEdges H b₄ ∩ completeEdges G H K φ Y).ncard ≤ 2 := by
    have h := Set.ncard_le_ncard hXsub (Set.toFinite _)
    have hp : ({s(b₄, b₁), s(b₄, b)} : Set (Sym2 (Fin n))).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le s(b₄, b₁) ({s(b₄, b)} : Set (Sym2 (Fin n)))
    omega
  have hsplit : incidentEdges H b₄ = (incidentEdges H b₄ ∩ completeEdges G H K φ Y) ∪
      (incidentEdges H b₄ \ completeEdges G H K φ Y) := by
    ext e
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hdeg₄ : (H.neighborSet b₄).ncard = 3 := by
    have hn := Set.ncard_union_le (incidentEdges H b₄ ∩ completeEdges G H K φ Y)
      (incidentEdges H b₄ \ completeEdges G H K φ Y)
    rw [← hsplit, incidentEdges_ncard] at hn
    have hv : 3 ≤ (H.neighborSet b₄).ncard := h4.vertex
    omega
  have hdeg₂ := (triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htriad).1
  have hnd : [b₂, b₄, b, b₁].Nodup := by
    simp [h4.ne_b, h4.ne_b1, h4.ne_b2, Ne.symm h4.ne_b2, hbb₂, hbb₂.symm,
      hb₁b₂.symm, hbb₁]
  obtain ⟨-, hbvs⟩ := k4_of_two_triads hJ hsub.1 hnd hb₂V h4.vertex hbV hb₁V hdeg₂ hdeg₄
    ⟨B₄, h4.branch, h4.track, hB₄pos⟩
    (linked_of_adj hb₂V hbV h02.symm) (linked_of_adj hb₂V hb₁V hadj.symm)
    (linked_of_adj h4.vertex hbV h40) (linked_of_adj h4.vertex hb₁V h41)
  have hb₃set : b₃ ∈ ({b₂, b₄, b, b₁} : Set (Fin n)) := hbvs ▸ hb₃V
  rcases hb₃set with h | h | h | h
  · exact hb₂b₃ h.symm
  · have h03 : H.Adj b b₃ := h.symm ▸ h40.symm
    have hB₃one := branch_length_one_of_adj J hJ H hsub.1 hB₃ hfrom₃ hB₃pos h03
    have he₃eq : e₃ = s(b, b₃) := by
      rw [trackEdges_eq_singleton_of_length_one hfrom₃ hB₃one] at he₃B₃
      exact he₃B₃
    exact hmiss (by rw [he₃eq, h]; simp)
  · exact hbb₃ h.symm
  · exact hb₁b₃ h.symm

/-- The bridge and all four assertions of printed claim (13). -/
theorem even_final_claim13
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (hB₁even : Even (trackLength B₁)) (hB₂odd : Odd (trackLength B₂)) :
    ∃ (e₄ : Sym2 (Fin n)) (B₄ : List (Fin n)) (b₄ : Fin n),
      e₄ ∈ incidentEdges H b₂ ∧ IsBranch H B₄ ∧ e₄ ∈ trackEdges B₄ ∧
      IsTrackFrom H B₄ b₂ b₄ ∧ b₄ = b₃ ∧ trackLength B₃ = 1 ∧
      Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ Even (trackLength B₄) := by
  classical
  obtain ⟨hshort, e₄, B₄, b₄, h4⟩ := exists_fourth G m J hJ n H K hsub φ Y hmin
    y₁ y₂ Q hQ hQY hy h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h8 h9 hadj hXb hB₁even
  have hb₄e₃ := fourth_end_incident G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h8 h9 hadj hXb hB₁even hshort e₄ B₄ b₄ h4
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  have hbcCopy := hbc
  obtain ⟨-, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  have hb₄B₃ := NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges he₃B₃ hb₄e₃
  have hb₄ : b₄ = b₃ := by
    rcases SubdivisionCompose.mem_ends_of_mem hfrom₃.2.1 hfrom₃.2.2 hb₄B₃
      (fun hi => hB₃.2.1 b₄ hi h4.vertex) with h | h
    · exact False.elim (h4.ne_b h)
    · exact h
  have he₃eq : e₃ = s(b, b₄) := eq_sym2_of_mem_mem h4.ne_b.symm he₃inc.2 hb₄e₃
  have h03 : H.Adj b b₃ := hb₄ ▸ H.mem_edgeSet.mp (he₃eq ▸ he₃inc.1)
  have hB₃one := branch_length_one_of_adj J hJ H hsub.1 hB₃ hfrom₃ hB₃pos h03
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hshort] at he₂B₂
    exact he₂B₂
  have h02 : H.Adj b b₂ := H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)
  obtain ⟨-, -, -, -, -, hd12, -, -⟩ := X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₁e₂ : e₁ ≠ e₂ := fun h => Set.disjoint_left.mp hd12 (h ▸ he₁X₁) he₂X₂
  have hall : ∀ e ∈ incidentEdges H b, e = e₁ ∨ e = e₂ ∨ e = e₃ := by
    intro e he
    by_cases h1 : e = e₁
    · exact Or.inl h1
    by_cases h2 : e = e₂
    · exact Or.inr (Or.inl h2)
    obtain ⟨C, c, hC, heC, hCfrom⟩ := branch_from_incident hJ hsub.1 hbV he
    have he₂B₂again : e₂ ∈ trackEdges B₂ := by
      rw [trackEdges_eq_singleton_of_length_one hfrom₂ hshort, he₂eq]
      rfl
    have hc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e B₁ B₂ C b₁ b₂ c :=
      ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he, h1, h2,
        hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂again, hfrom₂, hC, heC, hCfrom⟩
    have hb₄e := fourth_end_incident G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
      b e₁ e₂ e B₁ B₂ C b₁ b₂ c hc h8 h9 hadj hXb hB₁even hshort e₄ B₄ b₄ h4
    exact Or.inr (Or.inr ((eq_sym2_of_mem_mem h4.ne_b.symm he.2 hb₄e).trans he₃eq.symm))
  have hinc : incidentEdges H b = {e₁, e₂, e₃} := by
    ext e
    constructor
    · exact hall e
    · rintro (rfl | rfl | rfl) <;> assumption
  have hbdeg : (H.neighborSet b).ncard = 3 := by
    rw [← incidentEdges_ncard]
    exact Set.ncard_eq_three.mpr ⟨e₁, e₂, e₃, he₁e₂, he₃e₁.symm, he₃e₂.symm, hinc⟩
  have htriad := b2_triad G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbcCopy h9 hadj hXb hB₁even
  have hb₂deg := (triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htriad).1
  have hnd : [b, b₂, b₁, b₃].Nodup := by
    simp [hbb₁, hbb₂, hbb₃, hb₁b₂.symm, hb₁b₃, hb₂b₃]
  have hfrom₄ : IsTrackFrom H B₄ b₂ b₃ := hb₄ ▸ h4.track
  obtain ⟨hJiso, -⟩ := k4_of_two_triads hJ hsub.1 hnd hbV hb₂V hb₁V hb₃V hbdeg hb₂deg
    (linked_of_adj hbV hb₂V h02) ⟨B₁, hB₁, hfrom₁, hB₁pos⟩
    (linked_of_adj hbV hb₃V h03) (linked_of_adj hb₂V hb₁V hadj.symm)
    ⟨B₄, h4.branch, hfrom₄, one_le_trackLength_of_mem h4.edge⟩
  have hB₄even := fourth_branch_even hsub.2 hfrom₁ hB₁even hadj h03 hfrom₄
  exact ⟨e₄, B₄, b₄, h4.incident, h4.branch, h4.edge, h4.track, hb₄, hB₃one, hJiso, hB₄even⟩

end Workspace.ProofLemmas.Thm61EvenFinalClaim13
