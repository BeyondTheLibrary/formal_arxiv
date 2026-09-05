import Mathlib
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim3
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-!
# Local edge moves for 6.1, claims (5) and (6)

These lemmas spell out the paper's shorthand “apply (3) to an edge and a triad.”  At a
triad, the two non-complete incident edges are the unique edges in `X₁` and `X₂`.  Claim (3)
therefore says that every complete edge meets one of them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim5Helpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- At a triad, claim 6.1(3) makes every complete edge meet a non-complete incident edge.

This is the precise form of the paper's shorthand “by (3) applied to `g` and `v`.” -/
theorem complete_meets_noncomplete_at_triad
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (v : Fin n) (hv : Triad G H K φ Y v)
    (g : Sym2 (Fin n)) (hgX : g ∈ completeEdges G H K φ Y) :
    ∃ a : Sym2 (Fin n),
      a ∈ incidentEdges H v ∧ a ∉ completeEdges G H K φ Y ∧ MeetEdges g a := by
  classical
  obtain ⟨-, -, ⟨a₁, ha₁, -⟩, ⟨a₂, ha₂, -⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy v hv
  obtain ⟨-, -, -, hXX₁, hXX₂, -, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hmeet : MeetEdges a₁ a₂ := by
    intro hd
    exact hd v ⟨ha₁.1.2, ha₂.1.2⟩
  have hm := Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
    G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
      a₁ a₂ g ha₁.2 ha₂.2 hmeet hgX
  rcases hm with hm | hm
  · exact ⟨a₁, ha₁.1, Set.disjoint_right.mp hXX₁ ha₁.2, hm⟩
  · exact ⟨a₂, ha₂.1, Set.disjoint_right.mp hXX₂ ha₂.2, hm⟩

/-- Two distinct non-complete edges at a branch-vertex split between `X₁` and `X₂` (in one
of the two orders).  Claim (3) then makes every complete edge meet one of them. -/
theorem complete_meets_one_of_two_noncomplete
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (v : Fin n) (hv : v ∈ branchVertices H)
    (a₁ a₂ : Sym2 (Fin n)) (ha₁ : a₁ ∈ incidentEdges H v)
    (ha₂ : a₂ ∈ incidentEdges H v) (ha₁a₂ : a₁ ≠ a₂)
    (ha₁X : a₁ ∉ completeEdges G H K φ Y)
    (ha₂X : a₂ ∉ completeEdges G H K φ Y)
    (g : Sym2 (Fin n)) (hgX : g ∈ completeEdges G H K φ Y) :
    MeetEdges g a₁ ∨ MeetEdges g a₂ := by
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have split (Xi : Set (Sym2 (Fin n)))
      (hsat : SaturatesLineGraph H (completeEdges G H K φ Y ∪ Xi)) :
      a₁ ∈ Xi ∨ a₂ ∈ Xi := by
    by_contra h
    simp only [not_or] at h
    have h₁ : a₁ ∉ completeEdges G H K φ Y ∪ Xi := by simp [ha₁X, h.1]
    have h₂ : a₂ ∉ completeEdges G H K φ Y ∪ Xi := by simp [ha₂X, h.2]
    exact ha₁a₂ (hsat v hv ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩)
  have hs₁ := split (extraEdges G H K φ Y y₁) hsat₁
  have hs₂ := split (extraEdges G H K φ Y y₂) hsat₂
  have hmeet : MeetEdges a₁ a₂ := by
    intro hd
    exact hd v ⟨ha₁.2, ha₂.2⟩
  rcases hs₁ with ha₁X₁ | ha₂X₁ <;> rcases hs₂ with ha₁X₂ | ha₂X₂
  · exact False.elim ((Set.disjoint_left.mp hX₁X₂ ha₁X₁) ha₁X₂)
  · exact Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
      G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
        a₁ a₂ g ha₁X₁ ha₂X₂ hmeet hgX
  · have hm := Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
      G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
        a₂ a₁ g ha₂X₁ ha₁X₂ (by
          intro hd
          apply hmeet
          intro w hw
          exact hd w ⟨hw.2, hw.1⟩) hgX
    exact hm.elim Or.inr Or.inl
  · exact False.elim ((Set.disjoint_left.mp hX₁X₂ ha₂X₁) ha₂X₂)

/-- The first and last edges of a branch of length at least two cannot be joined by an
external edge at the last end.  Hence, if claim (3) makes the first edge meet a non-complete
edge at a triad, that edge is the last branch edge and the branch has length two.  The unique
chosen complete edge at the triad then lies outside the branch.

This is the first sentence of the proof of 6.1(5). -/
theorem long_branch_at_triad
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (B : List (Fin n)) (b c : Fin n) (e f : Sym2 (Fin n))
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B b c)
    (hlong : 1 < trackLength B)
    (heB : e ∈ trackEdges B) (heb : b ∈ e)
    (heX : e ∈ completeEdges G H K φ Y)
    (hfinc : f ∈ incidentEdges H c) (hfX : f ∈ completeEdges G H K φ Y)
    (hctriad : Triad G H K φ Y c) :
    trackLength B = 2 ∧ f ∉ trackEdges B := by
  classical
  have hpos : 1 ≤ trackLength B := by omega
  have hbc : b ≠ c := track_ends_ne hfrom hpos
  obtain ⟨a, hainc, haX, hmea⟩ :=
    complete_meets_noncomplete_at_triad G hG H K φ Y hYmajor hmin
      y₁ y₂ Q hQ hQY hy hQodd c hctriad e heX
  have haB : a ∈ trackEdges B := by
    by_contra haout
    obtain ⟨w, hwe, hwa⟩ := exists_common_end hmea
    rcases external_edge_meets_branch_only_at_ends
        hB hfrom heB hainc.1 haout hwa hwe with hwb | hwc
    · have haeq : a = s(b, c) := eq_sym2_of_mem_mem hbc (hwb ▸ hwa) hainc.2
      have hadj : H.Adj b c := by
        apply H.mem_edgeSet.mp
        rw [← haeq]
        exact hainc.1
      exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub.1 B b c hB hfrom (by omega)).2.2.2 hadj
    · have heq : e = s(b, c) := eq_sym2_of_mem_mem hbc heb (hwc ▸ hwe)
      have hadj : H.Adj b c := by
        apply H.mem_edgeSet.mp
        rw [← heq]
        obtain ⟨i, hi, rfl⟩ := heB
        exact hfrom.1.2.2 i hi
      exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub.1 B b c hB hfrom (by omega)).2.2.2 hadj
  have hle : trackLength B ≤ 2 :=
    trackLength_le_two_of_end_edges_meet hfrom hpos heB heb haB hainc.2 hmea
  have hlen : trackLength B = 2 := by omega
  refine ⟨hlen, ?_⟩
  intro hfB
  have hlist : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
  have hfa := (trackEdge_at_last hfrom hlist hfB hfinc.2).trans
    (trackEdge_at_last hfrom hlist haB hainc.2).symm
  apply haX
  rwa [← hfa]

/-- If the complete edge at the far end of a long branch meets its first edge, it is the last
edge of that branch, and the branch has length two. -/
theorem same_branch_complete_shape
    {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H)
    (B : List W) (b c : W) (e f : Sym2 W)
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B b c)
    (hlong : 1 < trackLength B)
    (heB : e ∈ trackEdges B) (heb : b ∈ e)
    (hfinc : f ∈ incidentEdges H c) (hef : e ≠ f) (hmeet : MeetEdges f e) :
    trackLength B = 2 ∧ f ∈ trackEdges B := by
  have hpos : 1 ≤ trackLength B := by omega
  have hbc : b ≠ c := track_ends_ne hfrom hpos
  have hfB : f ∈ trackEdges B := by
    by_contra hfout
    obtain ⟨w, hwf, hwe⟩ := exists_common_end hmeet
    rcases external_edge_meets_branch_only_at_ends
        hB hfrom heB hfinc.1 hfout hwf hwe with hwb | hwc
    · have hfeq : f = s(b, c) := eq_sym2_of_mem_mem hbc (hwb ▸ hwf) hfinc.2
      have hadj : H.Adj b c := by
        apply H.mem_edgeSet.mp
        rw [← hfeq]
        exact hfinc.1
      exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub B b c hB hfrom (by omega)).2.2.2 hadj
    · have heq : e = s(b, c) := eq_sym2_of_mem_mem hbc heb (hwc ▸ hwe)
      have hadj : H.Adj b c := by
        apply H.mem_edgeSet.mp
        rw [← heq]
        obtain ⟨i, hi, rfl⟩ := heB
        exact hfrom.1.2.2 i hi
      exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub B b c hB hfrom (by omega)).2.2.2 hadj
  have hmeet' : MeetEdges e f := by
    intro hd
    apply hmeet
    intro w hw
    exact hd w ⟨hw.2, hw.1⟩
  have hle := trackLength_le_two_of_end_edges_meet
    hfrom hpos heB heb hfB hfinc.2 hmeet'
  exact ⟨by omega, hfB⟩

/-- Every edge at a branch-vertex of a subdivision of a 3-connected graph belongs to a branch
which can be oriented away from that vertex. -/
theorem branch_from_incident
    {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H) (b : W) (hb : b ∈ branchVertices H)
    (e : Sym2 W) (he : e ∈ incidentEdges H b) :
    ∃ (B : List W) (c : W), IsBranch H B ∧ e ∈ trackEdges B ∧ IsTrackFrom H B b c := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices
      hι htrack hlen hdisj hnew hdeg
  have hbrange : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisj hcover hedges
  have hinterior : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v),
      w ∉ branchVertices H := by
    intro u v huv w hw hwbranch
    exact hnew u v huv w hw (hbrange hwbranch)
  have hTbranch : ∀ u v : U, J.Adj u v → IsBranch H (T u v) := by
    intro u v huv
    exact Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
      (htrack u v huv) (fun h => huv.ne (hι h)) (hinterior u v huv)
      (hrange ⟨u, rfl⟩) (hrange ⟨v, rfl⟩)
  have heE : e ∈ H.edgeSet := he.1
  rw [hedges] at heE
  simp only [Set.mem_iUnion] at heE
  obtain ⟨u, v, huv, heT⟩ := heE
  have hbT : b ∈ T u v :=
    Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
      heT he.2
  have hbnotint : b ∉ trackInterior (T u v) := fun hbint => hinterior u v huv b hbint hb
  rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (htrack u v huv).2.1 (htrack u v huv).2.2 hbT hbnotint with hbU | hbV
  · refine ⟨T u v, ι v, hTbranch u v huv, heT, ?_⟩
    rw [hbU]
    exact htrack u v huv
  · refine ⟨T v u, ι u, hTbranch v u huv.symm, ?_, ?_⟩
    · rw [hrev u v huv, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
      exact heT
    · rw [hbV]
      exact htrack v u huv.symm

end Workspace.ProofLemmas.Thm61Claim5Helpers
