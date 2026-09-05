import Mathlib
import Workspace.ProofLemmas.Thm61Claim1
import Workspace.ProofLemmas.Thm61Claim2
import Workspace.ProofLemmas.Thm61Claim4
import Workspace.ProofLemmas.Thm61Claim6Helpers
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# The asymmetric case in 6.1(6)

This file treats the orientation in which `B₁` has one edge and `B₂` is long.  The opposite
orientation follows by reversing the antipath and swapping subscripts 1 and 2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim6Oriented

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61Claim5Helpers
open Workspace.ProofLemmas.Thm61Claim6Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- Claim 6.1(6), after orienting the unique long branch as `B₂`. -/
theorem oriented
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃)
    (hB₁one : trackLength B₁ = 1) (hB₂long : 1 < trackLength B₂)
    (hB₃one : trackLength B₃ = 1) (hbtri : Triad G H K φ Y b) :
    Thm61Concl G m J n H K φ Y := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  rcases hf with ⟨hf₁, hf₂, hf₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hf' : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃ :=
    ⟨hf₁, hf₂, hf₃⟩
  rcases branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, hB₃pos, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
      hb₁b₂, hb₁b₃, hb₂b₃⟩
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₁X : e₁ ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hXX₁ he₁X₁
  have he₂X : e₂ ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hXX₂ he₂X₂
  have he₁e₂ : e₁ ≠ e₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ he₁X₁) (h ▸ he₂X₂)
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have he₁eq : e₁ = s(b, b₁) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁one] at he₁B₁
    exact Set.mem_singleton_iff.mp he₁B₁
  have he₃eq : e₃ = s(b, b₃) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₃ hB₃one] at he₃B₃
    exact Set.mem_singleton_iff.mp he₃B₃
  have hbb₁adj : H.Adj b b₁ := H.mem_edgeSet.mp (he₁eq ▸ he₁inc.1)
  have hbb₃adj : H.Adj b b₃ := H.mem_edgeSet.mp (he₃eq ▸ he₃inc.1)
  have hb₃tri := Workspace.ProofLemmas.Thm61Claim4.thm_6_1_claim4
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
      f₁ f₂ f₃ hf'
  have hmeet12 : MeetEdges e₁ e₂ := by
    intro hd
    exact hd b ⟨he₁inc.2, he₂inc.2⟩
  have hm₂ := complete_meets_one_of_two_noncomplete
    G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
      b hbV e₁ e₂ he₁inc he₂inc he₁e₂ he₁X he₂X f₂ hf₂.1
  rcases hm₂ with hf₂e₁ | hf₂e₂
  · have hf₂ne₂ : f₂ ≠ e₂ := fun h => he₂X (h ▸ hf₂.1)
    obtain ⟨-, -, hf₂eq⟩ := identify_cross_meeting
      J hJ H hsub.1 hB₁ hfrom₁ hB₂ hfrom₂ hB₁pos hB₂pos
        hb₂V hbb₂.symm hb₁b₂.symm he₁B₁ he₁inc.2 he₂B₂ he₂inc.2
        hf₂.1.1 hf₂.2.1.2 hf₂ne₂ hf₂e₁
    have hf₂out : f₂ ∉ trackEdges B₂ := by
      intro hf₂B
      exact branch_edge_avoids_other_branchVertex hB₂ hfrom₂ hf₂B hb₁V
        hbb₁.symm hb₁b₂ (by rw [hf₂eq]; simp)
    have hf₂adj : H.Adj b₁ b₂ := by
      apply H.mem_edgeSet.mp
      simpa [hf₂eq, Sym2.eq_swap] using hf₂.1.1
    obtain ⟨a, hainc, haX, hfa⟩ :=
      complete_meets_noncomplete_at_triad G hG H K φ Y hYmajor hmin
        y₁ y₂ Q hQ hQY hy hQodd b₃ hb₃tri f₂ hf₂.1
    obtain ⟨w, hwf, hwa⟩ := exists_common_end hfa
    rw [hf₂eq] at hwf
    have hw : w = b₂ := by
      rcases Sym2.mem_iff.mp hwf with hwb₂ | hwb₁
      · exact hwb₂
      · have haeq : a = s(b₁, b₃) :=
          eq_sym2_of_mem_mem hb₁b₃ (hwb₁ ▸ hwa) hainc.2
        have hadj : H.Adj b₁ b₃ := H.mem_edgeSet.mp (haeq ▸ hainc.1)
        exact False.elim (no_triangle_of_bipartite hsub.2 hbb₁adj hadj hbb₃adj)
    have haeq : a = s(b₂, b₃) :=
      eq_sym2_of_mem_mem hb₂b₃ (hw ▸ hwa) hainc.2
    have haadj : H.Adj b₂ b₃ := H.mem_edgeSet.mp (haeq ▸ hainc.1)
    have hainc₂ : a ∈ incidentEdges H b₂ := by
      refine ⟨hainc.1, ?_⟩
      rw [haeq]
      simp

    -- Let `e₂'` be the last edge of `B₂` at `b₂`.
    have hB₂len : 3 ≤ B₂.length := by simp only [trackLength] at hB₂long; omega
    let e₂' : Sym2 (Fin n) :=
      s(B₂[B₂.length - 2]'(by omega), B₂[B₂.length - 1]'(by omega))
    have he₂'B : e₂' ∈ trackEdges B₂ := by
      refine ⟨B₂.length - 2, by omega, ?_⟩
      dsimp [e₂']
      congr 1 <;> apply geq <;> omega
    have he₂'E : e₂' ∈ H.edgeSet := by
      obtain ⟨i, hi, heq⟩ := he₂'B
      rw [heq]
      exact hfrom₂.1.2.2 i hi
    have hlast₂ : B₂[B₂.length - 1]'(by omega) = b₂ :=
      last_getElem hfrom₂.2.2 (by omega)
    have hb₂e₂' : b₂ ∈ e₂' := by
      dsimp [e₂']
      rw [← hlast₂]
      simp
    have he₂'inc : e₂' ∈ incidentEdges H b₂ := ⟨he₂'E, hb₂e₂'⟩
    have he₂'ne₂ : e₂' ≠ e₂ := by
      intro h
      have helast := trackEdge_at_last hfrom₂ (by omega) he₂'B hb₂e₂'
      have hehead := trackEdge_at_head hfrom₂ (by omega) he₂B₂ he₂inc.2
      have heq := helast.symm.trans (h.trans hehead)
      rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have hi := hfrom₂.1.2.1.getElem_inj_iff.mp h₁
        omega
      · have hi := hfrom₂.1.2.1.getElem_inj_iff.mp h₂
        omega

    have hb₁tri : Triad G H K φ Y b₁ := by
      refine ⟨hb₁V, ?_⟩
      by_contra hnontri
      have hnt : (incidentEdges H b₁ ∩ completeEdges G H K φ Y).Nontrivial :=
        Set.not_subsingleton_iff.mp hnontri
      obtain ⟨x, hx, z, hz, hxz⟩ := hnt
      obtain ⟨x, hx, hxf₂⟩ : ∃ x,
          x ∈ incidentEdges H b₁ ∩ completeEdges G H K φ Y ∧ x ≠ f₂ := by
        by_cases h : x = f₂
        · exact ⟨z, hz, fun hz2 => hxz (h.trans hz2.symm)⟩
        · exact ⟨x, hx, h⟩
      have he₂'X : e₂' ∈ completeEdges G H K φ Y := by
        by_contra he₂'nX
        have hae₂' : a ≠ e₂' := by
          intro h
          exact branch_edge_avoids_other_branchVertex hB₂ hfrom₂ he₂'B hb₃V
            hbb₃.symm hb₂b₃.symm (by rw [← h, haeq]; simp)
        have hm := complete_meets_one_of_two_noncomplete
          G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
            b₂ hb₂V a e₂' hainc₂ he₂'inc hae₂' haX he₂'nX x hx.2
        rcases hm with hxa | hxe
        · obtain ⟨w, hwx, hwa'⟩ := exists_common_end hxa
          rw [haeq] at hwa'
          rcases Sym2.mem_iff.mp hwa' with hwb₂ | hwb₃
          · have hxeq : x = f₂ := by
              rw [hf₂eq]
              exact eq_sym2_of_mem_mem hb₁b₂.symm (hwb₂ ▸ hwx) hx.1.2
            exact False.elim (hxf₂ hxeq)
          · have hxeq : x = s(b₁, b₃) :=
              eq_sym2_of_mem_mem hb₁b₃ hx.1.2 (hwb₃ ▸ hwx)
            have hadj : H.Adj b₁ b₃ := H.mem_edgeSet.mp (hxeq ▸ hx.1.1)
            exact False.elim (no_triangle_of_bipartite hsub.2 hbb₁adj hadj hbb₃adj)
        · obtain ⟨w, hwx, hwe⟩ := exists_common_end hxe
          by_cases hwb₁ : w = b₁
          · exact branch_edge_avoids_other_branchVertex hB₂ hfrom₂ he₂'B hb₁V
              hbb₁.symm hb₁b₂ (hwb₁ ▸ hwe)
          by_cases hwb₂ : w = b₂
          · have hxeq : x = f₂ := by
              rw [hf₂eq]
              exact eq_sym2_of_mem_mem hb₁b₂.symm (hwb₂ ▸ hwx) hx.1.2
            exact False.elim (hxf₂ hxeq)
          have hxeq : x = s(b₁, w) :=
            eq_sym2_of_mem_mem (fun h => hwb₁ h.symm) hx.1.2 hwx
          have heeq : e₂' = s(w, b₂) :=
            eq_sym2_of_mem_mem hwb₂ hwe hb₂e₂'
          have h1w : H.Adj b₁ w := H.mem_edgeSet.mp (hxeq ▸ hx.1.1)
          have hwb₂adj : H.Adj w b₂ := H.mem_edgeSet.mp (heeq ▸ he₂'E)
          exact False.elim (no_triangle_of_bipartite hsub.2 h1w hwb₂adj hf₂adj)
      have hm := complete_meets_one_of_two_noncomplete
        G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
          b hbV e₁ e₂ he₁inc he₂inc he₁e₂ he₁X he₂X e₂' he₂'X
      have he₂'e₁ : MeetEdges e₂' e₁ → False := by
        intro hm
        have he₂'out : e₂' ∉ trackEdges B₁ := by
          intro he
          exact branch_edge_avoids_other_branchVertex hB₁ hfrom₁ he hb₂V
            hbb₂.symm hb₁b₂.symm hb₂e₂'
        obtain ⟨w, hwe, hwe₁⟩ := exists_common_end hm
        rcases external_edge_meets_branch_only_at_ends
            hB₁ hfrom₁ he₁B₁ he₂'E he₂'out hwe hwe₁ with hwb | hwb₁
        · have heq : e₂' = e₂ := by
            have he₂'atb : b ∈ e₂' := hwb ▸ hwe
            have hfirst := trackEdge_at_head hfrom₂ (by omega) he₂'B he₂'atb
            have hfirst₂ := trackEdge_at_head hfrom₂ (by omega) he₂B₂ he₂inc.2
            exact hfirst.trans hfirst₂.symm
          exact he₂'ne₂ heq
        · exact branch_edge_avoids_other_branchVertex hB₂ hfrom₂ he₂'B hb₁V
            hbb₁.symm hb₁b₂ (hwb₁ ▸ hwe)
      have he₂'e₂ : MeetEdges e₂' e₂ := hm.resolve_left he₂'e₁
      obtain ⟨hB₂two, -⟩ := same_branch_complete_shape
        J hJ H hsub.1 B₂ b b₂ e₂ e₂' hB₂ hfrom₂ hB₂long
          he₂B₂ he₂inc.2 he₂'inc he₂'ne₂.symm he₂'e₂
      have hlen₂ : B₂.length = 3 := by simp only [trackLength] at hB₂two; omega
      let w : Fin n := B₂[1]'(by omega)
      have hhead₂ := trackEdge_at_head hfrom₂ (by omega) he₂B₂ he₂inc.2
      have he₂eq : e₂ = s(b, w) := by
        rw [hhead₂]
        dsimp [w]
        congr 1
        exact head_getElem hfrom₂.2.1 (by omega)
      have he₂'eq : e₂' = s(w, b₂) := by
        have hlastedge := trackEdge_at_last hfrom₂ (by omega) he₂'B hb₂e₂'
        rw [hlastedge]
        congr 1
        · dsimp [w]
          apply geq
          omega
      have hbwadj : H.Adj b w := H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)
      have hwb₂adj : H.Adj w b₂ := H.mem_edgeSet.mp (he₂'eq ▸ he₂'E)
      have hnd : [b₁, b, w, b₂].Nodup := by
        have hwb : w ≠ b := by
          intro h
          have hi := hfrom₂.1.2.1.getElem_inj_iff.mp
            (h.trans (head_getElem hfrom₂.2.1 (by omega)).symm)
          omega
        have hwb₂ : w ≠ b₂ := by
          intro h
          have hi := hfrom₂.1.2.1.getElem_inj_iff.mp
            (h.trans (last_getElem hfrom₂.2.2 (by omega)).symm)
          omega
        have hb₁w : b₁ ≠ w := by
          intro h
          have hwint : w ∈ trackInterior B₂ :=
            Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem B₂ 0 (by
              rw [hlen₂]
              omega)
          exact hB₂.2.1 w hwint (h ▸ hb₁V)
        simp [hbb₁.symm, hb₁w, hb₁b₂, hwb.symm, hbb₂, hwb₂]
      exact Workspace.ProofLemmas.Thm61Claim2.thm_6_1_claim2
        G hG H hsub.2 K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
          b₁ b w b₂ hnd hbb₁adj.symm hbwadj hwb₂adj hf₂adj.symm hbV
          (by simpa [he₁eq, Sym2.eq_swap] using he₁X₁)
          (by simpa [he₂eq] using he₂X₂)
          (by simpa [he₂'eq] using he₂'X)
          (by simpa [hf₂eq, Sym2.eq_swap] using hf₂.1)
    have hB₁rev : IsBranch H B₁.reverse := isBranch_reverse hB₁
    have he₁rev : e₁ ∈ trackEdges B₁.reverse := by
      simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using he₁B₁
    have hfrom₁rev : IsTrackFrom H B₁.reverse b₁ b :=
      Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom₁
    have hb₂tri := triad_across_complete_edge
        G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
        y₁ y₂ Q hQ hQY hy hQodd b₁ b b₂ e₁ f₂ B₁.reverse hb₁tri hbV hb₂V
        hb₁b₂ ⟨he₁inc.1, by rw [he₁eq]; simp⟩ (by simpa [he₁eq] using he₁X₁)
        hB₁rev he₁rev hfrom₁rev
        ⟨hf₂.1.1, by rw [hf₂eq]; simp⟩ hf₂.1 (by rw [hf₂eq, Sym2.eq_swap])
    obtain ⟨hbdeg, -, -, -⟩ :=
      triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b hbtri
    obtain ⟨hb₂deg, -, -, -⟩ :=
      triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ hb₂tri

    -- The degree-three vertices `b,b₂` have the same two other neighbours.  Lift them to
    -- the source graph and use 3-connectivity to see that these four vertices exhaust it.
    obtain ⟨ι, T, hι, htrack, hTlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub.1
    have hJdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
    have hbrange : branchVertices H ⊆ Set.range ι :=
      Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
        htrack hrev hdisj hcover hedges
    obtain ⟨u₀, hu₀⟩ := hbrange hbV
    obtain ⟨u₁, hu₁⟩ := hbrange hb₁V
    obtain ⟨u₂, hu₂⟩ := hbrange hb₂V
    obtain ⟨u₃, hu₃⟩ := hbrange hb₃V
    have h0 : b = ι u₀ := hu₀.symm
    have h1 : b₁ = ι u₁ := hu₁.symm
    have h2 : b₂ = ι u₂ := hu₂.symm
    have h3 : b₃ = ι u₃ := hu₃.symm
    have hu01 : u₀ ≠ u₁ := fun h => hbb₁ (by rw [h0, h1, h])
    have hu02 : u₀ ≠ u₂ := fun h => hbb₂ (by rw [h0, h2, h])
    have hu03 : u₀ ≠ u₃ := fun h => hbb₃ (by rw [h0, h3, h])
    have hu12 : u₁ ≠ u₂ := fun h => hb₁b₂ (by rw [h1, h2, h])
    have hu13 : u₁ ≠ u₃ := fun h => hb₁b₃ (by rw [h1, h3, h])
    have hu23 : u₂ ≠ u₃ := fun h => hb₂b₃ (by rw [h2, h3, h])
    have lift_adj {p q : Fin m} (hpq : H.Adj (ι p) (ι q)) : J.Adj p q :=
      original_adj_of_subdivision_adj hι htrack hnew hedges hpq
    have hJ01 : J.Adj u₀ u₁ :=
      original_adj_of_branch_ends hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg
        hB₁ hfrom₁ hB₁pos h0 h1
    have hJ02 : J.Adj u₀ u₂ :=
      original_adj_of_branch_ends hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg
        hB₂ hfrom₂ hB₂pos h0 h2
    have hJ03 : J.Adj u₀ u₃ :=
      original_adj_of_branch_ends hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg
        hB₃ hfrom₃ hB₃pos h0 h3
    have hJ12 : J.Adj u₁ u₂ := lift_adj (by simpa [← h1, ← h2] using hf₂adj)
    have hJ23 : J.Adj u₂ u₃ := lift_adj (by simpa [← h2, ← h3] using haadj)
    have hJdeg0 : (J.neighborSet u₀).ncard = 3 := by
      apply le_antisymm
      · calc
          _ ≤ (H.neighborSet (ι u₀)).ncard :=
            original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew u₀
          _ = 3 := by rw [← h0, hbdeg]
      · exact hJdeg u₀
    have hJdeg2 : (J.neighborSet u₂).ncard = 3 := by
      apply le_antisymm
      · calc
          _ ≤ (H.neighborSet (ι u₂)).ncard :=
            original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew u₂
          _ = 3 := by rw [← h2, hb₂deg]
      · exact hJdeg u₂
    have hall : ∀ x : Fin m, x = u₀ ∨ x = u₂ ∨ x = u₁ ∨ x = u₃ :=
      four_vertices_of_two_degree_three hJ hJ02 hJ01 hJ03 hJ12.symm hJ23
        hu13 hJdeg0 hJdeg2
    have hJ13 : J.Adj u₁ u₃ := by
      by_contra hnot
      have hsubN : J.neighborSet u₁ ⊆ ({u₀, u₂} : Set (Fin m)) := by
        intro x hx
        rcases hall x with rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact False.elim (J.loopless.irrefl _ hx)
        · exact False.elim (hnot hx)
      have hle := Set.ncard_le_ncard hsubN (Set.toFinite _)
      rw [Set.ncard_pair hu02] at hle
      have := hJdeg u₁
      omega
    have hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) :=
      iso_top_of_four_vertices hu02 hu01 hu03 hu12.symm hu23 hu13
        hall hJ02 hJ01 hJ03 hJ12.symm hJ23 hJ13
    have hbvsub : branchVertices H ⊆ ({b, b₁, b₂, b₃} : Set (Fin n)) := by
      intro x hx
      obtain ⟨u, hu⟩ := hbrange hx
      rcases hall u with rfl | rfl | rfl | rfl
      · simp [hu, h0]
      · simp [hu, h2]
      · simp [hu, h1]
      · simp [hu, h3]
    have hbvsup : ({b, b₁, b₂, b₃} : Set (Fin n)) ⊆ branchVertices H := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hbV
      · exact hb₁V
      · exact hb₂V
      · exact hb₃V
    have hbveq : branchVertices H = ({b, b₁, b₂, b₃} : Set (Fin n)) :=
      Set.Subset.antisymm hbvsub hbvsup
    have hcycle : [b, b₁, b₂, b₃].Nodup := by
      simp [hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃]
    obtain ⟨-, hsub4⟩ := Workspace.ProofLemmas.Thm61Claim1Geometry.source_is_k4
      m J hJ H hsub.1 b b₁ b₂ b₃ hcycle hbveq
    obtain ⟨Bp, Bq, hBpfrom, hBqfrom, hBppos, hBqpos, -, -, hPQdisj,
        hPavoid, hQavoid, hedgeDecomp⟩ :=
      k4_structure hsub4 hsub.2 b b₁ b₂ b₃ hcycle hbveq
        hbb₁adj hf₂adj haadj hbb₃adj.symm
    have hBpbranch : IsBranch H Bp := by
      apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
        hBpfrom hb₁b₃
      · intro w hw hwbranch
        have hwn1 := Workspace.ProofLemmas.SubdivisionCompose.ne_head_of_mem_trackInterior
          hBpfrom.1.2.1 hBpfrom.2.1 hw
        have hwn3 := Workspace.ProofLemmas.SubdivisionCompose.ne_getLast_of_mem_trackInterior
          hBpfrom.1.2.1 hBpfrom.2.2 hw
        have hav := hPavoid w (Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hw)
        rw [hbveq] at hwbranch
        rcases hwbranch with h | h | h | h
        · exact hav.1 h
        · exact hwn1 h
        · exact hav.2 h
        · exact hwn3 h
      · exact hb₁V
      · exact hb₃V
    have hBqbranch : IsBranch H Bq := by
      apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
        hBqfrom hbb₂.symm
      · intro w hw hwbranch
        have hwn2 := Workspace.ProofLemmas.SubdivisionCompose.ne_head_of_mem_trackInterior
          hBqfrom.1.2.1 hBqfrom.2.1 hw
        have hwn0 := Workspace.ProofLemmas.SubdivisionCompose.ne_getLast_of_mem_trackInterior
          hBqfrom.1.2.1 hBqfrom.2.2 hw
        have hav := hQavoid w (Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hw)
        rw [hbveq] at hwbranch
        rcases hwbranch with h | h | h | h
        · exact hwn0 h
        · exact hav.1 h
        · exact hwn2 h
        · exact hav.2 h
      · exact hb₂V
      · exact hbV

    -- Let `r` and `q` be the first edges of the two diagonal branches.
    have hBplen : 2 ≤ Bp.length := by simp only [trackLength] at hBppos; omega
    have hBqlen : 2 ≤ Bq.length := by simp only [trackLength] at hBqpos; omega
    let r : Sym2 (Fin n) := s(Bp[0]'(by omega), Bp[1]'(by omega))
    let q : Sym2 (Fin n) := s(Bq[0]'(by omega), Bq[1]'(by omega))
    have hrB : r ∈ trackEdges Bp := ⟨0, by omega, rfl⟩
    have hqB : q ∈ trackEdges Bq := ⟨0, by omega, rfl⟩
    have hrE : r ∈ H.edgeSet := hBpfrom.1.2.2 0 (by omega)
    have hqE : q ∈ H.edgeSet := hBqfrom.1.2.2 0 (by omega)
    have hBp0 : Bp[0]'(by omega) = b₁ := head_getElem hBpfrom.2.1 (by omega)
    have hBq0 : Bq[0]'(by omega) = b₂ := head_getElem hBqfrom.2.1 (by omega)
    have hb₁r : b₁ ∈ r := by dsimp [r]; rw [← hBp0]; simp
    have hb₂q : b₂ ∈ q := by dsimp [q]; rw [← hBq0]; simp
    have hrinc : r ∈ incidentEdges H b₁ := ⟨hrE, hb₁r⟩
    have hqinc : q ∈ incidentEdges H b₂ := ⟨hqE, hb₂q⟩
    have hf₂inc₁ : f₂ ∈ incidentEdges H b₁ := by
      refine ⟨hf₂.1.1, ?_⟩
      rw [hf₂eq]
      simp
    have hrne : r ≠ f₂ := by
      intro h
      have hb₂r : b₂ ∈ r := by rw [h, hf₂eq]; simp
      have hb₂Bp := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
        hrB hb₂r
      exact (hPavoid b₂ hb₂Bp).2 rfl
    have hqne : q ≠ f₂ := by
      intro h
      have hb₁q : b₁ ∈ q := by rw [h, hf₂eq]; simp
      have hb₁Bq := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
        hqB hb₁q
      exact (hQavoid b₁ hb₁Bq).1 rfl
    have hrX : r ∉ completeEdges G H K φ Y := by
      intro hrX
      exact hrne (hb₁tri.2 ⟨hrinc, hrX⟩ ⟨hf₂inc₁, hf₂.1⟩)
    have hqX : q ∉ completeEdges G H K φ Y := by
      intro hqX
      exact hqne (hb₂tri.2 ⟨hqinc, hqX⟩ ⟨hf₂.2.1, hf₂.1⟩)
    have he₁r : e₁ ≠ r := by
      intro h
      have hbBp := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
        hrB (h ▸ he₁inc.2)
      exact (hPavoid b hbBp).1 rfl
    have haq : a ≠ q := by
      intro h
      have hb₃Bq := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
        hqB (h ▸ hainc.2)
      exact (hQavoid b₃ hb₃Bq).2 rfl

    have noXq : ∀ x ∈ trackEdges Bq, x ∉ completeEdges G H K φ Y := by
      intro x hxB hxX
      have hm := complete_meets_one_of_two_noncomplete
        G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
          b₁ hb₁V e₁ r ⟨he₁inc.1, by rw [he₁eq]; simp⟩ hrinc he₁r he₁X hrX x hxX
      rcases hm with hxe | hxr
      · obtain ⟨w, hwx, hwe⟩ := exists_common_end hxe
        have hwBq := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
          hxB hwx
        rw [he₁eq] at hwe
        rcases Sym2.mem_iff.mp hwe with hwb | hwb₁
        · have hxinc : x ∈ incidentEdges H b := ⟨hxX.1, hwb ▸ hwx⟩
          have hxeq := hbtri.2 ⟨hxinc, hxX⟩ ⟨he₃inc, he₃X⟩
          have hb₃x : b₃ ∈ x := by
            rw [hxeq, he₃eq]
            simp
          have hb₃Bq := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
            hxB hb₃x
          exact (hQavoid b₃ hb₃Bq).2 rfl
        · exact (hQavoid b₁ (hwb₁ ▸ hwBq)).1 rfl
      · obtain ⟨w, hwx, hwr⟩ := exists_common_end hxr
        have hwBq := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
          hxB hwx
        have hwBp := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
          hrB hwr
        exact hPQdisj w hwBp hwBq
    have noXp : ∀ x ∈ trackEdges Bp, x ∉ completeEdges G H K φ Y := by
      intro x hxB hxX
      have hm := complete_meets_one_of_two_noncomplete
        G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
          b₂ hb₂V a q hainc₂ hqinc haq haX hqX x hxX
      rcases hm with hxa | hxq
      · obtain ⟨w, hwx, hwa'⟩ := exists_common_end hxa
        have hwBp := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
          hxB hwx
        rw [haeq] at hwa'
        rcases Sym2.mem_iff.mp hwa' with hwb₂ | hwb₃
        · exact (hPavoid b₂ (hwb₂ ▸ hwBp)).2 rfl
        · have hxinc : x ∈ incidentEdges H b₃ := ⟨hxX.1, hwb₃ ▸ hwx⟩
          have he₃inc₃ : e₃ ∈ incidentEdges H b₃ := by
            refine ⟨he₃inc.1, ?_⟩
            rw [he₃eq]
            simp
          have hxeq := hb₃tri.2 ⟨hxinc, hxX⟩ ⟨he₃inc₃, he₃X⟩
          have hbx : b ∈ x := by
            rw [hxeq, he₃eq]
            simp
          have hbBp := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
            hxB hbx
          exact (hPavoid b hbBp).1 rfl
      · obtain ⟨w, hwx, hwq⟩ := exists_common_end hxq
        have hwBp := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
          hxB hwx
        have hwBq := Workspace.ProofLemmas.NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges
          hqB hwq
        exact hPQdisj w hwBp hwBq
    have hXC : completeEdges G H K φ Y ⊆
        ({s(b, b₁), s(b₁, b₂), s(b₂, b₃), s(b₃, b)} : Set (Sym2 (Fin n))) := by
      intro x hx
      have hxE : x ∈ H.edgeSet := hx.1
      rw [hedgeDecomp] at hxE
      rcases hxE with (hxC | hxP) | hxQ
      · exact hxC
      · exact False.elim (noXp x hxP hx)
      · exact False.elim (noXq x hxQ hx)
    have hXtwo : completeEdges G H K φ Y ⊆ ({f₂, e₃} : Set (Sym2 (Fin n))) := by
      intro x hx
      have hxC := hXC hx
      rcases hxC with hx1 | hx2 | hx3 | hx4
      · exact False.elim (he₁X (by simpa [he₁eq, ← hx1] using hx))
      · left
        rw [hf₂eq, Sym2.eq_swap]
        exact hx2
      · exact False.elim (haX (by simpa [haeq, ← hx3] using hx))
      · right
        rw [he₃eq, Sym2.eq_swap]
        exact hx4
    have hXcard : (completeEdges G H K φ Y).ncard ≤ 3 := by
      calc
        _ ≤ ({f₂, e₃} : Set (Sym2 (Fin n))).ncard :=
          Set.ncard_le_ncard hXtwo (Set.toFinite _)
        _ ≤ 3 := by
          have := Set.ncard_insert_le f₂ ({e₃} : Set (Sym2 (Fin n)))
          simp at this ⊢
          omega
    exact Workspace.ProofLemmas.Thm61Claim1.thm_6_1_claim_1
      G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
        y₁ y₂ Q hQ hQY hy b b₁ b₂ b₃ hcycle hbveq
        hbb₁adj hf₂adj haadj hbb₃adj.symm hXC hXcard
  · obtain ⟨-, hf₂B⟩ := same_branch_complete_shape
      J hJ H hsub.1 B₂ b b₂ e₂ f₂ hB₂ hfrom₂ hB₂long
        he₂B₂ he₂inc.2 hf₂.2.1 (fun h => he₂X (h ▸ hf₂.1)) hf₂e₂
    exact conclusion_of_chosen_in_long_branch
      G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
        y₁ y₂ Q hQ hQY hy hQodd B₂ b b₂ f₂ hB₂ hfrom₂ hB₂long hb₂V hf₂ hf₂B

end Workspace.ProofLemmas.Thm61Claim6Oriented
