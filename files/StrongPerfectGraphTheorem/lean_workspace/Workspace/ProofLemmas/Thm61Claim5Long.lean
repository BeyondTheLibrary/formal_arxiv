import Mathlib
import Workspace.ProofLemmas.Thm61Claim1
import Workspace.ProofLemmas.Thm61Claim4
import Workspace.ProofLemmas.Thm61Claim5Helpers
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.Thm61Claim1Card
import Workspace.ProofLemmas.K4AppearanceEightVertices

/-!
# The oriented long-branch case of 6.1(5)

We follow the edge identifications in the printed proof until they produce the four-cycle
`b-b₁-b₃-b₂-b`.  Claim 6.1(1) then finishes directly: only one displayed cycle edge is in
`X`.  This is a shorter endgame than reconstructing `J = K₄`, but uses exactly the same local
claims from the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim5Long

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim5Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.Thm61Claim1Helpers

/-- The long `B₃` case, oriented so that claim (3) makes `f₃` meet `e₁`. -/
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
    (hB₃long : 1 < trackLength B₃) (hf₃e₁ : MeetEdges f₃ e₁) :
    Thm61Concl G m J n H K φ Y := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  rcases hf with ⟨⟨hf₁X, hf₁inc, hpref₁⟩, ⟨hf₂X, hf₂inc, hpref₂⟩,
    ⟨hf₃X, hf₃inc, hpref₃⟩⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hf' : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃ :=
    ⟨⟨hf₁X, hf₁inc, hpref₁⟩, ⟨hf₂X, hf₂inc, hpref₂⟩,
      ⟨hf₃X, hf₃inc, hpref₃⟩⟩
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
  have he₁e₂meet : MeetEdges e₁ e₂ := by
    intro hd
    exact hd b ⟨he₁inc.2, he₂inc.2⟩
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hb₃tri := Workspace.ProofLemmas.Thm61Claim4.thm_6_1_claim4
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
      f₁ f₂ f₃ hf'
  obtain ⟨hB₃two, hf₃out⟩ := long_branch_at_triad
    G hG m J hJ n H K hsub φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
      B₃ b b₃ e₃ f₃ hB₃ hfrom₃ hB₃long he₃B₃ he₃inc.2 he₃X hf₃inc hf₃X hb₃tri
  have hf₃e₃ : f₃ ≠ e₃ := fun h => hf₃out (h ▸ he₃B₃)
  obtain ⟨hB₁one, he₁eq, hf₃eq⟩ :=
    identify_cross_meeting J hJ H hsub.1 hB₁ hfrom₁ hB₃ hfrom₃
      hB₁pos hB₃pos hb₃V hbb₃.symm hb₁b₃.symm
      he₁B₁ he₁inc.2 he₃B₃ he₃inc.2 hf₃X.1 hf₃inc.2 hf₃e₃ hf₃e₁
  have hB₁E := trackEdges_eq_singleton_of_length_one hfrom₁ hB₁one
  have hB₁adj : H.Adj b b₁ := by
    apply H.mem_edgeSet.mp
    rw [← he₁eq]
    exact he₁inc.1
  have hf₃adj : H.Adj b₁ b₃ := by
    apply H.mem_edgeSet.mp
    simpa [hf₃eq, Sym2.eq_swap] using hf₃X.1

  have hB₂one : trackLength B₂ = 1 := by
    by_contra hne
    have hB₂long : 1 < trackLength B₂ := by omega
    have hm₂ := Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
      G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
        e₁ e₂ f₂ he₁X₁ he₂X₂ he₁e₂meet hf₂X
    have hf₂e₂ : f₂ ≠ e₂ := fun h => he₂X (h ▸ hf₂X)
    rcases hm₂ with hf₂e₁ | hf₂e₂meet
    · obtain ⟨-, -, hf₂eq⟩ :=
        identify_cross_meeting J hJ H hsub.1 hB₁ hfrom₁ hB₂ hfrom₂
          hB₁pos hB₂pos hb₂V hbb₂.symm hb₁b₂.symm
          he₁B₁ he₁inc.2 he₂B₂ he₂inc.2 hf₂X.1 hf₂inc.2 hf₂e₂ hf₂e₁
      have hf₂adj : H.Adj b₁ b₂ := by
        apply H.mem_edgeSet.mp
        simpa [hf₂eq, Sym2.eq_swap] using hf₂X.1
      have hb₂b₃nadj : ¬ H.Adj b₂ b₃ := by
        intro hadj
        exact no_triangle_of_bipartite hsub.2 hf₂adj hadj hf₃adj
      obtain ⟨a, hainc, haX, hmeet⟩ :=
        complete_meets_noncomplete_at_triad G hG H K φ Y hYmajor hmin
          y₁ y₂ Q hQ hQY hy hQodd b₃ hb₃tri f₂ hf₂X
      obtain ⟨w, hwf, hwa⟩ := exists_common_end hmeet
      rcases Sym2.mem_iff.mp (hf₂eq ▸ hwf) with hwb₂ | hwb₁
      · have haeq : a = s(b₂, b₃) :=
          eq_sym2_of_mem_mem hb₂b₃ (hwb₂ ▸ hwa) hainc.2
        exact hb₂b₃nadj (H.mem_edgeSet.mp (haeq ▸ hainc.1))
      · have haeq : a = f₃ := by
          have haeq' : a = s(b₁, b₃) :=
            eq_sym2_of_mem_mem hb₁b₃ (hwb₁ ▸ hwa) hainc.2
          rw [haeq', hf₃eq, Sym2.eq_swap]
        exact haX (haeq ▸ hf₃X)
    · obtain ⟨hB₂two, hf₂B₂⟩ := same_branch_complete_shape
        J hJ H hsub.1 B₂ b b₂ e₂ f₂ hB₂ hfrom₂ hB₂long
          he₂B₂ he₂inc.2 hf₂inc hf₂e₂.symm hf₂e₂meet
      obtain ⟨col⟩ :=
        Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
      have hcol₂ : col b = col b₂ :=
        (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff
          (H := H) (q := B₂) (a := b) (b := b₂) col hfrom₂).mp
          (by rw [hB₂two]; simp)
      have hcol₃ : col b = col b₃ :=
        (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff
          (H := H) (q := B₃) (a := b) (b := b₃) col hfrom₃).mp
          (by rw [hB₃two]; simp)
      have hb₂b₃nadj : ¬ H.Adj b₂ b₃ := by
        intro hadj
        exact col.valid hadj (hcol₂.symm.trans hcol₃)
      obtain ⟨a, hainc, haX, hmeet⟩ :=
        complete_meets_noncomplete_at_triad G hG H K φ Y hYmajor hmin
          y₁ y₂ Q hQ hQY hy hQodd b₃ hb₃tri f₂ hf₂X
      have haout : a ∉ trackEdges B₂ := by
        intro haB
        exact branch_edge_avoids_other_branchVertex hB₂ hfrom₂ haB hb₃V
          hbb₃.symm hb₂b₃.symm hainc.2
      obtain ⟨w, hwf, hwa⟩ := exists_common_end hmeet
      rcases external_edge_meets_branch_only_at_ends
          hB₂ hfrom₂ hf₂B₂ hainc.1 haout hwa hwf with hwb | hwb₂
      · have hlist₂ : 2 ≤ B₂.length := by
          simp only [trackLength] at hB₂pos
          omega
        have hfhead := trackEdge_at_head hfrom₂ hlist₂ hf₂B₂ (hwb ▸ hwf)
        have hehead := trackEdge_at_head hfrom₂ hlist₂ he₂B₂ he₂inc.2
        exact hf₂e₂ (hfhead.trans hehead.symm)
      · have haeq : a = s(b₂, b₃) :=
          eq_sym2_of_mem_mem hb₂b₃ (hwb₂ ▸ hwa) hainc.2
        exact hb₂b₃nadj (H.mem_edgeSet.mp (haeq ▸ hainc.1))

  have hB₂E := trackEdges_eq_singleton_of_length_one hfrom₂ hB₂one
  have he₂eq : e₂ = s(b, b₂) := by
    rw [hB₂E] at he₂B₂
    exact Set.mem_singleton_iff.mp he₂B₂
  have hB₂adj : H.Adj b b₂ := by
    apply H.mem_edgeSet.mp
    rw [← he₂eq]
    exact he₂inc.1
  obtain ⟨a, hainc, haX, hmeet⟩ :=
    complete_meets_noncomplete_at_triad G hG H K φ Y hYmajor hmin
      y₁ y₂ Q hQ hQY hy hQodd b₃ hb₃tri f₂ hf₂X
  obtain ⟨w, hwf, hwa⟩ := exists_common_end hmeet
  have hwb₃ : w ≠ b₃ := by
    intro h
    have hf₂at₃ : f₂ ∈ incidentEdges H b₃ := ⟨hf₂X.1, h ▸ hwf⟩
    obtain ⟨-, ⟨fx, hfx, huniq⟩, -, -⟩ :=
      triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₃ hb₃tri
    have hf₂fx := huniq f₂ ⟨hf₂at₃, hf₂X⟩
    have hf₃fx := huniq f₃ ⟨hf₃inc, hf₃X⟩
    have hf₂f₃ : f₂ = f₃ := hf₂fx.trans hf₃fx.symm
    have hb₂f₃ : b₂ ∈ f₃ := hf₂f₃ ▸ hf₂inc.2
    rw [hf₃eq] at hb₂f₃
    rcases Sym2.mem_iff.mp hb₂f₃ with h | h
    · exact hb₂b₃ h
    · exact hb₁b₂ h.symm
  have hwb₂ : w = b₂ := by
    by_contra hne
    have hf₂eqw : f₂ = s(b₂, w) :=
      eq_sym2_of_mem_mem (fun h => hne h.symm) hf₂inc.2 hwf
    have haeqw : a = s(w, b₃) := eq_sym2_of_mem_mem hwb₃ hwa hainc.2
    have hb₂w : H.Adj b₂ w := H.mem_edgeSet.mp (hf₂eqw ▸ hf₂X.1)
    have hwb₃adj : H.Adj w b₃ := H.mem_edgeSet.mp (haeqw ▸ hainc.1)
    obtain ⟨col⟩ :=
      Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
    have hcol₂ : col b ≠ col b₂ := col.valid hB₂adj
    have hcol₃ : col b = col b₃ :=
      (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff
        (H := H) (q := B₃) (a := b) (b := b₃) col hfrom₃).mp
        (by rw [hB₃two]; simp)
    have hcolw₂ : col w ≠ col b₂ := col.valid hb₂w.symm
    have hcolw₃ : col w ≠ col b₃ := col.valid hwb₃adj
    have heq : col b₂ = col b₃ := bool_eq_of_ne_ne (col w) (col b₂) (col b₃)
      hcolw₂ hcolw₃
    exact hcol₂ (hcol₃.trans heq.symm)
  have haeq : a = s(b₂, b₃) :=
    eq_sym2_of_mem_mem hb₂b₃ (hwb₂ ▸ hwa) hainc.2
  have haadj : H.Adj b₂ b₃ := H.mem_edgeSet.mp (haeq ▸ hainc.1)
  have hcycle : [b, b₁, b₃, b₂].Nodup := by
    simp [hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃.symm]

  -- The last edge of the two-edge branch `B₃` is the second non-complete edge at `b₃`.
  have hB₃len : B₃.length = 3 := by simp only [trackLength] at hB₃two; omega
  let d₃ : Sym2 (Fin n) := s(B₃[1]'(by omega), B₃[2]'(by omega))
  have hd₃B : d₃ ∈ trackEdges B₃ := ⟨1, by omega, rfl⟩
  have hlast₃ : B₃[2]'(by omega) = b₃ := by
    have h := last_getElem hfrom₃.2.2 (by omega)
    convert h using 1 <;> apply geq <;> omega
  have hb₃d₃ : b₃ ∈ d₃ := by
    dsimp [d₃]
    rw [← hlast₃]
    simp
  have hd₃inc : d₃ ∈ incidentEdges H b₃ := by
    refine ⟨?_, hb₃d₃⟩
    exact hfrom₃.1.2.2 1 (by omega)
  have he₃first := trackEdge_at_head hfrom₃ (by omega) he₃B₃ he₃inc.2
  have hd₃ne₃ : d₃ ≠ e₃ := by
    intro hde
    rw [he₃first] at hde
    rcases Sym2.eq_iff.mp hde with ⟨h10, h21⟩ | ⟨h11, h20⟩
    · have hi := hfrom₃.1.2.1.getElem_inj_iff.mp h10
      omega
    · have hi := hfrom₃.1.2.1.getElem_inj_iff.mp h20
      omega
  have hd₃X : d₃ ∉ completeEdges G H K φ Y := by
    intro hdX
    have heq := hb₃tri.2 ⟨hd₃inc, hdX⟩ ⟨hf₃inc, hf₃X⟩
    exact hf₃out (heq ▸ hd₃B)
  have had₃ : a ≠ d₃ := by
    intro had
    have hb₂d₃ : b₂ ∈ d₃ := by
      rw [← had, haeq]
      simp
    exact branch_edge_avoids_other_branchVertex hB₃ hfrom₃ hd₃B hb₂V
      hbb₂.symm hb₂b₃ hb₂d₃

  -- A fourth edge at `b` would have to meet one of the two non-complete edges at `b₃`.
  -- Both possibilities contradict either the named branches or bipartiteness.
  have hbdeg : (H.neighborSet b).ncard = 3 := by
    by_contra hne
    have hinc4 : 4 ≤ (incidentEdges H b).ncard := by
      rw [incidentEdges_ncard]
      have hgt : 3 < (H.neighborSet b).ncard := lt_of_le_of_ne hbV (Ne.symm hne)
      omega
    have hnsub : ¬ incidentEdges H b ⊆ ({e₁, e₂, e₃} : Set (Sym2 (Fin n))) := by
      intro hs
      have hle := Set.ncard_le_ncard hs (Set.toFinite _)
      have hcard : ({e₁, e₂, e₃} : Set (Sym2 (Fin n))).ncard ≤ 3 := by
        calc
          _ ≤ ({e₂, e₃} : Set (Sym2 (Fin n))).ncard + 1 := Set.ncard_insert_le _ _
          _ ≤ ({e₃} : Set (Sym2 (Fin n))).ncard + 2 := by
            have := Set.ncard_insert_le e₂ ({e₃} : Set (Sym2 (Fin n)))
            omega
          _ = 3 := by simp
      omega
    obtain ⟨g, hginc, hgnot⟩ := Set.not_subset.mp hnsub
    have hgne₁ : g ≠ e₁ := fun h => hgnot (by simp [h])
    have hgne₂ : g ≠ e₂ := fun h => hgnot (by simp [h])
    have hgne₃ : g ≠ e₃ := fun h => hgnot (by simp [h])
    have hgX : g ∈ completeEdges G H K φ Y :=
      other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
        hginc hgne₁ hgne₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
    have hgm := complete_meets_one_of_two_noncomplete
      G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
        b₃ hb₃V a d₃ hainc hd₃inc had₃ haX hd₃X g hgX
    rcases hgm with hga | hgd
    · obtain ⟨w, hwg, hwa'⟩ := exists_common_end hga
      rw [haeq] at hwa'
      rcases Sym2.mem_iff.mp hwa' with hwb₂ | hwb₃'
      · have hgeq : g = e₂ := by
          rw [he₂eq]
          exact eq_sym2_of_mem_mem hbb₂ hginc.2 (hwb₂ ▸ hwg)
        exact hgne₂ hgeq
      · have hgeq : g = s(b, b₃) :=
          eq_sym2_of_mem_mem hbb₃ hginc.2 (hwb₃' ▸ hwg)
        have hadj : H.Adj b b₃ := H.mem_edgeSet.mp (hgeq ▸ hginc.1)
        exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
          J hJ H hsub.1 B₃ b b₃ hB₃ hfrom₃ (by omega)).2.2.2 hadj
    · have hgout : g ∉ trackEdges B₃ := by
        intro hgB
        have hlist : 2 ≤ B₃.length := by omega
        have hge := trackEdge_at_head hfrom₃ hlist hgB hginc.2
        exact hgne₃ (hge.trans he₃first.symm)
      obtain ⟨w, hwg, hwd⟩ := exists_common_end hgd
      rcases external_edge_meets_branch_only_at_ends
          hB₃ hfrom₃ hd₃B hginc.1 hgout hwg hwd with hwb | hwb₃'
      · have hdhead := trackEdge_at_head hfrom₃ (by omega) hd₃B (hwb ▸ hwd)
        exact hd₃ne₃ (hdhead.trans he₃first.symm)
      · have hgeq : g = s(b, b₃) :=
          eq_sym2_of_mem_mem hbb₃ hginc.2 (hwb₃' ▸ hwg)
        have hadj : H.Adj b b₃ := H.mem_edgeSet.mp (hgeq ▸ hginc.1)
        exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
          J hJ H hsub.1 B₃ b b₃ hB₃ hfrom₃ (by omega)).2.2.2 hadj

  -- Lift the four displayed branch-vertices back to `J`.  The two degree-three vertices
  -- `b,b₃` have the same two other neighbours, so 3-connectivity leaves only these four.
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
  have hJ13 : J.Adj u₁ u₃ := lift_adj (by simpa [← h1, ← h3] using hf₃adj)
  have hJ23 : J.Adj u₂ u₃ := lift_adj (by simpa [← h2, ← h3] using haadj)
  obtain ⟨hb₃deg, -, -, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₃ hb₃tri
  have hJdeg0 : (J.neighborSet u₀).ncard = 3 := by
    apply le_antisymm
    · calc
        _ ≤ (H.neighborSet (ι u₀)).ncard :=
          original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew u₀
        _ = 3 := by rw [← h0, hbdeg]
    · exact hJdeg u₀
  have hJdeg3 : (J.neighborSet u₃).ncard = 3 := by
    apply le_antisymm
    · calc
        _ ≤ (H.neighborSet (ι u₃)).ncard :=
          original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew u₃
        _ = 3 := by rw [← h3, hb₃deg]
    · exact hJdeg u₃
  have hall : ∀ x : Fin m, x = u₀ ∨ x = u₃ ∨ x = u₁ ∨ x = u₂ :=
    four_vertices_of_two_degree_three hJ hJ03 hJ01 hJ02 hJ13.symm hJ23.symm
      hu12 hJdeg0 hJdeg3
  have hJ12 : J.Adj u₁ u₂ := by
    by_contra hnot
    have hsubN : J.neighborSet u₁ ⊆ ({u₀, u₃} : Set (Fin m)) := by
      intro x hx
      rcases hall x with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (J.loopless.irrefl _ hx)
      · exact False.elim (hnot hx)
    have hle := Set.ncard_le_ncard hsubN (Set.toFinite _)
    rw [Set.ncard_pair hu03] at hle
    have := hJdeg u₁
    omega
  have hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) :=
    iso_top_of_four_vertices hu03 hu01 hu02 hu13.symm hu23.symm hu12
      hall hJ03 hJ01 hJ02 hJ13.symm hJ23.symm hJ12
  have hbvsub : branchVertices H ⊆ ({b, b₁, b₃, b₂} : Set (Fin n)) := by
    intro x hx
    obtain ⟨u, hu⟩ := hbrange hx
    rcases hall u with rfl | rfl | rfl | rfl
    · simp [hu, h0]
    · simp [hu, h3]
    · simp [hu, h1]
    · simp [hu, h2]
  have hbvsup : ({b, b₁, b₃, b₂} : Set (Fin n)) ⊆ branchVertices H := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hbV
    · exact hb₁V
    · exact hb₃V
    · exact hb₂V
  have hbveq : branchVertices H = ({b, b₁, b₃, b₂} : Set (Fin n)) :=
    Set.Subset.antisymm hbvsub hbvsup
  obtain ⟨-, hsub4⟩ := Workspace.ProofLemmas.Thm61Claim1Geometry.source_is_k4
    m J hJ H hsub.1 b b₁ b₃ b₂ hcycle hbveq
  obtain ⟨Bp, Bq, hBpfrom, hBqfrom, hBppos, hBqpos, hBpeven, hBqeven,
      hPQdisj, hPavoid, hQavoid, hedgeDecomp⟩ :=
    Workspace.ProofLemmas.Thm61Claim1Helpers.k4_structure
      hsub4 hsub.2 b b₁ b₃ b₂ hcycle hbveq
        hB₁adj hf₃adj haadj.symm hB₂adj.symm
  have hBpbranch : IsBranch H Bp := by
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
      hBpfrom hb₁b₂
    · intro w hw hwbranch
      have hwn1 := Workspace.ProofLemmas.SubdivisionCompose.ne_head_of_mem_trackInterior
        hBpfrom.1.2.1 hBpfrom.2.1 hw
      have hwn2 := Workspace.ProofLemmas.SubdivisionCompose.ne_getLast_of_mem_trackInterior
        hBpfrom.1.2.1 hBpfrom.2.2 hw
      have hav := hPavoid w (Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hw)
      rw [hbveq] at hwbranch
      rcases hwbranch with h | h | h | h
      · exact hav.1 h
      · exact hwn1 h
      · exact hav.2 h
      · exact hwn2 h
    · exact hb₁V
    · exact hb₂V
  have hBqbranch : IsBranch H Bq := by
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
      hBqfrom hbb₃.symm
    · intro w hw hwbranch
      have hwn3 := Workspace.ProofLemmas.SubdivisionCompose.ne_head_of_mem_trackInterior
        hBqfrom.1.2.1 hBqfrom.2.1 hw
      have hwn0 := Workspace.ProofLemmas.SubdivisionCompose.ne_getLast_of_mem_trackInterior
        hBqfrom.1.2.1 hBqfrom.2.2 hw
      have hav := hQavoid w (Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hw)
      rw [hbveq] at hwbranch
      rcases hwbranch with h | h | h | h
      · exact hwn0 h
      · exact hav.1 h
      · exact hwn3 h
      · exact hav.2 h
    · exact hb₃V
    · exact hbV
  obtain ⟨ι₄, T₄, hι₄, htrack₄, hlen₄, hrev₄, hdisj₄, hnew₄, hcover₄, hedges₄⟩ :=
    hsub4
  have hdeg₄ : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected
      (⊤ : SimpleGraph (Fin 4)) Workspace.ProofLemmas.SubdivisionCounting.k4_three_connected
  have hBqEdges : trackEdges Bq = trackEdges B₃ :=
    Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
      hι₄ htrack₄ hlen₄ hrev₄ hdisj₄ hnew₄ hcover₄ hedges₄ hdeg₄
        hBqbranch (by simp only [trackLength] at hBqpos; omega) hBqfrom
        hB₃ (by simp only [trackLength] at hB₃pos; omega) hfrom₃
        hb₃V hbV (Or.inr ⟨rfl, rfl⟩)
  have hBqtwo : trackLength Bq = 2 := by
    rw [← Workspace.ProofLemmas.K4AppearanceEightVertices.trackEdges_ncard Bq
        hBqfrom.1.2.1,
      hBqEdges,
      Workspace.ProofLemmas.K4AppearanceEightVertices.trackEdges_ncard B₃
        hfrom₃.1.2.1,
      hB₃two]

  -- Let `D` be the remaining branch, from `b₂` to `b₁`, containing `f₂`.
  obtain ⟨D, c, hD, hf₂D, hDfrom⟩ :=
    branch_from_incident J hJ H hsub.1 b₂ hb₂V f₂ hf₂inc
  have hDpos : 1 ≤ trackLength D := one_le_trackLength_of_mem hf₂D
  have hcV := (Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 D b₂ c hD hDfrom hDpos).2
  have hb₂c : b₂ ≠ c := track_ends_ne hDfrom hDpos
  have hc : c = b₁ := by
    have hcset : c ∈ ({b, b₁, b₃, b₂} : Set (Fin n)) := hbveq ▸ hcV
    rcases hcset with hcb | hcb₁ | hcb₃ | hcb₂
    · have hDone := branch_length_one_of_adj J hJ H hsub.1 hD hDfrom hDpos
          (hcb ▸ hB₂adj.symm)
      have hDE := trackEdges_eq_singleton_of_length_one hDfrom hDone
      have hf₂eq : f₂ = e₂ := by
        rw [hDE] at hf₂D
        have := Set.mem_singleton_iff.mp hf₂D
        rw [this, hcb, he₂eq, Sym2.eq_swap]
      exact False.elim (he₂X (hf₂eq ▸ hf₂X))
    · exact hcb₁
    · have hDone := branch_length_one_of_adj J hJ H hsub.1 hD hDfrom hDpos
          (hcb₃ ▸ haadj)
      have hDE := trackEdges_eq_singleton_of_length_one hDfrom hDone
      have hf₂eq : f₂ = a := by
        rw [hDE] at hf₂D
        have := Set.mem_singleton_iff.mp hf₂D
        rw [this, hcb₃, haeq, Sym2.eq_swap]
      exact False.elim (haX (hf₂eq ▸ hf₂X))
    · exact False.elim (hb₂c (Set.mem_singleton_iff.mp hcb₂).symm)
  subst c
  have hDlist : 2 ≤ D.length := by simp only [trackLength] at hDpos; omega
  let d : Sym2 (Fin n) := s(D[D.length - 2]'(by omega), D[D.length - 1]'(by omega))
  have hdD : d ∈ trackEdges D := by
    refine ⟨D.length - 2, by omega, ?_⟩
    dsimp [d]
    congr 1 <;> apply geq <;> omega
  have hdE : d ∈ H.edgeSet := by
    obtain ⟨i, hi, heq⟩ := hdD
    rw [heq]
    exact hDfrom.1.2.2 i hi
  have hDlast : D[D.length - 1]'(by omega) = b₁ := last_getElem hDfrom.2.2 (by omega)
  have hb₁d : b₁ ∈ d := by
    dsimp [d]
    rw [← hDlast]
    simp
  have hdinc : d ∈ incidentEdges H b₁ := ⟨hdE, hb₁d⟩
  have haoutD : a ∉ trackEdges D := by
    intro haD
    exact branch_edge_avoids_other_branchVertex hD hDfrom haD hb₃V
      hb₂b₃.symm hb₁b₃.symm (by rw [haeq]; simp)
  have hd₃outD : d₃ ∉ trackEdges D := by
    intro hdD'
    exact branch_edge_avoids_other_branchVertex hD hDfrom hdD' hb₃V
      hb₂b₃.symm hb₁b₃.symm hb₃d₃
  have hdX : d ∉ completeEdges G H K φ Y := by
    intro hdX'
    have hm := complete_meets_one_of_two_noncomplete
      G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
        b₃ hb₃V a d₃ hainc hd₃inc had₃ haX hd₃X d hdX'
    rcases hm with hda | hdd₃
    · obtain ⟨w, hwd, hwa'⟩ := exists_common_end hda
      rcases external_edge_meets_branch_only_at_ends
          hD hDfrom hdD hainc.1 haoutD hwa' hwd with hwb₂ | hwb₁
      · have hdeq : d = s(b₂, b₁) := eq_sym2_of_mem_mem hb₁b₂.symm
            (hwb₂ ▸ hwd) hb₁d
        have hadj : H.Adj b₂ b₁ := H.mem_edgeSet.mp (hdeq ▸ hdE)
        exact no_triangle_of_bipartite hsub.2 hB₂adj.symm hB₁adj hadj
      · rw [haeq] at hwa'
        rcases Sym2.mem_iff.mp hwa' with h | h
        · exact hb₁b₂ (hwb₁.symm.trans h)
        · exact hb₁b₃ (hwb₁.symm.trans h)
    · obtain ⟨w, hwd, hwd₃⟩ := exists_common_end hdd₃
      rcases external_edge_meets_branch_only_at_ends
          hD hDfrom hdD hd₃inc.1 hd₃outD hwd₃ hwd with hwb₂ | hwb₁
      · exact branch_edge_avoids_other_branchVertex hB₃ hfrom₃ hd₃B hb₂V
          hbb₂.symm hb₂b₃ (hwb₂ ▸ hwd₃)
      · exact branch_edge_avoids_other_branchVertex hB₃ hfrom₃ hd₃B hb₁V
          hbb₁.symm hb₁b₃ (hwb₁ ▸ hwd₃)
  have he₁d : e₁ ≠ d := by
    intro h
    have hbd : b ∈ d := h ▸ he₁inc.2
    exact branch_edge_avoids_other_branchVertex hD hDfrom hdD hbV
      hbb₂ hbb₁ hbd
  have hmD := complete_meets_one_of_two_noncomplete
    G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
      b₁ hb₁V e₁ d (by
        refine ⟨he₁inc.1, ?_⟩
        rw [he₁eq]
        simp) hdinc he₁d he₁X hdX f₂ hf₂X
  have hf₂d : MeetEdges f₂ d := by
    rcases hmD with hf₂e₁ | hf₂d
    · obtain ⟨w, hwf, hwe⟩ := exists_common_end hf₂e₁
      rw [he₁eq] at hwe
      rcases Sym2.mem_iff.mp hwe with hwb | hwb₁
      · have hf₂eq : f₂ = e₂ := by
          rw [he₂eq]
          exact eq_sym2_of_mem_mem hbb₂ (hwb ▸ hwf) hf₂inc.2
        exact False.elim (he₂X (hf₂eq ▸ hf₂X))
      · have hf₂eq : f₂ = s(b₂, b₁) :=
          eq_sym2_of_mem_mem hb₁b₂.symm hf₂inc.2 (hwb₁ ▸ hwf)
        have hadj : H.Adj b₂ b₁ := H.mem_edgeSet.mp (hf₂eq ▸ hf₂X.1)
        exact False.elim
          (no_triangle_of_bipartite hsub.2 hB₂adj.symm hB₁adj hadj)
    · exact hf₂d
  have hDle : trackLength D ≤ 2 :=
    trackLength_le_two_of_end_edges_meet hDfrom hDpos hf₂D hf₂inc.2 hdD hb₁d hf₂d
  have hDtwo : trackLength D = 2 := by
    have hDne : trackLength D ≠ 1 := by
      intro hone
      have hDE := trackEdges_eq_singleton_of_length_one hDfrom hone
      rw [hDE] at hf₂D
      have hf₂eq := Set.mem_singleton_iff.mp hf₂D
      have hadj : H.Adj b₂ b₁ := by
        apply H.mem_edgeSet.mp
        rw [← hf₂eq]
        exact hf₂X.1
      exact no_triangle_of_bipartite hsub.2 hB₂adj.symm hB₁adj hadj
    omega
  have hBpEdges : trackEdges Bp = trackEdges D :=
    Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
      hι₄ htrack₄ hlen₄ hrev₄ hdisj₄ hnew₄ hcover₄ hedges₄ hdeg₄
        hBpbranch (by simp only [trackLength] at hBppos; omega) hBpfrom
        hD (by simp only [trackLength] at hDpos; omega) hDfrom
        hb₁V hb₂V (Or.inr ⟨rfl, rfl⟩)
  have hBptwo : trackLength Bp = 2 := by
    rw [← Workspace.ProofLemmas.K4AppearanceEightVertices.trackEdges_ncard Bp
        hBpfrom.1.2.1,
      hBpEdges,
      Workspace.ProofLemmas.K4AppearanceEightVertices.trackEdges_ncard D
        hDfrom.1.2.1,
      hDtwo]
  have hsub4' : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H :=
    ⟨ι₄, T₄, hι₄, htrack₄, hlen₄, hrev₄, hdisj₄, hnew₄, hcover₄, hedges₄⟩
  have hcard := Workspace.ProofLemmas.Thm61Claim1Card.card_six_of_short_diagonals
    hsub4' b b₁ b₃ b₂ hcycle Bp Bq hBpfrom hBqfrom hBptwo hBqtwo
      hPQdisj hPavoid hQavoid hedgeDecomp
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hJiso, hcard⟩)))

end Workspace.ProofLemmas.Thm61Claim5Long
