import Mathlib
import Workspace.ProofLemmas.Thm61Claim6Helpers
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# The impossible both-long case in 6.1(6)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim6BothLong

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61Claim5Helpers
open Workspace.ProofLemmas.Thm61Claim6Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- The two branches `B₁,B₂` cannot both be long.  This is the first paragraph of claim (6). -/
theorem impossible
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
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃)
    (hB₁long : 1 < trackLength B₁) (hB₂long : 1 < trackLength B₂) : False := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  rcases hf with ⟨hf₁, hf₂, hf₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  rcases branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, -, -, hb₁V, hb₂V, -, hbb₁, hbb₂, -, hb₁b₂, -, -⟩
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₁X : e₁ ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hXX₁ he₁X₁
  have he₂X : e₂ ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hXX₂ he₂X₂
  have he₁e₂ : e₁ ≠ e₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ he₁X₁) (h ▸ he₂X₂)
  have hshape₁ : trackLength B₁ = 2 ∧ f₁ ∈ trackEdges B₁ := by
    have hm := complete_meets_one_of_two_noncomplete
      G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
        b hbV e₁ e₂ he₁inc he₂inc he₁e₂ he₁X he₂X f₁ hf₁.1
    rcases hm with hm | hm
    · exact same_branch_complete_shape J hJ H hsub.1 B₁ b b₁ e₁ f₁
        hB₁ hfrom₁ hB₁long he₁B₁ he₁inc.2 hf₁.2.1
        (fun h => he₁X (h ▸ hf₁.1)) hm
    · have hf₁ne₁ : f₁ ≠ e₁ := fun h => he₁X (h ▸ hf₁.1)
      obtain ⟨hB₂one, -, -⟩ := identify_cross_meeting
        J hJ H hsub.1 hB₂ hfrom₂ hB₁ hfrom₁ hB₂pos hB₁pos
          hb₁V hbb₁.symm hb₁b₂ he₂B₂ he₂inc.2 he₁B₁ he₁inc.2
          hf₁.1.1 hf₁.2.1.2 hf₁ne₁ hm
      omega
  have hshape₂ : trackLength B₂ = 2 ∧ f₂ ∈ trackEdges B₂ := by
    have hm := complete_meets_one_of_two_noncomplete
      G hG H K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
        b hbV e₁ e₂ he₁inc he₂inc he₁e₂ he₁X he₂X f₂ hf₂.1
    rcases hm with hm | hm
    · have hf₂ne₂ : f₂ ≠ e₂ := fun h => he₂X (h ▸ hf₂.1)
      obtain ⟨hB₁one, -, -⟩ := identify_cross_meeting
        J hJ H hsub.1 hB₁ hfrom₁ hB₂ hfrom₂ hB₁pos hB₂pos
          hb₂V hbb₂.symm hb₁b₂.symm he₁B₁ he₁inc.2 he₂B₂ he₂inc.2
          hf₂.1.1 hf₂.2.1.2 hf₂ne₂ hm
      omega
    · exact same_branch_complete_shape J hJ H hsub.1 B₂ b b₂ e₂ f₂
        hB₂ hfrom₂ hB₂long he₂B₂ he₂inc.2 hf₂.2.1
        (fun h => he₂X (h ▸ hf₂.1)) hm
  have hB₁two := hshape₁.1
  have hf₁B := hshape₁.2
  have hB₂two := hshape₂.1
  have hf₂B := hshape₂.2
  have hb₂tri := chosen_in_branch_is_triad hb₂V hfrom₂ hB₂pos hf₂ hf₂B
  obtain ⟨a, hainc, haX, hmeet⟩ :=
    complete_meets_noncomplete_at_triad G hG H K φ Y hYmajor hmin
      y₁ y₂ Q hQ hQY hy hQodd b₂ hb₂tri f₁ hf₁.1
  have haout : a ∉ trackEdges B₁ := by
    intro haB
    exact branch_edge_avoids_other_branchVertex hB₁ hfrom₁ haB hb₂V
      hbb₂.symm hb₁b₂.symm hainc.2
  obtain ⟨w, hwf, hwa⟩ := exists_common_end hmeet
  rcases external_edge_meets_branch_only_at_ends
      hB₁ hfrom₁ hf₁B hainc.1 haout hwa hwf with hwb | hwb₁
  · have hlist : 2 ≤ B₁.length := by simp only [trackLength] at hB₁pos; omega
    have hfhead := trackEdge_at_head hfrom₁ hlist hf₁B (hwb ▸ hwf)
    have hehead := trackEdge_at_head hfrom₁ hlist he₁B₁ he₁inc.2
    exact he₁X ((hfhead.trans hehead.symm) ▸ hf₁.1)
  · have haeq : a = s(b₁, b₂) :=
      eq_sym2_of_mem_mem hb₁b₂ (hwb₁ ▸ hwa) hainc.2
    have hadj : H.Adj b₁ b₂ := H.mem_edgeSet.mp (haeq ▸ hainc.1)
    obtain ⟨col⟩ :=
      Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
    have hc₁ : col b = col b₁ :=
      (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mp
        (by rw [hB₁two]; simp)
    have hc₂ : col b = col b₂ :=
      (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom₂).mp
        (by rw [hB₂two]; simp)
    exact col.valid hadj (hc₁.symm.trans hc₂)

end Workspace.ProofLemmas.Thm61Claim6BothLong
