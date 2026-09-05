import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers
import Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance
import Workspace.ProofLemmas.BipartiteClosedWalkEven

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenEndgameClaim12

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- The part of printed claim (12) driven solely by claim (10): neither of the two branches
from `b` contains a complete edge, the two selected complete edges meet, and their branch ends
are nonadjacent. -/
theorem claim12_prelim
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
    (f₁ f₂ : Sym2 (Fin n))
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    Disjoint (trackEdges B₁) (completeEdges G H K φ Y) ∧
      Disjoint (trackEdges B₂) (completeEdges G H K φ Y) ∧
      MeetEdges f₁ f₂ ∧ ¬ H.Adj b₁ b₂ := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
      he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
      hB₃, he₃B₃, hfrom₃⟩
  rcases branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, hB₃pos, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
      hb₁b₂, hb₁b₃, hb₂b₃⟩
  have hB₁len : 2 ≤ B₁.length := by
    have h := hB₁pos
    simp only [trackLength] at h
    omega
  have hB₂len : 2 ≤ B₂.length := by
    have h := hB₂pos
    simp only [trackLength] at h
    omega
  obtain ⟨hXE, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₁notX : e₁ ∉ completeEdges G H K φ Y := fun he =>
    (Set.disjoint_left.mp hXX₁ he he₁X₁)
  have he₂notX : e₂ ∉ completeEdges G H K φ Y := fun he =>
    (Set.disjoint_left.mp hXX₂ he he₂X₂)
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂
        hX₁X₂ hsat₁ hsat₂
  have hf₁E : f₁ ∈ H.edgeSet := hXE hf₁X
  have hf₂E : f₂ ∈ H.edgeSet := hXE hf₂X
  have hf₁dis : DisjointEdges f₁ e₃ := by
    unfold MeetEdges at hf₁e
    exact Classical.byContradiction hf₁e
  have hf₂dis : DisjointEdges f₂ e₃ := by
    unfold MeetEdges at hf₂e
    exact Classical.byContradiction hf₂e
  have hbf₁ : b ∉ f₁ := fun hb => hf₁dis b ⟨hb, he₃inc.2⟩
  have hbf₂ : b ∉ f₂ := fun hb => hf₂dis b ⟨hb, he₃inc.2⟩
  obtain ⟨z₃, hP₃, he₃eq⟩ := edge_track_from_incident he₃inc
  have hP₃len : 2 ≤ [b, z₃].length := by simp
  have hP₃X : ∃ e ∈ trackEdges [b, z₃], e ∈ completeEdges G H K φ Y := by
    refine ⟨e₃, ⟨0, by simp, ?_⟩, he₃X⟩
    simpa using he₃eq
  have hz₃B₃ : z₃ ∈ B₃ := by
    have hm := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges
      (show s(b, z₃) ∈ trackEdges B₃ by simpa [he₃eq] using he₃B₃)
    exact hm.2
  have hB₁B₂ : ∀ w ∈ B₁, w ∈ B₂ → w = b :=
    branches_from_common_end_meet_only hJ hsub.1 hB₁ hfrom₁ hB₂ hfrom₂
      hB₁pos hB₂pos hbV hb₁V hb₂V hbb₁ hbb₂ hb₁b₂
  have hB₁B₃ : ∀ w ∈ B₁, w ∈ B₃ → w = b :=
    branches_from_common_end_meet_only hJ hsub.1 hB₁ hfrom₁ hB₃ hfrom₃
      hB₁pos hB₃pos hbV hb₁V hb₃V hbb₁ hbb₃ hb₁b₃
  have hB₂B₃ : ∀ w ∈ B₂, w ∈ B₃ → w = b :=
    branches_from_common_end_meet_only hJ hsub.1 hB₂ hfrom₂ hB₃ hfrom₃
      hB₂pos hB₃pos hbV hb₂V hb₃V hbb₂ hbb₃ hb₂b₃
  have hf₁outB₂ : f₁ ∉ trackEdges B₂ := by
    intro hf
    exact (branch_edge_avoids_other_branchVertex hB₂ hfrom₂ hf hb₁V
      hbb₁.symm hb₁b₂ hf₁b)
  have hf₂outB₁ : f₂ ∉ trackEdges B₁ := by
    intro hf
    exact (branch_edge_avoids_other_branchVertex hB₁ hfrom₁ hf hb₂V
      hbb₂.symm hb₁b₂.symm hf₂b)
  have memP₃_edge : ∀ {w : Fin n}, w ∈ [b, z₃] → w ∈ e₃ := by
    intro w hw
    rw [he₃eq]
    simpa using hw
  have memP₃_B₃ : ∀ {w : Fin n}, w ∈ [b, z₃] → w ∈ B₃ := by
    intro w hw
    simp at hw
    rcases hw with rfl | rfl
    · exact List.mem_of_mem_head? hfrom₃.2.1
    · exact hz₃B₃
  have cross_B₁_f₂ : ∀ {w : Fin n}, w ∈ B₁ → w ∈ f₂ → False := by
    intro w hwB hwf
    rcases external_edge_inter_branch_only_at_ends hB₁ hfrom₁ hB₁pos
        hf₂E hf₂outB₁ hwB hwf with hwb | hwb₁
    · exact hbf₂ (hwb ▸ hwf)
    · apply hf₂ne
      exact eq_sym2_of_mem_mem hb₁b₂ (hwb₁ ▸ hwf) hf₂b
  have cross_f₁_B₂ : ∀ {w : Fin n}, w ∈ f₁ → w ∈ B₂ → False := by
    intro w hwf hwB
    rcases external_edge_inter_branch_only_at_ends hB₂ hfrom₂ hB₂pos
        hf₁E hf₁outB₂ hwB hwf with hwb | hwb₂
    · exact hbf₁ (hwb ▸ hwf)
    · apply hf₁ne
      exact eq_sym2_of_mem_mem hb₁b₂ hf₁b (hwb₂ ▸ hwf)
  have branch_P₃_disjoint (i : Fin 2) :
      ∀ w ∈ (if i = 0 then B₁ else B₂), w ∈ [b, z₃] → w = b := by
    intro w hwB hwP
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte] at hwB
      exact hB₁B₃ w hwB (memP₃_B₃ hwP)
    · simp only [hi, ↓reduceIte] at hwB
      exact hB₂B₃ w hwB (memP₃_B₃ hwP)
  -- First claim: no edge of `B₁` is complete.
  have hnoB₁ : Disjoint (trackEdges B₁) (completeEdges G H K φ Y) := by
    rw [Set.disjoint_left]
    intro x hxB hxX
    obtain ⟨P₂, z₂, hP₂, hP₂len, hf₂P₂, hP₂mem, hP₂first⟩ :=
      extend_branch_through_incident_edge hB₂ hfrom₂ hB₂pos
        ⟨hf₂E, hf₂b⟩ hbf₂
    have h12 : ∀ w ∈ B₁, w ∈ P₂ → w = b := by
      intro w hw1 hw2
      rcases hP₂mem w hw2 with hw2 | hw2
      · exact hB₁B₂ w hw1 hw2
      · exact False.elim (cross_B₁_f₂ hw1 hw2)
    have h13 : ∀ w ∈ B₁, w ∈ [b, z₃] → w = b :=
      branch_P₃_disjoint 0
    have h23 : ∀ w ∈ P₂, w ∈ [b, z₃] → w = b := by
      intro w hw2 hw3
      rcases hP₂mem w hw2 with hw2 | hw2
      · exact hB₂B₃ w hw2 (memP₃_B₃ hw3)
      · exact False.elim (hf₂dis w ⟨hw2, memP₃_edge hw3⟩)
    have hc := h10 b b₁ z₂ z₃ B₁ P₂ [b, z₃]
      hfrom₁ hP₂ hP₃ hB₁len
      hP₂len hP₃len h12 h13 h23 ⟨x, hxB, hxX⟩
      ⟨f₂, hf₂P₂, hf₂X⟩ hP₃X
    have hfirst1 : s(B₁[0]'(by omega), B₁[1]'(by omega)) ∉
        completeEdges G H K φ Y := by
      have heq := trackEdge_at_head hfrom₁ hB₁len
        he₁B₁ he₁inc.2
      exact fun hh => he₁notX (heq ▸ hh)
    have hfirst2 : s(P₂[0]'(by omega), P₂[1]'(by omega)) ∉
        completeEdges G H K φ Y := by
      have hp := hP₂first hP₂len
      have hbfirst : b ∈ s(P₂[0]'(by omega), P₂[1]'(by omega)) := by
        rw [head_getElem hP₂.2.1 (by omega)]
        simp
      have hpEq := trackEdge_at_head hfrom₂ hB₂len hp hbfirst
      have heEq := trackEdge_at_head hfrom₂ hB₂len he₂B₂ he₂inc.2
      exact fun hh => he₂notX ((hpEq.trans heEq.symm) ▸ hh)
    rcases hc with h | h | h
    · exact hfirst1 h.1
    · exact hfirst1 h.1
    · exact hfirst2 h.1
  -- The `B₂` assertion is the same fan with the first two arms exchanged.
  have hnoB₂ : Disjoint (trackEdges B₂) (completeEdges G H K φ Y) := by
    rw [Set.disjoint_left]
    intro x hxB hxX
    obtain ⟨P₁, z₁, hP₁, hP₁len, hf₁P₁, hP₁mem, hP₁first⟩ :=
      extend_branch_through_incident_edge hB₁ hfrom₁ hB₁pos
        ⟨hf₁E, hf₁b⟩ hbf₁
    have h12 : ∀ w ∈ P₁, w ∈ B₂ → w = b := by
      intro w hw1 hw2
      rcases hP₁mem w hw1 with hw1 | hw1
      · exact hB₁B₂ w hw1 hw2
      · exact False.elim (cross_f₁_B₂ hw1 hw2)
    have h13 : ∀ w ∈ P₁, w ∈ [b, z₃] → w = b := by
      intro w hw1 hw3
      rcases hP₁mem w hw1 with hw1 | hw1
      · exact hB₁B₃ w hw1 (memP₃_B₃ hw3)
      · exact False.elim (hf₁dis w ⟨hw1, memP₃_edge hw3⟩)
    have h23 : ∀ w ∈ B₂, w ∈ [b, z₃] → w = b :=
      branch_P₃_disjoint 1
    have hc := h10 b z₁ b₂ z₃ P₁ B₂ [b, z₃]
      hP₁ hfrom₂ hP₃ hP₁len
      hB₂len hP₃len h12 h13 h23
      ⟨f₁, hf₁P₁, hf₁X⟩ ⟨x, hxB, hxX⟩ hP₃X
    have hfirst1 : s(P₁[0]'(by omega), P₁[1]'(by omega)) ∉
        completeEdges G H K φ Y := by
      have hp := hP₁first hP₁len
      have hbfirst : b ∈ s(P₁[0]'(by omega), P₁[1]'(by omega)) := by
        rw [head_getElem hP₁.2.1 (by omega)]
        simp
      have hpEq := trackEdge_at_head hfrom₁ hB₁len hp hbfirst
      have heEq := trackEdge_at_head hfrom₁ hB₁len he₁B₁ he₁inc.2
      exact fun hh => he₁notX ((hpEq.trans heEq.symm) ▸ hh)
    have hfirst2 : s(B₂[0]'(by omega), B₂[1]'(by omega)) ∉
        completeEdges G H K φ Y := by
      have heq := trackEdge_at_head hfrom₂ hB₂len
        he₂B₂ he₂inc.2
      exact fun hh => he₂notX (heq ▸ hh)
    rcases hc with h | h | h
    · exact hfirst1 h.1
    · exact hfirst1 h.1
    · exact hfirst2 h.1
  have hfmeet : MeetEdges f₁ f₂ := by
    by_contra hmeet
    have hfdis : DisjointEdges f₁ f₂ := by
      unfold MeetEdges at hmeet
      exact Classical.byContradiction hmeet
    obtain ⟨P₁, z₁, hP₁, hP₁len, hf₁P₁, hP₁mem, hP₁first⟩ :=
      extend_branch_through_incident_edge hB₁ hfrom₁ hB₁pos
        ⟨hf₁E, hf₁b⟩ hbf₁
    obtain ⟨P₂, z₂, hP₂, hP₂len, hf₂P₂, hP₂mem, hP₂first⟩ :=
      extend_branch_through_incident_edge hB₂ hfrom₂ hB₂pos
        ⟨hf₂E, hf₂b⟩ hbf₂
    have h12 : ∀ w ∈ P₁, w ∈ P₂ → w = b := by
      intro w hw1 hw2
      rcases hP₁mem w hw1 with hw1 | hw1 <;>
        rcases hP₂mem w hw2 with hw2 | hw2
      · exact hB₁B₂ w hw1 hw2
      · exact False.elim (cross_B₁_f₂ hw1 hw2)
      · exact False.elim (cross_f₁_B₂ hw1 hw2)
      · exact False.elim (hfdis w ⟨hw1, hw2⟩)
    have h13 : ∀ w ∈ P₁, w ∈ [b, z₃] → w = b := by
      intro w hw1 hw3
      rcases hP₁mem w hw1 with hw1 | hw1
      · exact hB₁B₃ w hw1 (memP₃_B₃ hw3)
      · exact False.elim (hf₁dis w ⟨hw1, memP₃_edge hw3⟩)
    have h23 : ∀ w ∈ P₂, w ∈ [b, z₃] → w = b := by
      intro w hw2 hw3
      rcases hP₂mem w hw2 with hw2 | hw2
      · exact hB₂B₃ w hw2 (memP₃_B₃ hw3)
      · exact False.elim (hf₂dis w ⟨hw2, memP₃_edge hw3⟩)
    have hc := h10 b z₁ z₂ z₃ P₁ P₂ [b, z₃]
      hP₁ hP₂ hP₃ hP₁len hP₂len hP₃len h12 h13 h23
      ⟨f₁, hf₁P₁, hf₁X⟩ ⟨f₂, hf₂P₂, hf₂X⟩ hP₃X
    have hfirst1 : s(P₁[0]'(by omega), P₁[1]'(by omega)) ∉
        completeEdges G H K φ Y := by
      exact Set.disjoint_left.mp hnoB₁ (hP₁first hP₁len)
    have hfirst2 : s(P₂[0]'(by omega), P₂[1]'(by omega)) ∉
        completeEdges G H K φ Y := by
      exact Set.disjoint_left.mp hnoB₂ (hP₂first hP₂len)
    rcases hc with h | h | h
    · exact hfirst1 h.1
    · exact hfirst1 h.1
    · exact hfirst2 h.1
  have hbadj : ¬ H.Adj b₁ b₂ := by
    intro hadj
    obtain ⟨u, huf₁, huf₂⟩ := exists_common_end hfmeet
    have hu1 : u ≠ b₁ := by
      intro hu
      apply hf₂ne
      exact eq_sym2_of_mem_mem hb₁b₂ (hu ▸ huf₂) hf₂b
    have hu2 : u ≠ b₂ := by
      intro hu
      apply hf₁ne
      exact eq_sym2_of_mem_mem hb₁b₂ hf₁b (hu ▸ huf₁)
    have h1u : H.Adj b₁ u := by
      apply H.mem_edgeSet.mp
      have hfeq : f₁ = s(b₁, u) := eq_sym2_of_mem_mem hu1.symm hf₁b huf₁
      rw [← hfeq]
      exact hf₁E
    have hu2adj : H.Adj u b₂ := by
      apply H.mem_edgeSet.mp
      have hfeq : f₂ = s(u, b₂) := eq_sym2_of_mem_mem hu2 huf₂ hf₂b
      rw [← hfeq]
      exact hf₂E
    exact no_triangle_of_bipartite hsub.2 h1u hu2adj hadj
  exact ⟨hnoB₁, hnoB₂, hfmeet, hbadj⟩

/-- The next paragraph of (12), in one orientation: `f₁` is the unique complete edge at
`b₁`.  In the contradiction argument a hypothetical second edge makes `B₁` even, which is
exactly the parity needed for the invocation of claim (9). -/
theorem claim12_unique_left
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
    (h9 : Claim9 G H K φ Y y₁ y₂) (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ : Sym2 (Fin n))
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    ∃! f : Sym2 (Fin n), f ∈ incidentEdges H b₁ ∧
      f ∈ completeEdges G H K φ Y := by
  classical
  have hpre := claim12_prelim G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e
      hf₁ne hf₂ne
  rcases hpre with ⟨hnoB₁, hnoB₂, hf₁f₂, hb₁b₂nadj⟩
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
      he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
      hB₃, he₃B₃, hfrom₃⟩
  rcases branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, hB₃pos, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
      hb₁b₂, hb₁b₃, hb₂b₃⟩
  obtain ⟨hXE, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hB₁len : 2 ≤ B₁.length := by
    have h := hB₁pos
    simp only [trackLength] at h
    omega
  have hB₂len : 2 ≤ B₂.length := by
    have h := hB₂pos
    simp only [trackLength] at h
    omega
  have hf₁E : f₁ ∈ H.edgeSet := hXE hf₁X
  have hf₂E : f₂ ∈ H.edgeSet := hXE hf₂X
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hf₁dis : DisjointEdges f₁ e₃ := by
    unfold MeetEdges at hf₁e
    exact Classical.byContradiction hf₁e
  have hf₂dis : DisjointEdges f₂ e₃ := by
    unfold MeetEdges at hf₂e
    exact Classical.byContradiction hf₂e
  have hbf₁ : b ∉ f₁ := fun hb => hf₁dis b ⟨hb, he₃inc.2⟩
  have hbf₂ : b ∉ f₂ := fun hb => hf₂dis b ⟨hb, he₃inc.2⟩
  have hb₁f₂ : b₁ ∉ f₂ := by
    intro hb₁
    apply hf₂ne
    exact eq_sym2_of_mem_mem hb₁b₂ hb₁ hf₂b
  have hf₂outB₁ : f₂ ∉ trackEdges B₁ := by
    intro hf
    exact branch_edge_avoids_other_branchVertex hB₁ hfrom₁ hf hb₂V
      hbb₂.symm hb₁b₂.symm hf₂b
  obtain ⟨z₃, hP₃, he₃eq⟩ := edge_track_from_incident he₃inc
  have hP₃len : 2 ≤ [b, z₃].length := by simp
  have hP₃X : ∃ e ∈ trackEdges [b, z₃], e ∈ completeEdges G H K φ Y := by
    refine ⟨e₃, ⟨0, by simp, ?_⟩, he₃X⟩
    simpa using he₃eq
  have hz₃B₃ : z₃ ∈ B₃ := by
    have hm := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges
      (show s(b, z₃) ∈ trackEdges B₃ by simpa [he₃eq] using he₃B₃)
    exact hm.2
  have hB₁B₂ : ∀ w ∈ B₁, w ∈ B₂ → w = b :=
    branches_from_common_end_meet_only hJ hsub.1 hB₁ hfrom₁ hB₂ hfrom₂
      hB₁pos hB₂pos hbV hb₁V hb₂V hbb₁ hbb₂ hb₁b₂
  have hB₁B₃ : ∀ w ∈ B₁, w ∈ B₃ → w = b :=
    branches_from_common_end_meet_only hJ hsub.1 hB₁ hfrom₁ hB₃ hfrom₃
      hB₁pos hB₃pos hbV hb₁V hb₃V hbb₁ hbb₃ hb₁b₃
  have hB₂B₃ : ∀ w ∈ B₂, w ∈ B₃ → w = b :=
    branches_from_common_end_meet_only hJ hsub.1 hB₂ hfrom₂ hB₃ hfrom₃
      hB₂pos hB₃pos hbV hb₂V hb₃V hbb₂ hbb₃ hb₂b₃
  have memP₃_edge : ∀ {w : Fin n}, w ∈ [b, z₃] → w ∈ e₃ := by
    intro w hw
    rw [he₃eq]
    simpa using hw
  have memP₃_B₃ : ∀ {w : Fin n}, w ∈ [b, z₃] → w ∈ B₃ := by
    intro w hw
    simp at hw
    rcases hw with rfl | rfl
    · exact List.mem_of_mem_head? hfrom₃.2.1
    · exact hz₃B₃
  have hb₁not_e₃ : b₁ ∉ e₃ := by
    intro hb₁e
    have heq : e₃ = s(b, b₁) := eq_sym2_of_mem_mem hbb₁ he₃inc.2 hb₁e
    have hadj : H.Adj b b₁ := H.mem_edgeSet.mp (heq ▸ he₃inc.1)
    have hlen1 := branch_length_one_of_adj J hJ H hsub.1 hB₁ hfrom₁ hB₁pos hadj
    have hset := trackEdges_eq_singleton_of_length_one hfrom₁ hlen1
    have he₁eq : e₁ = s(b, b₁) := by
      rw [hset] at he₁B₁
      exact Set.mem_singleton_iff.mp he₁B₁
    exact he₃e₁ (heq.trans he₁eq.symm)
  have b_not_complete_at_b₁ : ∀ {f : Sym2 (Fin n)},
      f ∈ incidentEdges H b₁ → f ∈ completeEdges G H K φ Y → b ∉ f := by
    intro f hf hfX hbf
    have hfeq : f = s(b, b₁) := by
      rw [Sym2.eq_swap]
      exact eq_sym2_of_mem_mem hbb₁.symm hf.2 hbf
    have hadj : H.Adj b b₁ := H.mem_edgeSet.mp (hfeq ▸ hf.1)
    have hlen1 := branch_length_one_of_adj J hJ H hsub.1 hB₁ hfrom₁ hB₁pos hadj
    have hset := trackEdges_eq_singleton_of_length_one hfrom₁ hlen1
    have hfB : f ∈ trackEdges B₁ := by rw [hset, hfeq]; simp
    exact Set.disjoint_left.mp hnoB₁ hfB hfX
  have unique : ∀ f : Sym2 (Fin n),
      f ∈ incidentEdges H b₁ ∧ f ∈ completeEdges G H K φ Y → f = f₁ := by
    intro f hf
    by_contra hff₁
    have hbf : b ∉ f := b_not_complete_at_b₁ hf.1 hf.2
    have hfoutB₂ : f ∉ trackEdges B₂ := by
      intro hfB
      exact branch_edge_avoids_other_branchVertex hB₂ hfrom₂ hfB hb₁V
        hbb₁.symm hb₁b₂ hf.1.2
    have hff₂dis : DisjointEdges f f₂ := by
      by_contra hm
      have hm' : MeetEdges f f₂ := hm
      have hsubsingle := meeting_edges_at_vertex_subsingleton hsub.2 hf₂E hb₁f₂
      have heq := hsubsingle ⟨⟨hf₁E, hf₁b⟩, hf₁f₂⟩ ⟨hf.1, hm'⟩
      exact hff₁ heq.symm
    have hfe₃ : MeetEdges f e₃ := by
      by_contra hnot
      have hfed : DisjointEdges f e₃ := by
        unfold MeetEdges at hnot
        exact Classical.byContradiction hnot
      obtain ⟨P₁, z₁, hP₁, hP₁len, hfP₁, hP₁mem, hP₁first⟩ :=
        extend_branch_through_incident_edge hB₁ hfrom₁ hB₁pos hf.1 hbf
      obtain ⟨P₂, z₂, hP₂, hP₂len, hf₂P₂, hP₂mem, hP₂first⟩ :=
        extend_branch_through_incident_edge hB₂ hfrom₂ hB₂pos
          ⟨hf₂E, hf₂b⟩ hbf₂
      have h12 : ∀ w ∈ P₁, w ∈ P₂ → w = b := by
        intro w hw1 hw2
        rcases hP₁mem w hw1 with hw1 | hw1 <;>
          rcases hP₂mem w hw2 with hw2 | hw2
        · exact hB₁B₂ w hw1 hw2
        · rcases external_edge_inter_branch_only_at_ends hB₁ hfrom₁ hB₁pos
              hf₂E hf₂outB₁ hw1 hw2 with hwb | hwb₁
          · exact hwb
          · exact False.elim (hb₁f₂ (hwb₁ ▸ hw2))
        · rcases external_edge_inter_branch_only_at_ends hB₂ hfrom₂ hB₂pos
              hf.1.1 hfoutB₂ hw2 hw1 with hwb | hwb₂
          · exact hwb
          · exfalso
            apply hb₁b₂nadj
            apply H.mem_edgeSet.mp
            have hfeq : f = s(b₁, b₂) :=
              eq_sym2_of_mem_mem hb₁b₂ hf.1.2 (hwb₂ ▸ hw1)
            exact hfeq ▸ hf.1.1
        · exact False.elim (hff₂dis w ⟨hw1, hw2⟩)
      have h13 : ∀ w ∈ P₁, w ∈ [b, z₃] → w = b := by
        intro w hw1 hw3
        rcases hP₁mem w hw1 with hw1 | hw1
        · exact hB₁B₃ w hw1 (memP₃_B₃ hw3)
        · exact False.elim (hfed w ⟨hw1, memP₃_edge hw3⟩)
      have h23 : ∀ w ∈ P₂, w ∈ [b, z₃] → w = b := by
        intro w hw2 hw3
        rcases hP₂mem w hw2 with hw2 | hw2
        · exact hB₂B₃ w hw2 (memP₃_B₃ hw3)
        · exact False.elim (hf₂dis w ⟨hw2, memP₃_edge hw3⟩)
      have hc := h10 b z₁ z₂ z₃ P₁ P₂ [b, z₃]
        hP₁ hP₂ hP₃ hP₁len hP₂len hP₃len h12 h13 h23
        ⟨f, hfP₁, hf.2⟩ ⟨f₂, hf₂P₂, hf₂X⟩ hP₃X
      have hfirst1 : s(P₁[0]'(by omega), P₁[1]'(by omega)) ∉
          completeEdges G H K φ Y :=
        Set.disjoint_left.mp hnoB₁ (hP₁first hP₁len)
      have hfirst2 : s(P₂[0]'(by omega), P₂[1]'(by omega)) ∉
          completeEdges G H K φ Y :=
        Set.disjoint_left.mp hnoB₂ (hP₂first hP₂len)
      rcases hc with h | h | h
      · exact hfirst1 h.1
      · exact hfirst1 h.1
      · exact hfirst2 h.1
    have hB₁even : Even (trackLength B₁) := by
      obtain ⟨u, huf, hue₃⟩ := exists_common_end hfe₃
      have hu₁ : u ≠ b₁ := fun hu => hb₁not_e₃ (hu ▸ hue₃)
      have hub : u ≠ b := fun hu => hbf (hu ▸ huf)
      have h₁u : H.Adj b₁ u := by
        apply H.mem_edgeSet.mp
        have hfeq : f = s(b₁, u) := eq_sym2_of_mem_mem hu₁.symm hf.1.2 huf
        exact hfeq ▸ hf.1.1
      have hbu : H.Adj b u := by
        apply H.mem_edgeSet.mp
        have heq : e₃ = s(b, u) := eq_sym2_of_mem_mem hub.symm he₃inc.2 hue₃
        exact heq ▸ he₃inc.1
      obtain ⟨col⟩ :=
        Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
      apply (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mpr
      exact (bool_eq_of_ne_ne (col u) (col b) (col b₁)
        (col.valid hbu).symm (col.valid h₁u).symm)
    -- Claim (9), applied to `z₃-B₁-z₁`, contradicts the complete edge `f₂`.
    obtain ⟨z₁, hf₁track, hf₁eq⟩ := edge_track_from_incident ⟨hf₁E, hf₁b⟩
    have hz₁b₁ : z₁ ≠ b₁ := by
      have hadj : H.Adj b₁ z₁ := by simpa using hf₁track.1.2.2 0 (by simp)
      exact hadj.ne.symm
    have hf₁outB₁ : f₁ ∉ trackEdges B₁ := by
      intro hm
      exact Set.disjoint_left.mp hnoB₁ hm hf₁X
    have hz₁B₁ : z₁ ∉ B₁ := by
      intro hz
      rcases external_edge_inter_branch_only_at_ends hB₁ hfrom₁ hB₁pos
          hf₁E hf₁outB₁ hz (by rw [hf₁eq]; simp) with hzb | hzb₁
      · exact hbf₁ (by rw [hf₁eq, hzb]; simp)
      · exact hz₁b₁ hzb₁
    have hz₃b : z₃ ≠ b := by
      have hadj : H.Adj b z₃ := by simpa using hP₃.1.2.2 0 (by simp)
      exact hadj.ne.symm
    have hz₃B₁ : z₃ ∉ B₁ := by
      intro hz
      have := hB₁B₃ z₃ hz hz₃B₃
      exact hz₃b this
    have hz₃z₁ : z₃ ≠ z₁ := by
      intro h
      exact hf₁dis z₁ ⟨by rw [hf₁eq]; simp, by rw [he₃eq, h]; simp⟩
    let P : List (Fin n) := z₃ :: (B₁ ++ [z₁])
    have hhang := hang_track hfrom₁ hB₁len
      (by exact (hP₃.1.2.2 0 (by simp)).symm)
      (by exact hf₁track.1.2.2 0 (by simp)) hz₃B₁ hz₁B₁ hz₃z₁
    have hP : IsTrackFrom H P z₃ z₁ := by simpa [P] using hhang.1
    have hPlenEq : P.length = B₁.length + 2 := by simpa [P] using hhang.2.1
    have hPlen : 5 ≤ P.length := by
      rcases hB₁even with ⟨k, hk⟩
      simp only [trackLength] at hk hB₁pos
      omega
    have hPeven : Even (trackLength P) := by
      rcases hB₁even with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      simp only [trackLength] at hk ⊢
      omega
    have hedges := hang_edges hfrom₁ hB₁len (u := z₃) (v := z₁)
    have hfirst : s(P[0]'(by omega), P[1]'(by omega)) ∈
        completeEdges G H K φ Y := by
      have hp : s(P[0]'(by omega), P[1]'(by omega)) = s(z₃, b) := by
        simpa [P] using hedges.1
      rw [hp, Sym2.eq_swap, ← he₃eq]
      exact he₃X
    have hlast : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega)) ∈
        completeEdges G H K φ Y := by
      have hp : s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega)) =
          s(b₁, z₁) := by
        simpa [P] using hedges.2.1
      rw [hp, ← hf₁eq]
      exact hf₁X
    have hint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < P.length,
        s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ completeEdges G H K φ Y := by
      intro i hi hi' hcomp
      have hp := hedges.2.2 i hi (by simpa [P] using hi')
      have hmem : s(B₁[i - 1]'(by omega), B₁[i]'(by omega)) ∈ trackEdges B₁ :=
        ⟨i - 1, by
          simp only [P, List.length_cons, List.length_append, List.length_singleton,
            List.length_nil] at hi'
          omega, by
          congr 1
          exact geq B₁ (by omega) (by omega) (by omega)⟩
      exact Set.disjoint_left.mp hnoB₁ hmem (hp ▸ hcomp)
    have hc := h9 Y (Or.inl rfl) P hP.1 hPlen hPeven hfirst hlast hint f₂ hf₂X
    have hp₁ : P[1]'(by omega) = b := by
      have hget := hhang.2.2.1 0 (by omega) (by omega)
      rw [head_getElem hfrom₁.2.1 (by omega)] at hget
      simpa [P] using hget
    have hplast : P[P.length - 2]'(by omega) = b₁ := by
      have hget := hhang.2.2.1 (B₁.length - 1) (by omega) (by omega)
      have hb₁last := last_getElem hfrom₁.2.2 (by omega)
      rw [hb₁last] at hget
      have hidx : P.length - 2 = (B₁.length - 1) + 1 := by omega
      exact (geq P hidx (by omega) (by omega)).trans (by simpa [P] using hget)
    rcases hc with hc | hc
    · exact hbf₂ (hp₁ ▸ hc)
    · exact hb₁f₂ (hplast ▸ hc)
  refine ⟨f₁, ⟨⟨hf₁E, hf₁b⟩, hf₁X⟩, ?_⟩
  intro f hf
  exact unique f hf

/-- Symmetrizing the preceding argument gives the two triads.  Claim (8), together with the
nonadjacency already forced by claim (10), then makes both original branches single edges. -/
theorem claim12_triads_and_short
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ : Sym2 (Fin n))
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    Triad G H K φ Y b₁ ∧ Triad G H K φ Y b₂ ∧
      trackLength B₁ = 1 ∧ trackLength B₂ = 1 := by
  classical
  have hu₁ := claim12_unique_left G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
    h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ hf₁X hf₁b hf₁e
      hf₂X hf₂b hf₂e hf₁ne hf₂ne
  have hQrev : IsAntipathFrom G Q.reverse y₂ y₁ :=
    Workspace.ProofLemmas.PathBasics.isAntipathFrom_reverse hQ
  have hQYrev : ∀ v : V, v ∈ Q.reverse ↔ v ∈ Y := by
    intro v
    simpa using hQY v
  have h9swap : Claim9 G H K φ Y y₂ y₁ := by
    intro Y' hY' P hP hlen heven hfirst hlast hint f hf
    apply h9 Y' _ P hP hlen heven hfirst hlast hint f hf
    rcases hY' with rfl | hY' | hY'
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hY')
    · exact Or.inr (Or.inl hY')
  have hbcswap : BranchChoice G H K φ Y y₂ y₁ b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ := by
    rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
      he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
      hB₃, he₃B₃, hfrom₃⟩
    exact ⟨hbV, hnon, he₂inc, he₂X₂, he₁inc, he₁X₁, he₃inc,
      he₃e₂, he₃e₁, hB₂, he₂B₂, hfrom₂, hB₁, he₁B₁, hfrom₁,
      hB₃, he₃B₃, hfrom₃⟩
  have hf₂ne' : f₂ ≠ s(b₂, b₁) := by simpa [Sym2.eq_swap] using hf₂ne
  have hf₁ne' : f₁ ≠ s(b₂, b₁) := by simpa [Sym2.eq_swap] using hf₁ne
  have hu₂ := claim12_unique_left G m J hJ n H K hsub φ Y hmin y₂ y₁ Q.reverse
    hQrev hQYrev hy.symm h9swap h10 b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ hbcswap
      f₂ f₁ hf₂X hf₂b hf₂e hf₁X hf₁b hf₁e hf₂ne' hf₁ne'
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
      he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
      hB₃, he₃B₃, hfrom₃⟩
  rcases branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, -, -, hb₁V, hb₂V, -, hbb₁, hbb₂, -, hb₁b₂, -, -⟩
  have htri₁ : Triad G H K φ Y b₁ := ⟨hb₁V, by
    intro a ha c hc
    exact hu₁.unique ⟨ha.1, ha.2⟩ ⟨hc.1, hc.2⟩⟩
  have htri₂ : Triad G H K φ Y b₂ := ⟨hb₂V, by
    intro a ha c hc
    exact hu₂.unique ⟨ha.1, ha.2⟩ ⟨hc.1, hc.2⟩⟩
  obtain ⟨-, -, hX₁uniq₁, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₁ htri₁
  obtain ⟨-, -, -, hX₂uniq₂⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htri₂
  obtain ⟨a₁, ha₁, -⟩ := hX₁uniq₁
  obtain ⟨a₂, ha₂, -⟩ := hX₂uniq₂
  have ha₁eq : a₁ = e₁ := by
    by_contra hne
    have hm := h8 a₁ e₂ ha₁.2 he₂X₂
    obtain ⟨-, -, hcross⟩ := identify_cross_meeting J hJ H hsub.1
      hB₂ hfrom₂ hB₁ hfrom₁ hB₂pos hB₁pos hb₁V hbb₁.symm hb₁b₂
      he₂B₂ he₂inc.2 he₁B₁ he₁inc.2 ha₁.1.1 ha₁.1.2 hne hm
    apply (claim12_prelim G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' f₁ f₂ hf₁X hf₁b hf₁e
        hf₂X hf₂b hf₂e hf₁ne hf₂ne).2.2.2
    apply H.mem_edgeSet.mp
    rw [← hcross]
    exact ha₁.1.1
  have ha₂eq : a₂ = e₂ := by
    by_contra hne
    have hm0 := h8 e₁ a₂ he₁X₁ ha₂.2
    have hm : MeetEdges a₂ e₁ := by
      simpa only [MeetEdges, DisjointEdges, and_comm] using hm0
    obtain ⟨-, -, hcross⟩ := identify_cross_meeting J hJ H hsub.1
      hB₁ hfrom₁ hB₂ hfrom₂ hB₁pos hB₂pos hb₂V hbb₂.symm hb₁b₂.symm
      he₁B₁ he₁inc.2 he₂B₂ he₂inc.2 ha₂.1.1 ha₂.1.2 hne hm
    apply (claim12_prelim G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' f₁ f₂ hf₁X hf₁b hf₁e
        hf₂X hf₂b hf₂e hf₁ne hf₂ne).2.2.2
    apply H.mem_edgeSet.mp
    have heq : s(b₁, b₂) = a₂ :=
      (show s(b₁, b₂) = s(b₂, b₁) from Sym2.eq_swap).trans hcross.symm
    rw [heq]
    exact ha₂.1.1
  have hadj₁ : H.Adj b b₁ := by
    apply H.mem_edgeSet.mp
    have heq : e₁ = s(b, b₁) := eq_sym2_of_mem_mem hbb₁ he₁inc.2 (ha₁eq ▸ ha₁.1.2)
    rw [← heq]
    exact he₁inc.1
  have hadj₂ : H.Adj b b₂ := by
    apply H.mem_edgeSet.mp
    have heq : e₂ = s(b, b₂) := eq_sym2_of_mem_mem hbb₂ he₂inc.2 (ha₂eq ▸ ha₂.1.2)
    rw [← heq]
    exact he₂inc.1
  exact ⟨htri₁, htri₂,
    branch_length_one_of_adj J hJ H hsub.1 hB₁ hfrom₁ hB₁pos hadj₁,
    branch_length_one_of_adj J hJ H hsub.1 hB₂ hfrom₂ hB₂pos hadj₂⟩

/-- The labelled `u,v` skeleton in the middle of printed claim (12). -/
theorem claim12_cross_skeleton
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ : Sym2 (Fin n))
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    ∃ (d₁ d₂ : Sym2 (Fin n)) (u v : Fin n),
      d₁ ∈ incidentEdges H b₁ ∧ d₁ ∈ extraEdges G H K φ Y y₂ ∧
      d₂ ∈ incidentEdges H b₂ ∧ d₂ ∈ extraEdges G H K φ Y y₁ ∧
      f₁ = s(b₁, u) ∧ f₂ = s(b₂, u) ∧
      d₁ = s(b₁, v) ∧ d₂ = s(b₂, v) ∧
      u ≠ b₁ ∧ u ≠ b₂ ∧ v ≠ b₁ ∧ v ≠ b₂ ∧ u ≠ v := by
  classical
  obtain ⟨htri₁, htri₂, hB₁one, hB₂one⟩ :=
    claim12_triads_and_short G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂
      hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
  obtain ⟨-, -, -, hbadj⟩ :=
    claim12_prelim G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ hf₁X hf₁b hf₁e
        hf₂X hf₂b hf₂e hf₁ne hf₂ne
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hb₁b₂, -, -⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  obtain ⟨-, -, -, hX₂uniq₁⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₁ htri₁
  obtain ⟨-, -, hX₁uniq₂, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htri₂
  obtain ⟨d₁, hd₁, -⟩ := hX₂uniq₁
  obtain ⟨d₂, hd₂, -⟩ := hX₁uniq₂
  have hdmeet0 := h8 d₂ d₁ hd₂.2 hd₁.2
  have hdmeet : MeetEdges d₁ d₂ := by
    simpa only [MeetEdges, DisjointEdges, and_comm] using hdmeet0
  obtain ⟨u, huf₁, huf₂⟩ := exists_common_end
    (claim12_prelim G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ hf₁X hf₁b hf₁e
        hf₂X hf₂b hf₂e hf₁ne hf₂ne).2.2.1
  obtain ⟨v, hvd₁, hvd₂⟩ := exists_common_end hdmeet
  have hu₁ : u ≠ b₁ := by
    intro h
    apply hbadj
    apply H.mem_edgeSet.mp
    have heq : f₂ = s(b₁, b₂) := eq_sym2_of_mem_mem hb₁b₂ (h ▸ huf₂) hf₂b
    exact heq ▸ hf₂X.1
  have hu₂ : u ≠ b₂ := by
    intro h
    apply hbadj
    apply H.mem_edgeSet.mp
    have heq : f₁ = s(b₁, b₂) := eq_sym2_of_mem_mem hb₁b₂ hf₁b (h ▸ huf₁)
    exact heq ▸ hf₁X.1
  have hv₁ : v ≠ b₁ := by
    intro h
    apply hbadj
    apply H.mem_edgeSet.mp
    have heq : d₂ = s(b₁, b₂) := eq_sym2_of_mem_mem hb₁b₂ (h ▸ hvd₂) hd₂.1.2
    exact heq ▸ hd₂.1.1
  have hv₂ : v ≠ b₂ := by
    intro h
    apply hbadj
    apply H.mem_edgeSet.mp
    have heq : d₁ = s(b₁, b₂) := eq_sym2_of_mem_mem hb₁b₂ hd₁.1.2 (h ▸ hvd₁)
    exact heq ▸ hd₁.1.1
  have hf₁eq : f₁ = s(b₁, u) := eq_sym2_of_mem_mem hu₁.symm hf₁b huf₁
  have hf₂eq : f₂ = s(b₂, u) := eq_sym2_of_mem_mem hu₂.symm hf₂b huf₂
  have hd₁eq : d₁ = s(b₁, v) := eq_sym2_of_mem_mem hv₁.symm hd₁.1.2 hvd₁
  have hd₂eq : d₂ = s(b₂, v) := eq_sym2_of_mem_mem hv₂.symm hd₂.1.2 hvd₂
  have huv : u ≠ v := by
    intro huv
    have heq : f₁ = d₁ := by rw [hf₁eq, hd₁eq, huv]
    obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, -, -⟩ :=
      X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
    exact (Set.disjoint_left.mp hXX₂ hf₁X) (heq ▸ hd₁.2)
  exact ⟨d₁, d₂, u, v, hd₁.1, hd₁.2, hd₂.1, hd₂.2,
    hf₁eq, hf₂eq, hd₁eq, hd₂eq, hu₁, hu₂, hv₁, hv₂, huv⟩

/-- Every further edge at the common end `v` is complete and meets `e₃`, exactly as in the
four-edge-track application of claim (9) in the paper. -/
theorem claim12_other_edge_at_v
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : H.IsBipartite) (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    {b b₁ b₂ : Fin n} {e₁ e₂ e₃ d₁ d₂ f₁ : Sym2 (Fin n)} {u v : Fin n}
    (he₁ : e₁ ∈ incidentEdges H b) (he₁X : e₁ ∈ extraEdges G H K φ Y y₁)
    (he₂ : e₂ ∈ incidentEdges H b) (he₂X : e₂ ∈ extraEdges G H K φ Y y₂)
    (he₃ : e₃ ∈ incidentEdges H b) (he₃ne₁ : e₃ ≠ e₁) (he₃ne₂ : e₃ ≠ e₂)
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁X : d₁ ∈ extraEdges G H K φ Y y₂)
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂X : d₂ ∈ extraEdges G H K φ Y y₁)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y)
    (he₁eq : e₁ = s(b, b₁)) (he₂eq : e₂ = s(b, b₂))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (hf₁eq : f₁ = s(b₁, u))
    (hbb₁ : b ≠ b₁) (hbb₂ : b ≠ b₂) (hb₁b₂ : b₁ ≠ b₂)
    (hvb₁ : v ≠ b₁) (hvb₂ : v ≠ b₂) (huv : u ≠ v)
    (hbf₁ : b ∉ f₁) :
    ∀ g ∈ incidentEdges H v, g ≠ d₁ → g ≠ d₂ →
      g ∈ completeEdges G H K φ Y ∧ MeetEdges g e₃ := by
  classical
  obtain ⟨hXE, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hd₁v : d₁ ∈ incidentEdges H v := by
    refine ⟨hd₁.1, ?_⟩
    rw [hd₁eq]
    simp
  have hd₂v : d₂ ∈ incidentEdges H v := by
    refine ⟨hd₂.1, ?_⟩
    rw [hd₂eq]
    simp
  have hd₁d₂ : d₁ ≠ d₂ := by
    intro h
    exact (Set.disjoint_right.mp hX₁X₂ hd₁X) (h ▸ hd₂X)
  have hvb : v ≠ b := by
    intro hvb
    have heq : d₁ = e₁ := by rw [hd₁eq, he₁eq, hvb, Sym2.eq_swap]
    exact (Set.disjoint_left.mp hX₁X₂ (heq ▸ he₁X)) hd₁X
  intro g hg hg₁ hg₂
  have hvbranch : v ∈ branchVertices H := by
    have hsubinc : ({d₁, d₂, g} : Set (Sym2 (Fin n))) ⊆ incidentEdges H v := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;> assumption
    have hcard : ({d₁, d₂, g} : Set (Sym2 (Fin n))).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨d₁, d₂, g, hd₁d₂, hg₁.symm, hg₂.symm, rfl⟩
    have hle := Set.ncard_le_ncard hsubinc (Set.toFinite _)
    rw [hcard, incidentEdges_ncard] at hle
    exact hle
  have hgX : g ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hvbranch hd₂v hd₂X hd₁v hd₁X hg
      hg₂ hg₁ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  refine ⟨hgX, ?_⟩
  by_contra hgm
  have hgdis : DisjointEdges g e₃ := by
    unfold MeetEdges at hgm
    exact Classical.byContradiction hgm
  obtain ⟨w, hgeq⟩ := Sym2.mem_iff_exists.mp hg.2
  have hvw : v ≠ w := by
    have hadj : H.Adj v w := by
      apply H.mem_edgeSet.mp
      rw [← hgeq]
      exact hg.1
    exact hadj.ne
  have hwb₂ : w ≠ b₂ := by
    intro hw
    apply hg₂
    rw [hgeq, hw, hd₂eq, Sym2.eq_swap]
  have hwb₁ : w ≠ b₁ := by
    intro hw
    apply hg₁
    rw [hgeq, hw, hd₁eq, Sym2.eq_swap]
  have hwb : w ≠ b := by
    intro hw
    have hvb₂adj : H.Adj v b₂ := by
      apply H.mem_edgeSet.mp
      simpa only [hd₂eq, Sym2.eq_swap] using hd₂.1
    have hb₂b : H.Adj b₂ b := by
      apply H.mem_edgeSet.mp
      simpa only [he₂eq, Sym2.eq_swap] using he₂.1
    have hvbadj : H.Adj v b := by
      apply H.mem_edgeSet.mp
      have heq : s(v, b) = g := by rw [← hw, ← hgeq]
      rw [heq]
      exact hg.1
    exact no_triangle_of_bipartite hsub hvb₂adj hb₂b hvbadj
  obtain ⟨z₃, hP₃, he₃eq⟩ := edge_track_from_incident he₃
  have hbz₃ : b ≠ z₃ := by
    have hadj : H.Adj b z₃ := by simpa using hP₃.1.2.2 0 (by simp)
    exact hadj.ne
  have hz₃b₂ : z₃ ≠ b₂ := by
    intro hz
    apply he₃ne₂
    rw [he₃eq, he₂eq, hz]
  have hz₃v : z₃ ≠ v := by
    intro hz
    exact hgdis v ⟨by rw [hgeq]; simp, by rw [he₃eq, ← hz]; simp⟩
  have hz₃w : z₃ ≠ w := by
    intro hz
    exact hgdis w ⟨by rw [hgeq]; simp, by rw [he₃eq, hz]; simp⟩
  let P : List (Fin n) := [w, v, b₂, b, z₃]
  have hP : IsTrackList H P := by
    refine ⟨by simp [P], ?_, ?_⟩
    · simp only [P, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        or_false, not_or]
      exact ⟨⟨hvw.symm, hwb₂, hwb, hz₃w.symm⟩,
        ⟨⟨hvb₂, hvb, hz₃v.symm⟩,
          ⟨⟨hbb₂.symm, hz₃b₂.symm⟩, ⟨hbz₃, by simp⟩⟩⟩⟩
    · intro i hi
      have hi' : i ≤ 3 := by simp only [P, List.length_cons, List.length_nil] at hi; omega
      interval_cases i <;> simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
      · apply H.mem_edgeSet.mp
        simpa only [hgeq, Sym2.eq_swap] using hg.1
      · apply H.mem_edgeSet.mp
        simpa only [hd₂eq, Sym2.eq_swap] using hd₂.1
      · apply H.mem_edgeSet.mp
        simpa only [he₂eq, Sym2.eq_swap] using he₂.1
      · apply H.mem_edgeSet.mp
        rw [← he₃eq]
        exact he₃.1
  have hfirst : s(P[0]'(by simp [P]), P[1]'(by simp [P])) ∈
      completeEdges G H K φ Y := by
    simpa only [P, List.getElem_cons_zero, List.getElem_cons_succ, hgeq, Sym2.eq_swap]
      using hgX
  have hlast : s(P[P.length - 2]'(by simp [P]), P[P.length - 1]'(by simp [P])) ∈
      completeEdges G H K φ Y := by
    simpa only [P, List.length_cons, List.length_nil, List.getElem_cons_zero,
      List.getElem_cons_succ, he₃eq] using
        (other_incident_is_complete φ Y y₁ y₂
          (show b ∈ branchVertices H from by
            -- It is part of the branch-choice data; recovering it directly avoids carrying
            -- that whole record through this local lemma.
            have hsubinc : ({e₁, e₂, e₃} : Set (Sym2 (Fin n))) ⊆ incidentEdges H b := by
              intro e he
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
              rcases he with rfl | rfl | rfl <;> assumption
            have he₁e₂ : e₁ ≠ e₂ := by
              intro heq
              exact (Set.disjoint_left.mp hX₁X₂ he₁X) (heq ▸ he₂X)
            have hc : ({e₁, e₂, e₃} : Set (Sym2 (Fin n))).ncard = 3 :=
              Set.ncard_eq_three.mpr ⟨e₁, e₂, e₃, he₁e₂, he₃ne₁.symm,
                he₃ne₂.symm, rfl⟩
            have hle := Set.ncard_le_ncard hsubinc (Set.toFinite _)
            rw [hc, incidentEdges_ncard] at hle
            exact hle)
          he₁ he₁X he₂ he₂X he₃ he₃ne₁ he₃ne₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂)
  have hint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < P.length,
      s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ completeEdges G H K φ Y := by
    intro i hi hi2
    have hi' : i ≤ 2 := by simp only [P, List.length_cons, List.length_nil] at hi2; omega
    interval_cases i
    · simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
      simpa only [hd₂eq, Sym2.eq_swap] using Set.disjoint_right.mp hXX₁ hd₂X
    · simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
      simpa only [he₂eq, Sym2.eq_swap] using Set.disjoint_right.mp hXX₂ he₂X
  have hpen := h9 Y (Or.inl rfl) P hP (by simp [P]) (by
    refine ⟨2, ?_⟩
    simp [P, trackLength]) hfirst hlast hint f₁ hf₁X
  have hvf₁ : v ∉ f₁ := by
    rw [hf₁eq]
    simp [hvb₁, huv.symm]
  rcases hpen with hpen | hpen
  · exact hvf₁ (by simpa [P] using hpen)
  · exact hbf₁ (by simpa [P] using hpen)

/-- The displayed cross edges account for two or three edges at `v`; there cannot be a fourth
one.  This packages the degree conclusion in the middle of printed claim (12), while retaining
all of the labelled skeleton needed by the three cases that follow it. -/
theorem claim12_cross_skeleton_and_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ : Sym2 (Fin n))
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    ∃ (d₁ d₂ : Sym2 (Fin n)) (u v : Fin n),
      d₁ ∈ incidentEdges H b₁ ∧ d₁ ∈ extraEdges G H K φ Y y₂ ∧
      d₂ ∈ incidentEdges H b₂ ∧ d₂ ∈ extraEdges G H K φ Y y₁ ∧
      f₁ = s(b₁, u) ∧ f₂ = s(b₂, u) ∧
      d₁ = s(b₁, v) ∧ d₂ = s(b₂, v) ∧
      u ≠ b₁ ∧ u ≠ b₂ ∧ v ≠ b₁ ∧ v ≠ b₂ ∧ u ≠ v ∧
      ((H.neighborSet v).ncard = 2 ∨ (H.neighborSet v).ncard = 3) := by
  classical
  obtain ⟨d₁, d₂, u, v, hd₁, hd₁X, hd₂, hd₂X, hf₁eq, hf₂eq,
      hd₁eq, hd₂eq, hu₁, hu₂, hv₁, hv₂, huv⟩ :=
    claim12_cross_skeleton G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂
      hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
  rcases hbc with ⟨hbV, hnon, he₁, he₁X, he₂, he₂X, he₃, he₃ne₁, he₃ne₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁, he₁X, he₂, he₂X, he₃, he₃ne₁, he₃ne₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, -, -, -, -, hbb₁, hbb₂, -, hb₁b₂, -, -⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
  obtain ⟨-, -, hB₁one, hB₂one⟩ :=
    claim12_triads_and_short G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' f₁ f₂
      hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
  have he₁eq : e₁ = s(b, b₁) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁one] at he₁B₁
    exact Set.mem_singleton_iff.mp he₁B₁
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hB₂one] at he₂B₂
    exact Set.mem_singleton_iff.mp he₂B₂
  have hd₁v : d₁ ∈ incidentEdges H v := by
    refine ⟨hd₁.1, ?_⟩
    rw [hd₁eq]
    simp
  have hd₂v : d₂ ∈ incidentEdges H v := by
    refine ⟨hd₂.1, ?_⟩
    rw [hd₂eq]
    simp
  obtain ⟨-, -, -, -, -, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hd₁d₂ : d₁ ≠ d₂ := by
    intro h
    exact (Set.disjoint_right.mp hX₁X₂ hd₁X) (h ▸ hd₂X)
  have hvb : v ≠ b := by
    intro hvb
    have heq : d₂ = e₂ := by rw [hd₂eq, he₂eq, hvb, Sym2.eq_swap]
    exact (Set.disjoint_left.mp hX₁X₂ hd₂X) (by rw [heq]; exact he₂X)
  have hbf₁ : b ∉ f₁ := by
    intro hbf
    exact hf₁e (by
      unfold MeetEdges DisjointEdges
      push Not
      exact ⟨b, hbf, he₃.2⟩)
  have hother := claim12_other_edge_at_v G n H K hsub.2 φ Y hmin y₁ y₂ Q hQ hQY hy h9
    he₁ he₁X he₂ he₂X he₃ he₃ne₁ he₃ne₂ hd₁ hd₁X hd₂ hd₂X hf₁X
    he₁eq he₂eq hd₁eq hd₂eq hf₁eq hbb₁ hbb₂ hb₁b₂ hv₁ hv₂ huv hbf₁
  have hsubsingle :
      (incidentEdges H v \ ({d₁, d₂} : Set (Sym2 (Fin n)))).Subsingleton :=
    other_incident_edges_subsingleton hsub.2 hB₃ hfrom₃ hB₃pos he₃B₃ he₃.2
      (by apply H.mem_edgeSet.mp; rw [← he₂eq]; exact he₂.1)
      (by apply H.mem_edgeSet.mp; rw [← hd₂eq]; exact hd₂.1)
      hd₁v hd₂v hd₁d₂ hvb (fun g hg hg₁ hg₂ => (hother g hg hg₁ hg₂).2)
  have hge2 : 2 ≤ (H.neighborSet v).ncard := by
    have hpair : ({d₁, d₂} : Set (Sym2 (Fin n))) ⊆ incidentEdges H v := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      · exact hd₁v
      · exact hd₂v
    have hle := Set.ncard_le_ncard hpair (Set.toFinite _)
    rw [Set.ncard_pair hd₁d₂, incidentEdges_ncard] at hle
    exact hle
  have hle3 : (H.neighborSet v).ncard ≤ 3 := by
    by_cases hex : ∃ g ∈ incidentEdges H v, g ≠ d₁ ∧ g ≠ d₂
    · obtain ⟨g, hg, hg₁, hg₂⟩ := hex
      have hsub : incidentEdges H v ⊆ ({d₁, d₂, g} : Set (Sym2 (Fin n))) := by
        intro e he
        by_cases he₁ : e = d₁
        · simp [he₁]
        by_cases he₂ : e = d₂
        · simp [he₂]
        have hem : e ∈ incidentEdges H v \ ({d₁, d₂} : Set (Sym2 (Fin n))) := by
          exact ⟨he, by simp [he₁, he₂]⟩
        have hgm : g ∈ incidentEdges H v \ ({d₁, d₂} : Set (Sym2 (Fin n))) := by
          exact ⟨hg, by simp [hg₁, hg₂]⟩
        have heg := hsubsingle hem hgm
        simp [heg]
      calc
        (H.neighborSet v).ncard = (incidentEdges H v).ncard := (incidentEdges_ncard v).symm
        _ ≤ ({d₁, d₂, g} : Set (Sym2 (Fin n))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 3 := by
          calc
            ({d₁, d₂, g} : Set (Sym2 (Fin n))).ncard
                ≤ ({d₂, g} : Set (Sym2 (Fin n))).ncard + 1 := Set.ncard_insert_le _ _
            _ ≤ ({g} : Set (Sym2 (Fin n))).ncard + 1 + 1 := by
              have := Set.ncard_insert_le d₂ ({g} : Set (Sym2 (Fin n)))
              omega
            _ = 3 := by simp
    · have hsub : incidentEdges H v ⊆ ({d₁, d₂} : Set (Sym2 (Fin n))) := by
        intro e he
        by_contra hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hm
        exact hex ⟨e, he, hm.1, hm.2⟩
      calc
        (H.neighborSet v).ncard = (incidentEdges H v).ncard := (incidentEdges_ncard v).symm
        _ ≤ ({d₁, d₂} : Set (Sym2 (Fin n))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 3 := by
          have := Set.ncard_insert_le d₁ ({d₂} : Set (Sym2 (Fin n)))
          simp only [Set.ncard_singleton] at this
          omega
  refine ⟨d₁, d₂, u, v, hd₁, hd₁X, hd₂, hd₂X, hf₁eq, hf₂eq,
    hd₁eq, hd₂eq, hu₁, hu₂, hv₁, hv₂, huv, ?_⟩
  omega

/-- Pure subdivision theory for the degree-two branch of (12).  The two displayed two-edge
routes from `b₁` to `b₂` cannot both have internal degree-two vertices.  Consequently `u` is a
branch vertex; the two degree-three ends then force the original graph to be `K₄`, with
`u = b₃`, and the displayed four-cycle witnesses degeneracy. -/
theorem claim12_degree_two_structure
    {m n : ℕ} (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (H : SimpleGraph (Fin n)) (hsub : IsSubdivision J H)
    {B₃ : List (Fin n)} {b b₁ b₂ b₃ u v : Fin n}
    (hB₃ : IsBranch H B₃) (hfrom₃ : IsTrackFrom H B₃ b b₃)
    (hB₃pos : 1 ≤ trackLength B₃)
    (hbV : b ∈ branchVertices H) (hb₁V : b₁ ∈ branchVertices H)
    (hb₂V : b₂ ∈ branchVertices H) (hb₃V : b₃ ∈ branchVertices H)
    (hbb₁ : b ≠ b₁) (hbb₂ : b ≠ b₂) (hbb₃ : b ≠ b₃)
    (hb₁b₂ : b₁ ≠ b₂) (hb₁b₃ : b₁ ≠ b₃) (hb₂b₃ : b₂ ≠ b₃)
    (hub : u ≠ b) (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂)
    (hv₁ : v ≠ b₁) (hv₂ : v ≠ b₂)
    (huv : u ≠ v)
    (hbb₁A : H.Adj b b₁) (hbb₂A : H.Adj b b₂)
    (hb₁u : H.Adj b₁ u) (hub₂ : H.Adj u b₂)
    (hb₁v : H.Adj b₁ v) (hvb₂ : H.Adj v b₂)
    (hb₁deg : (H.neighborSet b₁).ncard = 3)
    (hb₂deg : (H.neighborSet b₂).ncard = 3)
    (hvdeg : (H.neighborSet v).ncard = 2) :
    u = b₃ ∧ Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ DegenerateAppearance J H := by
  classical
  have hDvfrom : IsTrackFrom H [b₁, v, b₂] b₁ b₂ := by
    refine ⟨⟨by simp, by simp [hv₁.symm, hb₁b₂, hv₂], ?_⟩, rfl, rfl⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with rfl | rfl
    · simpa using hb₁v
    · simpa using hvb₂
  have hDv : IsBranch H [b₁, v, b₂] := by
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch hDvfrom hb₁b₂
    · intro w hw
      have hwv : w = v := by simpa [trackInterior] using hw
      rw [hwv]
      show ¬ 3 ≤ (H.neighborSet v).ncard
      omega
    · exact hb₁V
    · exact hb₂V
  have hDufrom : IsTrackFrom H [b₁, u, b₂] b₁ b₂ := by
    refine ⟨⟨by simp, by simp [hu₁.symm, hb₁b₂, hu₂], ?_⟩, rfl, rfl⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with rfl | rfl
    · simpa using hb₁u
    · simpa using hub₂
  have huV : u ∈ branchVertices H := by
    by_contra huV
    have hDu : IsBranch H [b₁, u, b₂] := by
      apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch hDufrom hb₁b₂
      · intro w hw
        have hwu : w = u := by simpa [trackInterior] using hw
        simpa [hwu] using huV
      · exact hb₁V
      · exact hb₂V
    obtain ⟨ι, T, hι, htrack, hTlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
    have hJdeg : ∀ x : Fin m, 3 ≤ (J.neighborSet x).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
    have heq := Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
      hι htrack hTlen hrev hdisj hnew hcover hedges
      hJdeg hDu (by simp) hDufrom hDv (by simp) hDvfrom hb₁V hb₂V (Or.inl ⟨rfl, rfl⟩)
    have heu : s(b₁, u) ∈ trackEdges [b₁, u, b₂] := ⟨0, by simp, by simp⟩
    have hev : s(b₁, v) ∈ trackEdges [b₁, v, b₂] := ⟨0, by simp, by simp⟩
    have heu' : s(b₁, u) ∈ trackEdges [b₁, v, b₂] := heq ▸ heu
    have hfirstu := trackEdge_at_head hDvfrom (by simp) heu' (by simp)
    have hfirstv := trackEdge_at_head hDvfrom (by simp) hev (by simp)
    have huv' : s(b₁, u) = s(b₁, v) := hfirstu.trans hfirstv.symm
    rcases Sym2.eq_iff.mp huv' with ⟨-, h⟩ | ⟨h, -⟩
    · exact huv h
    · exact hv₁ h.symm
  obtain ⟨ι, T, hι, htrack, hTlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hJdeg : ∀ x : Fin m, 3 ≤ (J.neighborSet x).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hbrange : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisj hcover hedges
  obtain ⟨j₀, hj₀⟩ := hbrange hbV
  obtain ⟨j₁, hj₁⟩ := hbrange hb₁V
  obtain ⟨j₂, hj₂⟩ := hbrange hb₂V
  obtain ⟨j₃, hj₃⟩ := hbrange hb₃V
  obtain ⟨ju, hju⟩ := hbrange huV
  have h0 : b = ι j₀ := hj₀.symm
  have h1 : b₁ = ι j₁ := hj₁.symm
  have h2 : b₂ = ι j₂ := hj₂.symm
  have h3 : b₃ = ι j₃ := hj₃.symm
  have hu : u = ι ju := hju.symm
  have hj01 : j₀ ≠ j₁ := fun h => hbb₁ (by rw [h0, h1, h])
  have hj02 : j₀ ≠ j₂ := fun h => hbb₂ (by rw [h0, h2, h])
  have hj12 : j₁ ≠ j₂ := fun h => hb₁b₂ (by rw [h1, h2, h])
  have hj1u : j₁ ≠ ju := fun h => hu₁ (by rw [h1, hu, h])
  have hj2u : j₂ ≠ ju := fun h => hu₂ (by rw [h2, hu, h])
  have hj0u : j₀ ≠ ju := fun h => hub (by rw [h0, hu, h])
  have hJ12 : J.Adj j₁ j₂ :=
    original_adj_of_branch_ends hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg
      hDv hDvfrom (by simp [trackLength]) h1 h2
  have lift_adj {p q : Fin m} (hpq : H.Adj (ι p) (ι q)) : J.Adj p q :=
    original_adj_of_subdivision_adj hι htrack hnew hedges hpq
  have hJ10 : J.Adj j₁ j₀ := lift_adj (by simpa [← h1, ← h0] using hbb₁A.symm)
  have hJ20 : J.Adj j₂ j₀ := lift_adj (by simpa [← h2, ← h0] using hbb₂A.symm)
  have hJ1u : J.Adj j₁ ju := lift_adj (by simpa [← h1, ← hu] using hb₁u)
  have hJ2u : J.Adj j₂ ju := lift_adj (by simpa [← h2, ← hu] using hub₂.symm)
  have hJdeg1 : (J.neighborSet j₁).ncard = 3 := by
    apply le_antisymm
    · calc
        (J.neighborSet j₁).ncard ≤ (H.neighborSet (ι j₁)).ncard :=
          original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew j₁
        _ = 3 := by rw [← h1, hb₁deg]
    · exact hJdeg j₁
  have hJdeg2 : (J.neighborSet j₂).ncard = 3 := by
    apply le_antisymm
    · calc
        (J.neighborSet j₂).ncard ≤ (H.neighborSet (ι j₂)).ncard :=
          original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew j₂
        _ = 3 := by rw [← h2, hb₂deg]
    · exact hJdeg j₂
  have hall : ∀ x : Fin m, x = j₁ ∨ x = j₂ ∨ x = j₀ ∨ x = ju :=
    four_vertices_of_two_degree_three hJ hJ12 hJ10 hJ1u hJ20 hJ2u hj0u
      hJdeg1 hJdeg2
  have hj3u : j₃ = ju := by
    rcases hall j₃ with h | h | h | h
    · exact False.elim (hb₁b₃ (by rw [h1, h3, h]))
    · exact False.elim (hb₂b₃ (by rw [h2, h3, h]))
    · exact False.elim (hbb₃ (by rw [h0, h3, h]))
    · exact h
  have hub₃ : u = b₃ := by rw [hu, h3, hj3u]
  have hJ0u : J.Adj j₀ ju := by
    by_contra hnot
    have hsubN : J.neighborSet j₀ ⊆ ({j₁, j₂} : Set (Fin m)) := by
      intro x hx
      rcases hall x with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (J.loopless.irrefl _ hx)
      · exact False.elim (hnot hx)
    have hle := Set.ncard_le_ncard hsubN (Set.toFinite _)
    rw [Set.ncard_pair hj12] at hle
    have := hJdeg j₀
    omega
  have hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) :=
    iso_top_of_four_vertices hj12 hJ10.ne hJ1u.ne hJ20.ne hJ2u.ne hj0u
      hall hJ12 hJ10 hJ1u hJ20 hJ2u hJ0u
  have hbvsub : branchVertices H ⊆ ({b, b₁, u, b₂} : Set (Fin n)) := by
    intro x hx
    obtain ⟨j, hj⟩ := hbrange hx
    rcases hall j with rfl | rfl | rfl | rfl
    · simp [hj, h1]
    · simp [hj, h2]
    · simp [hj, h0]
    · simp [hj, hu]
  have hnd : [b, b₁, u, b₂].Nodup := by
    simp [hbb₁, hub.symm, hu₁.symm, hbb₂, hu₂, hb₁b₂]
  have hdegapp : DegenerateAppearance J H := by
    left
    refine ⟨hJiso, b, b₁, u, b₂, hnd, hbb₁A, hb₁u, hub₂, hbb₂A.symm, hbvsub⟩
  exact ⟨hub₃, hJiso, hdegapp⟩

/-- In the first terminal case of (12), where the common end `v` is `b₃`, the third incident
edge at `b₃` is the last edge of `B₃`.  Since it must meet the first edge, `B₃` has exactly two
edges; both are complete. -/
theorem claim12_v_eq_b3_short_complete
    {n : ℕ} (H : SimpleGraph (Fin n))
    (hbip : H.IsBipartite) {X : Set (Sym2 (Fin n))}
    {B : List (Fin n)} {b b₁ b₂ b₃ : Fin n} {e₃ d₁ d₂ : Sym2 (Fin n)}
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B b b₃)
    (hpos : 1 ≤ trackLength B)
    (hb₁V : b₁ ∈ branchVertices H) (hb₂V : b₂ ∈ branchVertices H)
    (hbb₁ : b ≠ b₁) (hbb₂ : b ≠ b₂) (hbb₃ : b ≠ b₃)
    (hb₁b₃ : b₁ ≠ b₃) (hb₂b₃ : b₂ ≠ b₃)
    (he₃B : e₃ ∈ trackEdges B) (he₃b : b ∈ e₃) (he₃X : e₃ ∈ X)
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁eq : d₁ = s(b₁, b₃))
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂eq : d₂ = s(b₂, b₃))
    (hbb₂A : H.Adj b b₂) (hd₁d₂ : d₁ ≠ d₂)
    (hdeg : (H.neighborSet b₃).ncard = 2 ∨ (H.neighborSet b₃).ncard = 3)
    (hother : ∀ g ∈ incidentEdges H b₃, g ≠ d₁ → g ≠ d₂ → g ∈ X ∧ MeetEdges g e₃) :
    trackLength B = 2 ∧ trackEdges B ⊆ X ∧ (H.neighborSet b₃).ncard = 3 := by
  classical
  have hB2 : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
  let g : Sym2 (Fin n) := s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega))
  have hgB : g ∈ trackEdges B := by
    refine ⟨B.length - 2, by omega, ?_⟩
    dsimp [g]
    congr 2 <;> omega
  have hgE : g ∈ H.edgeSet := by
    apply H.mem_edgeSet.mpr
    change H.Adj B[B.length - 2] B[B.length - 1]
    have hi : B.length - 2 + 1 = B.length - 1 := by omega
    simpa only [hi] using hfrom.1.2.2 (B.length - 2) (by omega)
  have hlast : B[B.length - 1]'(by omega) = b₃ := last_getElem hfrom.2.2 (by omega)
  have hb₃g : b₃ ∈ g := by dsimp [g]; rw [← hlast]; simp
  have hginc : g ∈ incidentEdges H b₃ := ⟨hgE, hb₃g⟩
  have hgd₁ : g ≠ d₁ := by
    intro h
    have hb₁g : b₁ ∈ g := h ▸ hd₁.2
    exact branch_edge_avoids_other_branchVertex hB hfrom hgB hb₁V
      hbb₁.symm hb₁b₃ hb₁g
  have hgd₂ : g ≠ d₂ := by
    intro h
    have hb₂g : b₂ ∈ g := h ▸ hd₂.2
    exact branch_edge_avoids_other_branchVertex hB hfrom hgB hb₂V
      hbb₂.symm hb₂b₃ hb₂g
  obtain ⟨hgX, hmeet⟩ := hother g hginc hgd₁ hgd₂
  have hmeet' : MeetEdges e₃ g := by
    simpa only [MeetEdges, DisjointEdges, and_comm] using hmeet
  have hle2 := trackLength_le_two_of_end_edges_meet hfrom hpos he₃B he₃b hgB hb₃g hmeet'
  have hne1 : trackLength B ≠ 1 := by
    intro hone
    have hBE := trackEdges_eq_singleton_of_length_one hfrom hone
    have heq : e₃ = s(b, b₃) := by
      rw [hBE] at he₃B
      exact Set.mem_singleton_iff.mp he₃B
    have hbb₃A : H.Adj b b₃ := by
      apply H.mem_edgeSet.mp
      rw [← heq]
      obtain ⟨i, hi, hie⟩ := he₃B
      rw [hie]
      exact hfrom.1.2.2 i hi
    have hb₂b₃A : H.Adj b₂ b₃ := by
      apply H.mem_edgeSet.mp
      rw [← hd₂eq]
      exact hd₂.1
    exact no_triangle_of_bipartite hbip hbb₂A hb₂b₃A hbb₃A
  have hlen : trackLength B = 2 := by omega
  have hBlen : B.length = 3 := by simp only [trackLength] at hlen; omega
  have hsubX : trackEdges B ⊆ X := by
    intro e he
    obtain ⟨i, hi, hie⟩ := he
    have heB : e ∈ trackEdges B := ⟨i, hi, hie⟩
    have hi' : i = 0 ∨ i = 1 := by rw [hBlen] at hi; omega
    rcases hi' with rfl | rfl
    · have hbe : b ∈ e := by
        rw [hie]
        have h0 : B[0]'(by omega) = b := head_getElem hfrom.2.1 (by omega)
        rw [h0]
        simp
      have heq := trackEdge_at_head hfrom hB2 heB hbe
      have heq₃ := trackEdge_at_head hfrom hB2 he₃B he₃b
      exact (heq.trans heq₃.symm) ▸ he₃X
    · have hb₃e : b₃ ∈ e := by
        rw [hie]
        have h2 : B[2]'(by omega) = b₃ := by
          have := last_getElem hfrom.2.2 (by omega)
          simpa [hBlen] using this
        rw [h2]
        simp
      have heq := trackEdge_at_last hfrom hB2 heB hb₃e
      have heqg := trackEdge_at_last hfrom hB2 hgB hb₃g
      exact (heq.trans heqg.symm) ▸ hgX
  have hdeg3 : (H.neighborSet b₃).ncard = 3 := by
    rcases hdeg with hdeg2 | hdeg3
    · have : 3 ≤ (H.neighborSet b₃).ncard := by
        have hpair : ({d₁, d₂, g} : Set (Sym2 (Fin n))) ⊆ incidentEdges H b₃ := by
          intro e he
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
          rcases he with rfl | rfl | rfl
          · refine ⟨hd₁.1, ?_⟩
            rw [hd₁eq]
            simp
          · refine ⟨hd₂.1, ?_⟩
            rw [hd₂eq]
            simp
          · exact hginc
        have hc : ({d₁, d₂, g} : Set (Sym2 (Fin n))).ncard = 3 :=
          Set.ncard_eq_three.mpr ⟨d₁, d₂, g, hd₁d₂, hgd₁.symm, hgd₂.symm, rfl⟩
        have hle := Set.ncard_le_ncard hpair (Set.toFinite _)
        rw [hc, incidentEdges_ncard] at hle
        exact hle
      omega
    · exact hdeg3
  exact ⟨hlen, hsubX, hdeg3⟩

/-- The degree-two terminal branch of printed claim (12), including the complement
overshadowed-appearance construction. -/
theorem claim12_degree_two_conclusion
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
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
    (f₁ f₂ d₁ d₂ : Sym2 (Fin n)) (u v : Fin n)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂))
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁X : d₁ ∈ extraEdges G H K φ Y y₂)
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂X : d₂ ∈ extraEdges G H K φ Y y₁)
    (hf₁eq : f₁ = s(b₁, u)) (hf₂eq : f₂ = s(b₂, u))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂) (hv₁ : v ≠ b₁) (hv₂ : v ≠ b₂)
    (huv : u ≠ v) (hvdeg : (H.neighborSet v).ncard = 2) :
    Thm61Concl G m J n H K φ Y := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁, he₁X, he₂, he₂X, he₃, he₃ne₁, he₃ne₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁, he₁X, he₂, he₂X, he₃, he₃ne₁, he₃ne₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
      hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
  obtain ⟨htri₁, htri₂, hB₁one, hB₂one⟩ :=
    claim12_triads_and_short G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' f₁ f₂
      hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
  obtain ⟨hb₁deg, -, -, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₁ htri₁
  obtain ⟨hb₂deg, -, -, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htri₂
  have he₁eq : e₁ = s(b, b₁) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁one] at he₁B₁
    exact Set.mem_singleton_iff.mp he₁B₁
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hB₂one] at he₂B₂
    exact Set.mem_singleton_iff.mp he₂B₂
  obtain ⟨hXE, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁ he₁X he₂ he₂X he₃
      he₃ne₁ he₃ne₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hf₁dis : DisjointEdges f₁ e₃ := by
    unfold MeetEdges at hf₁e
    exact Classical.byContradiction hf₁e
  have hf₂dis : DisjointEdges f₂ e₃ := by
    unfold MeetEdges at hf₂e
    exact Classical.byContradiction hf₂e
  have hub : u ≠ b := by
    intro hub
    have heq : f₁ = e₁ := by rw [hf₁eq, hub, he₁eq, Sym2.eq_swap]
    exact (Set.disjoint_left.mp hXX₁ hf₁X) (heq ▸ he₁X)
  have hvb : v ≠ b := by
    intro hvb
    have heq : d₁ = e₁ := by rw [hd₁eq, hvb, he₁eq, Sym2.eq_swap]
    exact (Set.disjoint_left.mp hX₁X₂ he₁X) (by rw [← heq]; exact hd₁X)
  have hbb₁A : H.Adj b b₁ := by
    apply H.mem_edgeSet.mp
    rw [← he₁eq]
    exact he₁.1
  have hbb₂A : H.Adj b b₂ := by
    apply H.mem_edgeSet.mp
    rw [← he₂eq]
    exact he₂.1
  have hb₁uA : H.Adj b₁ u := by
    apply H.mem_edgeSet.mp
    rw [← hf₁eq]
    exact hXE hf₁X
  have hub₂A : H.Adj u b₂ := by
    apply H.mem_edgeSet.mp
    rw [Sym2.eq_swap, ← hf₂eq]
    exact hXE hf₂X
  have hb₁vA : H.Adj b₁ v := by
    apply H.mem_edgeSet.mp
    rw [← hd₁eq]
    exact hd₁.1
  have hvb₂A : H.Adj v b₂ := by
    apply H.mem_edgeSet.mp
    rw [Sym2.eq_swap, ← hd₂eq]
    exact hd₂.1
  obtain ⟨hub₃, hJiso, hdegapp⟩ := claim12_degree_two_structure J hJ H hsub.1
    hB₃ hfrom₃ hB₃pos hbV hb₁V hb₂V hb₃V hbb₁ hbb₂ hbb₃ hb₁b₂
    hb₁b₃ hb₂b₃ hub hu₁ hu₂ hv₁ hv₂ huv hbb₁A hbb₂A hb₁uA hub₂A
    hb₁vA hvb₂A hb₁deg hb₂deg hvdeg
  subst u
  have hsymm : ∀ {a c : Sym2 (Fin n)}, DisjointEdges a c → DisjointEdges c a := by
    intro a c h x hx
    exact h x ⟨hx.2, hx.1⟩
  have hb₁e₃ : b₁ ∉ e₃ := by
    intro h
    exact hf₁dis b₁ ⟨hf₁b, h⟩
  have hb₂e₃ : b₂ ∉ e₃ := by
    intro h
    exact hf₂dis b₂ ⟨hf₂b, h⟩
  have hb₃e₃ : b₃ ∉ e₃ := by
    intro h
    exact hf₁dis b₃ ⟨by rw [hf₁eq]; simp, h⟩
  have hd₁d₂ : d₁ ≠ d₂ := by
    intro h
    exact (Set.disjoint_right.mp hX₁X₂ hd₁X) (h ▸ hd₂X)
  have he₃d₁ne : e₃ ≠ d₁ := by
    intro h
    exact hb₁e₃ (h ▸ hd₁.2)
  have he₃d₂ne : e₃ ≠ d₂ := by
    intro h
    exact hb₂e₃ (h ▸ hd₂.2)
  have hve₃ : v ∉ e₃ := by
    intro hve₃
    have hd₁v : d₁ ∈ incidentEdges H v := ⟨hd₁.1, by rw [hd₁eq]; simp⟩
    have hd₂v : d₂ ∈ incidentEdges H v := ⟨hd₂.1, by rw [hd₂eq]; simp⟩
    have he₃v : e₃ ∈ incidentEdges H v := ⟨he₃.1, hve₃⟩
    have hsubinc : ({d₁, d₂, e₃} : Set (Sym2 (Fin n))) ⊆ incidentEdges H v := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;> assumption
    have hc : ({d₁, d₂, e₃} : Set (Sym2 (Fin n))).ncard = 3 :=
      Set.ncard_eq_three.mpr
        ⟨d₁, d₂, e₃, hd₁d₂, he₃d₁ne.symm, he₃d₂ne.symm, rfl⟩
    have hle := Set.ncard_le_ncard hsubinc (Set.toFinite _)
    rw [hc, incidentEdges_ncard, hvdeg] at hle
    omega
  have disjoint_pair {a c : Fin n} {e : Sym2 (Fin n)} (ha : a ∉ e) (hc : c ∉ e) :
      DisjointEdges e s(a, c) := by
    intro x hx
    rcases Sym2.mem_iff.mp hx.2 with h | h
    · exact ha (h ▸ hx.1)
    · exact hc (h ▸ hx.1)
  have he₃d₂ : DisjointEdges e₃ d₂ := by rw [hd₂eq]; exact disjoint_pair hb₂e₃ hve₃
  have he₃f₂ : DisjointEdges e₃ f₂ := hsymm hf₂dis
  have he₃f₁ : DisjointEdges e₃ f₁ := hsymm hf₁dis
  have he₃d₁ : DisjointEdges e₃ d₁ := by rw [hd₁eq]; exact disjoint_pair hb₁e₃ hve₃
  have he₃m₁ : MeetEdges e₃ e₁ := by
    unfold MeetEdges DisjointEdges
    push Not
    exact ⟨b, he₃.2, he₁.2⟩
  have he₃m₂ : MeetEdges e₃ e₂ := by
    unfold MeetEdges DisjointEdges
    push Not
    exact ⟨b, he₃.2, he₂.2⟩
  have hB₃two : 2 ≤ trackLength B₃ := by
    by_contra hlt
    have hone : trackLength B₃ = 1 := by omega
    have hset := trackEdges_eq_singleton_of_length_one hfrom₃ hone
    have heq : e₃ = s(b, b₃) := by
      rw [hset] at he₃B₃
      exact Set.mem_singleton_iff.mp he₃B₃
    have hbb₃A : H.Adj b b₃ := by
      apply H.mem_edgeSet.mp
      rw [← heq]
      exact he₃.1
    exact no_triangle_of_bipartite hsub.2 hbb₁A hb₁uA hbb₃A
  have hB₃len : 3 ≤ B₃.length := by simp only [trackLength] at hB₃two; omega
  let g : Sym2 (Fin n) := s(B₃[B₃.length - 2]'(by omega), B₃[B₃.length - 1]'(by omega))
  have hgB : g ∈ trackEdges B₃ := by
    refine ⟨B₃.length - 2, by omega, ?_⟩
    dsimp [g]
    congr 2 <;> omega
  have hgE : g ∈ H.edgeSet := by
    apply H.mem_edgeSet.mpr
    change H.Adj B₃[B₃.length - 2] B₃[B₃.length - 1]
    have hi : B₃.length - 2 + 1 = B₃.length - 1 := by omega
    simpa only [hi] using hfrom₃.1.2.2 (B₃.length - 2) (by omega)
  have hbg : b ∉ g := by
    intro hbg
    have hhead : B₃[0]'(by omega) = b := head_getElem hfrom₃.2.1 (by omega)
    rcases Sym2.mem_iff.mp hbg with h | h
    · rw [← hhead] at h
      have hi := hB₃.1.2.1.getElem_inj_iff.mp h
      omega
    · rw [← hhead] at h
      have hi := hB₃.1.2.1.getElem_inj_iff.mp h
      omega
  have hb₁g : b₁ ∉ g :=
    branch_edge_avoids_other_branchVertex hB₃ hfrom₃ hgB hb₁V hbb₁.symm hb₁b₃
  have hb₂g : b₂ ∉ g :=
    branch_edge_avoids_other_branchVertex hB₃ hfrom₃ hgB hb₂V hbb₂.symm hb₂b₃
  have hgd₁ : g ≠ d₁ := by
    intro h
    exact hb₁g (h ▸ hd₁.2)
  have hgd₂ : g ≠ d₂ := by
    intro h
    exact hb₂g (h ▸ hd₂.2)
  have hvg : v ∉ g := by
    intro hvg
    have hd₁v : d₁ ∈ incidentEdges H v := ⟨hd₁.1, by rw [hd₁eq]; simp⟩
    have hd₂v : d₂ ∈ incidentEdges H v := ⟨hd₂.1, by rw [hd₂eq]; simp⟩
    have hgv : g ∈ incidentEdges H v := ⟨hgE, hvg⟩
    have hsubinc : ({d₁, d₂, g} : Set (Sym2 (Fin n))) ⊆ incidentEdges H v := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;> assumption
    have hc : ({d₁, d₂, g} : Set (Sym2 (Fin n))).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨d₁, d₂, g, hd₁d₂, hgd₁.symm, hgd₂.symm, rfl⟩
    have hle := Set.ncard_le_ncard hsubinc (Set.toFinite _)
    rw [hc, incidentEdges_ncard, hvdeg] at hle
    omega
  have hgd₂dis : DisjointEdges g d₂ := by rw [hd₂eq]; exact disjoint_pair hb₂g hvg
  have hge₁ : DisjointEdges g e₁ := by rw [he₁eq]; exact disjoint_pair hbg hb₁g
  have hge₂ : DisjointEdges g e₂ := by rw [he₂eq]; exact disjoint_pair hbg hb₂g
  have hgd₁dis : DisjointEdges g d₁ := by rw [hd₁eq]; exact disjoint_pair hb₁g hvg
  have hnd : [b, b₁, b₂, b₃, v].Nodup := by
    simp [hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃,
      hvb.symm, hv₁.symm, hv₂.symm, huv]
  have hYout : ∀ x ∈ Y, x ∉ K := fun x hx => (hYmajor x hx).1
  have happ :=
    Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance.shortK4ComplementAppearanceOfEdges
      G m J hJiso n H K φ Y Q y₁ y₂ hQ hQY hy hQeven hYout
      b b₁ b₂ b₃ v e₁ e₂ e₃ f₁ f₂ d₁ d₂ g hnd
      he₁.1 he₂.1 he₃.1 (hXE hf₁X) (hXE hf₂X) hd₁.1 hd₂.1 hgE
      he₁eq he₂eq hf₁eq hf₂eq hd₁eq hd₂eq
      he₃d₂ he₃f₂ he₃f₁ he₃d₁ he₃m₁ he₃m₂ he₃ne₁ he₃ne₂
      hd₂X he₁X hf₂X hf₁X he₂X hd₁X he₃X
      hgd₂dis hge₁ hge₂ hgd₁dis
  exact Or.inr (Or.inl ⟨Or.inr hJiso, hdegapp, happ⟩)

end Workspace.ProofLemmas.Thm61EvenEndgameClaim12
