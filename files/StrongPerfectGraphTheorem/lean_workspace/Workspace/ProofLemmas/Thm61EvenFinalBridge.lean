import Workspace.ProofLemmas.Thm61EvenFinalTracks

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenFinalBridge

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.Thm61EvenFinalTracks

/-- The application of (10) in the bridging paragraph: a complete edge at `b₂`,
other than `b₁b₂` and missing `e₃`, forces `B₁` to have no complete edge. -/
theorem no_complete_left
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
    (f₂ : Sym2 (Fin n))
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    Disjoint (trackEdges B₁) (completeEdges G H K φ Y) := by
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
  have hf₂E : f₂ ∈ H.edgeSet := hXE hf₂X
  have hf₂dis : DisjointEdges f₂ e₃ := by
    unfold MeetEdges at hf₂e
    exact Classical.byContradiction hf₂e
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
  exact hnoB₁

/-- Printed bridging paragraph: "So there is no such edge `f`, and therefore `b₂` is a triad."
The supposed second complete edge first excludes complete edges on `B₁` by (10), then
contradicts (9) on `T`. -/
theorem b2_triad
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
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (heven : Even (trackLength B₁)) : Triad G H K φ Y b₂ := by
  classical
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  have hbcCopy := hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨hXE, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hb₂not_e₃ : b₂ ∉ e₃ :=
    branch_edge_avoids_other_branchVertex hB₃ hfrom₃ he₃B₃ hb₂V hbb₂.symm hb₂b₃
  obtain ⟨z₃, hP₃, he₃eq⟩ := edge_track_from_incident he₃inc
  have h03 : H.Adj b z₃ := hP₃.1.2.2 0 (by simp)
  have hz₃B₃ : z₃ ∈ B₃ := by
    exact (BranchClassification.mem_of_mem_trackEdges
      (show s(b, z₃) ∈ trackEdges B₃ by simpa [he₃eq] using he₃B₃)).2
  have hB₁B₃ := branches_from_common_end_meet_only hJ hsub.1 hB₁ hfrom₁ hB₃ hfrom₃
    hB₁pos hB₃pos hbV hb₁V hb₃V hbb₁ hbb₃ hb₁b₃
  have hz₃B₁ : z₃ ∉ B₁ := fun hz => h03.ne (hB₁B₃ z₃ hz hz₃B₃).symm
  have hb₂B₁ : b₂ ∉ B₁ := by
    intro hb₂B₁
    have hn : b₂ ∉ trackInterior B₁ := fun hi => hB₁.2.1 b₂ hi hb₂V
    rcases SubdivisionCompose.mem_ends_of_mem hfrom₁.2.1 hfrom₁.2.2 hb₂B₁ hn with h | h
    · exact hbb₂ h.symm
    · exact hb₁b₂ h.symm
  have hz₃b₂ : z₃ ≠ b₂ := by
    intro h
    exact hb₂not_e₃ (by rw [he₃eq, h]; simp)
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
  have hcol01 := (BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mp heven
  have hcol02 : col b ≠ col b₂ := hcol01.symm ▸ col.valid hadj
  have hbf : ∀ f ∈ incidentEdges H b₂, f ∈ completeEdges G H K φ Y → b ∉ f := by
    intro f hf hfX hbf
    have hfeq := eq_sym2_of_mem_mem hbb₂ hbf hf.2
    have h02 : H.Adj b b₂ := H.mem_edgeSet.mp (hfeq ▸ hf.1)
    have hshort := branch_length_one_of_adj J hJ H hsub.1 hB₂ hfrom₂ hB₂pos h02
    have he₂eq : e₂ = s(b, b₂) := by
      have he := he₂B₂
      rw [trackEdges_eq_singleton_of_length_one hfrom₂ hshort] at he
      exact he
    exact he₂X₂.2 ((hfeq.trans he₂eq.symm) ▸ hfX)
  have unique : ∀ f ∈ incidentEdges H b₂, f ∈ completeEdges G H K φ Y → f = s(b₁, b₂) := by
    intro f hf hfX
    by_contra hne
    have hfm : ¬ MeetEdges f e₃ := by
      intro hm
      obtain ⟨w, hwf, hwe⟩ := exists_common_end hm
      rw [he₃eq] at hwe
      rcases Sym2.mem_iff.mp hwe with hwb | hwz
      · exact hbf f hf hfX (hwb ▸ hwf)
      · have hz₃f : z₃ ∈ f := hwz ▸ hwf
        have hfeq : f = s(b₂, z₃) := eq_sym2_of_mem_mem hz₃b₂.symm hf.2 hz₃f
        have h23 : H.Adj b₂ z₃ := H.mem_edgeSet.mp (hfeq ▸ hf.1)
        exact hcol02 (bool_eq_of_ne_ne (col z₃) (col b) (col b₂)
          (col.valid h03).symm (col.valid h23).symm)
    have hno := no_complete_left G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbcCopy f hfX hf.2 hfm hne
    have hfirst : s(z₃, b) ∈ completeEdges G H K φ Y := by
      rw [Sym2.eq_swap, ← he₃eq]
      exact he₃X
    rcases complete_edge_hits_ends h9 hfrom₁ hB₁pos heven h03.symm hadj
      hz₃B₁ hb₂B₁ hz₃b₂ hfirst hXb hno f hfX with hb | hb₁
    · exact hbf f hf hfX hb
    · exact hne (eq_sym2_of_mem_mem hb₁b₂ hb₁ hf.2)
  refine ⟨hb₂V, ?_⟩
  intro f hf g hg
  exact (unique f hf.1 hf.2).trans (unique g hg.1 hg.2).symm

/-- The next bridging sentence: "Since it is not incident with `e₁`, it follows that
`E(B₂) = {e₂}`." Apply (8) to the `X₂` edge at the triad `b₂`; bipartiteness forces
its common end with `e₁` to be `b`. -/
theorem b2_short
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
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (hadj : H.Adj b₁ b₂) (heven : Even (trackLength B₁))
    (htriad : Triad G H K φ Y b₂) : trackLength B₂ = 1 ∧ e₂ = s(b, b₂) := by
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨-, -, -, d, hd, -⟩ := triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htriad
  obtain ⟨w, hwe, hwd⟩ := exists_common_end (h8 e₁ d he₁X₁ hd.2)
  have hb₂not_e₁ : b₂ ∉ e₁ :=
    branch_edge_avoids_other_branchVertex hB₁ hfrom₁ he₁B₁ hb₂V hbb₂.symm hb₁b₂.symm
  have hwb₂ : w ≠ b₂ := fun h => hb₂not_e₁ (h ▸ hwe)
  have hwb : w = b := by
    by_contra hne
    have heq : e₁ = s(b, w) := eq_sym2_of_mem_mem (Ne.symm hne) he₁inc.2 hwe
    have hdq : d = s(b₂, w) := eq_sym2_of_mem_mem hwb₂.symm hd.1.2 hwd
    have hbw : H.Adj b w := H.mem_edgeSet.mp (heq ▸ he₁inc.1)
    have h2w : H.Adj b₂ w := H.mem_edgeSet.mp (hdq ▸ hd.1.1)
    obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
    have h01 := (BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mp heven
    have h02 : col b ≠ col b₂ := h01.symm ▸ col.valid hadj
    exact h02 (bool_eq_of_ne_ne (col w) (col b) (col b₂)
      (col.valid hbw).symm (col.valid h2w).symm)
  have hdq : d = s(b, b₂) := eq_sym2_of_mem_mem hbb₂ (hwb ▸ hwd) hd.1.2
  have h02 : H.Adj b b₂ := H.mem_edgeSet.mp (hdq ▸ hd.1.1)
  have hshort := branch_length_one_of_adj J hJ H hsub.1 hB₂ hfrom₂ hB₂pos h02
  refine ⟨hshort, ?_⟩
  rw [trackEdges_eq_singleton_of_length_one hfrom₂ hshort] at he₂B₂
  exact he₂B₂

/-- The opening of (13): "no edge in `X₂` is incident with `b₄`. Consequently `b₄`
is not a triad." The same argument works at any branch-vertex outside `b,b₁,b₂`. -/
theorem not_triad_away
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
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (heven : Even (trackLength B₁)) (he₂eq : e₂ = s(b, b₂))
    (c : Fin n) (hcV : c ∈ branchVertices H)
    (hcb : c ≠ b) (hcb₁ : c ≠ b₁) (hcb₂ : c ≠ b₂) : ¬ Triad G H K φ Y c := by
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hb₁not_e₁ : b₁ ∉ e₁ := by
    intro hm
    have heq := eq_sym2_of_mem_mem hbb₁ he₁inc.2 hm
    have h01 : H.Adj b b₁ := H.mem_edgeSet.mp (heq ▸ he₁inc.1)
    have hshort := branch_length_one_of_adj J hJ H hsub.1 hB₁ hfrom₁ hB₁pos h01
    rw [hshort] at heven
    simp at heven
  intro htriad
  obtain ⟨-, -, -, d, hd, -⟩ := triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy c htriad
  obtain ⟨w, hwe, hwd⟩ := exists_common_end (h8 e₁ d he₁X₁ hd.2)
  have hdout : d ∉ trackEdges B₁ := by
    intro hm
    exact branch_edge_avoids_other_branchVertex hB₁ hfrom₁ hm hcV hcb hcb₁ hd.1.2
  have hw : w = b := by
    rcases external_edge_meets_branch_only_at_ends hB₁ hfrom₁ he₁B₁ hd.1.1 hdout hwd hwe
      with hw | hw
    · exact hw
    · exact False.elim (hb₁not_e₁ (hw ▸ hwe))
  have hextraout : ∀ f ∈ extraEdges G H K φ Y y₂,
      f ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    intro f hf h
    rcases h with h | h
    · exact hf.2 h
    · exact Set.disjoint_left.mp hX₁X₂ h hf
  have hde₂ : d = e₂ := hsat₁ b hbV
    ⟨⟨hd.1.1, hw ▸ hwd⟩, hextraout d hd.2⟩ ⟨he₂inc, hextraout e₂ he₂X₂⟩
  have hce₂ : c ∈ s(b, b₂) := (hde₂.trans he₂eq) ▸ hd.1.2
  rcases Sym2.mem_iff.mp hce₂ with h | h
  · exact hcb h
  · exact hcb₂ h

/-- The edge form of the first assertion of (13): no `X₂` edge is incident with this branch-vertex. -/
theorem no_extra2_away
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
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (heven : Even (trackLength B₁)) (he₂eq : e₂ = s(b, b₂))
    (c : Fin n) (hcV : c ∈ branchVertices H)
    (hcb : c ≠ b) (hcb₁ : c ≠ b₁) (hcb₂ : c ≠ b₂) : ∀ d ∈ incidentEdges H c, d ∉ extraEdges G H K φ Y y₂ := by
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hb₁not_e₁ : b₁ ∉ e₁ := by
    intro hm
    have heq := eq_sym2_of_mem_mem hbb₁ he₁inc.2 hm
    have h01 : H.Adj b b₁ := H.mem_edgeSet.mp (heq ▸ he₁inc.1)
    have hshort := branch_length_one_of_adj J hJ H hsub.1 hB₁ hfrom₁ hB₁pos h01
    rw [hshort] at heven
    simp at heven
  intro d hdInc hdExtra
  have hd := And.intro hdInc hdExtra
  obtain ⟨w, hwe, hwd⟩ := exists_common_end (h8 e₁ d he₁X₁ hd.2)
  have hdout : d ∉ trackEdges B₁ := by
    intro hm
    exact branch_edge_avoids_other_branchVertex hB₁ hfrom₁ hm hcV hcb hcb₁ hd.1.2
  have hw : w = b := by
    rcases external_edge_meets_branch_only_at_ends hB₁ hfrom₁ he₁B₁ hd.1.1 hdout hwd hwe
      with hw | hw
    · exact hw
    · exact False.elim (hb₁not_e₁ (hw ▸ hwe))
  have hextraout : ∀ f ∈ extraEdges G H K φ Y y₂,
      f ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    intro f hf h
    rcases h with h | h
    · exact hf.2 h
    · exact Set.disjoint_left.mp hX₁X₂ h hf
  have hde₂ : d = e₂ := hsat₁ b hbV
    ⟨⟨hd.1.1, hw ▸ hwd⟩, hextraout d hd.2⟩ ⟨he₂inc, hextraout e₂ he₂X₂⟩
  have hce₂ : c ∈ s(b, b₂) := (hde₂.trans he₂eq) ▸ hd.1.2
  rcases Sym2.mem_iff.mp hce₂ with h | h
  · exact hcb h
  · exact hcb₂ h

end Workspace.ProofLemmas.Thm61EvenFinalBridge
