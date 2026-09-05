import Mathlib
import Workspace.ProofLemmas.Thm61Claim5
import Workspace.ProofLemmas.Thm61Claim5Helpers

/-!
# Repeated local moves for 6.1(6)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim6Helpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim5Helpers
open Workspace.ProofLemmas.Thm61Claim1Helpers

/-- If an edge chosen outside a branch when possible actually lies in the branch, it is the
only complete edge at that branch end.  Thus the end is a triad. -/
theorem chosen_in_branch_is_triad
    {V : Type*} {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V}
    {B : List (Fin n)} {b c : Fin n} {f : Sym2 (Fin n)}
    (hcV : c ∈ branchVertices H) (hfrom : IsTrackFrom H B b c)
    (hpos : 1 ≤ trackLength B)
    (hf : ChosenOutside G H K φ Y B c f) (hfB : f ∈ trackEdges B) :
    Triad G H K φ Y c := by
  refine ⟨hcV, ?_⟩
  intro g hg k hk
  have all_in : ∀ x : Sym2 (Fin n),
      x ∈ incidentEdges H c → x ∈ completeEdges G H K φ Y → x ∈ trackEdges B := by
    intro x hxinc hxX
    by_contra hxout
    exact hf.2.2 ⟨x, hxX, hxinc, hxout⟩ hfB
  have hgB := all_in g hg.1 hg.2
  have hkB := all_in k hk.1 hk.2
  have hlist : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
  exact (trackEdge_at_last hfrom hlist hgB hg.1.2).trans
    (trackEdge_at_last hfrom hlist hkB hk.1.2).symm

/-- Reverse a long branch at its triad end and invoke claim (5).  This is the paper's
“the theorem holds by (5) with the two ends exchanged” move. -/
theorem conclusion_of_chosen_in_long_branch
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
    (B : List (Fin n)) (b c : Fin n) (f : Sym2 (Fin n))
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B b c)
    (hlong : 1 < trackLength B)
    (hcV : c ∈ branchVertices H)
    (hf : ChosenOutside G H K φ Y B c f) (hfB : f ∈ trackEdges B) :
    Thm61Concl G m J n H K φ Y := by
  classical
  have hpos : 1 ≤ trackLength B := by omega
  have hctri := chosen_in_branch_is_triad hcV hfrom hpos hf hfB
  obtain ⟨-, ⟨x, hx, -⟩, ⟨a₁, ha₁, -⟩, ⟨a₂, ha₂, -⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy c hctri
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ ha₁.2) (h ▸ ha₂.2)
  have ha₁X : a₁ ∉ completeEdges G H K φ Y :=
    Set.disjoint_right.mp hXX₁ ha₁.2
  have ha₂X : a₂ ∉ completeEdges G H K φ Y :=
    Set.disjoint_right.mp hXX₂ ha₂.2
  obtain ⟨C₁, c₁, hC₁, ha₁C₁, hfromC₁⟩ :=
    branch_from_incident J hJ H hsub.1 c hcV a₁ ha₁.1
  obtain ⟨C₂, c₂, hC₂, ha₂C₂, hfromC₂⟩ :=
    branch_from_incident J hJ H hsub.1 c hcV a₂ ha₂.1
  have hfa₁ : f ≠ a₁ := by intro h; exact ha₁X (h ▸ hf.1)
  have hfa₂ : f ≠ a₂ := by intro h; exact ha₂X (h ▸ hf.1)
  have hfrev : f ∈ trackEdges B.reverse := by
    simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using hfB
  have hBrev : IsBranch H B.reverse := isBranch_reverse hB
  have hfromrev : IsTrackFrom H B.reverse c b :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom
  have hfinc : f ∈ incidentEdges H c := hf.2.1
  have hchoice : BranchChoice G H K φ Y y₁ y₂
      c a₁ a₂ f C₁ C₂ B.reverse c₁ c₂ b :=
    ⟨hcV, ⟨a₁, ha₁.1, a₂, ha₂.1, ha₁a₂, ha₁X, ha₂X⟩,
      ha₁.1, ha₁.2, ha₂.1, ha₂.2, hfinc, hfa₁, hfa₂,
      hC₁, ha₁C₁, hfromC₁, hC₂, ha₂C₂, hfromC₂,
      hBrev, hfrev, hfromrev⟩
  obtain ⟨g₁, g₂, g₃, hg⟩ := exists_oddFChoice
    G m J hJ n H K hsub φ Y hYanti hmin y₁ y₂ Q hQ hQY hy
      c a₁ a₂ f C₁ C₂ B.reverse c₁ c₂ b hchoice
  apply Workspace.ProofLemmas.Thm61Claim5.thm_6_1_claim5
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd c a₁ a₂ f C₁ C₂ B.reverse c₁ c₂ b
      hchoice g₁ g₂ g₃ hg
  left
  simpa [trackLength] using hlong

/-- Transfer claim (4) across a complete edge.  At the triad `v`, keep a named `X₁` branch,
choose the unique `X₂` branch, and use the complete edge `vc` as the third branch.  Claim (4)
then says that `c` is a triad. -/
theorem triad_across_complete_edge
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
    (hQY : ∀ z : V, z ∈ Q ↔ z ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (v a c : Fin n) (e f : Sym2 (Fin n)) (A : List (Fin n))
    (hvtri : Triad G H K φ Y v) (haV : a ∈ branchVertices H)
    (hcV : c ∈ branchVertices H) (hvc : v ≠ c)
    (heinc : e ∈ incidentEdges H v) (heX₁ : e ∈ extraEdges G H K φ Y y₁)
    (hA : IsBranch H A) (heA : e ∈ trackEdges A) (hAfrom : IsTrackFrom H A v a)
    (hfinc : f ∈ incidentEdges H v) (hfX : f ∈ completeEdges G H K φ Y)
    (hfeq : f = s(v, c)) : Triad G H K φ Y c := by
  classical
  obtain ⟨-, -, -, ⟨a₂, ha₂, -⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy v hvtri
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hea₂ : e ≠ a₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ heX₁) (h ▸ ha₂.2)
  have heX : e ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hXX₁ heX₁
  have ha₂X : a₂ ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hXX₂ ha₂.2
  have hfa₂ : f ≠ a₂ := by intro h; exact ha₂X (h ▸ hfX)
  have hfe : f ≠ e := by intro h; exact heX (h ▸ hfX)
  obtain ⟨C₂, c₂, hC₂, ha₂C₂, hC₂from⟩ :=
    branch_from_incident J hJ H hsub.1 v hvtri.1 a₂ ha₂.1
  have hfadj : H.Adj v c := by
    apply H.mem_edgeSet.mp
    rw [← hfeq]
    exact hfinc.1
  have hpairfrom : IsTrackFrom H [v, c] v c :=
    Workspace.ProofLemmas.HPrimeTracks.isTrackFrom_pair hfadj
  have hpair : IsBranch H [v, c] := by
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
      hpairfrom hvc
    · intro w hw
      simp [trackInterior] at hw
    · exact hvtri.1
    · exact hcV
  have hfPair : f ∈ trackEdges [v, c] := by
    refine ⟨0, by simp, ?_⟩
    simpa using hfeq
  have hchoice : BranchChoice G H K φ Y y₁ y₂
      v e a₂ f A C₂ [v, c] a c₂ c :=
    ⟨hvtri.1, ⟨e, heinc, a₂, ha₂.1, hea₂, heX, ha₂X⟩,
      heinc, heX₁, ha₂.1, ha₂.2, hfinc, hfe, hfa₂,
      hA, heA, hAfrom, hC₂, ha₂C₂, hC₂from, hpair, hfPair, hpairfrom⟩
  obtain ⟨g₁, g₂, g₃, hg⟩ := exists_oddFChoice
    G m J hJ n H K hsub φ Y hYanti hmin y₁ y₂ Q hQ hQY hy
      v e a₂ f A C₂ [v, c] a c₂ c hchoice
  exact Workspace.ProofLemmas.Thm61Claim4.thm_6_1_claim4
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd v e a₂ f A C₂ [v, c] a c₂ c
      hchoice g₁ g₂ g₃ hg

end Workspace.ProofLemmas.Thm61Claim6Helpers
