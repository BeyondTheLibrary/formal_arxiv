import Mathlib
import Workspace.ProofLemmas.Thm61Claim4
import Workspace.ProofLemmas.Thm61Claim5Helpers

/-!
# The short-branch symmetry step in 6.1(5)

When `B₃` has one edge, that edge is the unique complete edge at the triad `b₃`.  We orient
the three branches at `b₃` and apply claim (4) with `b` and `b₃` exchanged, exactly as in the
last sentence of the printed proof of claim (5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim5Short

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim5Helpers

/-- If `B₃` has one edge, claim (4) with the two ends exchanged makes `b` a triad. -/
theorem centre_is_triad
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
    (hB₃one : trackLength B₃ = 1) : Triad G H K φ Y b := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hbasic := branchChoice_basic G m J hJ n H K hsub φ Y hmin
    y₁ y₂ Q hQ hQY hy b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
  rcases hbasic with ⟨-, -, -, -, -, -, hb₃V, -, -, hbb₃, -, -, -⟩
  have hb₃tri := Workspace.ProofLemmas.Thm61Claim4.thm_6_1_claim4
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
      f₁ f₂ f₃ hf
  obtain ⟨-, ⟨x, hx, huniqX⟩, ⟨a₁, ha₁, -⟩, ⟨a₂, ha₂, -⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₃ hb₃tri
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hB₃E := trackEdges_eq_singleton_of_length_one hfrom₃ hB₃one
  have he₃eq : e₃ = s(b, b₃) := by
    rw [hB₃E] at he₃B₃
    exact Set.mem_singleton_iff.mp he₃B₃
  have he₃inc₃ : e₃ ∈ incidentEdges H b₃ := by
    refine ⟨he₃inc.1, ?_⟩
    rw [he₃eq]
    simp
  have he₃x := huniqX e₃ ⟨he₃inc₃, he₃X⟩
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ ha₁.2) (h ▸ ha₂.2)
  have ha₁X : a₁ ∉ completeEdges G H K φ Y :=
    Set.disjoint_right.mp hXX₁ ha₁.2
  have ha₂X : a₂ ∉ completeEdges G H K φ Y :=
    Set.disjoint_right.mp hXX₂ ha₂.2
  obtain ⟨C₁, c₁, hC₁, ha₁C₁, hfromC₁⟩ :=
    branch_from_incident J hJ H hsub.1 b₃ hb₃V a₁ ha₁.1
  obtain ⟨C₂, c₂, hC₂, ha₂C₂, hfromC₂⟩ :=
    branch_from_incident J hJ H hsub.1 b₃ hb₃V a₂ ha₂.1
  have he₃a₁ : e₃ ≠ a₁ := by
    intro h
    exact ha₁X (h ▸ he₃X)
  have he₃a₂ : e₃ ≠ a₂ := by
    intro h
    exact ha₂X (h ▸ he₃X)
  have hrevB₃ : IsBranch H B₃.reverse := isBranch_reverse hB₃
  have he₃rev : e₃ ∈ trackEdges B₃.reverse := by
    simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using he₃B₃
  have hfromrev : IsTrackFrom H B₃.reverse b₃ b :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom₃
  have hchoice : BranchChoice G H K φ Y y₁ y₂
      b₃ a₁ a₂ e₃ C₁ C₂ B₃.reverse c₁ c₂ b :=
    ⟨hb₃V, ⟨a₁, ha₁.1, a₂, ha₂.1, ha₁a₂, ha₁X, ha₂X⟩,
      ha₁.1, ha₁.2, ha₂.1, ha₂.2, he₃inc₃, he₃a₁, he₃a₂,
      hC₁, ha₁C₁, hfromC₁, hC₂, ha₂C₂, hfromC₂,
      hrevB₃, he₃rev, hfromrev⟩
  obtain ⟨g₁, g₂, g₃, hg⟩ := exists_oddFChoice
    G m J hJ n H K hsub φ Y hYanti hmin y₁ y₂ Q hQ hQY hy
      b₃ a₁ a₂ e₃ C₁ C₂ B₃.reverse c₁ c₂ b hchoice
  exact Workspace.ProofLemmas.Thm61Claim4.thm_6_1_claim4
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd b₃ a₁ a₂ e₃ C₁ C₂ B₃.reverse c₁ c₂ b
      hchoice g₁ g₂ g₃ hg

end Workspace.ProofLemmas.Thm61Claim5Short
