import Workspace.ProofLemmas.Thm61EvenFinalBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenFinalFourth

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.Thm61EvenFinalTracks Workspace.ProofLemmas.Thm61EvenFinalBridge

/-- The branch chosen immediately before (13), with the endpoint restrictions and the
nontriad assertion proved in the first sentences of (13). -/
structure FourthBranch
    {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ : V)
    (b b₁ b₂ : Fin n) (e₄ : Sym2 (Fin n)) (B₄ : List (Fin n)) (b₄ : Fin n) : Prop where
  incident : e₄ ∈ incidentEdges H b₂
  extra : e₄ ∈ extraEdges G H K φ Y y₁
  branch : IsBranch H B₄
  edge : e₄ ∈ trackEdges B₄
  track : IsTrackFrom H B₄ b₂ b₄
  vertex : b₄ ∈ branchVertices H
  ne_b : b₄ ≠ b
  ne_b1 : b₄ ≠ b₁
  ne_b2 : b₄ ≠ b₂
  nontriad : ¬ Triad G H K φ Y b₄

/-- "Let `e₄` be the edge incident with `b₂` different from `b₁b₂` and not in `B₂`.
... Let `B₄` be the branch of `H` containing `e₄`, and let `b₄` be the other end of `B₄`."
The conclusions also record `B₂` having one edge and the opening assertions of (13). -/
theorem exists_fourth
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
    (heven : Even (trackLength B₁)) :
    trackLength B₂ = 1 ∧ ∃ e₄ B₄ b₄, FourthBranch G H K φ Y y₁ b b₁ b₂ e₄ B₄ b₄ := by
  classical
  have htriad := b2_triad G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h9 hadj hXb heven
  obtain ⟨hshort, he₂eq⟩ := b2_short G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h8 hadj heven htriad
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  have hbcCopy := hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨-, -, he₄uniq, -⟩ := triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htriad
  obtain ⟨e₄, he₄, -⟩ := he₄uniq
  obtain ⟨B₄, b₄, hB₄, he₄B₄, hfrom₄⟩ := branch_from_incident hJ hsub.1 hb₂V he₄.1
  have he₂inc₂ : e₂ ∈ incidentEdges H b₂ := ⟨he₂inc.1, by rw [he₂eq]; simp⟩
  have hpair : IsTrackFrom H [b₂, b₁] b₂ b₁ := HPrimeTracks.isTrackFrom_pair hadj.symm
  have hpairBr : IsBranch H [b₂, b₁] := Thm82BranchDelta.isBranch_of_ends_branch hpair
    hb₁b₂.symm (by simp [trackInterior]) hb₂V hb₁V
  obtain ⟨-, -, -, -, -, hd12, -, -⟩ := X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₄e₂ : e₄ ≠ e₂ := by
    intro h
    exact Set.disjoint_left.mp hd12 he₄.2 (h.symm ▸ he₂X₂)
  have hp₄ : s(b₁, b₂) ≠ e₄ := fun h => he₄.2.2 (h ▸ hXb)
  have hp₂ : s(b₁, b₂) ≠ e₂ := fun h => he₂X₂.2 (h ▸ hXb)
  have hnew : BranchChoice G H K φ Y y₁ y₂ b₂ e₄ e₂ s(b₁, b₂)
      B₄ B₂.reverse [b₂, b₁] b₄ b b₁ := by
    refine ⟨hb₂V, ⟨e₄, he₄.1, e₂, he₂inc₂, he₄e₂, he₄.2.2, he₂X₂.2⟩,
      he₄.1, he₄.2, he₂inc₂, he₂X₂, ⟨H.mem_edgeSet.mpr hadj, by simp⟩,
      hp₄, hp₂, hB₄, he₄B₄, hfrom₄, isBranch_reverse hB₂, ?_,
      TrackSlice.isTrackFrom_reverse hfrom₂, hpairBr, ?_, hpair⟩
    · rwa [SubdivisionCounting.trackEdges_reverse]
    · refine ⟨0, by simp, ?_⟩
      simp [Sym2.eq_swap]
  obtain ⟨-, -, -, -, hb₄V, -, -, hb₂b₄, -, -, hb₄b, hb₄b₁, -⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b₂ e₄ e₂ s(b₁, b₂) B₄ B₂.reverse [b₂, b₁] b₄ b b₁ hnew
  have hnot := not_triad_away G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbcCopy h8 heven he₂eq b₄ hb₄V hb₄b hb₄b₁ hb₂b₄.symm
  exact ⟨hshort, e₄, B₄, b₄, he₄.1, he₄.2, hB₄, he₄B₄, hfrom₄,
    hb₄V, hb₄b, hb₄b₁, hb₂b₄.symm, hnot⟩

end Workspace.ProofLemmas.Thm61EvenFinalFourth
