import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim5
import Workspace.ProofLemmas.Thm61Claim6
import Workspace.ProofLemmas.Thm61Claim4
import Workspace.ProofLemmas.Thm61OddEndgame

/-!
# 6.1, claim (7): if the antipath `Q` is odd then the theorem holds

PAPER (proof of 6.1, printed p. 31):

> *"(7) If `Q` is odd then the theorem holds."*

This is the conclusion of the first of the two cases of the proof of 6.1 — the case in which the
antipath `Q` whose vertex set is `Y` has odd length.  It is reached through claims (1)–(6):

* *(1) If the branch-vertices of `H` form a 4-cycle `C` and `X` consists of at most three edges
  of `C`, then the theorem holds.*
* *(2) If `Q` is odd then there is no cycle of `H` with edge-set `{h₁,h₂,h₃,h₄}` in order, such
  that the common end of `h₁` and `h₂` is a branch-vertex, `h₁ ∈ X₁`, `h₂ ∈ X₂`, and
  `h₃, h₄ ∈ X`.*
* *(3) If `Q` is odd and `h₁ ∈ X₁` meets `h₂ ∈ X₂`, then every edge in `X` meets at least one of
  `h₁, h₂`.*
* *(4) If `Q` is odd then `b₃` is a triad.*
* *(5) If `Q` is odd and either `B₃` has length `> 1` or `b` is not a triad, then the theorem
  holds.*
* *(6) If `Q` is odd and one of `B₁, B₂` has length `> 1` then the theorem holds.*
* *(7) For by (5) and (6) we may assume that `E(Bᵢ) = {eᵢ}` for `i = 1,2,3` … Since `H` is a
  subdivision of a 3-connected graph, `J = K₃,₃`, and `L(H)` is a degenerate appearance of `J`,
  and there is a `J`-enlargement that appears in `Ḡ`, so the third outcome of the theorem
  holds.*

The auxiliary sets of the proof are recovered from the hypotheses below and are not parameters:
`X` is the set of `Y`-complete vertices of `L(H)` and, for `i = 1, 2`, `Xᵢ` is the set of
`Y \ {yᵢ}`-complete vertices of `L(H)` that are not in `X` (where `y₁, y₂` are the ends of `Q`).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61OddCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61Claim5
open Workspace.ProofLemmas.Thm61Claim6
open Workspace.ProofLemmas.Thm61Claim4
open Workspace.ProofLemmas.Thm61OddEndgame

/-- **6.1(7)** *"If `Q` is odd then the theorem holds."* -/
theorem thm_6_1_odd_case
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Y})
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          VertexComplete G (↑(φ ⟨e, he⟩) : V) Y₁})
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q)) :
    Thm61Concl G m J n H K φ Y := by
  classical
  obtain ⟨b, e₁, e₂, e₃, B₁, B₂, B₃, b₁, b₂, b₃, hbc⟩ :=
    exists_branchChoice G m J hJ n H K hsub φ Y hYanti hnotsat hmin
      y₁ y₂ Q hQ hQY hy
  obtain ⟨f₁, f₂, f₃, hf⟩ :=
    exists_oddFChoice G m J hJ n H K hsub φ Y hYanti hmin
      y₁ y₂ Q hQ hQY hy b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  by_cases hcase5 : 1 < trackLength B₃ ∨ ¬ Triad G H K φ Y b
  · exact thm_6_1_claim5 G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
      f₁ f₂ f₃ hf hcase5
  by_cases hcase6 : 1 < trackLength B₁ ∨ 1 < trackLength B₂
  · exact thm_6_1_claim6 G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
      f₁ f₂ f₃ hf hcase6
  have hbc' := hbc
  rcases hbc' with ⟨-, -, -, -, -, -, -, -, -, -, he₁B₁, -, -, he₂B₂, -, -, he₃B₃, -⟩
  have edge_forces_one_le : ∀ {B : List (Fin n)} {e : Sym2 (Fin n)},
      e ∈ trackEdges B → 1 ≤ trackLength B := by
    intro B e he
    obtain ⟨i, hi, -⟩ := he
    simp only [trackLength]
    omega
  have hB₁ : trackLength B₁ = 1 := by
    have hlo := edge_forces_one_le he₁B₁
    have hhi : ¬ 1 < trackLength B₁ := fun h => hcase6 (Or.inl h)
    omega
  have hB₂ : trackLength B₂ = 1 := by
    have hlo := edge_forces_one_le he₂B₂
    have hhi : ¬ 1 < trackLength B₂ := fun h => hcase6 (Or.inr h)
    omega
  have hB₃ : trackLength B₃ = 1 := by
    have hlo := edge_forces_one_le he₃B₃
    have hhi : ¬ 1 < trackLength B₃ := fun h => hcase5 (Or.inl h)
    omega
  have htriad : Triad G H K φ Y b := by
    by_contra h
    exact hcase5 (Or.inr h)
  have htriad₃ := thm_6_1_claim4 G hG m J hJ n H K hsub φ Y hYanti hYmajor
    hnotsat hmin y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
    f₁ f₂ f₃ hf
  have hskeleton := short_odd_skeleton G hG m J hJ n H K hsub φ Y hYmajor hmin
    y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
    f₁ f₂ f₃ hf htriad₃ hB₁ hB₂ hB₃
  have hend := short_odd_configuration_gives_third_outcome G hG m J hJ n H K hsub φ
    Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ f₃ hf htriad htriad₃
    hB₁ hB₂ hB₃ hskeleton
  exact Or.inr (Or.inr (Or.inl hend))

end Workspace.ProofLemmas.Thm61OddCase
