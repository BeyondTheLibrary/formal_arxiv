import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim1
import Workspace.ProofLemmas.Thm61Claim2
import Workspace.ProofLemmas.Thm61Claim3
import Workspace.ProofLemmas.Thm61Claim4
import Workspace.ProofLemmas.Thm61Claim5
import Workspace.ProofLemmas.Thm61Claim6BothLong
import Workspace.ProofLemmas.Thm61Claim6Oriented

/-!
# 6.1, claim (6): if one of `B₁, B₂` is long, the theorem holds

PAPER (proof of 6.1, printed p. 31), the fifth claim of the odd case:

> *"(6) If `Q` is odd and one of `B₁, B₂` has length `> 1` then the theorem holds.*
>
> *For suppose first that they both have length at least two.  Then, for `i = 1, 2`, by (3)
> applied to `b` and `fᵢ` we deduce that `E(Bᵢ) = {eᵢ, fᵢ}` and therefore `fᵢ` is the unique edge
> of `X` incident with `bᵢ`.  This contradicts (3) applied to `f₁` and `b₂`.  So at least one of
> `B₁, B₂` has length 1, and from the symmetry we may assume that `E(B₁) = {e₁}` and `B₂` has
> length at least two.  If `f₂ ∈ E(B₂)` then `b₂` is a triad, and the theorem holds by (5) with
> `b, b₂` exchanged, so we may assume that `f₂ ∉ E(B₂)`.  Let `e₂'` be the edge of `B₂` incident
> with `b₂`.  By (3) applied to `f₂` and `b` we deduce that `f₂ = b₁b₂`, and that no edge incident
> with `b₂` belongs to `X` except `f₂` and possibly `e₂'`.  By (3) and (4) applied to `f₂` and
> `b₃`, it follows that `b₃` is adjacent to `b₂` and `b₂b₃ ∉ X`.  Suppose for a contradiction that
> `b₁` is not a triad, and choose `e₁' ∈ X \ {b₁b₂}` incident with `b₁`.  By (3) applied to `e₁'`
> and `b₂`, it follows that `e₂' ∈ X`, and from (3) applied to `e₂'` and `b` we deduce that
> `E(B₂) = {e₂, e₂'}`.  But now the edges `e₁, e₂, e₂', f₂` contradict (2).  This proves that `b₁`
> is a triad, and from (4) with `b, b₁` exchanged, we deduce that `b₂` is a triad.  Since `H` is
> cyclically 3-connected, it follows that `H` is the union of `B₁, B₂, B₃`, the edges `b₁b₂` and
> `b₂b₃` and a branch `B` with ends `b₁` and `b₃`.  From (3) applied to `b₁`, we deduce that no
> edge of `B₂` belongs to `X`, and by (3) applied to `b₂` it follows that no edge of `B` belongs
> to `X`.  But then the theorem holds by (1).  This proves (6)."*

*"The theorem holds"* is `Workspace.ProofLemmas.Thm61Conclusion.Thm61Concl`, the disjunction of
the five printed outcomes of 6.1 — the same predicate used by `Thm61Claim1`, `Thm61Claim5`,
`Thm61Claim8`, `Thm61EvenEndgame` and `Thm61OddCase`.

The configuration `b`, `eᵢ`, `Bᵢ`, `bᵢ`, `fᵢ` is `Thm61BranchChoice.BranchChoice` /
`Thm61BranchChoice.OddFChoice`; *"one of `B₁, B₂` has length `> 1`"* is
`1 < trackLength B₁ ∨ 1 < trackLength B₂`.

The printed argument cites (1), (2), (3), (4) and (5); the closing sentence *"But then the
  theorem holds by (1)"* is `Workspace.ProofLemmas.Thm61Claim1.thm_6_1_claim_1`, which is imported
here for exactly that reason.

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim6

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61BranchChoice

/-- **6.1(6)** *"If `Q` is odd and one of `B₁, B₂` has length `> 1` then the theorem holds."* -/
theorem thm_6_1_claim6
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
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃)
    -- *"one of `B₁, B₂` has length `> 1`"*
    (hcase : 1 < trackLength B₁ ∨ 1 < trackLength B₂) :
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
  rcases Workspace.ProofLemmas.Thm61EvenEndgameHelpers.branchChoice_basic
      G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
        b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, hB₃pos, -, -, -, -, -, -, -, -, -, -⟩
  by_cases hclaim5 : 1 < trackLength B₃ ∨ ¬ Triad G H K φ Y b
  · exact Workspace.ProofLemmas.Thm61Claim5.thm_6_1_claim5
      G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
        y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
        hbc' f₁ f₂ f₃ hf' hclaim5
  · have hB₃one : trackLength B₃ = 1 := by
      have hnlong : ¬ 1 < trackLength B₃ := fun h => hclaim5 (Or.inl h)
      omega
    have hbtri : Triad G H K φ Y b := by
      by_contra hn
      exact hclaim5 (Or.inr hn)
    by_cases hB₁long : 1 < trackLength B₁
    · by_cases hB₂long : 1 < trackLength B₂
      · exact False.elim (Workspace.ProofLemmas.Thm61Claim6BothLong.impossible
          G hG m J hJ n H K hsub φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
            b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' f₁ f₂ f₃ hf'
            hB₁long hB₂long)
      · have hB₂one : trackLength B₂ = 1 := by omega
        have hQrev : IsAntipathFrom G Q.reverse y₂ y₁ :=
          Workspace.ProofLemmas.PathBasics.isAntipathFrom_reverse hQ
        have hQYrev : ∀ v : V, v ∈ Q.reverse ↔ v ∈ Y := by
          intro v
          rw [List.mem_reverse]
          exact hQY v
        have hoddrev : Odd (pathLength Q.reverse) := by
          rw [Workspace.ProofLemmas.PathBasics.pathLength_reverse]
          exact hQodd
        have hbcSwap : BranchChoice G H K φ Y y₂ y₁
            b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ :=
          ⟨hbV, hnon, he₂inc, he₂X₂, he₁inc, he₁X₁,
            he₃inc, he₃e₂, he₃e₁,
            hB₂, he₂B₂, hfrom₂, hB₁, he₁B₁, hfrom₁, hB₃, he₃B₃, hfrom₃⟩
        have hfSwap : OddFChoice G H K φ Y B₂ B₁ B₃ b₂ b₁ b₃ f₂ f₁ f₃ :=
          ⟨hf₂, hf₁, hf₃⟩
        exact Workspace.ProofLemmas.Thm61Claim6Oriented.oriented
          G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
            y₂ y₁ Q.reverse hQrev hQYrev hy.symm hoddrev
            b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ hbcSwap f₂ f₁ f₃ hfSwap
            hB₂one hB₁long hB₃one hbtri
    · have hB₁one : trackLength B₁ = 1 := by omega
      have hB₂long : 1 < trackLength B₂ := hcase.resolve_left hB₁long
      exact Workspace.ProofLemmas.Thm61Claim6Oriented.oriented
        G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
          y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
          hbc' f₁ f₂ f₃ hf' hB₁one hB₂long hB₃one hbtri

end Workspace.ProofLemmas.Thm61Claim6
