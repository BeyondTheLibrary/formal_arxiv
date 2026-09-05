import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim3
import Workspace.ProofLemmas.Thm61Claim4
import Workspace.ProofLemmas.Thm61Claim5Long
import Workspace.ProofLemmas.Thm61Claim5Short

/-!
# 6.1, claim (5): if `B₃` is long or `b` is not a triad, the theorem holds

PAPER (proof of 6.1, printed pp. 30–31), the fourth claim of the odd case:

> *"(5) If `Q` is odd and either `B₃` has length `> 1` or `b` is not a triad, then the theorem
> holds.*
>
> *For assume that `B₃` has length `≥ 2`.  By (3) applied to `e₃` and the two edges of
> `E(H) \ X` incident with `b₃` it follows that `B₃` has length two and `f₃ ∉ E(B₃)`.  (Later we
> will use the shorthand "by (3) applied to `e₃` and `b₃`".)  By (3) applied to `f₃`, `e₁` and
> `e₂` we deduce that `f₃` is incident with `e₁` or `e₂`, and so from the symmetry we may assume
> that `f₃ = b₁b₃` and `E(B₁) = {e₁}`.  Suppose that `B₂` has length at least two.  By (3)
> applied to `f₂`, `e₁` and `e₂`, it follows that either `f₂ = b₁b₂` or `E(B₂) = {e₂, f₂}`; and
> therefore in both cases `b₂, b₃` are nonadjacent, since `H` is bipartite.  But this contradicts
> (3) applied to `f₂` and `b₃`.  It follows that `B₂` has length 1, and `E(B₂) = {e₂}`.  From (3)
> applied to `f₂` and `b₃` we deduce that `b₂` is adjacent to `b₃` and `b₂b₃ ∉ X`.  The vertex `b`
> has degree 3, for a fourth edge incident with `b` would violate (3) applied to that edge and
> `b₃`.  Since `H` is cyclically 3-connected, it follows that `H` is the union of `B₁, B₂, B₃`,
> the edges `b₁b₃, b₂b₃` and a branch `B` with ends `b₁` and `b₂`.  The branch `B` includes `f₂`,
> and its edge incident with `b₁`, say `e`, is not in `X` by (3) applied to `e` and `b₃`.  But `e`
> meets `f₂`, by (3) applied to `f₂` and `b₁`.  Thus `B` has length two, and hence the fourth
> outcome of the theorem holds.  We may therefore assume that `E(B₃) = {e₃}`.  In this case `e₃`
> is the only member of `X` incident with `b₃`, and from (4) with `b, b₃` exchanged it follows
> that `b` is a triad.  This proves (5)."*

*"The theorem holds"* is `Workspace.ProofLemmas.Thm61Conclusion.Thm61Concl`, the disjunction of
the five printed outcomes of 6.1 — the same predicate used by `Thm61Claim1`, `Thm61Claim8`,
`Thm61EvenEndgame` and `Thm61OddCase`.

The configuration `b`, `eᵢ`, `Bᵢ`, `bᵢ`, `fᵢ` is `Thm61BranchChoice.BranchChoice` /
`Thm61BranchChoice.OddFChoice`, and *"`b` is a triad"* is `Thm61BranchChoice.Triad G H K φ Y b`;
*"`B₃` has length `> 1`"* is `1 < trackLength B₃`.

The printed argument cites (3) (`Workspace.ProofLemmas.Thm61Claim3`, proved) and (4)
(`Workspace.ProofLemmas.Thm61Claim4`) — the latter *"with `b, b₃` exchanged"*, which is why (4)
is stated for an arbitrary configuration.  Claim (5) is itself applied *"with `b, b₂`
exchanged"* inside the proof of (6), so it too is stated for an arbitrary configuration.

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim5

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61BranchChoice

/-- **6.1(5)** *"If `Q` is odd and either `B₃` has length `> 1` or `b` is not a triad, then the
  theorem holds."* -/
theorem thm_6_1_claim5
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
    -- *"either `B₃` has length `> 1` or `b` is not a triad"*
    (hcase : 1 < trackLength B₃ ∨ ¬ Triad G H K φ Y b) :
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
  have hB₃pos : 1 ≤ trackLength B₃ := by
    obtain ⟨i, hi, -⟩ := he₃B₃
    simp only [trackLength]
    omega
  by_cases hlong : 1 < trackLength B₃
  · have hmeet : MeetEdges e₁ e₂ := by
      intro hd
      exact hd b ⟨he₁inc.2, he₂inc.2⟩
    have hm := Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
      G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
        e₁ e₂ f₃ he₁X₁ he₂X₂ hmeet hf₃.1
    rcases hm with hm | hm
    · exact Workspace.ProofLemmas.Thm61Claim5Long.oriented
        G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
          y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
          hbc' f₁ f₂ f₃ hf' hlong hm
    · have hQrev : IsAntipathFrom G Q.reverse y₂ y₁ :=
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
      exact Workspace.ProofLemmas.Thm61Claim5Long.oriented
        G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
          y₂ y₁ Q.reverse hQrev hQYrev hy.symm hoddrev
          b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ hbcSwap f₂ f₁ f₃ hfSwap hlong hm
  · have hone : trackLength B₃ = 1 := by omega
    have htri := Workspace.ProofLemmas.Thm61Claim5Short.centre_is_triad
      G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
        y₁ y₂ Q hQ hQY hy hQodd b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
        hbc' f₁ f₂ f₃ hf' hone
    exact False.elim (hcase.elim hlong (fun hn => hn htri))

end Workspace.ProofLemmas.Thm61Claim5
