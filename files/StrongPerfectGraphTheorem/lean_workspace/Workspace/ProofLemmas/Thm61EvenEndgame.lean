import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.Thm61Claim1
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61EvenEndgameSteps

/-!
# 6.1, even case: the configuration argument (11), (12), (13) and the closing paragraph

PAPER (proof of 6.1, printed pp. 32–33).  Everything after claim (10) — the refinement of the
choice of `b`, claims (11), (12), (13), and the paragraph that ends *"This proves 6.1"*.  The
printed text is reproduced here verbatim, because it is the script for this module.

> *"Earlier (preceding (4)) we chose `b` such that at least two edges of `H` incident with `b`
> did not belong to `X`.  Let us refine this choice; now in addition we choose `b` such that
> `B₃` is as long as possible.*
>
> *(11) For `i = 1, 2` there is an edge `fᵢ ∈ X` incident with `bᵢ` that does not meet `e₃`.*
>
> *For it suffices to prove this for `i = 1`, and it clearly holds if there are at least two
> members of `X` incident with `b₁`.  So we may assume that there is a unique member of `X`
> incident with `b₁`, and that this edge meets `e₃`, and therefore is the edge `b₁b₃`.  But then
> `b₁` is a triad, and `E(B₃) = {e₃}`, and `|E(B₁)| > 1`, because `H` is bipartite.  The unique
> edge of `X₁` incident with `b₁` meets `e₂` by (8); and hence this edge is `b₁b₂`, and
> `e₂ = bb₂`.  Suppose for a contradiction that there is a fourth edge `bv` incident with `b`,
> and let `f` be an edge incident with `b₃` different from `bb₂, b₁b₂`; then `v ≠ b, b₁, b₂, b₃`,
> and there is a track of length 4 with vertices `b₃-b₁-b₂-b-v` in order; its end-edges belong to
> `X` and its internal edges do not; and `f ∈ X` is not incident with any penultimate vertex of
> this track, contrary to (9).  This proves that `b` has degree three.  Since `H` is cyclically
> 3-connected, it follows that `H` consists of `B₁, B₂, B₃`, the edges `b₁b₂, b₁b₃`, and a branch
> `B` with ends `b₂` and `b₃` that includes a member of `X` incident with `b₂`.  Since `H` is
> bipartite, it follows that `|E(B)| > 1`, and hence `b₂` and `B` contradict the choice of `b`
> and `B₃`.  This proves (11).*
>
> *(12) If there exist `f₁, f₂` as in (11) with `f₁, f₂ ≠ b₁b₂` then the theorem holds.*
>
> *For it follows from (10) applied to subtracks of the tracks with edge-sets `E(B₁) ∪ {f₁}`,
> `E(B₂) ∪ {f₂}` and `{e₃}` that `B₁, B₂` include no member of `X`, and that `f₁` meets `f₂`.
> Thus `b₁` is not adjacent to `b₂`.  We claim that for `i = 1,2` the edge `fᵢ` is the only edge
> of `X` incident with `bᵢ`.  For suppose that say `f₁' ∈ X` is incident with `b₁`.  By (10)
> applied to the vertex `b` and the tracks with edge-sets `E(B₁) ∪ {f₁'}`, `E(B₂) ∪ {f₂}` and
> `{e₃}`, we deduce that `f₁'` meets `e₃`.  Thus `B₁` is even.  Let `P` be the track obtained
> from `B₁` by adding `e₃` and `f₁`; then `P` and the edge `f₂` violate (9).  This proves our
> claim that `fᵢ` is the only edge of `X` incident with `bᵢ` for `i = 1,2`.  Consequently, `b₁`
> and `b₂` are triads.  From (8) we deduce that `B₁` and `B₂` have length one.  For `i = 1,2` let
> `dᵢ` be the edge incident with `bᵢ` different from `eᵢ, fᵢ`; so `d₁ ∈ X₂` and `d₂ ∈ X₁`.  By (8)
> the edges `d₁, d₂` meet; let `v` denote their common end.  Every edge `g` incident with `v`
> other than `d₁` and `d₂` belongs to `X`.  If some such `g` does not meet `e₃` then the edges
> `g, d₂, e₂, e₃` form a track with end-edges in `X` and internal edges not in `X`, and `f₁` is
> not incident with a penultimate vertex of this track, contrary to (9).  So every such edge `g`
> meets `e₃` and hence is incident with `b₃` (since `H` is bipartite).  Thus `v` has degree two
> or three.  If `v = b₃`, then `B₃` has length 2 and both its edges belong to `X`, and the fourth
> outcome of the theorem holds.  If `v ≠ b₃` and `v` has degree 3, then the third edge incident
> with `v` is `vb₃`, and `b` is a triad, and `H` consists of the vertices `b, b₁, b₂, b₃, v` and a
> branch `B` with ends `b₃` and `u`, where `u` is the common end of `f₁` and `f₂`; but then
> `J = K₃,₃`, and if `B` has length 1 then the second outcome of the theorem holds, and otherwise
> the first outcome holds.  Finally, if `v ≠ b₃` and `v` has degree two, then `b₃` is the common
> end of `f₁, f₂`, and `J = K₄` and the second outcome of the theorem holds.  This proves (12).*
>
> *From (11) and (12) we may therefore assume that `b₁, b₂` are adjacent, and the edge
> `b₁b₂ ∈ X`.  From the symmetry we may assume that `B₁` is even and `B₂` is odd.  Let `T` be the
> track formed by `B₁` and the edges `e₃, b₁b₂`.  So `T` is even.  Suppose that there is an edge
> (say `f`) in `X` incident with `b₂` and different from `b₁b₂`.  By (10) no edge of `B₁` belongs
> to `X`, and yet `f` is not incident with a penultimate vertex of `T`, contrary to (9).  So
> there is no such edge `f`, and therefore `b₂` is a triad.  Let `e₄` be the edge incident with
> `b₂` different from `b₁b₂` and not in `B₂`.  So `e₄ ∈ X₁ ∪ X₂`, and therefore by (8), `e₄` meets
> one of `e₁, e₂`.  Since it is not incident with `e₁`, it follows that `E(B₂) = {e₂}`, and
> `e₄ ∈ X₁`.  Let `B₄` be the branch of `H` containing `e₄`, and let `b₄` be the other end of
> `B₄`.*
>
> *(13) `b₄ = b₃`, and `B₃` has length 1, and `H` is a subdivision of `K₄`, and `B₄` is even.*
>
> *For `b₄` is different from `b, b₁, b₂`.  Since `B₁` is even, and `e₂` is the unique edge in
> `X₂` incident with `b`, it follows that no edge in `X₂` incident with `b₄` meets `e₁`, and
> therefore by (8), no edge in `X₂` is incident with `b₄`.  Consequently `b₄` is not a triad, and
> so there are at least two edges (say `g₁, g₂`) in `X` incident with `b₄`.  By (10) (applied to
> three tracks with common end `b₂`), each of them meets either `b₁b₂` or `e₃`.  But no edge in
> `X` is incident with both `b₂` and `b₄`, since `e₄ ∈ X₁`; so `g₁, g₂` are either incident with
> `b₁` or meet `e₃`.*
>
> *Suppose that `b₄` is not incident with `e₃`.  Then at most one of `g₁, g₂` is incident with
> `b₁`, and at most one meets `e₃` (since `H` is bipartite), so there is exactly one of each.
> Hence `b₁` is adjacent to `b₄`, and `b₁b₄ ∈ X`; and (since `H` is bipartite and `B₁` is even)
> `b` is adjacent to `b₄` and `bb₄ ∈ X`, and `b₄` has degree 3.  Since `b₄` is not incident with
> `e₃`, and `b₄` is adjacent to `b`, it follows that `b₄ ≠ b₃`; and since `H` is cyclically
> 3-connected and `b₂` is a triad, this is impossible.  So `b₄` is incident with `e₃`, that is,
> `b₄ = b₃` and `B₃` has length 1.  Since this holds for every choice of `e₃`, we deduce that `b`
> has degree 3, and therefore `H` is a subdivision of `K₄`.  It follows that `B₄` is even.  This
> proves (13).*
>
> *Let `B₅` be the branch of `H` between `b₁, b₃`.  Since no edge incident with `b₃` meets `e₁`
> except `e₃`, it follows that `b₃` is not a triad.  Suppose that no edge of `B₁` is in `X`.
> Then by (9) applied to `T`, every edge in `X` is incident with one of `b, b₁`.  In particular,
> no edge of `B₄` is in `X`; and since `b₃` is not a triad, it follows that `B₅` has length 1 and
> its edge is in `X`.  Thus `b₃` is adjacent to both `b, b₁`, and the edges `bb₃, b₁b₃` both
> belong to `X`; but then the theorem holds by (1).*
>
> *So we may assume that some edge of `B₁` is in `X`.  This edge is not incident with a
> penultimate vertex of the track formed by `B₄` and the edges `b₁b₂, e₃`, so by (9), some edge
> of `B₄` belongs to `X`.  By (10) applied to `B₁`, a subtrack of `B₂ ∪ B₄` and the track
> consisting of the edge `e₃`, we deduce that the only edge of `B₄` in `X` is the edge incident
> with `b₃`.  By (10) applied to the track with edge-set `E(B₂) ∪ {b₁b₂}`, a subtrack of `B₁` and
> the track consisting of the edge `e₃`, we deduce that the only edge of `B₁` in `X` is the edge
> incident with `b₁`.  But `B₅` is odd, and if it has length `> 1` then the first outcome of the
> theorem holds.  So we may assume that `b₁b₃` is an edge.  Now the tracks `B₁, B₄` are even;
> their end-edges belong to `X ∪ X₁`, and their other edges do not (by (8)), and `e₃` is not
> incident with a penultimate vertex of these tracks; so by (9), `B₁` and `B₄` both have length
> 2.  But then the fourth outcome of the theorem holds.  This proves 6.1."*

The whole argument is driven by a single configuration chosen at the start:

* a branch-vertex `b` of `H` incident with at least two edges not in `X` (this exists exactly
  because `X` does not saturate `L(H)`), chosen so that the branch `B₃` below is as long as
  possible;
* `eᵢ ∈ Xᵢ` incident with `b` for `i = 1, 2` (these exist because `X ∪ Xᵢ` saturates `L(H)`),
  and `e₃` some third edge incident with `b` (which exists because `b` has degree `≥ 3`);
* `Bᵢ` the branch of `H` containing `eᵢ`, and `bᵢ` its other end.

Because the configuration is proof-local, and because the printed argument passes between (11),
(12), (13) and the closing paragraph freely — reusing `b`, `bᵢ`, `Bᵢ`, `T`, `B₄`, `B₅` and the
maximality of `B₃` throughout — the four printed steps are bundled here into a single work item
rather than split into four modules with a hand-invented interface.  (The same call was made for
`Thm85Endgame`; see `PROVING_NOTES.md`.)

The three claims the argument uses are supplied as hypotheses in the exact form in which the
other modules of the even case prove them: `Thm61EvenClaims.Claim8` (proved in
`Workspace.ProofLemmas.Thm61Claim8`), `Claim9` (`Workspace.ProofLemmas.Thm61Claim9`) and
`Claim10` (`Workspace.ProofLemmas.Thm61Claim10`).  The closing paragraph also invokes claim (1)
of the proof, which belongs to the part preceding the odd/even split and is stated (with no
parity hypothesis on `Q`, precisely because both halves use it) as
`Workspace.ProofLemmas.Thm61Claim1.thm_6_1_claim_1`; that module is imported here so the
closing paragraph's *"but then the theorem holds by (1)"* can cite it directly.

## This attempt: the assembly

The printed argument is carved into the blocks the paper itself marks out, stated in
`Workspace.ProofLemmas.Thm61EvenEndgameSteps`:

* `exists_maximal_config` — *"There is a branch-vertex `b` of `H` incident with at least two
  edges not in `X` …"* (preceding (4)) refined by *"now in addition we choose `b` such that `B₃`
  is as long as possible"* (preceding (11));
* `thm_6_1_claim_11` — (11);
* `thm_6_1_claim_12` — (12);
* `thm_6_1_even_final` — the bridging paragraph, (13) and the closing paragraph.

What is done *here* is exactly the printed sentence *"From (11) and (12) we may therefore assume
that `b₁, b₂` are adjacent, and the edge `b₁b₂ ∈ X`"*: (11) produces `f₁, f₂`; if a pair as in
(11) can be chosen with both members different from `b₁b₂` then (12) finishes, and otherwise one
of the two edges `f₁, f₂` supplied by (11) *is* `b₁b₂`, which is exactly the hypothesis
`thm_6_1_even_final` runs with.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61EvenClaims

/-- **6.1, even case, endgame.**  Claims (11), (12), (13) and the closing paragraph of the
printed proof: given (8), (9) and (10), the theorem holds. -/
theorem thm_6_1_even_endgame
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
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y) :
    Thm61Concl G m J n H K φ Y := by
  -- *"Earlier (preceding (4)) we chose `b` such that at least two edges of `H` incident with `b`
  -- did not belong to `X`.  Let us refine this choice; now in addition we choose `b` such that
  -- `B₃` is as long as possible."*
  obtain ⟨b, e₁, e₂, e₃, B₁, B₂, B₃, b₁, b₂, b₃, hcfg, hmax⟩ :=
    Thm61EvenEndgameSteps.exists_maximal_branchChoice G m J hJ n H K hsub φ Y hYanti hnotsat hmin
      y₁ y₂ Q hQ hQY hy
  -- *"(11) For `i = 1, 2` there is an edge `fᵢ ∈ X` incident with `bᵢ` that does not meet
  -- `e₃`."*
  obtain ⟨⟨f₁, hf₁X, hf₁b, hf₁e⟩, ⟨f₂, hf₂X, hf₂b, hf₂e⟩⟩ :=
    Thm61EvenEndgameSteps.thm_6_1_claim_11 G hG m J hJ n H K hsub φ Y hYanti hYmajor
      hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hcfg hmax
  -- *"(12) If there exist `f₁, f₂` as in (11) with `f₁, f₂ ≠ b₁b₂` then the theorem holds."*
  by_cases hcase : ∃ g₁ g₂ : Sym2 (Fin n),
      (g₁ ∈ completeEdges G H K φ Y ∧ b₁ ∈ g₁ ∧ ¬ MeetEdges g₁ e₃ ∧ g₁ ≠ s(b₁, b₂)) ∧
        (g₂ ∈ completeEdges G H K φ Y ∧ b₂ ∈ g₂ ∧ ¬ MeetEdges g₂ e₃ ∧ g₂ ≠ s(b₁, b₂))
  · obtain ⟨g₁, g₂, ⟨hg₁X, hg₁b, hg₁e, hg₁ne⟩, ⟨hg₂X, hg₂b, hg₂e, hg₂ne⟩⟩ := hcase
    exact Thm61EvenEndgameSteps.thm_6_1_claim_12 G hG m J hJ n H K hsub φ Y hYanti hYmajor
      hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hcfg hmax
      g₁ g₂ hg₁X hg₁b hg₁e hg₂X hg₂b hg₂e hg₁ne hg₂ne
  · -- *"From (11) and (12) we may therefore assume that `b₁, b₂` are adjacent, and the edge
    -- `b₁b₂ ∈ X`."*  Indeed, otherwise the pair `f₁, f₂` produced by (11) would already be a
    -- pair as in (12).
    have hor : f₁ = s(b₁, b₂) ∨ f₂ = s(b₁, b₂) := by
      by_contra hcon
      push Not at hcon
      exact hcase ⟨f₁, f₂, ⟨hf₁X, hf₁b, hf₁e, hcon.1⟩, ⟨hf₂X, hf₂b, hf₂e, hcon.2⟩⟩
    have hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y := by
      rcases hor with h | h
      · rw [← h]; exact hf₁X
      · rw [← h]; exact hf₂X
    have hadj : H.Adj b₁ b₂ := by
      obtain ⟨he, -⟩ := hXb
      exact (SimpleGraph.mem_edgeSet H).mp he
    -- The bridging paragraph, (13) and the closing paragraph.
    exact Thm61EvenEndgameSteps.thm_6_1_even_final G hG m J hJ n H K hsub φ Y hYanti hYmajor
      hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hcfg hmax
      hadj hXb

end Workspace.ProofLemmas.Thm61EvenEndgame
