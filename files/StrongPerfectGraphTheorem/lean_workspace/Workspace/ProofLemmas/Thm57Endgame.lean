import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim4
import Workspace.ProofLemmas.Thm57EndgameHelpers

/-!
# 5.7 — the endgame (the paragraph after printed claim (4))

PAPER (printed pp. 24–25):

> We may assume that statement 1 of the theorem does not hold, and so there is a branch-vertex
> of `H` incident with `≥ 2` edges not in `X`.  Hence there is a connected subgraph `A` of
> `H \ X`, containing a branch-vertex and at least two edges incident with it.  Choose such a
> subgraph `A` maximal.  It follows that `V(A)` is not contained in any branch of `H`.  By (4),
> there is no 3-edge matching among the edges in `X` that meet `V(A)`; and since this set of
> edges forms a bipartite subgraph, it follows from König's theorem that there are two vertices
> `c₁, c₂ ∈ V(H)` such that every edge in `X` with an end in `V(A)` is incident with one of
> `c₁, c₂`.  From the maximality of `A`, every edge of `H` between `V(A)` and `V(H) \ V(A)`
> belongs to `X` and therefore is incident with one of `c₁, c₂`; and so there are two subgraphs
> `C, D` of `H` with `V(C) = V(A) ∪ {c₁,c₂}`, `V(D) = (V(H) \ V(A)) ∪ {c₁,c₂}` and `C ∪ D = H`.
>
> Now `V(C)` is not contained in a branch of `H`, because it contains `V(A)` and we already saw
> that `V(A)` is not contained in a branch; and we may assume that `V(D)` is not contained in a
> branch by (2), since every edge in `X` has an end in `V(D)`.  But `V(D) ≠ V(H)` since
> `|V(C)| ≥ |V(A)| ≥ 3 > |V(C ∩ D)|`; and since `H` is cyclically 3-connected, it follows that
> `V(C) = V(H)`.  Hence every edge in `X` is incident with one of `c₁, c₂`.  For `i = 1, 2` let
> `Aᵢ = δ(cᵢ) ∩ X`, and let `Bᵢ = δ(cᵢ) \ Aᵢ`.  By (2), we may assume that `c₁, c₂` do not
> belong to the same branch.  Consequently `c₁, c₂` are nonadjacent, and `H \ {c₁, c₂}` is
> connected, by 5.5.  By (1) we may assume that there exist disjoint edges `a₁c₁ ∈ A₁` and
> `a₂c₂ ∈ A₂`.  Take a minimal track in `H \ {c₁, c₂}` between `a₁, a₂`; then by the hypothesis
> of the theorem, this track has odd length, and so `c₁, c₂` have opposite biparity.  There is
> therefore no track `T` in `H` with first edge in `A₁`, second edge in `B₁` (and hence second
> vertex `c₁`), last vertex `c₂` and last edge in `A₂`; and a similar statement holds with
> `c₁, c₂` exchanged.  By 5.6, it follows that `B₁, B₂ = ∅`, and therefore statement 6 of the
> theorem holds.  This proves 5.7.

(`V(G)` in the printed text of this paragraph is a typo for `V(H)`; see `AMBIGUITIES.md` §A4.)

The two *"we may assume … by (2)"* moves are discharged by the hypothesis `hnoB`: at the call
site, if some branch of `H` meets every edge of `X` then `Thm57Claim2` already gives the
conclusion.  Likewise `hdisj` is granted by claim (1) and `hnotsat` is the *"statement 1 does
not hold"* assumption.

Cites `Workspace.Statements.S05.SPGT.thm_5_5` and `thm_5_6` — both are still `sorry` at the
time of writing, so any axiom check on `thm_5_7` will report their `sorryAx` until §5's
earlier statements are discharged.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **5.7, endgame** — when alternative 1 fails, `X` has two disjoint edges and no branch of
`H` meets every edge of `X`, alternative 6 holds. -/
theorem thm57Endgame (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) (hdisj : TwoDisjointEdges H X)
    (hnoB : ¬ SomeBranchMeetsAll H X) (hnotsat : ¬ SaturatesLineGraph H X) :
    Stmt57_6 H X := by
  exact Thm57EndgameHelpers.endgame_core
    H hbip hc3 X hXE hnotrack hdisj hnoB hnotsat

end Workspace.ProofLemmas.Thm57Endgame
