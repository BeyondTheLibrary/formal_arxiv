import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim2Window
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.Thm57Claim2Parity

/-!
# 5.7, printed claim (2)

PAPER (printed p. 22):

> **(2) If there is a branch `B` of `H` such that every edge in `X` has at least one end in
> `V(B)` then the theorem holds.**
>
> For suppose there is such a branch `B`, and let `C ⊆ B` be a track, minimal such that every
> edge in `X` has an end in `V(C)`.  By (1) we may assume that `C` has length `≥ 1`.  Let
> `c₁, c₂` be the ends of `C`.  For `i = 1, 2` let `Aᵢ` be the set of edges in `δ(cᵢ)` that are
> in `X` and not in `C`; and let `Bᵢ` be the set of edges in `δ(cᵢ)` that are not in `X` and
> not in `C`.  From the minimality of `C`, it follows that `A₁, A₂` are both nonempty.
>
> Suppose first that `c₁, c₂` have the same biparity. … [track-parity contradiction, using
> cyclic 3-connectivity, the simplicity of `J`, and three paths `P₁, P₂, P₃` from a fourth
> branch-vertex `b`] …
>
> We may assume therefore that `c₁, c₂` have different biparity.  It follows that no vertex of
> `V(H)` is incident with all edges in `A₁ ∪ A₂`.  Let `H'` be the graph obtained from `H` by
> deleting the internal vertices and edges of `C`.  There is no track `T` in `H'` with first
> edge in `A₁`, second edge in `B₁` (and hence second vertex `c₁`), last vertex `c₂` and last
> edge in `A₂`; … A similar statement holds with `c₁, c₂` exchanged.  By 5.6 applied to `H'`,
> it follows that `B₁ ∪ B₂ = ∅`, and so one of statements 3,4,5 of the theorem holds.  This
> proves (2).

The hypothesis `hdisj` is the standing assumption granted by claim (1) (the printed *"By (1) we
may assume that `C` has length `≥ 1`"*): if `X` has no two disjoint edges, `Thm57Claim1`
already gives the conclusion, so this carve-out is only ever invoked with it available.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup
open Workspace.ProofLemmas.Thm57Claim2Window

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **5.7 (2)** — if some branch of `H` meets every edge of `X`, the theorem holds. -/
theorem thm57Claim2 (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) (hdisj : TwoDisjointEdges H X)
    (hB : SomeBranchMeetsAll H X) :
    Concl57 H X := by
  classical
  obtain ⟨B, i, j, hi, hj, hbranch, hij, hmeet, hA₁, hA₂, hmin⟩ :=
    exists_minimal_window H X hXE hdisj hB
  have houtside : X \ trackEdges (Workspace.ProofLemmas.TrackSlice.slice B i j) ⊆
      incidentEdges H B[i] ∪ incidentEdges H B[j] :=
    Workspace.ProofLemmas.Thm57Claim2Structure.edges_outside_window_meet_an_end
      H X hXE hbranch hij hj hmeet
  rcases Workspace.ProofLemmas.Thm57Claim2Parity.same_or_different_biparity
      H hbip B[i] B[j] with hsame | hdiff
  · exact (Workspace.ProofLemmas.Thm57Claim2Parity.same_biparity_impossible
      H hc3 X hXE hnotrack hdisj hbranch hij hj hA₁ hA₂ houtside hsame).elim
  · have hempty := Workspace.ProofLemmas.Thm57Claim2Parity.different_biparity_exhaustion
      H hbip hc3 X hXE hnotrack hbranch hij hj hA₁ hA₂ houtside hdiff
    rcases Workspace.ProofLemmas.Thm57Claim2Structure.classify_after_exhaustion
        H X hbranch hij hj hdiff houtside hempty with h₃ | h₄ | h₅
    · exact Or.inr (Or.inr (Or.inl h₃))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h₄)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₅))))

end Workspace.ProofLemmas.Thm57Claim2
