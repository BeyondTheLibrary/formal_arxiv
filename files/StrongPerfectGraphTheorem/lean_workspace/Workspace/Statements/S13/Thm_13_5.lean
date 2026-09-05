/-  Proof attempt 1 for statement 13.5 (`Workspace.Statements.S13.SPGT.thm_13_5`).

    The paper's proof of 13.5 is printed at the head of §24 (printed p. 145):

      "We recall that we are trying to prove 13.5.  In view of 23.5, it suffices to show
       the following, which is 1.8.12, and the objective of the remainder of the paper:
       24.1  Let G ∈ F₁₁; then either G is complete, or G is bipartite, or G admits a
       balanced skew partition."

    So the argument is exactly: 23.5 (in its "in particular" form, `thm_23_5_recalcitrant`:
    for every recalcitrant `G`, one of `G, Ḡ` lies in `F₁₁`), followed by 24.1 applied to
    whichever of `G, Ḡ` lies in `F₁₁`.  In each case 24.1's third alternative is killed by
    the last bullet of *recalcitrant* (`G` admits no balanced skew partition) — for `Ḡ`
    via `admitsBalancedSkewPartition_compl` — its second alternative is one of the two
    disjuncts of the goal, and its first alternative ("complete") forces the complement to
    have no edges at all, hence to be 2-colourable, which is the other disjunct.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.Statements.S23.Thm_23_5_recalcitrant
import Workspace.Statements.S24.Thm_24_1
import Workspace.ProofLemmas.ClassLemmas

set_option autoImplicit false

namespace Workspace.Statements.S13

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

namespace SPGT

/-- A graph with no edges at all is 2-colourable, hence bipartite.  (Used twice below:
`G` complete makes `Ḡ` edgeless, and `Ḡ` complete makes `G` edgeless.) -/
private theorem bipartite_of_no_adj {W : Type*} {H : SimpleGraph W}
    (h : ∀ u v : W, ¬ H.Adj u v) : H.IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) fun {u v} hadj => absurd hadj (h u v)⟩

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **13.5** (printed p. 86), introduced by *"The remainder of the paper is basically a proof
of the following."*

PAPER: *"If `G` is recalcitrant then either `G` or `Ḡ` is bipartite."*

Followed by *"Clearly any counterexample to 1.3 is recalcitrant, so 13.5 will imply 1.3."*
*Recalcitrant* is the four-bullet notion defined immediately before the statement and
transcribed in `Workspace.Types.LongOddPrism`; *bipartite* is Mathlib's
`SimpleGraph.IsBipartite`, and the paper's `Ḡ` is `Gᶜ`. -/
theorem thm_13_5 (G : SimpleGraph V) (hG : Recalcitrant G) :
    G.IsBipartite ∨ Gᶜ.IsBipartite := by
  -- The last bullet of *recalcitrant*: `G` admits no balanced skew partition.
  have hbsp : ¬ AdmitsBalancedSkewPartition G := hG.2.2.2.2
  -- "In view of 23.5": one of `G, Ḡ` belongs to `F₁₁`.
  rcases _root_.Workspace.Statements.S23.SPGT.thm_23_5_recalcitrant G hG with h11 | h11
  · -- `G ∈ F₁₁`; apply 24.1 to `G`.
    rcases _root_.Workspace.Statements.S24.SPGT.thm_24_1 G h11 with hcomp | hbip | hskew
    · -- `G` complete, so `Ḡ` has no edges and is therefore bipartite.
      refine Or.inr (bipartite_of_no_adj ?_)
      intro u v huv
      rw [SimpleGraph.compl_adj] at huv
      exact huv.2 (hcomp u v huv.1)
    · exact Or.inl hbip
    · exact absurd hskew hbsp
  · -- `Ḡ ∈ F₁₁`; apply 24.1 to `Ḡ`.
    rcases _root_.Workspace.Statements.S24.SPGT.thm_24_1 Gᶜ h11 with hcomp | hbip | hskew
    · -- `Ḡ` complete, so `G` has no edges and is therefore bipartite.
      refine Or.inl (bipartite_of_no_adj ?_)
      intro u v huv
      have hcv : Gᶜ.Adj u v := hcomp u v (G.ne_of_adj huv)
      rw [SimpleGraph.compl_adj] at hcv
      exact hcv.2 huv
    · exact Or.inr hbip
    · exact absurd
        (_root_.Workspace.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp hskew)
        hbsp


end SPGT

end Workspace.Statements.S13
