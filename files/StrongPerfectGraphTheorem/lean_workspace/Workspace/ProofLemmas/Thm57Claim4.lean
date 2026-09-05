import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim3
import Workspace.ProofLemmas.Thm57Claim4Core
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# 5.7, printed claim (4)

PAPER (printed p. 24):

> **(4) There do not exist a connected subgraph `A` of `H\X` and three mutually disjoint edges
> `x₁, x₂, x₃ ∈ X` such that each `xᵢ` has at least one end in `V(A)`.**
>
> For suppose such `A, x₁, x₂, x₃` exist.  We may assume `A` is a maximal connected subgraph of
> `H \ X`.  For `1 ≤ i ≤ 3` let `xᵢ` have ends `aᵢ, bᵢ`, where `a₁, a₂, a₃` have the same
> biparity.  Let `K` be the graph with vertex set `{a₁,a₂,a₃,b₁,b₂,b₃}`, in which two vertices
> of `K` are adjacent if there is a track in `A` joining them not using any other vertex of
> `K`. … [`a₁,a₂,a₃` pairwise nonadjacent in `K` by the no-even-track hypothesis, likewise
> `b₁,b₂,b₃`; by (3), `a₃` is not adjacent in `K` to both `b₁` and `b₂`, and five similar
> statements; then the maximal connected `S ⊆ A` containing the interior of `P₃`, cyclic
> 3-connectivity of `H`, and a final application of (3)] … This proves (4).

Encoding notes.

* `H \ X` is `H.deleteEdges X`.  *"connected subgraph `A`"* is rendered by its vertex set
  together with `Core.ConnectedSet (H.deleteEdges X) A`: a connected subgraph on vertex set `S`
  makes the induced subgraph on `S` connected, so the non-existence statement below is the one
  the paper needs (and is formally the stronger of the two readings).
* *"mutually disjoint"* is `Tracks.DisjointEdges` pairwise, *"has at least one end in `V(A)`"*
  is `∃ v ∈ A, v ∈ xᵢ`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **5.7 (4)** — no connected subgraph of `H \ X` meets three mutually disjoint edges of
`X`. -/
theorem thm57Claim4 (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) :
    ¬ ∃ (A : Set W) (x₁ x₂ x₃ : Sym2 W),
      ConnectedSet (H.deleteEdges X) A ∧
      x₁ ∈ X ∧ x₂ ∈ X ∧ x₃ ∈ X ∧
      DisjointEdges x₁ x₂ ∧ DisjointEdges x₁ x₃ ∧ DisjointEdges x₂ x₃ ∧
      (∃ v ∈ A, v ∈ x₁) ∧ (∃ v ∈ A, v ∈ x₂) ∧ (∃ v ∈ A, v ∈ x₃) := by
  classical
  rintro ⟨A, x₁, x₂, x₃, hconn, hx₁, hx₂, hx₃, hd₁₂, hd₁₃, hd₂₃,
    hm₁, hm₂, hm₃⟩
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  let x : Fin 3 → Sym2 W := ![x₁, x₂, x₃]
  have hxX : ∀ i, x i ∈ X := by
    intro i
    fin_cases i <;> simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> assumption
  have hsym : ∀ {e f : Sym2 W}, DisjointEdges e f → DisjointEdges f e := by
    intro e f h w hw
    exact h w ⟨hw.2, hw.1⟩
  have hdisj : ∀ i j, i ≠ j → DisjointEdges (x i) (x j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hij ⊢
    all_goals first | contradiction | assumption | apply hsym <;> assumption
  have hmeet : ∀ i, ∃ v ∈ A, v ∈ x i := by
    intro i
    fin_cases i <;> simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> assumption
  have hpair : ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      Workspace.ProofLemmas.Thm57Claim4Core.EndpointCleanConnection
        H X (x i) (x j) u v P → col u ≠ col v := by
    intro i j hij u v P hu hv hP
    exact Workspace.ProofLemmas.Thm57Claim4Core.endpointCleanConnection_different_color
      H X hXE hnotrack col (hxX i) (hxX j) (hdisj i j hij) hu hv hP
  have hinternal : ∃ i, ∀ v ∈ x i, v ∈ A :=
    Workspace.ProofLemmas.Thm57Claim4Core.some_marked_edge_internal
      H X col x A hconn (fun i => hXE (hxX i)) hdisj hmeet hpair
  exact Workspace.ProofLemmas.Thm57Claim4Core.sixTerminalCore
    H hc3 X col x A hconn hxX (fun i => hXE (hxX i)) hdisj hmeet hinternal hpair
      (Workspace.ProofLemmas.Thm57Claim3.thm57Claim3 H X hnotrack)

end Workspace.ProofLemmas.Thm57Claim4
