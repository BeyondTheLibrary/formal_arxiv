import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.CubeExtraction
import Workspace.ProofLemmas.CubeAssembly

/-!
# 14.3

PAPER (printed p. 91):

> *"Proof.  We may assume that `G, Ḡ` do not admit proper 2-joins, and `G` does not admit a
> balanced skew partition.  Suppose for a contradiction that `G` contains a double diamond; then
> it contains a cube, and so there is a maximal cube `(A, B, C, D)` in `G`, forming `K`.  Let `F`
> be the set of all minor vertices in `V(G) \ V(K)`, and `Y` the set of all major ones. … Hence
> there is no such graph `G`.  This proves 14.3."*

The four printed claims and the two closing constructions live in
`Workspace.ProofLemmas.Cube*`; `CubeAssembly.cube_main` is everything from *"Let `F` be the set
of all minor vertices"* to the end.  What is left here is the first two sentences: negate the
conclusion to get the three *"we may assume"* hypotheses, then extract a cube from the double
diamond and enlarge it to a maximal one.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.Statements.S14

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **14.3** (printed p. 91), introduced by *"The main result of this section is 1.8.6, which
we restate, the following:"*

PAPER: *"Let `G ∈ F₅`.  If `G` contains a double diamond as an induced subgraph, then either
one of `G, Ḡ` admits a proper 2-join, or `G` admits a balanced skew partition.  In particular,
every recalcitrant graph belongs to `F₆`."*

This is one of the twelve main steps of the proof of 1.3: it discharges 1.8.6.

Notes on the transcription.

* This is the **published** form: *"one of `G, Ḡ` admits a **proper** 2-join"* (the arXiv
  draft says *"a 2-join"*).
* A double diamond is the eight-vertex graph of printed p. 87; *"`G` contains a double diamond
  as an induced subgraph"* is the existence of eight vertices of `G` realising exactly that
  adjacency pattern (`IsDoubleDiamond`).
* The final sentence *"In particular, every recalcitrant graph belongs to `F₆`"* is genuine
  mathematical content — unlike the *"In particular, 1.8.k holds"* sentences elsewhere in the
  paper, which merely name a step of the outline — so it is formalized too, but **not** here:
  it speaks about **all** graphs, not about `G`, and the paper asserts it outright, so making
  it a conjunct under this theorem's hypotheses (`G ∈ F₅` and `G` contains a double diamond)
  would assert it only if those hypotheses are satisfiable.  It is therefore the separate,
  hypothesis-free theorem `thm_14_3_recalcitrant` below. -/
theorem thm_14_3 (G : SimpleGraph V) (hG : InF5 G)
    (hdd : ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V, IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄) :
    (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨ AdmitsBalancedSkewPartition G := by
  classical
  by_contra hcon
  -- *"We may assume that `G, Ḡ` do not admit proper 2-joins, and `G` does not admit a balanced
  -- skew partition."*
  have h2G : ¬ AdmitsProper2Join G := fun h => hcon (Or.inl (Or.inl h))
  have h2Gc : ¬ AdmitsProper2Join Gᶜ := fun h => hcon (Or.inl (Or.inr h))
  have hno : ¬ AdmitsBalancedSkewPartition G := fun h => hcon (Or.inr h)
  -- *"Suppose for a contradiction that `G` contains a double diamond; then it contains a cube,
  -- and so there is a maximal cube `(A, B, C, D)` in `G`, forming `K`."*
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, hdd'⟩ := hdd
  obtain ⟨A, B, C, D, hcube⟩ :=
    _root_.Workspace.ProofLemmas.CubeExtraction.exists_maximalCube G
      ⟨_, _, _, _, _root_.Workspace.ProofLemmas.CubeExtraction.isCube_of_doubleDiamond hdd'⟩
  -- *"… Hence there is no such graph `G`.  This proves 14.3."*
  exact _root_.Workspace.ProofLemmas.CubeAssembly.cube_main hG h2G h2Gc hno hcube


end SPGT

end Workspace.Statements.S14
