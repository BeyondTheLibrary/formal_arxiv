import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.Statements.S22.Thm_22_5
import Workspace.ProofLemmas.KiteTailBasics

/-!
# 23.2 step (2) — *"`y` is not adjacent to both `x₀`, `x₁`"*

PAPER (23.2, printed p. 139):

> *"Let `A₀ = V(C) \ {z, x₀, x₁}`.  Since `G` does not admit a skew partition, there is a path
> `T` of `G \ {x₀,x₁}` from `z` to `A₀`, such that no vertex in its interior is in `Y` or
> `Y`-complete.  Let `y` be the neighbour of `z` in `T`.*
>
> ***(2) `y` is not adjacent to both `x₀`, `x₁`.***
>
> *For assume it is.  By 22.3 there is no kite for `(C,Y)`, and with respect to the wheel
> `(C,Y)`, `T` is a tail for `z` (because at least one of the `Y`-complete edges `c₁c₂`,
> `c₂c₃` belongs to `C \ {x₀,z,x₁}`).  This contradicts 22.5, and therefore proves (2)."*

The hypotheses below are exactly the clauses of `Workspace.Types.WheelSystems.SPGT.IsTail`
other than *"the neighbour of `z` in `T` is adjacent to `x₀,x₁`"* — which is the assumption
the paper refutes — and the parenthetical *"because at least one of the `Y`-complete edges
`c₁c₂`, `c₂c₃` belongs to `C \ {x₀,z,x₁}`"*, which is the hypothesis `hedge`.

The paper's appeal to **22.3** (*"there is no kite for `(C,Y)`"*) is invisible here: the
*published* definition of a tail — the one `IsTail` transcribes — no longer carries the
no-kite clause the arXiv draft folded into it, and the published 22.5 correspondingly needs
no such hypothesis.  See the discussion in `Workspace.Types.WheelSystems` and in
`KiteTailBasics`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232NoDoubleNeighbour

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (23.2, printed p. 139), step (2):** *"`y` is not adjacent to both `x₀`, `x₁`."*

`T = z :: y :: R` is the path of `G \ {x₀,x₁}` from `z` to `A₀ = V(C) \ {z,x₀,x₁}` produced by
the previous sentence, and `y` is the neighbour of `z` on it.  Were `y` adjacent to both `x₀`
and `x₁`, `T` would be a tail for `z` with respect to `(C,Y)`, contrary to 22.5. -/
theorem not_adj_both (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (z x₀ x₁ y : V) (T R : List V)
    (hz : z ∈ C) (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hc0 : VertexComplete G x₀ Y) (hcz : VertexComplete G z Y)
    (hc1 : VertexComplete G x₁ Y)
    (hedge : ∃ u v : V, u ∈ C ∧ v ∈ C ∧
      (u ≠ x₀ ∧ u ≠ z ∧ u ≠ x₁) ∧ (v ≠ x₀ ∧ v ≠ z ∧ v ≠ x₁) ∧ EdgeComplete G Y u v)
    (hTeq : T = z :: y :: R)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hend : ∃ w : V, IsPathFrom G T z w ∧ w ∈ C ∧ w ≠ z ∧ w ≠ x₀ ∧ w ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y) :
    ¬ (G.Adj y x₀ ∧ G.Adj y x₁) := by
  rintro ⟨hy0, hy1⟩
  -- "with respect to the wheel `(C,Y)`, `T` is a tail for `z`"
  have htail : IsTail G C Y z x₀ x₁ T :=
    KiteTailBasics.isTail_mk hopt.1 hz hnb havoid hend hc0 hcz hc1 hedge
      ⟨y, R, hTeq, hy0, hy1⟩ hint
  -- "This contradicts 22.5."
  exact _root_.Workspace.Statements.S22.SPGT.thm_22_5 G hG hbsp C Y hopt z hz
    ⟨x₀, x₁, T, htail⟩

end Workspace.ProofLemmas.Thm232NoDoubleNeighbour
