import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.PriorWorkProofs.Tutte.Main
import Workspace.PriorWorkProofs.EightFlow.Reduction
import Workspace.PriorWorkProofs.Jaeger.Reduction

/-!
# Prior work invoked by the proof of the Cycle Double Cover Conjecture

The three results from the literature that *"A Proof of the Cycle Double Cover Conjecture"*
cites and uses as black boxes:

* `jaeger_cubic_reduction` — Jaeger [3, Proposition 4]: it suffices to treat loopless
  cubic graphs;
* `kilpatrick_jaeger_nowhere_zero_gamma_flow` — Kilpatrick [5], Jaeger [4]: the 8-flow
  theorem, i.e. every finite bridgeless graph has a nowhere-zero `Γ`-flow (`Γ = 𝔽₂³`);
* `tutte_group_flow` — Tutte [9]: for a finite abelian group `A` of order `k`, a graph has a
  nowhere-zero `A`-flow iff it has a nowhere-zero integer `k`-flow, with the corollary
  `tutte_gamma_flow_iff_integer_eight_flow` the paper uses (`A = Γ`, `k = 8`).

Each statement carries both `V(G).Finite` and `E(G).Finite`, both load-bearing on this
project's `finsum`/`ncard`-based definitions.
-/

open Graph
open scoped Graph
open Workspace.Types.Gamma Workspace.Types.Orientation

namespace Workspace.PriorWork

/-! ## Prior work A — reduction to the loopless cubic case -/

/-- **Prior work A (Jaeger [3, Proposition 4]) — reduction to the loopless cubic case.**

> In order to prove Theorem 1.1 it suffices to treat **loopless cubic** graphs: if every
> finite bridgeless loopless cubic multigraph has a cycle double cover, then every finite
> bridgeless multigraph has a cycle double cover.

The hypothesis quantifies over **all** vertex and edge types in the ambient universes,
not merely over the vertex and edge types of the graph in the conclusion: the reduction
replaces each vertex by a small gadget and so produces a cubic graph on a larger vertex
and edge type. Both statements are universally quantified over graphs, so this theorem
is an implication between two `∀`-statements. -/
theorem jaeger_cubic_reduction.{u, v}
    (H : ∀ (α : Type u) (β : Type v) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.IsLoopless → G.IsCubic → G.Bridgeless →
        G.HasCycleDoubleCover) :
    ∀ (α : Type u) (β : Type v) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.Bridgeless → G.HasCycleDoubleCover :=
  Workspace.PriorWorkProofs.Jaeger.jaeger_cubic_reduction_proof H

/-! ## Prior work B — the 8-flow theorem -/

/-- **Prior work B (Kilpatrick [5]; Jaeger [4]) — the 8-flow theorem.**

> Every finite bridgeless graph has a nowhere-zero `Γ`-flow, where `Γ = 𝔽₂³`.

Being a flow is a property relative to an orientation `O` of `G`; the statement is given
for an arbitrary orientation.

Proved (not admitted) as `Workspace.PriorWorkProofs.EightFlow.bridgeless_gamma_flow`; the only
admission on that path is `Workspace.PriorWork.nash_williams_three_edge_disjoint_spanning_trees`. -/
theorem kilpatrick_jaeger_nowhere_zero_gamma_flow {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (hG : G.Bridgeless) (O : Orientation G) :
    ∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f :=
  Workspace.PriorWorkProofs.EightFlow.bridgeless_gamma_flow G hV hE hG O

/-! ## Prior work C — Tutte's group-flow theorem -/

/-- **Prior work C (Tutte's group-flow theorem [9]).**

> For a finite abelian group `A` of order `k`, a graph has a nowhere-zero `A`-flow if and
> only if it has a nowhere-zero integer `k`-flow.

Here `Graph.IsIntegerKFlow O φ k` already builds in nowhere-zeroness, since it demands
`0 < |φ e| < k` on every edge of `G`. -/
theorem tutte_group_flow {α β : Type*} {A : Type*} [AddCommGroup A] [Finite A] {k : ℕ}
    (hA : Nat.card A = k) (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (O : Orientation G) :
    (∃ f : β → A, G.IsFlow O f ∧ G.IsNowhereZero f) ↔
      (∃ φ : β → ℤ, G.IsIntegerKFlow O φ (k : ℤ)) :=
  Workspace.PriorWorkProofs.Tutte.tutte_group_flow_proved hA G hV hE O

/-- **Prior work C, the corollary the paper actually uses** (Tutte [9], with `A = Γ` and
`k = |Γ| = 8`).

> In particular (with `A = Γ`, `k = 8`), a graph has a nowhere-zero `Γ`-flow if and only
> if it has a nowhere-zero integer `8`-flow. -/
theorem tutte_gamma_flow_iff_integer_eight_flow {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (O : Orientation G) :
    (∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f) ↔
      (∃ φ : β → ℤ, G.IsIntegerKFlow O φ 8) :=
  Workspace.PriorWorkProofs.Tutte.tutte_gamma_flow_iff_integer_eight_flow_proved G hV hE O

end Workspace.PriorWork
