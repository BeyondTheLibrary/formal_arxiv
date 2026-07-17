import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.Types.EdgeColouring
import Workspace.Types.LocalOrdering
import Workspace.Types.LocalShift
import Workspace.Types.TwoElementAssignment
import Workspace.Types.SystemL
import Workspace.PriorWork
import Workspace.Facts.Lemma21
import Workspace.Facts.Construction
import Workspace.Facts.Duality

/-!
# The Cycle Double Cover Conjecture — main theorem

This file states `theorem_1_1`, the main result of *"A Proof of the Cycle Double Cover
Conjecture"*: every finite bridgeless undirected graph has a cycle double cover. The
supporting results live in the imported files — the prior work invoked
(`Workspace.PriorWork`), the facts inside the proof of Lemma 2.1 (`Workspace.Facts.Lemma21`),
the construction of the palettes `P_e` (`Workspace.Facts.Construction`) and the duality
argument proving Lemma 2.2 (`Workspace.Facts.Duality`).

`theorem_1_1_cubic_case` (the loopless cubic case) is the paper's own content and is
genuinely proved here via `cubic_case_aux`; `theorem_1_1_of_cubic_case` is Jaeger's
reduction (`Workspace.PriorWork.jaeger_cubic_reduction`) and merely cites it.

`G : Graph α β` is a multigraph — parallel edges and loops are both allowed — and the theorem
assumes only finiteness and bridgelessness. `HasCycleDoubleCover` asks for a *multiset* of
cycles covering every edge exactly twice with multiplicity. Every statement carries both
`V(G).Finite` and `E(G).Finite`, both load-bearing on this project's `finsum`/`ncard`-based
definitions (and `E(G).Finite` does not follow from `V(G).Finite`, since parallel edges are
allowed).
-/

open Graph
open scoped Graph
open Workspace.Types.Gamma Workspace.Types.Orientation
open Workspace.Types.LocalOrdering Workspace.Types.LocalShift Workspace.Types.SystemL

namespace Workspace.MainTheorem

variable {α β : Type*} {G : Graph α β} {P : β → Set Gamma} {v : α}

/-- Auxiliary proof of the loopless cubic case (paper §2 / Fact 5d), shared by
`theorem_1_1` and `theorem_1_1_cubic_case`. -/
private theorem cubic_case_aux (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hloop : G.IsLoopless) (hcubic : G.IsCubic) (hbr : G.Bridgeless) :
    G.HasCycleDoubleCover := by
  classical
  rcases Set.eq_empty_or_nonempty (V(G)) with hVe | ⟨v₀, hv₀⟩
  · have hEempty : E(G) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
      have hx := hxy.left_mem
      rw [hVe] at hx
      exact absurd hx (Set.notMem_empty x)
    exact (Graph.isCycleDoubleCover_zero_iff.2 hEempty).hasCycleDoubleCover
  · haveI : Nonempty α := ⟨v₀⟩
    haveI : Nonempty β := nonempty_edgeType_of_isCubic hcubic hv₀
    obtain ⟨O⟩ := Orientation.exists_orientation G
    obtain ⟨ord⟩ := exists_localOrdering hloop hcubic
    obtain ⟨f, hf, hnz⟩ :=
      Workspace.PriorWork.kilpatrick_jaeger_nowhere_zero_gamma_flow G hV hE hbr O
    let S : LocalShift G := ⟨f, ord⟩
    have hSflow : S.flow = f := rfl
    have hfS : G.IsFlow O S.flow := by rw [hSflow]; exact hf
    have hnzS : G.IsNowhereZero S.flow := by rw [hSflow]; exact hnz
    have hsol := Workspace.Facts.Duality.lemma_2_2 hV hE hloop hcubic O S hfS hnzS
    rw [SystemL.hasSolution_def] at hsol
    obtain ⟨t, ε, hEq⟩ := hsol
    have h4 : ∀ e ∈ E(G), ∀ u w, G.IsLink e u w →
        t u + t w + ε e • S.flow e = S.d e := by
      intro e he u w huw
      have hne : u ≠ w := (Graph.isLoopless_iff_forall_isLink_ne.1 hloop) e u w huw
      have key := hEq e he
      rw [LocalShift.setOf_inc_eq_pair huw, finsum_mem_pair hne,
        SystemL.ofLocalShift_flow, SystemL.ofLocalShift_rhs] at key
      exact key
    obtain ⟨-, hP_build⟩ :=
      Workspace.Facts.Construction.fact_5d hV hE hloop hcubic O S hfS hnzS t ε h4
    let Pfun : β → Set Gamma := fun e =>
      if he : e ∈ E(G) then
        {t (Graph.exists_isLink_of_mem_edgeSet he).choose
            + S.g (Graph.exists_isLink_of_mem_edgeSet he).choose e,
          t (Graph.exists_isLink_of_mem_edgeSet he).choose
            + S.g (Graph.exists_isLink_of_mem_edgeSet he).choose e + S.flow e}
      else ∅
    have hPspec : ∀ e ∈ E(G), ∃ z, G.Inc e z ∧
        Pfun e = {t z + S.g z e, t z + S.g z e + S.flow e} := by
      intro e he
      refine ⟨(Graph.exists_isLink_of_mem_edgeSet he).choose, ?_, ?_⟩
      · exact (Graph.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec.inc_left
      · simp only [Pfun, dif_pos he]
    have hP : G.IsTwoElementAssignment Pfun := hP_build Pfun hPspec
    exact Workspace.Facts.Lemma21.lemma_2_1 hV hE hloop hcubic hP

/-! ## Theorem 1.1 — the main theorem -/

/-- **Theorem 1.1.** Every finite bridgeless undirected graph has a cycle double cover.

`G` is a multigraph (parallel edges and loops both allowed); no looplessness or cubicness is
assumed, since the reduction to the loopless cubic case is a step of the proof
(`Workspace.PriorWork.jaeger_cubic_reduction`). `G.Bridgeless` says no edge is a bridge, and
`G.HasCycleDoubleCover` asks for a multiset of cycles containing every edge exactly twice
with multiplicity. -/
theorem theorem_1_1 (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : G.Bridgeless) :
    G.HasCycleDoubleCover := by
  exact Workspace.PriorWork.jaeger_cubic_reduction
    (fun α β G hV hE hloop hcubic hbr => cubic_case_aux G hV hE hloop hcubic hbr)
    α β G hV hE hG

/-! ## The loopless cubic case, and the reduction to it -/

/-- **Theorem 1.1, the loopless cubic case** — the content the paper actually proves.

Every finite bridgeless loopless cubic multigraph has a cycle double cover. Paper §5's
Fact 5d assembles it from `Workspace.Facts.Duality.lemma_2_2` (a solution `(t, ε)` of the
system (4), hence palettes `P_e` satisfying condition (1)) via
`Workspace.Facts.Lemma21.lemma_2_1`, with the nowhere-zero `Γ`-flow supplied by
`Workspace.PriorWork.kilpatrick_jaeger_nowhere_zero_gamma_flow`.

This is strictly weaker than `theorem_1_1` (it carries the extra `hloop`, `hcubic`) and is
not a substitute for it: it is the paper's own content, proved here rather than admitted. -/
theorem theorem_1_1_cubic_case (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hloop : G.IsLoopless) (hcubic : G.IsCubic) (hbr : G.Bridgeless) :
    G.HasCycleDoubleCover := by
  exact cubic_case_aux G hV hE hloop hcubic hbr

/-- **Theorem 1.1 follows from the loopless cubic case** — Jaeger's reduction [3, Prop. 4].

If every finite bridgeless loopless cubic multigraph has a cycle double cover, then so does
every finite bridgeless multigraph. The hypothesis `H` is universally quantified over **all**
vertex and edge types in the ambient universes, not merely over those of the conclusion's
graph: Jaeger's reduction replaces each vertex by a gadget, so the cubic graph it produces
lives on a larger type. Discharged by `Workspace.PriorWork.jaeger_cubic_reduction`. -/
theorem theorem_1_1_of_cubic_case.{u, v}
    (H : ∀ (α : Type u) (β : Type v) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.IsLoopless → G.IsCubic → G.Bridgeless →
        G.HasCycleDoubleCover) :
    ∀ (α : Type u) (β : Type v) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.Bridgeless → G.HasCycleDoubleCover := by
  exact Workspace.PriorWork.jaeger_cubic_reduction H

end Workspace.MainTheorem
