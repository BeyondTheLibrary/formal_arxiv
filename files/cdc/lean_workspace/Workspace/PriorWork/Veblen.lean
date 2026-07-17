import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover

/-!
# Prior-work black box: Veblen's cycle decomposition (general even case)

The admitted prior-work `axiom` for Veblen's cycle decomposition, referencing only the
accepted `Types`.

> **(Veblen 1912, folklore).** Every finite graph in which every vertex has even degree is
> an edge-disjoint union of cycles.

The `{0,2}`-degree special case is proved as
`Workspace.Facts.Lemma21.fact_2_1b_decomposition`; the general even case is strictly stronger
and is admitted here.
-/

open scoped Graph

namespace Workspace.PriorWork

/-- **E2 — Veblen's cycle decomposition (general even case).**

A finite graph `K` in which every vertex has even degree decomposes into an edge-disjoint
family of cycles: there is a multiset `D` of cycles of `K` in which every edge of `K` occurs
exactly once. (The `{0,2}`-degree special case is proved as
`Workspace.Facts.Lemma21.fact_2_1b_decomposition`; this is the strictly stronger statement
allowing higher even degrees.)

Admitted from Veblen (1912) / folklore; see the module docstring. -/
axiom veblen_even_decomposition {α β : Type*} (K : Graph α β)
    (hV : V(K).Finite) (hE : E(K).Finite) (hloop : K.IsLoopless)
    (hdeg : ∀ x ∈ V(K), Even (K.degree x)) :
    ∃ D : Multiset (Graph α β), (∀ C ∈ D, K.IsCycle C) ∧
      ∀ e ∈ E(K), D.edgeMultiplicity e = 1

end Workspace.PriorWork
