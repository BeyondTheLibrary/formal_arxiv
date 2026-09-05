import Mathlib
import Workspace.Types.Tracks
import Workspace.PriorWork.DiracK4Subdivision
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.SubdivisionDatumRealize
import Workspace.ProofLemmas.Thm53Assembly

/-!
# Step 1 of 5.3: *"There is a subgraph of `H` which is a subdivision of `K₄`"*

The opening sentence of the printed proof of 5.3 (`paper/proofs/5_3.md`, published page 19) is
asserted with no proof and no citation.  It is Dirac's theorem — *every graph of minimum degree
`≥ 3` contains a subdivision of `K₄`* — but it cannot be applied to `H` directly: `H` is a
subdivision, so the internal vertices of its tracks have degree exactly `2`.  It must be applied
to the 3-connected graph `J` that `H` subdivides, and the resulting `K₄`-subdivision then has to
be pushed back up through `IsSubdivision J H`.

That push-up is what the `K₄`-subdivision *datum* of `Workspace.ProofLemmas.SubdivisionDatum`
exists for — the six *local* clauses of `IsSubdivision (⊤ : SimpleGraph (Fin 4)) _`, dropping the
two *exactness* clauses (cover, edge-set), which are exactly the clauses that break under
composition.  The chain is

```
Dirac(J)                                              ∃ SJ : J.Subgraph, IsSubdivision K₄ SJ.coe
  → (A) SubdivisionDatum.hasK4Datum_of_subgraph_subdivision        HasK4Datum J
  → (C) SubdivisionCompose.hasK4Datum_of_subdivision               HasK4Datum H
  → (B) SubdivisionDatumRealize.exists_subgraph_isSubdivision_of_hasK4Datum
                                                      ∃ S : H.Subgraph, IsSubdivision K₄ S.coe
```

and the last line is `Thm53Assembly.HasK4SubdivisionSubgraph H`.

`CyclicallyThreeConnected H` unfolds to `∃ n J, IsKConnected J 3 ∧ IsSubdivision J H`, which
supplies both of Dirac's hypotheses: `Nonempty (Fin n)` from the `3 < Fintype.card` clause of
`IsKConnected` (the `[Nonempty U]` on the axiom is load-bearing, not decoration — at `U := Empty`
the degree hypothesis is vacuous and the conclusion false), and the minimum-degree bound from
`SubdivisionCounting.three_le_degree_of_three_connected`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm53Step1

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-- **Step 1 of 5.3.**  A cyclically 3-connected graph has a subgraph which is a subdivision of
`K₄`.

This discharges `Workspace.ProofLemmas.Thm53Assembly.HasK4SubdivisionSubgraph`, the first of the
three `def`-wrapped hypotheses of `Thm53Assembly.thm_5_3_of_steps`.  Note that no bipartiteness
hypothesis is needed: the printed sentence uses only cyclic 3-connectivity. -/
theorem hasK4SubdivisionSubgraph_of_cyclicallyThreeConnected {W : Type*} (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) : Thm53Assembly.HasK4SubdivisionSubgraph H := by
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  -- `IsKConnected J 3` has `3 < Fintype.card (Fin n)` as its first clause, so `Fin n` is nonempty.
  haveI : Nonempty (Fin n) := by
    have h := hJ.1
    rw [Fintype.card_fin] at h
    exact ⟨⟨0, by omega⟩⟩
  -- Dirac, applied to `J` — never to `H`.
  obtain ⟨SJ, hSJ⟩ :=
    _root_.Workspace.PriorWork.DiracK4Subdivision.exists_k4_subdivision_subgraph_of_min_degree_three
      J (fun v => SubdivisionCounting.three_le_degree_of_three_connected J hJ v)
  -- (A) → (C) → (B).
  exact SubdivisionDatumRealize.exists_subgraph_isSubdivision_of_hasK4Datum
    (SubdivisionCompose.hasK4Datum_of_subdivision
      (SubdivisionDatum.hasK4Datum_of_subgraph_subdivision SJ hSJ) hsub)

end Workspace.ProofLemmas.Thm53Step1
