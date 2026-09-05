import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge

/-!
# A minimum imperfect graph cannot be `ω`-coloured

Item P7 of the proof of 1.5.  The printed text says only

> *"Since `G` is minimum imperfect it cannot be `t`-coloured"*

where `t = ω(A ∪ B)`.  This module spells that out.  `G` is not perfect (P1), so
some `X` has `χ(G|X) ≠ ω(G|X)`; if `X ≠ V(G)` then `G|X` is perfect by
`SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ` and
`CliqueNumOfInducedSet.chromaticNumber_eq_cliqueNum_of_isPerfect` gives equality, a
contradiction.  So the defect occurs at `X = V(G)`, i.e. `χ(G) ≠ ω(G)` (transport
along `SimpleGraph.induceUnivIso`), and `SimpleGraph.cliqueNum_le_chromaticNumber`
upgrades that to `ω(G) < χ(G)`.

The caller obtains the paper's `t = ω(A ∪ B) = ω(G)` from `A ∪ B = V(G)` together
with `SimpleGraph.induceUnivIso` and `IsoTransport.cliqueNum_iso`.

Used at P7 and at the final contradiction of §6.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

/-- A minimum imperfect graph has no proper colouring with `ω(G)` colours. -/
theorem not_colorable_cliqueNum {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : MinimumImperfect G) :
    ¬ G.Colorable G.cliqueNum := by
  classical
  intro hcol
  -- P1: `G` is not perfect
  refine IsoTransport.minimumImperfect_not_perfect hG
    (fun hp => Workspace.MainTheorem.SPGT.thm_E5_perfect_implies_berge G hp) ?_
  -- but an `ω`-colouring of `G` would make it perfect
  have hchi : G.chromaticNumber = ((G.cliqueNum : ℕ) : ℕ∞) :=
    le_antisymm (SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol)
      SimpleGraph.cliqueNum_le_chromaticNumber
  intro X
  rcases eq_or_ne X Set.univ with rfl | hX
  · rw [IsoTransport.chromaticNumber_iso (SimpleGraph.induceUnivIso G),
      IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso G)]
    exact hchi
  · -- a proper induced subgraph is perfect by minimality
    exact CliqueNumOfInducedSet.chromaticNumber_eq_cliqueNum_of_isPerfect (G.induce X)
      (SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hX)

/-- Equivalently, `ω(G) < χ(G)` strictly. -/
theorem cliqueNum_lt_chromaticNumber {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : MinimumImperfect G) :
    ((G.cliqueNum : ℕ) : ℕ∞) < G.chromaticNumber := by
  refine not_le.mp ?_
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  exact not_colorable_cliqueNum hG

end Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable
