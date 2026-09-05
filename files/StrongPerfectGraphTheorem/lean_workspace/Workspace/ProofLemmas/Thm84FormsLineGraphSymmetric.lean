import Workspace.ProofLemmas.FormsLineGraphForcesRungSymmetry

/-!
# Alias: a family of rungs that forms a line graph is edge-indexed

This module is a **thin re-export** of
`Workspace.ProofLemmas.FormsLineGraphForcesRungSymmetry.formsLineGraph_forces_rung_symmetry`,
kept because `Workspace/Statements/S08/Thm_8_4.lean` cites it under this name.  All the
mathematics, the passage of the paper it transcribes, the reason the on-the-nose form
`R u v = R v u` is **false**, the three lemmas that are proved (`rung_end_unique`,
`rung_ends_swap`, `strip_inter_eq_union`) and the precise remaining gap are documented in
`FormsLineGraphForcesRungSymmetry.lean`.  Do not duplicate content here.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm84FormsLineGraphSymmetric

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A choice of rungs that forms a line graph is edge-indexed**: reversing the orientation of an
edge of `J` reverses the chosen rung.  Alias for
`FormsLineGraphForcesRungSymmetry.formsLineGraph_forces_rung_symmetry`. -/
theorem formsLineGraph_symm {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H) :
    ∀ u v : U, J.Adj u v → R v u = (R u v).reverse :=
  Workspace.ProofLemmas.FormsLineGraphForcesRungSymmetry.formsLineGraph_forces_rung_symmetry
    G J hJ S N hSN H R hForms

end Workspace.ProofLemmas.Thm84FormsLineGraphSymmetric
