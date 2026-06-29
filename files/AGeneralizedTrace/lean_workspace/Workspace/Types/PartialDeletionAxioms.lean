import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.TraceDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.TVDistance

namespace Workspace.Types.PartialDeletionAxioms

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.TraceDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.TVDistance

/-
The data-processing inequality for the partial-deletion process
(`partial_dominates_traceDist`) was previously admitted here as a structural
axiom. It is now PROVED, sorry-free, as
`Workspace.ProofLemmas.PartialDominatesHCore.partial_dominates_traceDist_of_gate`
(under the gate `2 * (n / 4) = n / 2`, which holds under the paper's
`n % 8 = 1`), via `bind_identity` + `Workspace.PriorWork.DataProcessingTV`.
The axiom has therefore been removed.
-/

end Workspace.Types.PartialDeletionAxioms
