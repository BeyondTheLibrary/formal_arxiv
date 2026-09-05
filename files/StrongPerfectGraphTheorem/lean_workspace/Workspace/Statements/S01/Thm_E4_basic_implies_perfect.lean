import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Types.Replication
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.ProofLemmas.BipartitePerfect
import Workspace.ProofLemmas.LineGraphBipartitePerfect
import Workspace.ProofLemmas.DoubleSplitPerfect
import Workspace.ProofLemmas.DoubleSplitSelfComplementary
import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_1_1

set_option linter.unusedSectionVars false

namespace Workspace.MainTheorem

open Workspace.Types.Core Workspace.Types.Decompositions
open Workspace.Types.BasicClasses Workspace.Types.Replication
open Workspace.Types.Classes Workspace.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **E4** — "every basic graph is perfect".  Bipartite: trivial.  Line graph of a
bipartite graph: König.  Double split: the reader.  Complements: Lovász' 1.1
(except for the double split case, which is self-complementary). -/
theorem thm_E4_basic_implies_perfect (G : SimpleGraph V) (hG : SPGT.IsBasic G) :
    SPGT.IsPerfect G := by
  classical
  -- perfection of the complement transfers back along `Gᶜᶜ = G` by 1.1 (Lovász).
  have hcompl : ∀ K : SimpleGraph V, Workspace.Types.Core.SPGT.IsPerfect Kᶜ →
      Workspace.Types.Core.SPGT.IsPerfect K := by
    intro K hK
    have h := _root_.Workspace.MainTheorem.SPGT.thm_1_1 Kᶜ hK
    simpa using h
  rcases hG with (hb | hl | hd) | (hb | hl | hd)
  -- `G` bipartite.
  · exact _root_.Workspace.ProofLemmas.BipartitePerfect G hb
  -- `G` the line graph of a bipartite graph.
  · obtain ⟨n, H, hHbip, ⟨e⟩⟩ := hl
    exact (_root_.Workspace.ProofLemmas.IsoTransport.isPerfect_iso e).mpr
      (_root_.Workspace.ProofLemmas.LineGraphBipartitePerfect H hHbip)
  -- `G` a double split graph.
  · exact _root_.Workspace.ProofLemmas.DoubleSplitPerfect G hd
  -- `Gᶜ` bipartite.
  · exact hcompl G (_root_.Workspace.ProofLemmas.BipartitePerfect Gᶜ hb)
  -- `Gᶜ` the line graph of a bipartite graph.
  · obtain ⟨n, H, hHbip, ⟨e⟩⟩ := hl
    exact hcompl G ((_root_.Workspace.ProofLemmas.IsoTransport.isPerfect_iso e).mpr
      (_root_.Workspace.ProofLemmas.LineGraphBipartitePerfect H hHbip))
  -- `Gᶜ` a double split graph; then so is `Gᶜᶜ = G`, and no appeal to 1.1 is needed.
  · have hGd : Workspace.Types.BasicClasses.SPGT.IsDoubleSplitGraph G := by
      have h := _root_.Workspace.ProofLemmas.DoubleSplitSelfComplementary.isDoubleSplitGraph_compl hd
      simpa using h
    exact _root_.Workspace.ProofLemmas.DoubleSplitPerfect G hGd

end SPGT

end Workspace.MainTheorem
