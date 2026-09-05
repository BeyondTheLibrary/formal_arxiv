import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Types.Replication
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.ProofLemmas.DisconnectedSetAnticompleteSplit
import Workspace.ProofLemmas.StarSeparationStableMaximumCliqueTransversal
import Workspace.ProofLemmas.StableTransversalWithPerfectRemainderColorable
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
import Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable

set_option linter.unusedSectionVars false

namespace Workspace.MainTheorem

open Workspace.Types.Core Workspace.Types.Decompositions
open Workspace.Types.BasicClasses Workspace.Types.Replication
open Workspace.Types.Classes Workspace.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **E6**, due to Chvátal [6]; used inside the proof of 1.5. -/
theorem thm_E6_no_star_cutset_in_minimum_imperfect
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G) :
    ¬ SPGT.AdmitsStarCutset G := by
  classical
  -- §0: unpack the star cutset.
  rintro ⟨A, B, ⟨hAB, hABdisj, hAconn, -⟩, v, hvB, hvcomplete⟩
  -- §1: the disconnected side splits into two nonempty anticomplete parts.
  obtain ⟨X, Y, hXne, hYne, hXYdisj, hXYA, hXYanti⟩ :=
    _root_.Workspace.ProofLemmas.DisconnectedSetAnticompleteSplit G A hAconn
  -- §2: both `X ∪ B` and `Y ∪ B` are proper subsets of `V(G)`, hence perfect.
  have hXB : X ∪ B ≠ Set.univ := by
    obtain ⟨y, hyY⟩ := hYne
    have hyX : y ∉ X := fun h => Set.disjoint_left.mp hXYdisj h hyY
    have hyA : y ∈ A := by rw [← hXYA]; exact Or.inr hyY
    have hyB : y ∉ B := fun h => Set.disjoint_left.mp hABdisj hyA h
    intro hEq
    have hmem : y ∈ X ∪ B := by rw [hEq]; trivial
    rcases (Set.mem_union y X B).mp hmem with h | h
    · exact hyX h
    · exact hyB h
  have hYB : Y ∪ B ≠ Set.univ := by
    obtain ⟨x, hxX⟩ := hXne
    have hxY : x ∉ Y := fun h => Set.disjoint_left.mp hXYdisj hxX h
    have hxA : x ∈ A := by rw [← hXYA]; exact Or.inl hxX
    have hxB : x ∉ B := fun h => Set.disjoint_left.mp hABdisj hxA h
    intro hEq
    have hmem : x ∈ Y ∪ B := by rw [hEq]; trivial
    rcases (Set.mem_union x Y B).mp hmem with h | h
    · exact hxY h
    · exact hxB h
  have hperfX :=
    _root_.Workspace.ProofLemmas.SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hXB
  have hperfY :=
    _root_.Workspace.ProofLemmas.SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hYB
  -- §§3-5: the two centre colour classes glue to a stable maximum-clique transversal.
  have hcover : (X ∪ Y) ∪ B = Set.univ := by rw [hXYA]; exact hAB
  obtain ⟨S, hvS, hSind, hShit⟩ :=
    _root_.Workspace.ProofLemmas.StarSeparationStableMaximumCliqueTransversal
      G X Y B v hvB hcover hXYdisj hXYanti hvcomplete hperfX hperfY
  -- §6: delete `S`, colour the perfect remainder, and add one colour.
  have hScompl : (Sᶜ : Set V) ≠ Set.univ := by
    intro hEq
    have hmem : v ∈ (Sᶜ : Set V) := by rw [hEq]; trivial
    exact hmem hvS
  have hperfR :=
    _root_.Workspace.ProofLemmas.SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hScompl
  have hcolor : G.Colorable G.cliqueNum :=
    _root_.Workspace.ProofLemmas.StableTransversalWithPerfectRemainderColorable
      G S ⟨v, hvS⟩ hSind hperfR hShit
  -- §7: contradiction with minimality.
  exact _root_.Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable.not_colorable_cliqueNum
    hG hcolor

end SPGT

end Workspace.MainTheorem
