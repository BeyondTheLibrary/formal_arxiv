import Workspace.Types.Core
import Workspace.ProofLemmas.AntitwinExtremalClique
import Workspace.ProofLemmas.AntitwinDualExtremalStableSet
import Workspace.ProofLemmas.AntitwinExtremalsForceProperInducedC5

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A finite graph that is nonperfect while all of its proper induced
subgraphs are perfect has no distinct antitwin pair. -/
theorem NoAntitwinsInCriticalImperfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hKnonperfect : ¬ SPGT.IsPerfect K)
    (hKproper : ∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect (K.induce X)) :
    ¬ ∃ u v : W, u ≠ v ∧
      ∀ z : W, z ≠ u → z ≠ v → Xor' (K.Adj z u) (K.Adj z v) := by
  rintro ⟨u, v, huv, hanti⟩
  obtain ⟨D, hDsub, hDnonempty, hDclique, hDmax⟩ :=
    AntitwinExtremalClique K hKnonperfect hKproper u v huv hanti
  obtain ⟨R, hRsub, hRnonempty, hRstable, hRmax⟩ :=
    AntitwinDualExtremalStableSet K hKnonperfect hKproper u v huv hanti
  obtain ⟨S, hSproper, hSnonperfect⟩ :=
    AntitwinExtremalsForceProperInducedC5 K u v huv hanti D R
      hDsub hDnonempty hDclique hDmax hRsub hRnonempty hRstable hRmax
  exact hSnonperfect (hKproper S hSproper)

end Workspace.ProofLemmas
