import Workspace.Types.Core
import Workspace.Statements.S01.Thm_1_1

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A finite graph that is nonperfect while all of its proper induced subgraphs
are perfect has the same critical-imperfect property after complementation. -/
theorem CriticalImperfectComplement
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hKnonperfect : ¬ SPGT.IsPerfect K)
    (hKproper : ∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect (K.induce X)) :
    ¬ SPGT.IsPerfect (Kᶜ) ∧
      ∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect ((Kᶜ).induce X) := by
  constructor
  · intro hKcperfect
    apply hKnonperfect
    simpa using Workspace.MainTheorem.SPGT.thm_1_1 Kᶜ hKcperfect
  · intro X hX
    letI : Fintype X := Fintype.ofFinite X
    have hperfect : SPGT.IsPerfect (K.induce X) := hKproper X hX
    have hcompl : SPGT.IsPerfect (K.induce X)ᶜ :=
      Workspace.MainTheorem.SPGT.thm_1_1 (K.induce X) hperfect
    have hinduce : (K.induce X)ᶜ = (Kᶜ).induce X := by
      ext u v
      simp [SimpleGraph.compl_adj, Subtype.ext_iff]
    rw [hinduce] at hcompl
    exact hcompl

end Workspace.ProofLemmas
