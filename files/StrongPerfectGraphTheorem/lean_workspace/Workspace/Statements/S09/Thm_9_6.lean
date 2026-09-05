/-  **9.6** — proof attempt 3.

    Identical in mathematical content to `Attempt_1`; the changes are upstream plus one
    syntax fix (`Attempt_2` split each helper's fully qualified name across a line break,
    which Lean reads as generalized field notation on a namespace, not as an identifier).
    `Attempt_1`
    failed with

        `Workspace.Statements.S09.SPGT.thm_9_6` has already been declared

    not because it imported the statement module directly (it did not), but because of a
    module-level import cycle:

        Workspace.ProofLemmas.Thm96Assembly
          -> Workspace.ProofLemmas.RecalcitrantInF5      (for `isDoubleSplitGraph_compl`)
          -> Workspace.Statements.S09.Thm_9_7            (RecalcitrantInF5 cites 9.7)
          -> Workspace.Statements.S09.Thm_9_6

    Nothing in the mathematics is circular — the paper's 9.7 cites 9.6, never the reverse.
    The single fact `Thm96Assembly` wanted from `RecalcitrantInF5` is the paper's own
    parenthetical on printed p. 2, *"(Note that if `G` is a double split graph then so is
    `Ḡ`.)"*, which cites nothing.  It has been split out into the statement-free module
    `Workspace.ProofLemmas.DoubleSplitSelfComplementary`; `RecalcitrantInF5` re-exports it,
    so every other reference is unaffected.  With that, `Thm96Assembly` no longer reaches
    `Thm_9_6` and the theorem can be declared here. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm96Assembly
import Workspace.ProofLemmas.DegenerateK4AppearanceYieldsStriation
import Workspace.ProofLemmas.BipartiteK4AppearanceHasAtLeastEightVertices
import Workspace.ProofLemmas.MaximalStriationForcesThm96Conclusion

set_option autoImplicit false

namespace Workspace.Statements.S09

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem thm_9_6 (G : SimpleGraph V) (hG : Berge G)
    (hdegG : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hdegGc : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hnoL33 : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)) :
    IsDoubleSplitGraph G ∨
    AdmitsBalancedSkewPartition G ∨
    (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨
    (¬ Appears G (⊤ : SimpleGraph (Fin 4)) ∧ ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4))) := by
  exact Workspace.ProofLemmas.Thm96Assembly.thm_9_6_of_steps G hG hdegG hdegGc hnoL33
    (fun Gx => Workspace.ProofLemmas.DegenerateK4AppearanceYieldsStriation.degenerateK4AppearanceYieldsStriation Gx)
    (fun Gx => Workspace.ProofLemmas.BipartiteK4AppearanceHasAtLeastEightVertices.BipartiteK4AppearanceHasAtLeastEightVertices Gx)
    (fun Gx => Workspace.ProofLemmas.MaximalStriationForcesThm96Conclusion.maximalStriationForcesThm96Conclusion Gx)


end SPGT

end Workspace.Statements.S09
