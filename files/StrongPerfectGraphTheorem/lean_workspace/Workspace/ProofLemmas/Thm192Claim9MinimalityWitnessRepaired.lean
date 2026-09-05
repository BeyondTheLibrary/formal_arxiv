import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra

/-!
# The minimality witness of claim (9) of 19.2, in the form that is true

PAPER (19.2, claim (9), printed p. 121):

> *"Choose `f ∈ A \ F` such that `A \ {f}` is connected.  From the minimality of `A`, there
> exists `y₀ ∈ Y` nonadjacent to `x₂` with no neighbour in `A \ {f}`."*

The printed sentence is sound for the printed choice of `A`, which is minimal subject to

* `A ⊆ A₁`, `A` connected,
* `x₀, x₁, x₂` have neighbours in `A`,
* every vertex of `Y` nonadjacent to `x₂` has a neighbour in `A`.

This project minimises over `GoodA`, which carries **one extra clause** — *"`y` has a
neighbour in `A`"* — added deliberately in `Thm192Setup` to repair the order of the two
extremal choices.  With that extra clause, `A \ {f}` may fail to be `GoodA` at the new
clause instead of at the `Y`-clause, and then no `y₀` need exist:
`Thm192Claim9MinimalityWitness.minimalityWitness` as stated is **false** (see
`lean_workspace/REPORT.md` for an explicit counterexample).

What the minimality of `A` does give is exactly the disjunction below: `A \ {f}` fails one
of the two "has a neighbour" clauses of `GoodA`.  Everything else it needs — `A \ {f} ⊆ A₁`,
connected, and containing neighbours of `x₀, x₁, x₂` — it inherits from `F ⊆ A \ {f}`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm192Claim9MinimalityWitnessRepaired

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"Choose `f ∈ A \ F` such that `A \ {f}` is connected.  From the minimality of `A`, …"* —
in the form that follows from the minimality of a `GoodA` set. -/
theorem minimalityWitness (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V)
    (Y : Set V) (y : V) (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (F : Set V) (hFA : F ⊆ A) (hFconn : ConnectedSet G F) (hFne : F ≠ A)
    (hF0 : ∃ a ∈ F, G.Adj (x 0) a) (hF1 : ∃ a ∈ F, G.Adj (x 1) a)
    (hF2 : ∃ a ∈ F, G.Adj (x 2) a) :
    ∃ f ∈ A \ F, ConnectedSet G (A \ {f}) ∧
      ((∃ y₀ ∈ Y, ¬ G.Adj y₀ (x 2) ∧ VertexAnticomplete G y₀ (A \ {f})) ∨
        VertexAnticomplete G y (A \ {f})) := by
  classical
  obtain ⟨a₀, ha₀F, -⟩ := id hF0
  obtain ⟨f, hf, hconn⟩ :=
    Thm192Infra.exists_noncut_outside hA.2.1 hFconn hFA hFne ⟨a₀, ha₀F⟩
  refine ⟨f, hf, hconn, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hFsub : F ⊆ A \ {f} := fun w hw => ⟨hFA hw, fun he => hf.2 (he ▸ hw)⟩
  have hgood : GoodA G z A₀ x Y y (A \ {f}) := by
    refine ⟨fun w hw => hA.1 hw.1, hconn, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨b, hb, hadj⟩ := hF0
      exact ⟨b, hFsub hb, hadj⟩
    · obtain ⟨b, hb, hadj⟩ := hF1
      exact ⟨b, hFsub hb, hadj⟩
    · obtain ⟨b, hb, hadj⟩ := hF2
      exact ⟨b, hFsub hb, hadj⟩
    · intro w hwY hw2
      by_contra hcc
      push_neg at hcc
      exact hcon.1 w hwY hw2 hcc
    · by_contra hcc
      push_neg at hcc
      exact hcon.2 hcc
  have hle := hAmin _ hgood
  have hss : A \ {f} ⊂ A := ⟨Set.diff_subset, fun hsub => (hsub hf.1).2 rfl⟩
  have hlt : (A \ {f}).ncard < A.ncard := Set.ncard_lt_ncard hss (Set.toFinite A)
  omega

end Workspace.ProofLemmas.Thm192Claim9MinimalityWitnessRepaired
