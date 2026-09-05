import Mathlib
import Workspace.Types.Core
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.LongOddPrism
import Workspace.ProofLemmas.Thm233Descent

set_option autoImplicit false

namespace Workspace.Statements.S23

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_23_3 (G : SimpleGraph V) (hG : InF9 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (s : ℕ) (hws : IsWheelSystem G z A₀ x s) :
    ¬ ∃ y : V,
        y ∉ insert z (wheelSystemX x s) ∧
        VertexComplete G y (insert z (wheelSystemX x s)) ∧
        (∃ a ∈ wheelSystemA G z A₀ x s, G.Adj y a) := by
  -- *"choose them with `s` minimum (it is important here that we minimize over all
  -- choices of the frame, not just of the wheel system)"* — run as strong induction
  -- on the height, with the frame, the base set and the sequence all quantified.
  have main : ∀ n : ℕ, ∀ (z' : V) (A' : Set V) (x' : ℕ → V),
      IsFrame G z' A' → IsWheelSystem G z' A' x' n →
      ¬ ∃ y : V,
          y ∉ insert z' (wheelSystemX x' n) ∧
          VertexComplete G y (insert z' (wheelSystemX x' n)) ∧
          (∃ a ∈ wheelSystemA G z' A' x' n, G.Adj y a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z' A' x' hf hw
      rintro ⟨y, hy₁, hy₂, hy₃⟩
      obtain ⟨r, -, hrn, hfr, hwr, hz₁, hz₂, hz₃⟩ :=
        Workspace.ProofLemmas.Thm233Descent.descent G hG hbsp z' A' hf x' n hw y hy₁ hy₂ hy₃
      exact ih r hrn y A' x' hfr hwr ⟨z', hz₁, hz₂, hz₃⟩
  exact main s z A₀ x hframe hws


end SPGT

end Workspace.Statements.S23
