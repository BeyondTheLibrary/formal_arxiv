import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Wheels
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Appearances
import Workspace.ProofLemmas.OddWheelClaimOne
import Workspace.ProofLemmas.OddWheelTrichotomy

set_option autoImplicit false

namespace Workspace.Statements.S16

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **16.1** (printed p. 96) -/
theorem thm_16_1 (G : SimpleGraph V) (hG : InF6 G)
    (C : List V) (Y : Set V) (hwheel : IsWheel G C Y)
    (v : V) (hvC : v ∉ C) (hvY : v ∉ Y) (hv : ¬ VertexComplete G v Y)
    (a b : V) (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : OppositeWheelParity G C Y a b) :
    (∀ P : List V, IsPathList G P →
        (∃ k : ℕ, P <+: C.rotate k ∨ P.reverse <+: C.rotate k) →
        (IsPathFrom G P a b ∨ IsPathFrom G P b a) →
        ∃ x ∈ P, ∃ y ∈ P, EdgeComplete G (Y ∪ {v}) x y) ∧
    ((∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ {u : V | u ∈ C ∧ G.Adj v u} = {a₁, a₂} ∧
          G.Adj a₁ a₂ ∧ VertexComplete G a₁ Y ∧ VertexComplete G a₂ Y) ∨
      (∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
          (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
          VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
          VertexComplete G p₃ (Y ∪ {v}) ∧
          ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) ∨
      IsWheel G C (Y ∪ {v})) := by
  -- The whole of 16.1 follows from claim (1) of its printed proof:
  -- `OddWheelTrichotomy.thm_16_1_of_claim1` is *"From (1) the first assertion of the theorem
  -- follows.  Now we prove the second assertion. …"* (printed p. 97), and
  -- `OddWheelClaimOne.claim_one` is claim (1) itself.
  exact Workspace.ProofLemmas.OddWheelTrichotomy.thm_16_1_of_claim1 hG.1.1.1 hwheel hvC hvY hv
    (Workspace.ProofLemmas.OddWheelClaimOne.claim_one hG hwheel hvC hvY hv) hva hvb hab


end SPGT

end Workspace.Statements.S16
