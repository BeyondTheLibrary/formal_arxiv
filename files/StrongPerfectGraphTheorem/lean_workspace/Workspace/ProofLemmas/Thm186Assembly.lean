import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm186Setup
import Workspace.ProofLemmas.Thm186Claim2
import Workspace.ProofLemmas.Thm186Final

/-!
# 18.6 — assembly

The printed proof is a minimal-counterexample argument:

> *"Proof.  Suppose the theorem is false, and choose a minimal counterexample `F`.  From 18.5
> `|F| ≥ 2`.  (1) … (2) … Thus there is no such `F`.  This proves 18.6."*

so the assembly is exactly: negate the conclusion, take a minimal counterexample
(`Thm186Setup.exists_minCounterexample`), run claim (2) (`Thm186Claim2.claim2`, which itself
runs claim (1)), and hand both to the closing paragraph
(`Thm186Final.final_contradiction`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm186Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **18.6**, in exactly the shape of the frozen
`Workspace.Statements.S18.SPGT.thm_18_6`. -/
theorem thm_18_6_full (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V) (P : List V)
    (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hF : ∀ f ∈ F, f ∉ X ∪ Y ∧ f ∉ P)
    (hFconn : ConnectedSet G F)
    (hFY : ∀ f ∈ F, ¬ VertexComplete G f Y) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ attachments G F {w : V | w ∈ P}, w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      ((∃ f ∈ F, VertexComplete G f X) → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  -- *"Suppose the theorem is false, and choose a minimal counterexample `F`."*
  by_contra hcon
  obtain ⟨F₀, hmin⟩ :=
    Thm186Setup.exists_minCounterexample G X Y P p₁ pₙ F ⟨hF, hFconn, hFY⟩ hcon
  -- *"(2) There do not exist `a, b` … This proves (2)."*
  have h2 := Thm186Claim2.claim2 G hG X Y P p₁ pₙ hopt hhead hlast F₀ hmin
  -- *"Choose `b` … contrary to 2.3.  Thus there is no such `F`.  This proves 18.6."*
  exact Thm186Final.final_contradiction G hG X Y P p₁ pₙ hopt hhead hlast F₀ hmin h2

end Workspace.ProofLemmas.Thm186Assembly
