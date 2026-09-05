import Mathlib
import Workspace.Types.Core
import Workspace.Types.Pseudowheels

/-!
# Building and eliminating a pseudowheel

`Workspace.Types.Pseudowheels.IsPseudowheel G X Y P` is a nine-clause conjunction with three
existentially bound vertices `p₁, p₂, pₙ`.  Section 23 uses it in the *eliminating* direction:
`G ∈ F₈` says no pseudowheel exists, all the clauses but one are verified by hand, and the
conclusion is that the remaining clause fails.

Printed proof of **23.2**, step (5) (printed p. 140):

> *"Since `G ∈ F₈`, `(Y, {x₀,x₁}, z-y-p₁-⋯-p_k)` is not a pseudowheel.  But the ends of the
> path `z-y-p₁-⋯-p_k` are `Y`-complete and its internal vertices are not; the path has length
> `≥ 4` (and therefore has even length by 13.6); `Y, z` are `{x₀,x₁}`-complete, and `y, p_k`
> are not.  So no other vertices of the path are `{x₀,x₁}`-complete."*

Note the paper's triple is `(X, Y, P) = (Y, {x₀,x₁}, z-y-p₁-⋯-p_k)` — the paper's **first**
component is the wheel's hub `Y`, and its **second** is the pair `{x₀,x₁}`.  So in Lean the
call is `IsPseudowheel G Y {x₀,x₁} (z :: y :: p)`, with the wheel hub in the `X` slot.  Getting
this backwards is the obvious trap and is the reason this module exists.

The clause that must fail is
`∃ v ∈ P, v ≠ p₁ ∧ VertexComplete G v Y` — *"some vertex of the path other than `z` is
`{x₀,x₁}`-complete"* — and its failure is exactly the paper's *"So no other vertices of the
path are `{x₀,x₁}`-complete"*, which is what 2.11 is then applied to.

Contents:

* `isPseudowheel_mk` — the builder, taking the paper's data in the paper's order.
* `not_vertexComplete_of_no_pseudowheel` — the eliminator used in step (5).
* `no_pseudowheel_of_inF8`-style access is left to the caller (`InF8` unfolds to a conjunction
  whose second component is the `G` half of *"`G` and `Ḡ` do not contain pseudowheels"*).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.PseudowheelBuilder

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT

variable {V : Type*} {G : SimpleGraph V} {X Y : Set V} {P : List V} {p₁ p₂ pₙ : V}

/-- **The builder.**  All nine clauses of `IsPseudowheel`, in the order the paper supplies
them. -/
theorem isPseudowheel_mk
    (hdisj : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXanti : AnticonnectedSet G X) (hYanti : AnticonnectedSet G Y)
    (hXY : Complete G X Y)
    (hpath : IsPathFrom G P p₁ pₙ) (hp₂ : P.tail.head? = some p₂)
    (hout : ∀ v ∈ P, v ∉ X ∧ v ∉ Y) (hlen : 5 ≤ P.length)
    (hXcomplete : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ))
    (hp₁Y : VertexComplete G p₁ Y)
    (hsecond : ∃ v ∈ P, v ≠ p₁ ∧ VertexComplete G v Y)
    (hp₂Y : ¬ VertexComplete G p₂ Y) (hpₙY : ¬ VertexComplete G pₙ Y) :
    IsPseudowheel G X Y P :=
  ⟨⟨hdisj, hXne, hYne, hXanti, hYanti, hXY⟩,
   p₁, p₂, pₙ, ⟨hpath, hp₂, hout, hlen⟩, hXcomplete, hp₁Y, hsecond, hp₂Y, hpₙY⟩

/-- **The eliminator — step (5) of 23.2.**  If `G` contains no pseudowheel and every clause of
`IsPseudowheel G X Y P` holds except possibly *"some vertex of `P` other than `p₁` is
`Y`-complete"*, then that clause fails: `p₁` is the only `Y`-complete vertex of `P`.

This is the printed *"So no other vertices of the path are `{x₀,x₁}`-complete"*, obtained from
`G ∈ F₈`.  Apply it with `X := Y_hub` and `Y := {x₀,x₁}`. -/
theorem not_vertexComplete_of_no_pseudowheel
    (hno : ¬ ∃ (X' Y' : Set V) (P' : List V), IsPseudowheel G X' Y' P')
    (hdisj : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXanti : AnticonnectedSet G X) (hYanti : AnticonnectedSet G Y)
    (hXY : Complete G X Y)
    (hpath : IsPathFrom G P p₁ pₙ) (hp₂ : P.tail.head? = some p₂)
    (hout : ∀ v ∈ P, v ∉ X ∧ v ∉ Y) (hlen : 5 ≤ P.length)
    (hXcomplete : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ))
    (hp₁Y : VertexComplete G p₁ Y)
    (hp₂Y : ¬ VertexComplete G p₂ Y) (hpₙY : ¬ VertexComplete G pₙ Y) :
    ∀ v ∈ P, v ≠ p₁ → ¬ VertexComplete G v Y := by
  intro v hv hvp₁ hvY
  exact hno ⟨X, Y, P, isPseudowheel_mk hdisj hXne hYne hXanti hYanti hXY hpath hp₂ hout hlen
    hXcomplete hp₁Y ⟨v, hv, hvp₁, hvY⟩ hp₂Y hpₙY⟩

/-- The same conclusion packaged as *"`p₁` is the unique `Y`-complete vertex of `P`"*, which is
the shape 2.11 wants for its hypothesis *"`p₁` is the unique `X`-complete vertex of `P`"*. -/
theorem unique_vertexComplete_of_no_pseudowheel
    (hno : ¬ ∃ (X' Y' : Set V) (P' : List V), IsPseudowheel G X' Y' P')
    (hdisj : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXanti : AnticonnectedSet G X) (hYanti : AnticonnectedSet G Y)
    (hXY : Complete G X Y)
    (hpath : IsPathFrom G P p₁ pₙ) (hp₂ : P.tail.head? = some p₂)
    (hout : ∀ v ∈ P, v ∉ X ∧ v ∉ Y) (hlen : 5 ≤ P.length)
    (hXcomplete : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ))
    (hp₁mem : p₁ ∈ P) (hp₁Y : VertexComplete G p₁ Y)
    (hp₂Y : ¬ VertexComplete G p₂ Y) (hpₙY : ¬ VertexComplete G pₙ Y) :
    ∀ v ∈ P, (VertexComplete G v Y ↔ v = p₁) := by
  intro v hv
  constructor
  · intro hvY
    by_contra hne
    exact not_vertexComplete_of_no_pseudowheel hno hdisj hXne hYne hXanti hYanti hXY hpath hp₂
      hout hlen hXcomplete hp₁Y hp₂Y hpₙY v hv hne hvY
  · rintro rfl
    exact hp₁Y

end Workspace.ProofLemmas.PseudowheelBuilder
