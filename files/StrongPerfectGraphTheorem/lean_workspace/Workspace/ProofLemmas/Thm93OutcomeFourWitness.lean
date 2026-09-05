import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.PathBasics
import Workspace.Types.Knots

/-!
# The witness clause of outcome 9.3.4

Outcome 9.3.4 asks, besides `f, x` having the same neighbours in `V(P₁) ∪ V(P₂) ∪ V(Q')`, for
a non-neighbour of `f` on the antipath of `x` other than `x` itself:

    ∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w.

Since `Q₁` and `Q₂` are disjoint and `Q'` is the antipath *not* containing `x`, the two
conditions `w ∈ Q₁ ∨ w ∈ Q₂` and `w ∉ Q'` say exactly that `w` lies on the antipath of `x`.

This module contains the one implication used on the case-(1) lane of 9.3: there the printed
clause `¬ G.Adj f y` is available, and `w := y` is a witness, because `y` is the other end of
the antipath of `x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93OutcomeFourWitness

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The printed clause of 9.3.4 implies the clause used in the statement.**

If `f` is not adjacent to `y`, then `y` itself witnesses the existential: it lies on one of the
two antipaths, not on `Q'`, and it differs from `x` because `x` and `y` are the two (distinct)
ends of the same antipath. -/
theorem witness_of_nonadj {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    {x y : V} {Q' : List V} {f : V}
    (hchoice : ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
      (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)))
    (hnadj : ¬ G.Adj f y) :
    ∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w := by
  obtain ⟨-, -, -, -, -, hdisj, -, -, hq₁len, hq₂len, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hxy₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hQ₁ hq₁len
  have hxy₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hQ₂ hq₂len
  have hx₁Q : x₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ₁).1
  have hy₁Q : y₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ₁).2
  have hx₂Q : x₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ₂).1
  have hy₂Q : y₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ₂).2
  rcases hchoice with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨e1, e2, e3⟩ := h <;> subst e1 <;> subst e2 <;> subst e3
  · exact ⟨y, Or.inl hy₁Q, hdisj y hy₁Q, Ne.symm hxy₁, hnadj⟩
  · exact ⟨y, Or.inl hx₁Q, hdisj y hx₁Q, hxy₁, hnadj⟩
  · exact ⟨y, Or.inr hy₂Q, fun hc => hdisj y hc hy₂Q, Ne.symm hxy₂, hnadj⟩
  · exact ⟨y, Or.inr hx₂Q, fun hc => hdisj y hc hx₂Q, hxy₂, hnadj⟩

end Workspace.ProofLemmas.Thm93OutcomeFourWitness
