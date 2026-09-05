import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Statements.S09.Thm_9_1
import Workspace.ProofLemmas.Thm93Case1Major

/-!
# 9.3 — the top-level case split of the printed proof

PAPER (proof of 9.3, printed p. 48):

> *"Define `aᵢ, bᵢ, xᵢ, yᵢ (i = 1, 2)` as usual.  By 9.1 there are two cases, depending
> whether `Q₁` and `Q₂` have length 1 or `P₁, P₂` have length 1.*
>
> *(1) If `Q₁, Q₂` have length 1 then the theorem holds.*
>
> *For assume `Q₁, Q₂` have length 1. … Suppose that the neighbour set of some `f ∈ F`
> saturates `L(H)`.  If `f` has a neighbour in both `V(P₁)` and `V(P₂)` then statement 1 of
> the theorem holds, so we assume it has no neighbour in `V(P₁)`.  But then … a contradiction.
> So we assume there is no such `f`, and hence we may apply 5.8. …*
>
> *Henceforth we may therefore assume that one of `Q₁, Q₂` has length `> 1`, and therefore by
> 9.1, both `P₁` and `P₂` have length 1."*

This module performs exactly that split, and discharges the part of claim (1) that precedes
the appeal to 5.8 (through `Thm93Case1Major.case1_saturating_dichotomy`).  What is left are
the two "lanes" the paper spends the rest of the proof on, taken here as hypotheses:

* `hcase1` — claim (1) from the point *"So we assume there is no such `f`, and hence we may
  apply 5.8"* onwards;
* `hcase2` — everything from *"Henceforth we may therefore assume …"* to the end.

Note on the split.  9.1 gives the *disjunction* "`P₁, P₂` have length 1 or `Q₁, Q₂` have
length 1"; the paper's *"Henceforth we may therefore assume that one of `Q₁, Q₂` has length
`> 1`"* is the complement of case (1), so the second lane may (and does) additionally assume
`¬(pathLength Q₁ = 1 ∧ pathLength Q₂ = 1)`.  When *both* alternatives of 9.1 hold, case (1)
applies and the second lane is not used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **9.3, reduced to the two lanes of the printed proof.** -/
theorem thm_9_3_of_cases (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (F : Set V) (hFsub : F ⊆ Kᶜ)
    -- claim (1) from *"So we assume there is no such `f`, and hence we may apply 5.8"* on
    (hcase1 : pathLength Q₁ = 1 → pathLength Q₂ = 1 →
      (∀ f ∈ F, ¬ ((({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton ∧
        (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton ∧
        (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton ∧
        (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton)) →
      ((∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)) ∨
       (∃ (a : V) (P P' : List V),
         ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
           (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)) ∧
         ∃ (R : List V) (r₁ r₂ : V),
           IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧
           (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
             (G.Adj r₁ w ↔ G.Adj a w)) ∧
           Anticomplete G ({v : V | v ∈ R} \ {r₁})
             ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
           (∃ w ∈ ({v : V | v ∈ P} \ {a} : Set V), G.Adj r₂ w) ∧
           Anticomplete G ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P} \ {a})) ∨
       (∃ (a b : V) (P P' : List V),
         ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
           (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
         ∃ (R : List V) (r₁ r₂ : V),
           IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧ Odd (pathLength R) ∧
           (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
             (G.Adj r₁ w ↔ G.Adj a w)) ∧
           (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
             (G.Adj r₂ w ↔ G.Adj b w)) ∧
           Anticomplete G {v : V | v ∈ SPGT.interior R}
             ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
           (∀ u ∈ R, ∀ w ∈ P, G.Adj u w → ((u = r₁ ∧ w = a) ∨ (u = r₂ ∧ w = b)))) ∨
       (∃ (x y : V) (Q' : List V),
         ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
           (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
         ∃ f ∈ F,
           (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
             (G.Adj f w ↔ G.Adj x w)) ∧
           (∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w))))
    -- everything from *"Henceforth we may therefore assume …"* to the end
    (hcase2 : pathLength P₁ = 1 → pathLength P₂ = 1 →
      ¬ (pathLength Q₁ = 1 ∧ pathLength Q₂ = 1) →
      ((∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)) ∨
       (∃ (a : V) (P P' : List V),
         ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
           (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)) ∧
         ∃ (R : List V) (r₁ r₂ : V),
           IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧
           (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
             (G.Adj r₁ w ↔ G.Adj a w)) ∧
           Anticomplete G ({v : V | v ∈ R} \ {r₁})
             ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
           (∃ w ∈ ({v : V | v ∈ P} \ {a} : Set V), G.Adj r₂ w) ∧
           Anticomplete G ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P} \ {a})) ∨
       (∃ (a b : V) (P P' : List V),
         ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
           (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
         ∃ (R : List V) (r₁ r₂ : V),
           IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧ Odd (pathLength R) ∧
           (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
             (G.Adj r₁ w ↔ G.Adj a w)) ∧
           (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
             (G.Adj r₂ w ↔ G.Adj b w)) ∧
           Anticomplete G {v : V | v ∈ SPGT.interior R}
             ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
           (∀ u ∈ R, ∀ w ∈ P, G.Adj u w → ((u = r₁ ∧ w = a) ∨ (u = r₂ ∧ w = b)))) ∨
       (∃ (x y : V) (Q' : List V),
         ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
           (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
         ∃ f ∈ F,
           (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
             (G.Adj f w ↔ G.Adj x w)) ∧
           (∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w)))) :
    (∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)) ∨
    (∃ (a : V) (P P' : List V),
      ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
        (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)) ∧
      ∃ (R : List V) (r₁ r₂ : V),
        IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₁ w ↔ G.Adj a w)) ∧
        Anticomplete G ({v : V | v ∈ R} \ {r₁})
          ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∃ w ∈ ({v : V | v ∈ P} \ {a} : Set V), G.Adj r₂ w) ∧
        Anticomplete G ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P} \ {a})) ∨
    (∃ (a b : V) (P P' : List V),
      ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
        (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
      ∃ (R : List V) (r₁ r₂ : V),
        IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧ Odd (pathLength R) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₁ w ↔ G.Adj a w)) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₂ w ↔ G.Adj b w)) ∧
        Anticomplete G {v : V | v ∈ SPGT.interior R}
          ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∀ u ∈ R, ∀ w ∈ P, G.Adj u w → ((u = r₁ ∧ w = a) ∨ (u = r₂ ∧ w = b)))) ∨
    (∃ (x y : V) (Q' : List V),
      ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
        (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
      ∃ f ∈ F,
        (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
          (G.Adj f w ↔ G.Adj x w)) ∧
        (∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w)) := by
  -- PAPER: *"By 9.1 there are two cases, depending whether `Q₁` and `Q₂` have length 1 or
  -- `P₁, P₂` have length 1."*
  obtain ⟨⟨hoP₁, hoP₂, -, -⟩, hdich⟩ :=
    _root_.Workspace.Statements.S09.SPGT.thm_9_1 G hG P₁ P₂ Q₁ Q₂ hknot
  by_cases hQ : pathLength Q₁ = 1 ∧ pathLength Q₂ = 1
  · -- PAPER: *"(1) If `Q₁, Q₂` have length 1 then the theorem holds."*
    -- The first two sentences of claim (1) are `case1_saturating_dichotomy`; the rest is the
    -- appeal to 5.8, which is `hcase1`.
    rcases Thm93Case1Major.case1_saturating_dichotomy G hG P₁ P₂ Q₁ Q₂
        a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hQ.1 hQ.2 hoP₁ hoP₂ K hK F hFsub with
      h | h
    · exact Or.inl h
    · exact hcase1 hQ.1 hQ.2 h
  · -- PAPER: *"Henceforth we may therefore assume that one of `Q₁, Q₂` has length `> 1`, and
    -- therefore by 9.1, both `P₁` and `P₂` have length 1."*
    have hP : pathLength P₁ = 1 ∧ pathLength P₂ = 1 := by
      rcases hdich with h | h
      · exact h
      · exact absurd h hQ
    exact hcase2 hP.1 hP.2 hQ

end Workspace.ProofLemmas.Thm93Assembly
