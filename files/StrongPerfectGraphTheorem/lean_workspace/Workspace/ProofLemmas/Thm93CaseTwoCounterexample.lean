import Workspace.ProofLemmas.Thm93CaseTwoCommon

/-!
# The missing outside-vertex hypothesis in the non-major target

The graph below is the complement of the line graph of the bipartite subdivision of `K₄`
with square `0-1-2-3-0` and diagonal branches `0-4-5-6-2` and `1-7-3`.
The vertex labels here are `a₁,b₁,a₂,b₂,x₁,z₁,z₂,y₁,x₂,y₂`, in this order.
The full obstruction, including the appearance dictionary, is described in `REPORT.md`.
This file checks the knot and the failure of its conclusion in Lean.

The frozen statement of 9.3 has since been repaired, with the user's approval: outcome 9.3.4
now asks only for a non-neighbour of `f` on the antipath of `x` other than `x`, instead of the
printed `¬ G.Adj f y`.  The graph below therefore no longer refutes
`Workspace.Statements.S09.SPGT.thm_9_3`; it refutes the **printed** conclusion, written out as
`PrintedConclusion` below, and that is what `not_conclusion` now says.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm93CaseTwoCounterexample

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

variable {V : Type*}

/-- **The conclusion of 9.3 as printed.**

This is `Thm93Infrastructure.Conclusion` with the printed form of outcome 9.3.4, namely
`¬ G.Adj f y`, in place of the repaired clause
`∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w`.  It is what the graph of this module
refutes; the repaired conclusion does hold for that graph, with the witness `w = 5`. -/
abbrev PrintedConclusion (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V) (K F : Set V) : Prop :=
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
        ¬ G.Adj f y)

/-- The twenty-nine edges of the counterexample. -/
def edges : Finset (Sym2 (Fin 10)) :=
  {s(0,1), s(0,4), s(0,8), s(0,5), s(0,6),
   s(2,3), s(2,4), s(2,9), s(2,5), s(2,6),
   s(1,7), s(1,9), s(1,5), s(1,6),
   s(3,8), s(3,7), s(3,5), s(3,6),
   s(4,8), s(4,7), s(4,9), s(4,6),
   s(8,7), s(8,5), s(8,6),
   s(7,9), s(7,5), s(9,5), s(9,6)}

/-- A ten-vertex knot with one long antipath. -/
def graph : SimpleGraph (Fin 10) := SimpleGraph.fromEdgeSet (↑edges)

instance : DecidableRel graph.Adj := by
  unfold graph
  infer_instance

/-- The two short paths. -/
theorem short_paths : IsPathFrom graph [0,1] 0 1 ∧ IsPathFrom graph [2,3] 2 3 := by
  exact ⟨⟨PathBasics.isPathList_pair (by decide), rfl, rfl⟩,
    ⟨PathBasics.isPathList_pair (by decide), rfl, rfl⟩⟩

/-- The two antipaths, of lengths three and one. -/
theorem antipaths : IsAntipathFrom graph [4,5,6,7] 4 7 ∧
    IsAntipathFrom graph [8,9] 8 9 := by
  refine ⟨⟨?_, rfl, rfl⟩, ⟨PathBasics.isPathList_pair (by decide), rfl, rfl⟩⟩
  exact _root_.ProofAttempts.Thm21Aux.isPathList_four graphᶜ 4 5 6 7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The data really form a knot. -/
theorem isKnot : IsKnot graph [0,1] [2,3] [4,5,6,7] [8,9] := by
  refine ⟨0,1,2,3,4,7,8,9, short_paths.1, short_paths.2, antipaths.1, antipaths.2, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, pathLength,
    List.length_cons, List.length_nil, Set.mem_insert_iff, Set.mem_singleton_iff,
    Anticomplete, Complete, VertexAnticomplete, VertexComplete, Set.mem_setOf_eq,
    forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals first | decide | change s(_, _) ∈ edges; decide

/-- The knot fills the graph. -/
theorem induces : KnotInduces [0,1] [2,3] [4,5,6,7] [8,9] (Set.univ : Set (Fin 10)) := by
  ext v
  fin_cases v <;> simp [KnotInduces]

/-- The vertex `x₁` does not resolve the knot. The edge `b₁z₁` has neither end in its
neighbour set. -/
theorem not_resolves : ¬ ResolvesKnot graph [0,1] [2,3] [4,5,6,7] [8,9]
    (graph.neighborSet 4 ∩ Set.univ) := by
  intro h
  have he := h.2.2.2 1 (by simp) 5 (by simp) (by decide)
  rcases he with h | h
  · exact (show ¬ graph.Adj 4 1 by decide) h.1
  · exact (show ¬ graph.Adj 4 5 by decide) h.1

/-- All four alternatives of 9.3 **as printed** fail for `F = {x₁}`. -/
theorem not_conclusion : ¬ PrintedConclusion graph [0,1] [2,3] [4,5,6,7] [8,9]
    0 1 2 3 4 7 8 9 Set.univ ({4} : Set (Fin 10)) := by
  rintro (⟨f, hf, hres⟩ | h | h | h)
  · have he : f = 4 := hf
    subst f
    exact not_resolves hres
  · obtain ⟨a, P, P', hchoice, R, r₁, r₂, hR, hRF, hsame, _⟩ := h
    have hr : r₁ = 4 := hRF r₁ (PathBasics.isPathFrom_ends_mem hR).1
    subst r₁
    rcases hchoice with h | h | h | h <;> cases h <;>
      have hh := (hsame 5 (by simp)).mpr (by decide) <;>
      exact (show ¬ graph.Adj 4 5 by decide) hh
  · obtain ⟨a, b, P, P', hchoice, R, r₁, r₂, hR, hRF, _, hsame, _⟩ := h
    have hr : r₁ = 4 := hRF r₁ (PathBasics.isPathFrom_ends_mem hR).1
    subst r₁
    rcases hchoice with h | h | h | h <;> cases h <;>
      have hh := (hsame 5 (by simp)).mpr (by decide) <;>
      exact (show ¬ graph.Adj 4 5 by decide) hh
  · obtain ⟨x, y, Q', hchoice, f, hf, hsame, hnon⟩ := h
    have he : f = 4 := hf
    subst f
    rcases hchoice with h | h | h | h <;> cases h
    · exact hnon (by decide)
    · exact (show ¬ graph.Adj 7 0 by decide) ((hsame 0 (by simp)).mp (by decide))
    · exact (show ¬ graph.Adj 4 3 by decide) ((hsame 3 (by simp)).mpr (by decide))
    · exact (show ¬ graph.Adj 9 0 by decide) ((hsame 0 (by simp)).mp (by decide))

end Workspace.ProofLemmas.Thm93CaseTwoCounterexample
