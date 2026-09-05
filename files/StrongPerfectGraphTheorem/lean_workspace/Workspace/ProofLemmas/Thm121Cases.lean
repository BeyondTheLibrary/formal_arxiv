import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm121Case1
import Workspace.ProofLemmas.Thm121Case2
import Workspace.ProofLemmas.Thm121Case3
import Workspace.ProofLemmas.Thm121Case4
import Workspace.ProofLemmas.Thm121Symmetry

/-!
# The existence half of 12.1 — the paper's four-case analysis

PAPER (printed p. 69, the proof of 12.1) — the printed argument establishes that **at least
one** of the three alternatives of 12.1 holds; that at most one of them holds is left implicit
by the authors and is discharged separately in `Workspace.ProofLemmas.Thm121Exclusive`.

The printed proof runs:

*"(1) If `v` is left- or right-diagonal then the theorem holds.*  For assume `v` is
right-diagonal say.  If it has no neighbours in `A ∪ C` then statement 3 of the theorem holds,
so we assume there is a step `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` such that `v` has a neighbour in
`R₁ \ b₁`.  Hence it can be linked onto the triangle `{a₀, a₁, a₂}`, via `v`-`a₀`, the path from
`v` to `a₁` with interior in `R₁ \ b₁`, and the path from `v` to `a₂` with interior in `R₂`, and
so by 2.4, `v` has a neighbour in `A`.  So it is major, and therefore statement 2 holds.  This
proves (1).*

*(2) If `v` is adjacent to both `a₀, b₀` then the theorem holds.*  For then it has a neighbour
in `R₀*`, since `R₀` is odd and has length `≥ 3` and `v` is adjacent to both its ends; and we
may assume that `v` has a neighbour in `V(S)`, for otherwise statement 1 of the theorem holds.
If `v` has no neighbour in `B` then it is a left-star by 11.1, and statement 3 of the theorem
holds, so we may assume it has neighbours in `B` and similarly in `A`.  Hence it is major.
Since `(S, V(R₀*), {v})` is not a 1-breaker, `v` does not have nonneighbours in both `A` and
`B`, so it is either left- or right-diagonal and the claim follows from (1).  This proves (2).*

*(3) If `v` is adjacent to `a₀` and not to `b₀` then the theorem holds.*  For we may assume `v`
has a neighbour in `V(S)`.  If `v` has a neighbour in `R₀*`, then by 11.2 it is either
`B`-complete (when it is right-diagonal and the claim follows from (1)) or a left-star (when
statement 3 holds).  So we may assume it has no neighbour in `R₀*`.  We may assume it has a
neighbour in `B ∪ C`, for otherwise it is minor and statement 1 of the theorem holds; let
`a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step such that `v` has a neighbour in `R₁ \ a₁`, and in
addition such that `v` is not adjacent to `b₂` if possible.  By 10.4, `v` has a neighbour in
`R₂`.  If `a₂` is its only neighbour in `R₂`, then the strip `S' = (A ∪ {v}, C, B)` is
step-connected, since `v`-`R`-`b₁`, `a₂`-`R₂`-`b₂` is an `S'`-step where `R` is the path from
`v` to `b₁` with interior in `R₁ \ a₁`; and since `v` is adjacent to `a₀` and has no other
neighbours in `R₀`, this is contrary to the maximality of the staircase.  So `v` has a
neighbour in `R₂ \ a₂`; and hence `v` can be linked onto the triangle `{b₀, b₁, b₂}` via
`v`-`a₀`-`R₀`-`b₀`, and for `i = 1, 2`, the path from `v` to `bᵢ` with interior in `Rᵢ \ aᵢ`.
By 2.4 it follows that `v` is adjacent to both `b₁, b₂`; and hence from our choice of the step
`R₁, R₂`, and since the strip is step-connected, it follows that `v` is right-diagonal, and the
claim follows from (1).  This proves (3).*

*(4) If `v` is nonadjacent to both `a₀, b₀` then the theorem holds.*  For then we may assume
that `v` has a neighbour in `V(S)`, since otherwise it is minor, and statement 3 of the theorem
holds.  Suppose first that `v` also has a neighbour in `R₀*`.  If `v` is a left-star then
statement 3 holds, so we assume not; and then by 11.2, `v` is `B`-complete.  Similarly `v` is
`A`-complete and therefore central, and statement 2 holds.  Thus we may assume that `v` has no
neighbour in `V(R₀)`, and therefore `v` is minor.  We claim that statement 1 holds, and to show
this we may assume that `v` is `A`-complete.  Let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step;
then by 10.4, `v` has no neighbour in `R₁ \ a₁` or in `R₂ \ a₂`, and therefore `v` is a
left-star, and statement 1 holds.  This proves (4).*

*But (2)-(4) cover all the possibilities, up to symmetry, and this completes the proof of
12.1."*

The results cited are 2.4 (the Roussel–Rubio "linking onto a triangle" lemma), 10.4, 11.1 and
11.2, together with the maximality of the staircase.

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm121Cases

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

/-- **At least one of the three alternatives of 12.1 holds** — the content of cases (1)–(4) of
the printed proof. -/
theorem thm121Cases {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  by_cases ha : G.Adj v a₀
  · by_cases hb : G.Adj v b₀
    · -- PAPER: *"(2) If `v` is adjacent to both `a₀, b₀` then the theorem holds."*
      exact Workspace.ProofLemmas.Thm121Case2.thm121Case2 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv ha hb
    · -- PAPER: *"(3) If `v` is adjacent to `a₀` and not to `b₀` then the theorem holds."*
      exact Workspace.ProofLemmas.Thm121Case3.thm121Case3 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv ha hb
  · by_cases hb : G.Adj v b₀
    · -- PAPER: *"But (2)-(4) cover all the possibilities, up to symmetry"* — the remaining
      -- possibility is case (3) applied to the staircase with its two ends exchanged.
      refine Workspace.ProofLemmas.Thm121Symmetry.thm121SwapConclusion G A C B a₀ b₀ R₀ v ?_
      exact Workspace.ProofLemmas.Thm121Case3.thm121Case3 G hG hK4 hprism hbreaker B C A b₀ a₀ R₀.reverse (Workspace.ProofLemmas.Thm121Symmetry.thm121SwapStaircase G A C B a₀ b₀ R₀ hK) v (by rw [Workspace.ProofLemmas.Thm121Symmetry.thm121SwapVertices A C B R₀]; exact hv) hb ha
    · -- PAPER: *"(4) If `v` is nonadjacent to both `a₀, b₀` then the theorem holds."*
      exact Workspace.ProofLemmas.Thm121Case4.thm121Case4 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv ha hb

end Workspace.ProofLemmas.Thm121Cases
