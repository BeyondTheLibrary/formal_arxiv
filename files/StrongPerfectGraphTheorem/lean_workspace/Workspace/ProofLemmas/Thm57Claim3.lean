import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim3Draft

/-!
# 5.7, printed claim (3)

PAPER (printed pp. 23–24):

> **(3) There do not exist three tracks of `H` with an end (`b` say) in common and otherwise
> vertex-disjoint, such that each contains an edge in `X`, and at least two of the three edges
> of the tracks incident with `b` do not belong to `X`.**
>
> For suppose that `P₁, P₂, P₃` are three such tracks, where `Pᵢ` is between `aᵢ` and `b`, for
> `1 ≤ i ≤ 3`.  We may assume that for each `i`, the only edge of `Pᵢ` in `X` is the edge
> incident with `aᵢ`.  Now two of `P₁, P₂, P₃` have lengths of the same parity, say `P₁, P₂`;
> and their union is an even track with end-edges in `X` and its other edges not in `X`.  By
> hypothesis it has length 2, and so `P₁, P₂` both have length 1.  But then at most one edge of
> `P₁ ∪ P₂ ∪ P₃` incident with `b` does not belong to `X`, a contradiction.  This proves (3).

Encoding notes.

* Each `Pᵢ` is the list of its vertices oriented **from `b`**, so `IsTrackFrom H Pᵢ b aᵢ`, and
  *"the edge of the track incident with `b`"* is `s(Pᵢ[0], Pᵢ[1])`.  The guard
  `2 ≤ Pᵢ.length` is what makes that edge exist (a track with an edge in `X` has one anyway;
  it is stated as a binder so the `getElem` side conditions discharge automatically).
* *"otherwise vertex-disjoint"* is *"any common vertex of two of the tracks is `b`"*.
* *"at least two of the three … do not belong to `X`"* is written as the disjunction over the
  three pairs.
* Only the no-even-track hypothesis of 5.7 is used; neither bipartiteness nor cyclic
  3-connectivity enters the printed argument for (3).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **5.7 (3)** — no three tracks meeting only at a common end `b`, each carrying an edge of
`X`, with at least two of the three `b`-incident edges outside `X`. -/
theorem thm57Claim3 (H : SimpleGraph W) (X : Set (Sym2 W))
    (hnotrack : NoEvenTrack57 H X) :
    ¬ ∃ (b a₁ a₂ a₃ : W) (P₁ P₂ P₃ : List W)
        (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
      IsTrackFrom H P₁ b a₁ ∧ IsTrackFrom H P₂ b a₂ ∧ IsTrackFrom H P₃ b a₃ ∧
      (∀ v : W, v ∈ P₁ → v ∈ P₂ → v = b) ∧
      (∀ v : W, v ∈ P₁ → v ∈ P₃ → v = b) ∧
      (∀ v : W, v ∈ P₂ → v ∈ P₃ → v = b) ∧
      (∃ e ∈ trackEdges P₁, e ∈ X) ∧
      (∃ e ∈ trackEdges P₂, e ∈ X) ∧
      (∃ e ∈ trackEdges P₃, e ∈ X) ∧
      ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
       (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
       (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X)) := by
  exact Workspace.ProofLemmas.Thm57Claim3Draft.draft H X hnotrack

end Workspace.ProofLemmas.Thm57Claim3
