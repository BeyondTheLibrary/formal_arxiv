import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# 5.7 — shared vocabulary for the carve-outs

Predicate abbreviations for the hypothesis and the two conjuncts of the conclusion of
`Workspace.Statements.S05.SPGT.thm_5_7` (printed p. 22).  Each `def` below is *literally* the
corresponding sub-formula of the frozen statement, so a hypothesis or goal of the frozen theorem
is accepted for the abbreviation by `exact` (definitional unfolding), with no rewriting.

Nothing here is a mathematical claim; this module carries no `sorry`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The hypothesis of 5.7: *"there is no track in `H` of even length `≥ 4`, with its end-edges
in `X` and with no other edge in `X`"*. -/
def NoEvenTrack57 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ¬ ∃ (q : List W) (_hq : 5 ≤ q.length),
    IsTrackList H q ∧ Even (trackLength q) ∧
    s(q[0], q[1]) ∈ X ∧ s(q[q.length - 2], q[q.length - 1]) ∈ X ∧
    ∀ e ∈ trackEdges q, e ≠ s(q[0], q[1]) →
      e ≠ s(q[q.length - 2], q[q.length - 1]) → e ∉ X

/-- 5.7 alternative 2: *"there is a branch-vertex `b` of `H` with `X ⊆ δ(b)`"*. -/
def Stmt57_2 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ b ∈ branchVertices H, X ⊆ incidentEdges H b

/-- 5.7 alternative 3: *"there is a branch `B` of `H` with `X ⊆ E(B)`"*. -/
def Stmt57_3 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ q : List W, IsBranch H q ∧ X ⊆ trackEdges q

/-- 5.7 alternative 4: *"there is a branch `B` of `H` with ends `b₁, b₂` say, such that
`X \ E(B) = δ(b₁) \ E(B)`"*. -/
def Stmt57_4 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ (q : List W) (b₁ b₂ : W), IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
    X \ trackEdges q = incidentEdges H b₁ \ trackEdges q

/-- 5.7 alternative 5: *"there is a branch `B` of `H` of odd length with ends `b₁, b₂` say,
such that `X \ E(B) = (δ(b₁) ∪ δ(b₂)) \ E(B)`"*. -/
def Stmt57_5 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ (q : List W) (b₁ b₂ : W), IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
    Odd (trackLength q) ∧
    X \ trackEdges q = (incidentEdges H b₁ ∪ incidentEdges H b₂) \ trackEdges q

/-- 5.7 alternative 6: *"there are two vertices `c₁, c₂` of `H`, of different biparity and not
in the same branch of `H`, such that `X = δ(c₁) ∪ δ(c₂)`"*. -/
def Stmt57_6 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ c₁ c₂ : W, DifferentBiparity H c₁ c₂ ∧
    (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
    X = incidentEdges H c₁ ∪ incidentEdges H c₂

/-- The six-fold disjunction — the first assertion of 5.7. -/
def Concl57 (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  SaturatesLineGraph H X ∨ Stmt57_2 H X ∨ Stmt57_3 H X ∨
    Stmt57_4 H X ∨ Stmt57_5 H X ∨ Stmt57_6 H X

/-- *"branch-vertices of `H` incident with more than one edge in `X`"*. -/
def BigBranchVertices (H : SimpleGraph W) (X : Set (Sym2 W)) : Set W :=
  {b ∈ branchVertices H | (incidentEdges H b ∩ X).Nontrivial}

/-- The final *"In particular …"* sentence of 5.7 — its second assertion. -/
def Concl57Final (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  (SaturatesLineGraph H X ∨ Stmt57_6 H X) ∨
    ((BigBranchVertices H X).ncard ≤ 2 ∧
      ((BigBranchVertices H X).ncard = 2 → Stmt57_5 H X))

/-- *"there are two disjoint edges in `X`"* — the standing assumption granted by claim (1). -/
def TwoDisjointEdges (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ e ∈ X, ∃ f ∈ X, DisjointEdges e f

/-- *"there is a branch `B` of `H` such that every edge in `X` has at least one end in
`V(B)`"* — the hypothesis of claim (2). -/
def SomeBranchMeetsAll (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∃ q : List W, IsBranch H q ∧ ∀ e ∈ X, ∃ v : W, v ∈ q ∧ v ∈ e

end Workspace.ProofLemmas.Thm57Setup
