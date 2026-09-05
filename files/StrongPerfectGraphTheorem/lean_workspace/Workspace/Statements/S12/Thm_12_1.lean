import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm121Cases
import Workspace.ProofLemmas.Thm121Exclusive

/-!
# Section 12 — Attachments in a staircase

The five numbered statements 12.1–12.5 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 69–77),
transcribed from `paper/pdf/S12_Attachments_in_a_staircase.md`.

All the defined terms used here are imported and never restated: *step-connected strip*,
*left-star*, *right-star*, *banister*, *1-breaker*, *staircase*, `V(K)`, *maximal*, *local*,
*minor*, *major*, *left-diagonal*, *right-diagonal*, *central*, *strongly maximal* and
*2-breaker* come
from `Workspace.Types.Staircases`; *even prism* from `Workspace.Types.Prisms`; *attachment*,
*appearance* from `Workspace.Types.Appearances`; *Berge*, *connected set*, *antipath*,
*interior*, *complete*/*anticomplete* from `Workspace.Types.Core`; *balanced skew partition*
from `Workspace.Types.Decompositions`.

Published-vs-draft note: case 1 of **12.1** is the published one, *"`v` is minor; and in that
case, either `v` is a left-star or `v` is not `A`-complete, and either `v` is a right-star or
`v` is not `B`-complete"*; the arXiv v1 draft has only *"`v` is minor"*.
-/

set_option autoImplicit false

namespace Workspace.Statements.S12

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **12.1** (printed p. 69)

PAPER: *"Let `G` be a Berge graph, such that there is no appearance of `K₄` in `G`, no even
prism in `G`, and no 1-breaker in `G`.  Let `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` be a maximal
staircase in `G`, and let `v ∈ V(G) \ V(K)`.  Then exactly one of the following holds:*

*1. `v` is minor; and in that case, either `v` is a left-star or `v` is not `A`-complete, and
either `v` is a right-star or `v` is not `B`-complete.*

*2. `v` is major; and in that case, it is either left- or right-diagonal or central.*

*3. `v` is a left-star with a neighbour in `R₀ \ a₀`, or a right-star with a neighbour in
`R₀ \ b₀`."*

Notes on the transcription.

* This is the **published** form of case 1.  The arXiv v1 draft reads only *"`v` is minor"*;
  the published version adds the clause about `A`- and `B`-completeness, and rewrites the
  proof of 12.1(4) accordingly.
* *"and in that case, …"* in cases 1 and 2 is part of the alternative, so each of those
  alternatives is the conjunction of the type of `v` with the extra conclusion.
* *"exactly one of the following holds"* is `∃! i : Fin 3, ![·, ·, ·] i`, the three
  alternatives being listed in the printed order.  (This is provably equivalent to
  `(P₁ ∨ P₂ ∨ P₃) ∧ ¬(P₁ ∧ P₂) ∧ ¬(P₁ ∧ P₃) ∧ ¬(P₂ ∧ P₃)`.) -/
theorem thm_12_1 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀) :
    ∃! i : Fin 3,
      ![-- 12.1.1
        MinorForStaircase G A C B a₀ R₀ b₀ v ∧
          (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
          (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B),
        -- 12.1.2
        MajorForStaircase G A C B a₀ R₀ b₀ v ∧
          (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
            CentralForStaircase G A C B a₀ R₀ b₀ v),
        -- 12.1.3
        (IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
          (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)] i := by
  -- PAPER: cases (1)–(4) of the printed proof show that at least one of the three alternatives
  -- holds; *"But (2)-(4) cover all the possibilities, up to symmetry, and this completes the
  -- proof of 12.1."*
  have hone :=
    Workspace.ProofLemmas.Thm121Cases.thm121Cases G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv
  -- That the three alternatives are mutually exclusive — the word *"exactly"* in the statement —
  -- is immediate from the definitions; see `Workspace.ProofLemmas.Thm121Exclusive`.
  have hexcl :=
    Workspace.ProofLemmas.Thm121Exclusive.thm121Exclusive G A C B a₀ b₀ R₀ hK.1 v
  exact Workspace.ProofLemmas.Thm121Exclusive.existsUnique_fin3 hone hexcl.1 hexcl.2.1 hexcl.2.2


end SPGT

end Workspace.Statements.S12
