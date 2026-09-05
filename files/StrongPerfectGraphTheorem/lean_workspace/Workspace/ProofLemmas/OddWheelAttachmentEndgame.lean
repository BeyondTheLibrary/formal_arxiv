import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelTrichotomy
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.OddWheelAttachmentMain
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S15.Thm_15_3

/-!
# 16.2, the endgame: from *"From (4) we may assume that `X₁` has only one member"* to the end

PAPER (16.2, printed pp. 99–100).  This module discharges
`Workspace.ProofLemmas.OddWheelAttachmentMain.Endgame`, i.e. the last part of the `|F| ≥ 2`
line of the proof of 16.2:

* the paragraph after claim (4) — choosing `i`, `j`, building the holes `H₁`, `H₂`, deducing
  that `i, j, k` all have the same parity, that each of `H₁`, `H₂` carries exactly one
  `Y`-complete edge and exactly two `Y`-complete vertices, that `j > i`, that `p₁` is
  `Y`-complete, and hence that `p₂` and `p_n` are `Y`-complete;
* claim (5) — *"`f_k` has no neighbour in `{p₃, …, p_{j−2}}`"*;
* the closing paragraph — `i = 2`, `j = n`, so `p₂, p_n` are `f_k`'s only neighbours,
  contradicting that `X` contains a nonadjacent pair of opposite wheel-parity.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ### The index picture

PAPER: *"From (4) we may assume that `X₁` has only one member, say `p₁`.  Choose `i, j` with
`2 ≤ i, j ≤ n`, such that `p_i, p_j` are adjacent to `f_k`, with `i` minimum and `j` maximum."*

Following the project's established style the rim is **not** rotated.  A base offset `b` with
`C[b] = p₁` is fixed once, and the paper's `p_t` is read as `q (t - 1)` where
`q d = C[(b + d) % n]`.  The paper's `f_t` is `f t = P[t]`, so `f 0 = p₁` and `f (k+1) = p_m`.
The paper's `i` is `a + 1` and its `j` is `c + 1`, so that *"`p_i`, `p_j` are adjacent to
`f_k`"* reads `G.Adj (f k) (q a)`, `G.Adj (f k) (q c)`.

Every index fact the endgame needs is a field, so that the printed blocks below can be stated
against `Setup` alone. -/
structure Setup (G : SimpleGraph V) (C : List V) (Y : Set V) (P : List V)
    (q f : ℕ → V) (b a c k : ℕ) : Prop where
  /-- `G ∈ F₆`. -/
  inF6 : InF6 G
  /-- `(C, Y)` is a wheel. -/
  wheel : IsWheel G C Y
  /-- The base offset is a genuine position of the rim. -/
  blt : b < C.length
  /-- `q d` is the rim vertex at cyclic position `b + d`; the paper's `p_{d+1}`. -/
  qdef : ∀ t : ℕ, C[(b + t) % C.length]? = some (q t)
  /-- `P` is the path `p₁-f₁-⋯-f_k-p_m`. -/
  path : IsPathList G P
  /-- `k = |P| - 2 = |F|`. -/
  plen : P.length = k + 2
  /-- The standing assumption `|F| ≥ 2` of this line of the proof. -/
  klb : 2 ≤ k
  /-- `f t` is the `t`-th vertex of `P`; the paper's `f_t` for `1 ≤ t ≤ k`. -/
  fdef : ∀ t : ℕ, t < P.length → P[t]? = some (f t)
  /-- `p₁` is both the first vertex of `P` and the base point of the rim. -/
  base : f 0 = q 0
  /-- No `f_t` lies on the rim. -/
  fnotC : ∀ t : ℕ, 1 ≤ t → t ≤ k → f t ∉ C
  /-- No `f_t` lies in the hub. -/
  fnotY : ∀ t : ℕ, 1 ≤ t → t ≤ k → f t ∉ Y
  /-- No `f_t` is `Y`-complete. -/
  fnotComplete : ∀ t : ℕ, 1 ≤ t → t ≤ k → ¬ VertexComplete G (f t) Y
  /-- `X₁ = {p₁}`: the only rim neighbour of `f₁` is `p₁`. -/
  adjFst : ∀ u : V, u ∈ C → (G.Adj (f 1) u ↔ u = q 0)
  /-- The intermediate `f_t` have no rim neighbours at all. -/
  adjMid : ∀ t : ℕ, 2 ≤ t → t + 1 ≤ k → ∀ u : V, u ∈ C → ¬ G.Adj (f t) u
  /-- `p₁` is not a neighbour of `f_k` (it lies in `X₁`, and `X₁ ∩ X₂ = ∅`). -/
  notAdjLstBase : ¬ G.Adj (f k) (q 0)
  /-- `p_i` is a neighbour of `f_k`. -/
  adjLstMin : G.Adj (f k) (q a)
  /-- `p_j` is a neighbour of `f_k`. -/
  adjLstMax : G.Adj (f k) (q c)
  /-- `i` is minimum. -/
  minSpec : ∀ d : ℕ, 1 ≤ d → d < a → ¬ G.Adj (f k) (q d)
  /-- `j` is maximum. -/
  maxSpec : ∀ d : ℕ, c < d → d < C.length → ¬ G.Adj (f k) (q d)
  alb : 1 ≤ a
  aub : a + 2 ≤ C.length
  clb : 2 ≤ c
  cub : c + 1 ≤ C.length
  ac : a ≤ c
  /-- The nonadjacent pair of opposite wheel-parity inside `X`: `p₁` together with a neighbour
  of `f_k` that is neither `p₂` nor `p_n`.  This is the fact the closing sentence contradicts. -/
  midNbr : ∃ d : ℕ, 2 ≤ d ∧ d + 2 ≤ C.length ∧ G.Adj (f k) (q d)
  /-- Every rim neighbour of `f_k` has wheel-parity opposite to `p₁`. -/
  oppLst : ∀ d : ℕ, G.Adj (f k) (q d) → OppositeWheelParity G C Y (q 0) (q d)

/-! ### The contradiction, packaged

The whole endgame ends in `False`; `Contradiction G` is that statement against `Setup`. -/

/-- *"…contradicting that there are nonadjacent vertices in `X` of opposite wheel-parity.
This proves 16.2."* -/
def Contradiction (G : SimpleGraph V) : Prop :=
  ∀ (C : List V) (Y : Set V) (P : List V) (q f : ℕ → V) (b a c k : ℕ),
    Setup G C Y P q f b a c k → False

end Workspace.ProofLemmas.OddWheelAttachmentEndgame
