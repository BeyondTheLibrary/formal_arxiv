/-  Proof attempt for statement 16.3 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 101).

    THE PAPER'S PROOF (paper/proofs/16_3.md) runs in four movements, and this file is the
    composition of the four modules that carry them:

    1. "Suppose (C,Y) is an odd wheel with Y maximal, and subject to that, such that the number
       of Y-complete edges in C is minimum."
         -> `WheelBasics.exists_optimal_odd_wheel`

    2. claim (1): "There is no vertex v in V(G) \ (V(C) u Y) such that v is not Y-complete and
       has nonadjacent neighbours in C of opposite wheel-parity."
         -> `OddWheelNoOddExtSegment.no_odd_ext_segment`     (Case A: no odd Y u {v}-segment)
         -> `OddWheelLines.no_bad_vertex_of_no_odd_ext_segment`  (Case B: the "lines" argument)
         glued as `OddWheelAssembly.claim_one`

    3. "Since (C,Y) is an odd wheel, C has at least two segments ... By 16.2 and (1), there is a
       3-vertex path p1-p2-p3 in C, all Y-complete, and a path p1-f1-...-fk-p3 with interior in
       F, such that there are no edges between {f1,...,fk} and {p4,...,pn}."
         -> `OddWheelBulletThree.exists_bullet_three`
            (which uses 15.2 for Z, the minimal connected F, and 16.2, with claim (1) killing
             the first two bullets of 16.2 via `OddWheelBullets12`)

    4. "But then C \ p2 can be completed to a hole C' say, via p1-f1-...-fk-p3 ... contrary to
       the optimality of (C,Y)."
         -> `OddWheelRebuild.contradiction_from_bullet_three`

    `OddWheelAssembly.thm_16_3_of_rebuild` is movements 1-3 with movement 4 abstracted as
    `RebuildStep G`; supplying it is the single `exact` below.

    Two places where the printed argument is compressed rather than complete are recorded in
    AMBIGUITIES.md as A27 (the chain hidden by "and so there is a unique Y u {v}-complete edge in
    C") and A27a (the odd segment might a priori cover all but one rim vertex).                -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Wheels
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Appearances
import Workspace.ProofLemmas.OddWheelAssembly
import Workspace.ProofLemmas.OddWheelRebuild

set_option autoImplicit false

namespace Workspace.Statements.S16

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **16.3** (printed p. 101) — the main result of Section 16; it is statement 7 of 1.8
(*"for every `G ∈ F₆`, either `G` admits a balanced skew partition, or `G ∈ F₇`"*), restated,
and is one of the twelve main steps of the proof of 1.3.

PAPER: *"Let `G ∈ F₆`.  If there is an odd wheel in `G` then `G` admits a balanced skew
partition.  In particular, every recalcitrant graph belongs to `F₇`."*

Transcription notes.

* *"there is an odd wheel in `G`"* is `∃ C Y, IsOddWheel G C Y`: a wheel `(C,Y)` of `G` — `C`
  a hole of length `≥ 6`, `Y` a non-null anticonnected set disjoint from `C`, with two disjoint
  `Y`-complete edges of `C` — some `Y`-segment of whose rim has odd length.
* The closing sentence *"In particular, every recalcitrant graph belongs to `F₇`"* is part of
  the statement, and is formalized — but **not** here.  It quantifies over **all** finite
  graphs, not just over `G`, and the paper asserts it outright, so putting it under this
  theorem's hypothesis `G ∈ F₆` would assert it only if that hypothesis is satisfiable.  It is
  the separate, hypothesis-free theorem `thm_16_3_recalcitrant` below. -/
theorem thm_16_3 (G : SimpleGraph V) (hG : InF6 G) :
    (∃ (C : List V) (Y : Set V), IsOddWheel G C Y) → AdmitsBalancedSkewPartition G := by
  refine _root_.Workspace.ProofLemmas.OddWheelAssembly.thm_16_3_of_rebuild G hG ?_
  intro C Y hw hodd hmin F hFC hFY hFconn hFnc p₁ p₂ p₃ hblock hY1 hY2 hY3 P hP hPF hPno
  exact _root_.Workspace.ProofLemmas.OddWheelRebuild.contradiction_from_bullet_three
    hG.1.1.1 hodd hmin F hFC hFY hFnc p₁ p₂ p₃ hblock hY1 hY2 hY3 P hP hPF hPno


end SPGT

end Workspace.Statements.S16
