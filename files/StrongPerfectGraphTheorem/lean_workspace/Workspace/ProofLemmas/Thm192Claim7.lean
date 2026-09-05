import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim6
import Workspace.ProofLemmas.Thm192Claim7Gap
import Workspace.ProofLemmas.Thm192Claim7Reduction

/-!
# Claim (7) of the printed proof of 19.2

PAPER (printed pp. 119–120):

> **(7)** *Not both `x₂, y` have neighbours in `{p₁,…,pₙ}`.*
>
> *For by (6) we may assume that `x₂` is nonadjacent to `x₀`, and similarly nonadjacent to
> `x₁`.  Choose `i` with `1 ≤ i ≤ n` maximum such that `x₂` is adjacent to `pᵢ`.  From the
> hole `z-x₂-pᵢ-⋯-pₙ-x₁-z` it follows that `i` is odd.  Suppose first that `x₂` is not
> `Y₀`-complete.  By (2), `z` is `Y`-complete and `(C, Y₀)` is a wheel.  By 16.1, `pᵢ, z`
> have the same wheel-parity, and so there are an odd number of `Y₀`-complete edges in
> `pᵢ-⋯-pₙ-x₁`.  By (4) no edge of the path `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete.  Consequently
> `zx₁` is the unique `Y`-complete edge of the hole `z-x₂-pᵢ-⋯-pₙ-x₁-z` (`= C₁` say).
> Suppose that `y` is nonadjacent to all `x₂, pᵢ,…,pₙ`.  Now `y` has a neighbour in
> `{p₁,…,pₙ}` by hypothesis, so `{p₁,…,pₙ,x₂}` (`= F` say) catches the triangle `{z,x₁,y}`.
> The only neighbour of `z` in `F` is `x₂`; the only neighbour of `x₁` in `F` is `pₙ`; and
> `y` is nonadjacent to both `x₂, pₙ` by assumption.  By 17.1, `F` includes a reflection of
> the triangle; but then `i = n` and there is an antihole of length 6 using `z, x₁, pₙ`,
> contrary to 15.7.  This proves that `y` is adjacent to one of `x₂, pᵢ,…,pₙ`.  Since there
> is an odd number of `Y₀`-complete edges in the path `pᵢ-⋯-pₙ-x₁`, it follows that every
> member of `Y` is adjacent to one of `x₂, pᵢ,…,pₙ`.  Consequently `Y` contains no hat for
> `C₁`.  Assume that `C₁` has length `≥ 6`.  By 2.10, `Y` contains a leap, so there are
> nonadjacent `y₁, y₂ ∈ Y` such that `y₁-x₂-pᵢ-⋯-pₙ-y₂` is a path, of odd length `≥ 5`.
> But the ends of this path are `{x₀,x₁}`-complete and its internal vertices are not,
> contrary to 13.6.  So `C₁` has length 4, that is, `i = n`, and `pₙ` is `Y₀`-complete.  By
> (4) it follows that `pₙ` is nonadjacent to `y`, and therefore `y` is adjacent to `x₂`
> (since we already showed that `y` is adjacent to one of `x₂, pᵢ,…,pₙ`).  From the symmetry
> between `x₀, x₁` we deduce that the same holds for `p₁`, that is, `p₁` is
> `Y₀ ∪ {x₂}`-complete and nonadjacent to `y`.  Let `Q` be an antipath between `x₂, y` with
> interior in `Y₀`; then the three antipaths `p₁-x₁`, `pₙ-x₀` and `y-Q-x₂` form a long prism
> in `G` with triangles `{p₁,pₙ,y}` and `{x₁,x₀,x₂}`, a contradiction.  This proves (7)
> assuming that `x₂` is not `Y₀`-complete.*
>
> *We therefore assume that `x₂` is `Y₀`-complete, and consequently nonadjacent to `y`.  Now
> `{x₂,p₁,…,pₙ}` is connected and catches the triangle `{z,x₁,y}`.  By 15.7, it contains no
> reflection of the triangle, since as before that would give an antihole of length 6 with
> three vertices in `C`.  So by 17.1, there is a vertex in `{x₂,p₁,…,pₙ}` with two
> neighbours in the triangle.  The only neighbour of `z` in it is `x₂`, which is nonadjacent
> to both `x₁, y`.  The only neighbour of `x₁` in it is `pₙ`, and therefore `y` is adjacent
> to `pₙ`.  We recall that `i` is maximum such that `x₂` is adjacent to `pᵢ`.  Since `y` is
> adjacent to `pₙ`, we may choose `j` with `i ≤ j ≤ n` minimum such that `y` is adjacent to
> `pⱼ`.  From the hole `z-x₂-pᵢ-⋯-pⱼ-y-z` we see that `j` is odd.  Suppose `j ≠ i`.  Then
> the path `x₂-pᵢ-⋯-pⱼ-y` is even and has length `≥ 4`.  By 13.7 with anticonnected sets
> `{x₀,x₁}`, `Y₀ ∪ {z}` we deduce that `Y₀ ∪ {z}` is not anticonnected, and hence `z` is
> `Y`-complete.  Consequently, by (4), no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete, and in
> particular `pₙ` is not `Y`-complete, and therefore not `Y₀`-complete (since `pₙ` is
> adjacent to `y`).  Since there is no `Y`-complete edge in the odd path `pⱼ-⋯-pₙ-x₁`, and
> the `Y`-complete vertex `z` has no neighbour in its interior, it follows from 2.2 that
> `pⱼ` is not `Y`-complete and hence not `Y₀`-complete.  By 18.2 with sets `{x₀,x₁}`, `Y₀`,
> since the `{x₀,x₁} ∪ Y₀`-complete vertex `z` has no neighbours in `A`, it follows that
> there are an odd number of `Y₀`-complete edges in the path `x₂-pᵢ-⋯-pⱼ-y`.  Since `y` is
> not `Y₀`-complete, they all belong to the path `x₂-pᵢ-⋯-pⱼ`.  Since `x₂z, zx₁` are both
> `Y₀`-complete edges and `x₁pₙ` is not, it follows that `pⱼ, pₙ` have opposite wheel-parity
> with respect to the wheel `(C₁, Y₀)`, where `C₁` is `z-x₂-pᵢ-⋯-pₙ-x₁-z`.  But `pⱼ, pₙ` are
> both not `Y₀`-complete, and so `(C₁, Y₀)` is an odd wheel, contrary to `G ∈ F₇`.  This
> proves that `j = i`, that is, `y` is adjacent to `pᵢ`.*
>
> *Suppose that `i < n`.  If `pᵢ` is not `Y`-complete then an antipath between `pᵢ` and `y`
> with interior in `Y₀` can be extended via `y-x₂-x₁-pᵢ` to an antihole sharing the vertices
> `pᵢ, x₁, x₂` with the hole `z-x₂-pᵢ-⋯-pₙ-x₁-z` (`= C₁` say), contrary to 15.7.  So `pᵢ` is
> `Y`-complete, and therefore so is `z`, by (4).  But then `(C₁, Y)` is an odd wheel, since
> `z, x₁, pᵢ` are `Y`-complete and `x₂, pₙ` are not (by (4)), contrary to `G ∈ F₇`.  So
> `i = n`, and hence `pₙ` is adjacent to both `x₂, y`.  From the symmetry between `x₀, x₁`
> it follows that `p₁` is adjacent to both `x₂, y`.  By (4), `p₁, pₙ` are not `Y`-complete.
> So in `Ḡ`, the connected set `Y ∪ {p₁,pₙ}` catches the triangle `{x₀,x₁,x₂}`;
> `x₀, x₁, x₂` all have unique neighbours in it, namely `pₙ, p₁, y` respectively; and these
> three vertices do not form a triangle since `yp₁` is not an edge (of `Ḡ`), contrary to
> 17.1.  This proves (7).*

Encoding is as in claim (6), with the hypothesis `x₀` adjacent to `x₂` dropped.

**`hcex`, the minimum-counterexample hypothesis.**  The printed proof of (7) cites claim (4)
repeatedly, and every citation is of an `hcex`-dependent conjunct of (4):

* *"By (4) no edge of the path `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete"* — claim (4)'s **second**
  conjunct, verbatim;
* *"Consequently, by (4), no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete"* (second paragraph) —
  the same second conjunct again;
* *"By (4) it follows that `pₙ` is nonadjacent to `y`"* — via (4)'s **fourth** conjunct
  (`pₙ` is not `Y ∪ {x₂}`-complete), which the paper derives from the second;
* *"`z, x₁, pᵢ` are `Y`-complete and `x₂, pₙ` are not (by (4))"* and *"By (4), `p₁, pₙ` are
  not `Y`-complete"* — (4)'s **third** and **fourth** conjuncts;
* *"So `pᵢ` is `Y`-complete, and therefore so is `z`, by (4)"* — this one uses (4)'s
  **first** conjunct, which is `hcex`-free, but it does not remove the dependence created by
  the citations above.

Claim (4)'s second/third/fourth conjuncts are reductios against the choice of `Y` as a
*minimum counterexample* (*"The second is immediate, for otherwise `(C,Y)` satisfies the
theorem"*), i.e. against the standing assumption `¬ Concl192 G z A₀ x Y` set up by the first
line of the proof of 19.2 (*"If possible, choose `Y` not satisfying the theorem, with `|Y|`
minimum"*).  Since `Concl192` is 19.2's actual conclusion it cannot be refuted from (7)'s own
hypotheses, so that standing assumption is carried explicitly as `hcex`, in the same binder
slot as in claims (4), (10), (11) and (12).  On the assembly side
(`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by `by_contra` on the goal
`Concl192 G z A₀ x Y` at the top of `core`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim7

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(7)** of the printed proof: *"Not both `x₂, y` have neighbours in
`{p₁,…,pₙ}`."* -/
theorem claim7 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y}))) :
    ¬ ((∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧ (∃ w ∈ SPGT.interior P, G.Adj y w)) := by
  intro hboth
  -- PAPER: *"For by (6) we may assume that `x₂` is nonadjacent to `x₀`, and similarly
  -- nonadjacent to `x₁`."*
  by_cases h02 : G.Adj (x 0) (x 2)
  · exact Thm192Claim6.claim6 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin hcex P hP hPint hPlen hchoice h02 hboth
  by_cases h12 : G.Adj (x 1) (x 2)
  · exact Thm192Claim7Reduction.claim6_at_x1 G hG z A₀ hframe x hws Y hHyp ih y hyY
      hyz hY0 A hA hAmin hcex P hP hPint hPlen hchoice h12 hboth
  have hx20 : ¬ G.Adj (x 2) (x 0) := fun h => h02 h.symm
  have hx21 : ¬ G.Adj (x 2) (x 1) := fun h => h12 h.symm
  by_cases hx2c : VertexComplete G (x 2) (Y \ {y})
  · have hx2y : ¬ G.Adj (x 2) y := by
      intro hadj
      apply hHyp.2.2.2.2.1
      intro w hwY
      by_cases hwy : w = y
      · simpa [hwy] using hadj
      · exact hx2c w ⟨hwY, by simpa using hwy⟩
    exact Thm192Claim7Gap.complete_endpoint_nonadjacent_case G hG z A₀ hframe x hws Y
      hHyp ih y hyY hyz hY0 A hA hAmin hcex P hP hPint hPlen hx2c hx2y hx20 hx21 hboth
  · rcases hchoice with hc | ⟨hwheel, htwo⟩
    · exact (hx2c hc).elim
    · exact Thm192Claim7Gap.noncomplete_endpoint_nonadjacent_case G hG z A₀ hframe x
        hws Y hHyp ih y hyY hyz hY0 A hA hAmin hcex P hP hPint hPlen hwheel htwo hx2c
        hx20 hx21 hboth

end Workspace.ProofLemmas.Thm192Claim7
