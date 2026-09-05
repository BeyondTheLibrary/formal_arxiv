import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Symmetry
import Workspace.ProofLemmas.Thm192Claim8Main

/-!
# Claim (8) of the printed proof of 19.2

PAPER (printed pp. 120–121):

> **(8)** *If `x₂` is nonadjacent to `y` then it is nonadjacent to both `x₀, x₁`.*
>
> *For assume `x₂` is nonadjacent to `y` and adjacent to `x₀` say.  Now `A ∪ {x₁}` catches
> the triangle `{z,x₀,x₂}`; it contains no reflection of this triangle, since `x₀, x₁` have
> no common neighbour in `A`; and the unique neighbour of `z` in this set is nonadjacent to
> both `x₀, x₂`.  So by 17.1 it follows that there is a vertex in `A` adjacent to both
> `x₀, x₂`.  Also, `A ∪ x₂` catches the triangle `{z,x₁,y}`.  Suppose that `A ∪ {x₂}`
> contains a reflection of this triangle; then there exists `f ∈ A` adjacent to `x₁, x₂` and
> not to `y`.  Since `f ∈ A` it follows that `f` is nonadjacent to `x₀`; but then
> `f-x₂-x₀-y-x₁-f` is an odd hole, a contradiction.  Hence by 17.1 there is a vertex in `A`
> adjacent to both `x₁, y`.  Consequently from (3), `A` is the vertex set of a path
> `f₁-⋯-f_k`, where `f₁` is adjacent to `x₀, x₂`, and `f_k` to `x₁, y`.  Since `f₁ ∈ A` it
> follows that `f₁` is not adjacent to `x₁`.*
>
> *Now assume that `f₁` is not the unique neighbour of `x₂` in `A`.  From (3), `f₁` is the
> unique neighbour of `x₀` in `A`.  By (7), `f_k` is not the unique neighbour of `x₁` in
> `A`, and so from (3) it is the unique neighbour of `y` in `A`.  In particular `y` is not
> adjacent to `f₁`.  Both `x₀, z` have unique neighbours in `A ∪ {x₁} = F` say, namely
> `f₁, x₁` respectively.  Now `x₀, z` are both `{x₂,y}`-complete, and `f₁, x₁` are not.
> Since `F \ {x₁}` is connected, this contradicts 17.3.  So `f₁` is the unique neighbour of
> `x₂` in `A`.  Suppose that `f_k` is the unique neighbour of `y` in `A`.  Then both `z, y`
> have unique neighbours in `A ∪ {x₂}`, namely `x₂, f_k` respectively; and `z, y` are
> `{x₀,x₁}`-complete, and `x₂, f_k` are not.  Once again this contradicts 17.3.  So `f_k` is
> not the unique neighbour of `y` in `A`, and therefore it is the unique neighbour of `x₁`
> in `F`.*
>
> *Suppose that `f_k` is `Y`-complete.  Since `f_k = pₙ`, it follows from (4) that `z` is
> not `Y`-complete; and so `x₂` is `Y₀`-complete by (2), and an antipath between `z, y` with
> interior in `Y₀` can be extended to an antihole via `y-x₂-f_k-z`, which shares the
> vertices `z, x₂, f_k` with the hole `z-x₂-f₁-⋯-f_k-x₁-z` (`= C₁` say), contrary to 15.7.
> So `f_k` is not `Y`-complete and therefore not `Y₀`-complete (and in particular, `Y₀` is
> nonempty).*
>
> *Suppose that `z` is not `Y`-complete; and therefore `Y₀ ∪ {z}` is anticonnected, and
> `x₂` is `Y₀`-complete by (2).  Choose `h` with `1 ≤ h < k` minimum such that `f_h` is
> adjacent to `y` (this exists since `f_k` is not the unique neighbour of `y` in `A`).  The
> path `x₂-f₁-⋯-f_h-y` is even, since it can be completed to a hole via `y-z-x₂`, and
> therefore the path `x₂-f₁-⋯-f_h-y-x₁` is odd (this is a path since `f_k` is the unique
> neighbour of `x₁` in `A`); and the ends of this path are `Y₀ ∪ {z}`-complete, and its
> internal vertices are not.  By 13.6 it has length 3.  So `f₁` is adjacent to `y` and `x₂`.
> If `f₁` is not `Y₀`-complete, then an antipath between `f₁, y` with interior in `Y₀` can
> be completed to an antihole via `y-x₂-x₁-f₁`, which shares the vertices `x₁, x₂, f₁` with
> the hole `C₁`, contrary to 15.7; while if `f₁` is `Y`-complete, then an antipath between
> `z, y` with interior in `Y₀` can be completed to an antihole via `y-x₂-x₁-f₁-z`, again
> contrary to 15.7.  This proves that `z` is `Y`-complete.*
>
> *In the hole `C₁`, `z, x₁` are `Y`-complete and `x₂, f_k` are not; so since `G ∈ F₇`, no
> other vertex of `C₁` is `Y`-complete.  By 2.10, `Y` contains a leap or hat for `C₁`.  From
> a hypothesis of the theorem, every vertex in `Y` has a neighbour in `A ∪ {x₂}`, so there
> is no hat, and hence there exist nonadjacent `y₁, y₂` in `Y` such that
> `y₁-x₂-f₁-⋯-f_k-y₂` is a path.  Since both ends of this path are `{x₀,x₁}`-complete, and
> no internal vertex is `{x₀,x₁}`-complete, this contradicts 13.6.  This proves (8).*

The statement of (8) mentions no path; the path `f₁-⋯-f_k` used in its proof is built
inside the proof out of claim (3).

**`hcex`, the minimum-counterexample hypothesis.**  The third paragraph of the printed proof
of (8) cites claim (4):

> *"Suppose that `f_k` is `Y`-complete.  Since `f_k = pₙ`, it follows from (4) that `z` is
> not `Y`-complete; …"*

This is the contrapositive of claim (4)'s **second** conjunct (*"if `z` is `Y`-complete then
no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete"*): `f_k = pₙ` being `Y`-complete makes `pₙx₁` a
`Y`-complete edge of that path, so `z` cannot be `Y`-complete.  That second conjunct is a
reductio against the choice of `Y` as a *minimum counterexample* (*"The second is immediate,
for otherwise `(C,Y)` satisfies the theorem"*), i.e. against the standing assumption
`¬ Concl192 G z A₀ x Y` set up by the first line of the proof of 19.2 (*"If possible, choose
`Y` not satisfying the theorem, with `|Y|` minimum"*).  Since `Concl192` is 19.2's actual
conclusion it cannot be refuted from (8)'s own hypotheses, so that standing assumption is
carried explicitly as `hcex`, in the same binder slot as in claims (4), (10), (11) and (12).
On the assembly side (`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by
`by_contra` on the goal `Concl192 G z A₀ x Y` at the top of `core`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(8)** of the printed proof: *"If `x₂` is nonadjacent to `y` then it is
nonadjacent to both `x₀, x₁`."* -/
theorem claim8 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (h2y : ¬ G.Adj (x 2) y) :
    ¬ G.Adj (x 2) (x 0) ∧ ¬ G.Adj (x 2) (x 1) := by
  constructor
  · intro hx20
    exact Thm192Claim8Main.half G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      hcex h2y hx20
  · -- *"and adjacent to `x₀` say"*: the `x₀ ↔ x₁` symmetry of 19.2
    intro hx21
    refine Thm192Claim8Main.half G hG z A₀ hframe (Thm192Symmetry.sw x)
      (Thm192Symmetry.sw_ws hws) Y (Thm192Symmetry.sw_hyp hHyp) (Thm192Symmetry.sw_ih ih)
      y hyY hyz hY0 A (Thm192Symmetry.sw_goodA hA) (Thm192Symmetry.sw_goodA_min hAmin)
      (fun hc => hcex ?_) (by rw [Thm192Symmetry.sw_two]; exact h2y)
      (by rw [Thm192Symmetry.sw_two, Thm192Symmetry.sw_zero]; exact hx21)
    have h := Thm192Symmetry.sw_concl hc
    rwa [Thm192Symmetry.sw_sw] at h

end Workspace.ProofLemmas.Thm192Claim8
