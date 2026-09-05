/-  Proof attempt 1 for statement 19.1 (`Workspace.Statements.S19.SPGT.thm_19_1`).

    THE PAPER'S PROOF.  19.1 is *stated* at the start of section 19 with only a sketch
    ("The proof of this is lengthy, but here is the idea. ... We handle these three cases
    separately; they are the results 19.2, 20.1, and 21.2 respectively. ... The proof of
    19.1 is completed in section 21."), and it is *restated and proved* at the end of
    section 21 as 21.3 ("Now we can deduce our main theorem about wheel systems, 19.1,
    which we restate"), whose printed proof ends with the sentence

        "Thus there is a wheel with hub Y . This proves 19.1."

    (perfect.pdf printed p. 137; paper/perfect_pdf.txt line 6463).  So the paper's own
    proof of 19.1 is: 21.3 is 19.1, and 21.3's proof (the r-minimality argument combining
    19.2, 21.2, 20.1) discharges it.  The printed statements of 19.1 and 21.3 are
    word-for-word identical, and so are their Lean renderings up to the order of the two
    hypotheses `t ≥ 1` and "x₀,…,x_{t+1} is a wheel system with hub Y".

    Hence the Lean proof is a single citation of `thm_21_3` with the hypotheses supplied
    in 21.3's order.  Nothing is reproved here; 21.3 carries the argument.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S21.Thm_21_3

set_option autoImplicit false

namespace Workspace.Statements.S19

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **19.1** (printed p. 117).

PAPER: *"Let `G ∈ F₈`, let `(z,A₀)` be a frame, and let `x₀,…,x_{t+1}` be a wheel
system with hub `Y`, and with `t ≥ 1`.  Define `Aᵢ, Xᵢ` as usual, and assume that
at most one member of `Y` has no neighbour in `A₁`.  Suppose that for all `r` with
`1 ≤ r ≤ t`, if `x₀,x₁,…,x_r,x_{t+1}` is a wheel system, then every member of `Y`
has a neighbour in `A_r ∪ {x_{t+1}}`.  Then there is a wheel with hub `Y`."*

19.1 is the only statement of Sections 19–20 about `F₈`; everything else is about
`F₇`.  It is stated here but proved only at the end of Section 21 (*"The proof of
19.1 is completed in section 21."*); its three cases are 19.2, 20.1 and 21.2.

Encoding notes.

* *"`x₀,…,x_{t+1}` is a wheel system with hub `Y`"* is
  `IsHubForWheelSystem G z A₀ x (t + 1) Y`, i.e. the wheel system has **height
  `t + 1`**; `t ≥ 1` is stated separately, exactly as printed.  The hub condition
  already carries `Y` nonempty and anticonnected, `Y ⊆ V(G) \ (A₀ ∪ {z})`, and
  `z, x₀,…,x_t` all `Y`-complete with `x_{t+1}` not.
* *"at most one member of `Y` has no neighbour in `A₁`"* is
  `{y ∈ Y | VertexAnticomplete G y A₁}.Subsingleton`.
* *"`x₀,x₁,…,x_r,x_{t+1}` is a wheel system"*: this is the sequence of height
  `r + 1` whose `j`-th term is `x j` for `j ≤ r` and whose last term is
  `x (t+1)`, i.e. `fun j => if j ≤ r then x j else x (t + 1)`.  (At `r = t` this
  is the given system again, so the hypothesis is not vacuous.)
* `A_r` in the conclusion of that implication is the `A_r` of the **given** wheel
  system, `wheelSystemA G z A₀ x r` — as the paper's *"Define `Aᵢ, Xᵢ` as usual"*
  prescribes.  (It agrees with the `A_r` of the truncated system, since the two
  systems have the same `X_r`.) -/
theorem thm_19_1 (G : SimpleGraph V) (hG : InF8 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (t : ℕ) (Y : Set V)
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) Y)
    (ht : 1 ≤ t)
    (hA₁ : {y ∈ Y | VertexAnticomplete G y (wheelSystemA G z A₀ x 1)}.Subsingleton)
    (hstep : ∀ r : ℕ, 1 ≤ r → r ≤ t →
      IsWheelSystem G z A₀ (fun j => if j ≤ r then x j else x (t + 1)) (r + 1) →
      ∀ y ∈ Y, ∃ a ∈ (wheelSystemA G z A₀ x r ∪ {x (t + 1)} : Set V), G.Adj y a) :
    ∃ C : List V, IsWheel G C Y := by
  -- "This proves 19.1."  (End of the proof of 21.3, printed p. 137.)
  exact _root_.Workspace.Statements.S21.SPGT.thm_21_3 G hG z A₀ hframe x t Y ht hhub hA₁ hstep


end SPGT

end Workspace.Statements.S19
