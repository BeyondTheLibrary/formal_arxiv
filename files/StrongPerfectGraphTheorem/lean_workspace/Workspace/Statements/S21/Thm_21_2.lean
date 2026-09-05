import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Pseudowheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm212

/-!
# Section 21 — From wheel systems to wheels

The three numbered statements 21.1, 21.2, 21.3 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/*Annals* version, printed pages
130–135).  Source of the verbatim quotations:
`paper/pdf/S21_From_wheel_systems_to_wheels.md`, `## Numbered statements`.

Section 21 introduces no defined term of its own; every notion used below already
lives in an imported module and nothing is restated here:

* `Workspace.Types.Core` — `IsPathList`, `pathLength`, `VertexComplete`,
  `VertexAnticomplete`, `Complete`, `AnticonnectedSet`;
* `Workspace.Types.Wheels` — `IsWheel` (§16's *wheel*, with rim `C` and hub `Y`);
* `Workspace.Types.Pseudowheels` — `IsPseudowheel` (§18's *pseudowheel*);
* `Workspace.Types.WheelSystems` — `IsFrame`, `IsWheelSystem`,
  `IsHubForWheelSystem`, `wheelSystemX` (`Xᵢ`), `wheelSystemA` (`Aᵢ`);
* `Workspace.Types.Classes` — `InF7`, `InF8` (the classes `F₇`, `F₈` of §1).

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* a *path* of the paper is the list `p : List V` of its vertices in order together
  with `IsPathList G p`; its length is `pathLength p = p.length - 1`, so the
  paper's `p₁,…,pₙ` are the entries of `p` and `n` is `p.length`;
* "`P` is a path in `G \ (X ∪ Y)`" is `IsPathList G p` together with
  `∀ v ∈ p, v ∉ X ∧ v ∉ Y`;
* the ends `p₁, pₙ` are pinned down by `p.head? = some p₁`,
  `p.getLast? = some pₙ`;
* the paper's 1-based `p_i` is the 0-based `p[i - 1]`; index bounds are stated as
  bounds on `p.length` so that the `getElem` side conditions are discharged
  automatically;
* "`v` has a neighbour in `S`" is `∃ a ∈ S, G.Adj v a`, and "`v` has no neighbour
  in `S`" is `VertexAnticomplete G v S`;
* "at most one member of `Y` has property `Q`" is `Set.Subsingleton {y ∈ Y | Q y}`;
* "there is a wheel in `G` with hub `Y`" is `∃ C : List V, IsWheel G C Y` — the
  hub is the *given* set `Y`, only the rim is existentially quantified;
* a wheel system is carried by a function `x : ℕ → V` together with its height
  (see the module docstring of `Workspace.Types.WheelSystems`), so the paper's
  "`x₀,…,x_{t+1}` is a wheel system with hub `Y`" is
  `IsHubForWheelSystem G z A₀ x (t + 1) Y`, which unfolds to: `x₀,…,x_{t+1}` is a
  wheel system, `Y` is a nonempty anticonnected subset of `V(G) \ (A₀ ∪ {z})`, and
  `z, x₀,…,x_t` are all `Y`-complete while `x_{t+1}` is not.

**Provenance note.**  21.2 is transcribed in its *published* form, whose ambient
hypothesis is `G ∈ F₇` together with the per-`Y` condition "there do not exist
`X, P` so that `(X, Y, P)` is a pseudowheel", and whose conclusion is the bare
"there is a wheel in `G` with hub `Y`".  (The arXiv draft instead assumes
`G ∈ F₈` and concludes a four-way disjunction; nothing from the draft is used
here.)  Likewise 21.3 is the published restatement of 19.1: it carries the guard
"if `x₀,x₁,…,x_r,x_{t+1}` is a wheel system" on the quantification over `r`, which
the draft lacks, and it does *not* conclude anything about `x_{t+1}` having a
neighbour in `A_r` and a non-neighbour in `X_r` (that clause survives only in
22.2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S21

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **21.2** (printed p. 131).

PAPER: *"Let `G ∈ F₇`, and let `Y ⊆ V(G)`, such that there do not exist `X, P` so
that `(X, Y, P)` is a pseudowheel.  Let `(z, A₀)` be a frame, and let `x₀,…,x_{t+1}`
be a wheel system with hub `Y`, and with `t ≥ 2`.  Define `Xᵢ, Aᵢ` as usual.
Suppose that `x_{t+1}` has no neighbour in `A_{t-1}`; and moreover that at most one
member of `Y` has no neighbour in `A_{t-1} ∪ {x_{t+1}}`, and any such vertex has a
neighbour in `A_t`.  Then there is a wheel in `G` with hub `Y`."*

(Introduced by: *"The final step of the proof of 19.1 is given by the following.
(In this paper we only apply it to graphs in containing no pseudowheels, that is,
graphs in `F₈`, so the first hypothesis could be simplified; but it is convenient
to present it this way for a future application.)"*  This is the **published**
form: the ambient hypothesis is `G ∈ F₇` plus the per-`Y` condition, not
`G ∈ F₈`.)

Encoding notes.

* *"`Y ⊆ V(G)`"* is vacuous for a `Set V`; the substantive hypothesis on `Y` is
  the absence of a pseudowheel `(X, Y, P)` **with this very `Y`** — both the
  anticonnected set `X` and the path `P` are quantified away.  The remaining
  standing hypotheses on `Y` (nonempty, anticonnected, disjoint from `A₀ ∪ {z}`)
  are part of `IsHubForWheelSystem`.
* *"`x₀,…,x_{t+1}` is a wheel system with hub `Y`"* is
  `IsHubForWheelSystem G z A₀ x (t + 1) Y`; with `t ≥ 2` the natural subtraction
  in `A_{t-1}` is the intended one.
* *"at most one member of `Y` has no neighbour in `A_{t-1} ∪ {x_{t+1}}`"* is the
  `Set.Subsingleton` of the set of such members, and *"any such vertex has a
  neighbour in `A_t`"* quantifies over exactly the same members.

**Proof (printed pp. 131–135).**  The printed argument is reproduced step for step by
`Workspace.ProofLemmas.Thm212`, whose six declarations are exactly the pieces the paper
marks out:

* `Thm212.claim1` — the opening claim *"(1) There do not exist `xᵢ, x_j ∈ X_t` joined by an
  odd path `xᵢ-x_{t+1}-P-x_j` of length ≥ 5 …"*;
* `Thm212.exists_goodPath` — *"Hence there is a path `x_{t+1}-p₁-⋯-p_m` … Choose such a path
  such that if possible, every member of `Y` has a neighbour in
  `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`"*;
* `Thm212.claim2` — *"(2) We may assume that one of `x₀,…,x_t` is nonadjacent to both
  `x_{t+1}, p₁`"* (the other alternative being the `Y`-square, where the theorem already
  holds by 20.1);
* `Thm212.claim3` — *"(3) Every vertex in `Y` has a neighbour in
  `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`"*;
* `Thm212.exists_extended` — *"we can extend the path `x_{t+1}-p₁-⋯-p_m` to a path
  `x_{t+1}-p₁-⋯-p_n` containing neighbours of all members of `X_t`.  By (2), we can choose
  `i` … and choose `s` …"*;
* `Thm212.endgame` — claims (4)–(9) and the concluding paragraph.

The theorem below is the paper's own chaining of those steps. -/
theorem thm_21_2 (G : SimpleGraph V) (hG : InF7 G) (Y : Set V)
    (hYpw : ¬ ∃ (X : Set V) (P : List V), IsPseudowheel G X Y P)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (t : ℕ) (ht : 2 ≤ t)
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) Y)
    (hxt1 : VertexAnticomplete G (x (t + 1)) (wheelSystemA G z A₀ x (t - 1)))
    (hone : Set.Subsingleton
      {y ∈ Y | VertexAnticomplete G y
        (wheelSystemA G z A₀ x (t - 1) ∪ {x (t + 1)})})
    (hsuch : ∀ y ∈ Y,
      VertexAnticomplete G y (wheelSystemA G z A₀ x (t - 1) ∪ {x (t + 1)}) →
        ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj y a) :
    ∃ C : List V, IsWheel G C Y := by
  -- The standing hypothesis package of the printed proof.
  have hsetup : Workspace.ProofLemmas.Thm212.Setup G Y z A₀ x t :=
    ⟨hG, hYpw, hframe, ht, hhub, hxt1, hone, hsuch⟩
  -- *"(1) There do not exist `xᵢ, x_j ∈ X_t` joined by an odd path …"*
  have hc1 := Workspace.ProofLemmas.Thm212.claim1 hsetup
  -- *"Hence there is a path `x_{t+1}-p₁-⋯-p_m` … Choose such a path such that if possible,
  -- every member of `Y` has a neighbour in `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`."*
  obtain ⟨p, hp, hopt⟩ := Workspace.ProofLemmas.Thm212.exists_goodPath hsetup
  -- *"(2) We may assume that one of `x₀,…,x_t` is nonadjacent to both `x_{t+1}, p₁`."*
  -- The discarded alternative is the `Y`-square, for which 20.1 already gives the wheel.
  rcases Workspace.ProofLemmas.Thm212.claim2 hsetup hp with hwheel | hc2
  · exact hwheel
  -- *"(3) Every vertex in `Y` has a neighbour in `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`."*
  have hc3 := Workspace.ProofLemmas.Thm212.claim3 hsetup hp hopt hc1 hc2
  -- *"… we can extend the path `x_{t+1}-p₁-⋯-p_m` to a path `x_{t+1}-p₁-⋯-p_n` containing
  -- neighbours of all members of `X_t`.  By (2), we can choose `i` … and choose `s` …"*
  obtain ⟨q, i, s, hext⟩ := Workspace.ProofLemmas.Thm212.exists_extended hsetup hp hc2 hc3
  -- Claims (4)–(9) and the concluding paragraph.
  exact Workspace.ProofLemmas.Thm212.endgame hsetup hp hopt hc1 hc3 hext


end SPGT

end Workspace.Statements.S21
