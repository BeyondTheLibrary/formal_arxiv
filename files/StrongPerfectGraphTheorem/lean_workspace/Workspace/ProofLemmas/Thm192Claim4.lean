import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim4Rim
import Workspace.ProofLemmas.Thm192Claim4Antihole

/-!
# Claim (4) of the printed proof of 19.2

PAPER (printed pp. 118–119):

> *Let `x₀-p₁-⋯-pₙ-x₁` be a path from `x₀` to `x₁` with interior in `A`, and let `C` be the
> hole `z-x₀-p₁-⋯-pₙ-x₁-z`.*
>
> **(4)** *If any vertex of `p₁,…,pₙ` is `Y ∪ {x₂}`-complete then `z` is `Y`-complete; and
> if `z` is `Y`-complete then no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete.  In particular,
> neither of `p₁, pₙ` is `Y ∪ {x₂}`-complete.*
>
> *For let `pᵢ` be `Y ∪ {x₂}`-complete, say, and suppose `z` is not `Y`-complete.  By (2),
> `x₂` is `Y₀`-complete and nonadjacent to `y`.  Let `Q` be an antipath between `z, y` with
> interior in `Y₀`, and let `R` be an antipath between `x₂, pᵢ` with interior in `{x₀,x₁}`.
> Then `z-Q-y-x₂-R-pᵢ-z` is an antihole, meeting the hole `C` in at least three vertices,
> contrary to 15.7.  This proves the first assertion.  The second is immediate, for
> otherwise `(C,Y)` satisfies the theorem.  For the third, note that if say `pₙ` is
> `Y ∪ {x₂}`-complete, then `pₙx₁` is a `Y`-complete edge, a contradiction.  This proves (4).*

Encoding notes.

* The path `x₀-p₁-⋯-pₙ-x₁` is the list `P` with `IsPathFrom G P (x 0) (x 1)`; its interior
  `p₁,…,pₙ` is `SPGT.interior P`, and `pᵢ = P[i]` for `1 ≤ i ≤ n`.  The hole `C` is the
  list `z :: P`; it does not occur in the *statement* of (4), only in its proof.
* `3 ≤ P.length` is carried as a hypothesis so that `p₁ = P[1]` and `pₙ = P[P.length - 2]`
  can be named.  It is not an extra assumption in substance: `x₀` and `x₁` are nonadjacent
  (`Thm192Setup.x0_not_adj_x1`), so any path between them has at least three vertices.
* *"no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete"* quantifies over the consecutive pairs
  `P[i], P[i+1]` of the list, which for an induced path are exactly its edges.
* **`hcex`, the minimum-counterexample hypothesis.**  The printed justification of the
  *second* assertion is one sentence: *"The second is immediate, for otherwise `(C,Y)`
  satisfies the theorem."*  That is a reductio against the very first line of the proof of
  19.2, *"If possible, choose `Y` not satisfying the theorem, with `|Y|` minimum"* — i.e.
  against the standing assumption that the present `Y` is a counterexample.  Spelled out:
  if `z` were `Y`-complete and some `P[i]P[i+1]` were a `Y`-complete edge, then `C = z :: P`
  is a hole, `zx₀` and `zx₁` are `Y`-complete edges, and one of them is vertex-disjoint from
  `P[i]P[i+1]`, so `IsWheel G (z :: P) Y` holds; together with `x 0, x 1, z ∈ C` and
  `{v | v ∈ C} ⊆ {x 0, x 1, z} ∪ A₁` that is *exactly* `Thm192Setup.Concl192 G z A₀ x Y`.
  It is a contradiction only against `¬ Concl192 G z A₀ x Y`, so that hypothesis is carried
  explicitly as `hcex`.  The *third* assertion is derived from the second (*"if say `pₙ` is
  `Y ∪ {x₂}`-complete, then `pₙx₁` is a `Y`-complete edge, a contradiction"*) and therefore
  needs `hcex` too.  Only the FIRST assertion is independent of it.
  On the assembly side (`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by
  `by_contra` on the goal `Concl192 G z A₀ x Y` at the top of `core`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(4)** of the printed proof: *"If any vertex of `p₁,…,pₙ` is `Y ∪ {x₂}`-complete
then `z` is `Y`-complete; and if `z` is `Y`-complete then no edge of `x₀-p₁-⋯-pₙ-x₁` is
`Y`-complete.  In particular, neither of `p₁, pₙ` is `Y ∪ {x₂}`-complete."* -/
theorem claim4 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
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
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length) :
    ((∃ w ∈ SPGT.interior P, VertexComplete G w (Y ∪ {x 2})) → VertexComplete G z Y) ∧
    (VertexComplete G z Y →
      ∀ (i : ℕ) (hi : i + 1 < P.length),
        ¬ EdgeComplete G Y (P[i]'(by omega)) (P[i + 1]'hi)) ∧
    ¬ VertexComplete G (P[1]'(by omega)) (Y ∪ {x 2}) ∧
    ¬ VertexComplete G (P[P.length - 2]'(by omega)) (Y ∪ {x 2}) := by
  have hPA : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1 :=
    fun w hw => hA.1 (hPint w hw)
  have hfirst : (∃ w ∈ SPGT.interior P, VertexComplete G w (Y ∪ {x 2})) →
      VertexComplete G z Y := by
    rintro ⟨w, hw, hwc⟩
    exact Thm192Claim4Antihole.complete_of_interior_complete hG hws hHyp ih hyY hyz hY0
      hP hPA hPlen hw hwc
  have hsecond : VertexComplete G z Y →
      ∀ (i : ℕ) (hi : i + 1 < P.length),
        ¬ EdgeComplete G Y (P[i]'(by omega)) (P[i + 1]'hi) := by
    intro hz i hi he
    exact hcex (Thm192Claim4Rim.wheel_of_complete_edge hG.1.1.1.1 hws hHyp hz hP hPA hPlen
      (List.getElem_mem (by omega)) (List.getElem_mem hi) he)
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · intro hc
    have hi := PathBasics.getElem_mem_interior hP.1 (k := 1) (by omega) (by omega) (by omega)
    have hz := hfirst ⟨_, hi, hc⟩
    apply hsecond hz 0 (by omega)
    refine ⟨PathBasics.path_adj_succ hP.1 (by omega), ?_, fun w hw => hc w (Or.inl hw)⟩
    rw [PathBasics.getElem_zero_of_head? hP.2.1 (by omega)]
    exact hHyp.2.2.1
  · intro hc
    have hi := PathBasics.getElem_mem_interior hP.1 (k := P.length - 2)
      (by omega) (by omega) (by omega)
    have hz := hfirst ⟨_, hi, hc⟩
    apply hsecond hz (P.length - 2) (by omega)
    refine ⟨PathBasics.path_adj_succ hP.1 (by omega), fun w hw => hc w (Or.inl hw), ?_⟩
    have he : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'(by omega) :=
      hP.1.2.1.getElem_inj_iff.mpr (by omega)
    rw [he, PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
    exact hHyp.2.2.2.1

end Workspace.ProofLemmas.Thm192Claim4
