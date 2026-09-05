import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim5Last
import Workspace.ProofLemmas.Thm192Claim5Cut

/-!
# Claim (5) of the printed proof of 19.2

PAPER (printed p. 119):

> **(5)** *With `p₁,…,pₙ` and `C` as in (4), if `x₀` is adjacent to `x₂`, then `x₂` is
> nonadjacent to all of `p₂,…,pₙ`.*
>
> *For suppose `x₂` is adjacent to one of `p₂,…,pₙ`, and choose `i` with `2 ≤ i ≤ n`
> maximum such that `x₂` is adjacent to `pᵢ`.  Suppose first that `i = n`.  Since
> `x₀, x₁, pₙ` belong to `C`, there is no antihole of length `≥ 5` containing them by 15.7.
> By (4), `pₙ` is not `Y`-complete, and hence there is an antipath between `pₙ, x₂` with
> interior in this set, and it can be completed via `x₂-x₁-x₀-pₙ` to an antihole of length
> `≥ 5` containing `x₀, x₁, pₙ`, a contradiction.  So `i < n`.*
>
> *Since the hole `C` is even, it follows that `n` is odd.  From the hole
> `z-x₂-pᵢ-⋯-pₙ-x₁-z` it follows that `i` is odd.  Since `i > 1`, `x₀-x₂-pᵢ-⋯-pₙ-x₁` is an
> odd path of length `≥ 5`.  Its ends are `Y ∪ {z}`-complete, and its internal vertices are
> not, so by 13.6, `Y ∪ {z}` is not anticonnected.  Hence `z` is `Y`-complete.  The ends of
> the same path are both `Y`-complete, so by 13.6, some edge of the path is `Y`-complete.
> Since `x₂` is not `Y`-complete, this edge belongs to `C`, contrary to (4).  This proves (5).*

Encoding: `pᵢ = P[i]`, and `2 ≤ i ≤ n` is `2 ≤ i` together with `i + 1 < P.length`
(recall `P.length = n + 2`).

**`hcex`, the minimum-counterexample hypothesis.**  The printed proof of (5) cites claim (4)
twice, and both citations are of `hcex`-dependent conjuncts of (4):

* *"By (4), `pₙ` is not `Y`-complete"* — this is claim (4)'s **fourth** conjunct
  (`¬ VertexComplete G pₙ (Y ∪ {x₂})`, specialised), whose own printed justification
  (*"if say `pₙ` is `Y ∪ {x₂}`-complete, then `pₙx₁` is a `Y`-complete edge, a
  contradiction"*) runs through (4)'s **second** conjunct;
* *"Since `x₂` is not `Y`-complete, this edge belongs to `C`, contrary to (4)"* — this is
  claim (4)'s **second** conjunct (*"if `z` is `Y`-complete then no edge of
  `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete"*) directly.

Only claim (4)'s **first** conjunct is free of `hcex`, and (5) does not use it.  Claim (4)'s
second and third/fourth conjuncts are reductios against the choice of `Y` as a *minimum
counterexample* (*"The second is immediate, for otherwise `(C,Y)` satisfies the theorem"*),
i.e. against the standing assumption `¬ Concl192 G z A₀ x Y` set up by the first line of the
proof of 19.2 (*"If possible, choose `Y` not satisfying the theorem, with `|Y|` minimum"*).
Since `Concl192` is 19.2's actual conclusion it cannot be refuted from (5)'s own hypotheses,
so that standing assumption is carried explicitly as `hcex`, in the same binder slot as in
claims (4), (10), (11) and (12).  On the assembly side
(`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by `by_contra` on the goal
`Concl192 G z A₀ x Y` at the top of `core`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim5

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(5)** of the printed proof: *"With `p₁,…,pₙ` and `C` as in (4), if `x₀` is
adjacent to `x₂`, then `x₂` is nonadjacent to all of `p₂,…,pₙ`."* -/
theorem claim5 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
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
    (h02 : G.Adj (x 0) (x 2)) :
    ∀ (i : ℕ), 2 ≤ i → ∀ (hi : i + 1 < P.length), ¬ G.Adj (x 2) (P[i]'(by omega)) := by
  classical
  have hPA : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1 :=
    fun w hw => hA.1 (hPint w hw)
  have hc4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
    A hA hAmin hcex P hP hPint hPlen
  have hlast := Thm192Claim5Last.last_not_adj hG hws hHyp hP hPA hPlen h02 hc4.2.2.2
  have h21 : ¬ G.Adj (x 2) (x 1) := by
    intro he
    apply hws.2.2.2.2.2.1 2 (by omega) (by omega)
    rw [show (2 : ℕ) - 1 = 1 from rfl, wheelSystemX_one]
    rintro a (rfl | rfl)
    · exact h02.symm
    · exact he
  intro i hi hiP hadj
  let k := Nat.findGreatest (fun j => ∃ hj : j < P.length, G.Adj (x 2) (P[j]'hj))
    (P.length - 1)
  have hspec : ∃ hk : k < P.length, G.Adj (x 2) (P[k]'hk) :=
    Nat.findGreatest_spec
      (P := fun j => ∃ hj : j < P.length, G.Adj (x 2) (P[j]'hj))
      (m := i) (n := P.length - 1) (by omega) ⟨by omega, hadj⟩
  obtain ⟨hkP, hkadj⟩ := hspec
  have hik : i ≤ k := Nat.le_findGreatest (by omega) ⟨by omega, hadj⟩
  have hk1 : k ≠ P.length - 1 := by
    intro he
    have helem : P[k]'hkP = P[P.length - 1]'(by omega) :=
      hP.1.2.1.getElem_inj_iff.mpr he
    rw [helem, PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)] at hkadj
    exact h21 hkadj
  have hk2 : k ≠ P.length - 2 := by
    intro he
    have helem : P[k]'hkP = P[P.length - 2]'(by omega) :=
      hP.1.2.1.getElem_inj_iff.mpr he
    exact hlast (helem ▸ hkadj)
  have hmax : ∀ (j : ℕ) (hj : j < P.length), k ≤ j →
      (G.Adj (x 2) (P[j]'hj) ↔ j = k) := by
    intro j hj hkj
    constructor
    · intro hjadj
      by_contra hne
      exact Nat.findGreatest_is_greatest
        (P := fun j => ∃ hj : j < P.length, G.Adj (x 2) (P[j]'hj))
        (n := P.length - 1) (k := j) (by omega)
        (by omega) ⟨hj, hjadj⟩
    · intro he
      subst j
      exact hkadj
  exact Thm192Claim5Cut.cut_contradiction hG hws hHyp hcex hP hPA hPlen h02
    (by omega) (by omega) hmax

end Workspace.ProofLemmas.Thm192Claim5
