import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim2Gap
import Workspace.ProofLemmas.Thm192Claim2Localization

/-!
# Claim (2) of the printed proof of 19.2

PAPER (printed p. 118):

> **(2)** *Either `x₂` is `Y₀`-complete and nonadjacent to `y`, or `z` is `Y`-complete and
> there is a path `x₀-p₁-⋯-pₙ-x₁` from `x₀` to `x₁` with interior in `A`, containing at
> least two `Y₀`-complete edges.*
>
> *For if `x₂` is `Y₀`-complete the first assertion holds, so we assume not; and in
> particular `Y₀` is nonempty.  From the minimality of `|Y|`, `z` is `Y₀`-complete and
> therefore `Y`-complete, and there is a path as in the claim.  This proves (2).*

(Here `y` is the vertex produced by claim (1) and `Y₀ = Y \ {y}`.)

The printed step applies the induction inside the graph induced on
`A ∪ {x₀,x₁,x₂,z} ∪ Y₀`, with the frame `(z,A)`: there the set called `A₁` is `A`
itself, so the wheel it returns has its rim inside `{x₀,x₁,z} ∪ A`.  That is
`Thm192Claim2Localization.inductive_wheel_with_rim_in_A`, and it is why the
induction hypothesis `ih` carries `Thm192Setup.IHInduced` alongside the usual
clause for smaller hubs in the same graph (see `REPORT.md`).

The wheel-to-path step and its edge count are proved separately. In particular, they
use the Berge hypothesis and completeness of both ends, which the original bridge
omitted. The statement of `claim2` is unchanged.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(2)** of the printed proof: *"Either `x₂` is `Y₀`-complete and nonadjacent
to `y`, or `z` is `Y`-complete and there is a path `x₀-p₁-⋯-p_n-x₁` from `x₀` to `x₁`
with interior in `A`, containing at least two `Y₀`-complete edges."*

The remaining obligation is the localized use of induction described in the module header. -/
theorem claim2 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard) :
    (VertexComplete G (x 2) (Y \ {y}) ∧ ¬ G.Adj (x 2) y) ∨
    (VertexComplete G z Y ∧
      ∃ P : List V, IsPathFrom G P (x 0) (x 1) ∧
        (∀ w ∈ SPGT.interior P, w ∈ A) ∧
        2 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧
              EdgeComplete G (Y \ {y}) u v}.ncard) := by
  classical
  by_cases hx2c : VertexComplete G (x 2) (Y \ {y})
  · left
    refine ⟨hx2c, ?_⟩
    intro hx2y
    apply hHyp.2.2.2.2.1
    intro w hwY
    by_cases hwy : w = y
    · simpa [hwy] using hx2y
    · exact hx2c w ⟨hwY, by simpa using hwy⟩
  · right
    have hY0ne : (Y \ {y}).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      apply hx2c
      rw [hne]
      intro w hw
      exact absurd hw (Set.notMem_empty w)
    have hY0anti : AnticonnectedSet G (Y \ {y}) := by
      rcases hY0 with he | ha
      · exact (Set.nonempty_iff_ne_empty.mp hY0ne he).elim
      · exact ha
    have hcard : (Y \ {y}).ncard < Y.ncard := by
      rw [Set.ncard_diff_singleton_of_mem hyY]
      have hpos : 0 < Y.ncard := (Set.ncard_pos (Set.toFinite Y)).mpr ⟨y, hyY⟩
      omega
    have hHyp0 : Hyp192 G z A₀ x (Y \ {y}) := by
      refine ⟨?_, hY0anti, ?_, ?_, hx2c, ?_⟩
      · intro w hw
        exact hHyp.1 w hw.1
      · intro w hw
        exact hHyp.2.2.1 w hw.1
      · intro w hw
        exact hHyp.2.2.2.1 w hw.1
      · intro w hw hn2
        exact hHyp.2.2.2.2.2 w hw.1 hn2
    have hcon0 : Concl192 G z A₀ x (Y \ {y}) := ih.1 _ hcard hHyp0
    have hzY : VertexComplete G z Y := by
      intro w hwY
      by_cases hwy : w = y
      · simpa [hwy] using hyz.symm
      · exact hcon0.1 w ⟨hwY, by simpa using hwy⟩
    refine ⟨hzY, ?_⟩
    have hlocal := Thm192Claim2Localization.inductive_wheel_with_rim_in_A
      G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0anti A hA hAmin hx2c hcon0
    exact Thm192Claim2Gap.path_in_minimal_A_of_inductive_wheel
      G hG.1.1.1.1 z A₀ x hws Y y A hA hAmin
      (fun w hw => hHyp.2.2.1 w hw.1)
      (fun w hw => hHyp.2.2.2.1 w hw.1) ⟨hcon0.1, hlocal⟩

end Workspace.ProofLemmas.Thm192Claim2
