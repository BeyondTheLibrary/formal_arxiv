import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Symmetry
import Workspace.ProofLemmas.Thm192Claim8
import Workspace.ProofLemmas.Thm192Claim10Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics

/-!
# Claim (10) of the printed proof of 19.2

PAPER (printed p. 122).  The claim is preceded by the interlude that names `f`:

> *From (7) and (9), it follows that there exists `f ∈ A` such that `A \ {f}` is connected,
> `f` does not belong to `C`, and `f` is the unique neighbour of `x₂` in `A`.*
>
> **(10)** *`x₂` is nonadjacent to both of `x₀, x₁`.*
>
> *For suppose that `x₂` is adjacent to `x₀` say.  Suppose first that `x₀` is not adjacent
> to `f`.  Then `A ∪ {x₁}` catches the triangle `{z,x₂,x₀}`; the only neighbour of `z` in
> `A ∪ {x₁}` is `x₁`; the only neighbour of `x₂` in `A ∪ {x₁}` is `f`; `x₁, f` are both
> nonadjacent to `x₀`; and `A ∪ {x₁}` contains no reflection of the triangle since that
> would give a 6-antihole with 3 vertices in common with `C`, contradicting 17.1.  So `x₀`
> is adjacent to `f`, and therefore `x₁` is nonadjacent to both `x₂, f`.  By (8) `x₂` is
> adjacent to `y`, and therefore not `Y₀`-complete.  By (2) `z` is `Y₀`-complete and
> `(C, Y₀)` is a wheel.  Let `x₂-q₁-⋯-q_k-x₁` be a path between `x₁, x₂` with interior in
> `A` (so `f = q₁`) and let `C₁` be the hole `z-x₂-q₁-⋯-q_k-x₁-z`.  From (9),
> `A = {q₁,…,q_k}`.  Since `q_k = pₙ` and `z` is `Y`-complete, it follows from (4) that
> `q_k` is not `Y`-complete.  Since `(C₁, Y)` is not an odd wheel, it follows that `(C₁, Y)`
> is not a wheel, and so `z, x₁` are the only `Y`-complete vertices in `C₁`, by 2.3.  By
> 2.10, `Y` contains a leap or hat for `C₁`.  But `y` is adjacent to `x₂`, and all other
> vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`, which is a subset of
> `{q₁,…,q_k}`, a contradiction.  This proves (10).*

Encoding notes.

* The vertex `f` of the interlude is carried as an explicit hypothesis block:
  `f ∈ A`, `A \ {f}` connected, `f ∉ C` (rendered as `f ∉ P`, since `f ∈ A` already gives
  `f ≠ z`), and `f` is the unique neighbour of `x₂` in `A`.
* The path `P` and the choice `hchoice` are those fixed just before claim (6).
* **Where *"all other vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`"* comes
  from.**  That sentence — the one that kills 2.10's *leap* alternative, since a leap needs
  a hub vertex with a *unique* neighbour in the rim interior — is the **second conjunct of
  `hchoice`'s right disjunct**: two distinct `Y₀`-complete vertices `c ≠ d` in
  `SPGT.interior P`, each adjacent to every vertex of `Y₀`.  It is **not** obtainable from
  the word *"wheel"*: `IsWheel` has no clause giving a hub vertex a rim neighbour, and its
  two-disjoint-edges clause yields at most **one** `Y₀`-complete interior vertex, because
  `z` absorbs one of the two edges.  The real source is the *other* conjunct of claim (2),
  the count `2 ≤ #{Y₀-complete edges of P}`, which the paper cites in precisely this form at
  claim (3) and at claim (9) and shorthands as *"is a wheel"* only here and at (6).
  `interludeChoice` supplies it via `Thm192Infra.two_complete_in_interior`; `y` itself is
  excluded because it is adjacent to `x₂`, which is what *"all **other** vertices"* means.
* **`hcex`, the minimum-counterexample hypothesis.**  The printed argument of (10) uses
  claim (4) in one sentence (p. 122): *"Since `q_k = pₙ` and `z` is `Y`-complete, it
  follows from **(4)** that `q_k` is not `Y`-complete."*  That is claim (4)'s **second**
  conjunct — *"if `z` is `Y`-complete then no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete"* —
  applied to the edge `pₙx₁`.  Claim (4)'s second conjunct is exactly the one whose
  printed justification is *"for otherwise `(C,Y)` satisfies 19.2"*, i.e. a reductio
  against the standing assumption *"choose `Y` not satisfying 19.2, with `|Y|` minimum"*.
  `Thm192Claim4.claim4` therefore carries `¬ Thm192Setup.Concl192 G z A₀ x Y` as an
  explicit hypothesis, and (10) must carry it too in order to invoke (4).
  On the assembly side (`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by
  `by_contra` on the goal `Concl192 G z A₀ x Y` at the top of `core`.

  **Not** the counterexample move: the later sentence *"Since `(C₁,Y)` is not an odd
  wheel, …"* is an appeal to `hG : InF7 G` (no odd wheel at all in `G`), **not** to `hcex`.
  It could not be the latter: `C₁ = z-x₂-q₁-⋯-q_k-x₁-z` contains `x₂`, and `x₂ ∉ A₁`,
  `x₂ ∉ {x₀,x₁,z}`, while `x₀ ∉ C₁`; so a wheel `(C₁,Y)` would fail both requirements
  `x₀ ∈ V(C)` and `V(C) ⊆ {x₀,x₁,z} ∪ A₁` of `Concl192`, and therefore could never
  witness it.  Do not re-derive the dependence from that sentence.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim10

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The one-sided form of claim (10).  The second side is obtained below by reversing
the fixed path and swapping `x₀,x₁`. -/
private theorem no_adj_zero (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (f : V) (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f) :
    ¬ G.Adj (x 2) (x 0) := by
  intro hx20
  have h0f : G.Adj (x 0) f :=
    Thm192Claim10Core.firstReflectionForcesAdjacencyWithPath G hG z A₀ x hws Y y A hA
      P hP hPint hPlen f hfA hfadj hfuniq hx20
  have hx21 : ¬ G.Adj (x 2) (x 1) := by
    intro hx21
    have hnot := hws.2.2.2.2.2.1 2 (by omega) (by omega)
    apply hnot
    rw [show 2 - 1 = 1 by omega, Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx20
    · exact hx21
  have h1f : ¬ G.Adj (x 1) f := by
    intro h1f
    refine Thm192Setup.wheelSystemA_no_complete f (hA.1 hfA) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact h0f.symm
    · exact h1f.symm
  have h2y : G.Adj (x 2) y := by
    by_contra h2y
    have h8 := Thm192Claim8.claim8 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
      A hA hAmin hcex h2y
    exact h8.1 hx20
  have h2Y0 : ¬ VertexComplete G (x 2) (Y \ {y}) := by
    intro h2Y0
    refine hHyp.2.2.2.2.1 ?_
    intro w hwY
    by_cases hwy : w = y
    · subst w
      exact h2y
    · exact h2Y0 w ⟨hwY, by simpa using hwy⟩
  exact Thm192Claim10Core.wheelLeapEndgame G hG z A₀ hframe x hws Y hHyp ih y hyY hyz
    hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
    hx20 hx21 h0f h1f h2y h2Y0

/-- Claim **(10)** of the printed proof: *"`x₂` is nonadjacent to both of `x₀, x₁`."* -/
theorem claim10 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
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
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (f : V) (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f) :
    ¬ G.Adj (x 2) (x 0) ∧ ¬ G.Adj (x 2) (x 1) := by
  classical
  have hzero := no_adj_zero G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
    hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
  refine ⟨hzero, ?_⟩
  let xs := Thm192Symmetry.sw x
  have hws' : IsWheelSystem G z A₀ xs 2 := Thm192Symmetry.sw_ws hws
  have hHyp' : Hyp192 G z A₀ xs Y := Thm192Symmetry.sw_hyp hHyp
  have ih' : (∀ Y' : Set V, Y'.ncard < Y.ncard →
      Hyp192 G z A₀ xs Y' → Concl192 G z A₀ xs Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard := Thm192Symmetry.sw_ih ih
  have hA' : GoodA G z A₀ xs Y y A := Thm192Symmetry.sw_goodA hA
  have hAmin' : ∀ B : Set V, GoodA G z A₀ xs Y y B → A.ncard ≤ B.ncard :=
    Thm192Symmetry.sw_goodA_min hAmin
  have hcex' : ¬ Concl192 G z A₀ xs Y := by
    intro hc
    have hh := Thm192Symmetry.sw_concl hc
    rw [Thm192Symmetry.sw_sw] at hh
    exact hcex hh
  have hP' : IsPathFrom G P.reverse (xs 0) (xs 1) := by
    simpa [xs, Thm192Symmetry.sw_zero, Thm192Symmetry.sw_one] using
      PathBasics.isPathFrom_reverse hP
  have hPint' : ∀ w ∈ SPGT.interior P.reverse, w ∈ A := by
    intro w hw
    exact hPint w (PathBasics.mem_interior_reverse.mp hw)
  have hznotA : z ∉ A := by
    intro hzA
    refine Thm192Setup.wheelSystemA_no_complete z (hA.1 hzA) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hws.2.2.2.2.2.2 0 (by omega)
    · exact hws.2.2.2.2.2.2 1 (by omega)
  have hznotP : z ∉ P := by
    intro hzP
    by_cases hz0 : z = x 0
    · exact (hws.2.2.1 0 (by omega)).2 hz0.symm
    by_cases hz1 : z = x 1
    · exact (hws.2.2.1 1 (by omega)).2 hz1.symm
    have hzI : z ∈ SPGT.interior P :=
      (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hzP, hz0, hz1⟩
    exact hznotA (hPint z hzI)
  have hzanti : ∀ w ∈ SPGT.interior P.reverse, ¬ G.Adj z w := by
    intro w hw
    exact Thm192Setup.wheelSystemA_no_z w (hA.1 (hPint' w hw))
  have hchoice' : VertexComplete G (xs 2) (Y \ {y}) ∨
      (IsWheel G (z :: P.reverse) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P.reverse, ∃ d ∈ SPGT.interior P.reverse, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})) := by
    rcases hchoice with hleft | ⟨hwheel, c, hc, d, hd, hcd, hcY, hdY⟩
    · left
      simpa [xs, Thm192Symmetry.sw_two] using hleft
    · right
      have hrev := PathBasics.isPathFrom_reverse hP
      have hhole : IsHoleList G (z :: P.reverse) :=
        PrismBasics.isHoleList_of_path_add_vertex hrev
          (by rw [pathLength, List.length_reverse]; omega)
          (hws.2.2.2.2.2.2 1 (by omega)) (hws.2.2.2.2.2.2 0 (by omega))
          (by simpa using hznotP) hzanti
      refine ⟨Thm192Symmetry.isWheel_congr hhole (by simp) (fun v => by simp) hwheel,
        c, ?_, d, ?_, hcd, hcY, hdY⟩
      · exact PathBasics.mem_interior_reverse.mpr hc
      · exact PathBasics.mem_interior_reverse.mpr hd
  have hfC' : f ∉ P.reverse := by simpa using hfC
  have hfadj' : G.Adj (xs 2) f := by simpa [xs, Thm192Symmetry.sw_two] using hfadj
  have hfuniq' : ∀ a ∈ A, G.Adj (xs 2) a → a = f := by
    intro a ha hadj
    apply hfuniq a ha
    simpa [xs, Thm192Symmetry.sw_two] using hadj
  have hone := no_adj_zero G hG z A₀ hframe xs hws' Y hHyp' ih' y hyY hyz hY0 A hA'
    hAmin' hcex' P.reverse hP' hPint' (by simpa using hPlen) hchoice' f hfA hfconn
    hfC' hfadj' hfuniq'
  simpa [xs, Thm192Symmetry.sw_zero, Thm192Symmetry.sw_two] using hone

end Workspace.ProofLemmas.Thm192Claim10
