import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim9MinimalityWitnessRepaired
import Workspace.ProofLemmas.Thm192Claim9YAdjX2TwoComplete
import Workspace.ProofLemmas.Thm192Claim9YAdjX2Rerun
import Workspace.ProofLemmas.NonCutVertices

/-!
# Claim (9) of 19.2 in the case that `x₂` is adjacent to `y`

## Why this file exists

The printed proof of claim (9) begins

> *"For suppose that such a set `F` exists with `F ≠ A`, and choose `f ∈ A \ {F}` such that
> `A \ {f}` is connected.  From the minimality of `A`, there exists `y₀ ∈ Y` nonadjacent to
> `x₂` with no neighbour in `A \ {f}`, and therefore `f` is the unique neighbour of `y₀` in
> `A`.  If `y₀ ∈ Y₀`, then `x₂` is not `Y₀`-complete, and therefore by (2) there are two
> `Y₀`-complete vertices in `A`, a contradiction.  So `y₀ = y`, and therefore `y` is not
> adjacent to `x₂`."*

so the printed argument *derives* `¬ G.Adj (x 2) y` from the minimality of the printed
choice of `A`.  The project minimises over `Thm192Setup.GoodA` instead, which carries the
extra clause *"`y` has a neighbour in `A`"* (added in `Thm192Setup` to repair the order of
the two extremal choices).  With that extra clause `A \ {f}` may fail to be `GoodA` at the
new clause rather than at the `Y`-clause, and then the printed `y₀` need not exist; see
`lean_workspace/REPORT.md` for an explicit eight-vertex counterexample, in which `y` *is*
adjacent to `x₂`.

`Thm192Claim9MinimalityWitnessRepaired.minimalityWitness` records what the minimality of a
`GoodA` set really gives: `A \ {f}` fails one of the two "has a neighbour" clauses.  When
`y` is nonadjacent to `x₂` the second failure is a special case of the first, so the printed
sentence is recovered verbatim (`Thm192Claim9MinimalityWitness.minimalityWitness`).  The
present file covers the one remaining case, `G.Adj (x 2) y`, which the printed proof excludes
by an argument the project's weaker minimality does not supply.

## What is proved here

`claim9_of_x2_adj_y` reduces that case, with no gap, to the single statement
`uniqueNeighbourContradiction` below: the printed configuration in which `f` is the unique
neighbour of `y` in `A`.  That statement is now proved, so this file has no gap.

`uniqueNeighbourContradiction` splits on whether the hub `Y` can be shrunk.  If some proper
anticonnected `Y₀ ⊆ Y` still contains `y` and still has a vertex nonadjacent to `x₂`, the
localized smaller-hub induction gives two distinct `Y₀`-complete vertices of `A`
(`Thm192Claim9YAdjX2TwoComplete.two_complete_in_A`), both of them neighbours of `y`, which
contradicts the uniqueness of `f`.  Otherwise `minimalHubContradiction` applies.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim9YAdjX2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The configuration of claim (9) in which `f` is the unique neighbour of `y` in `A`,
`x₂` is adjacent to `y`, and the hub cannot be shrunk.

PAPER (19.2, claim (9), printed p. 121): *"… and therefore `f` is the unique neighbour of
`y₀` in `A`.  If `y₀ ∈ Y₀`, then … a contradiction.  So `y₀ = y`, and therefore `y` is not
adjacent to `x₂`."*

`hminhub` says that no proper subset of `Y` still contains `y`, is still anticonnected and
still has a vertex nonadjacent to `x₂`.  Two consequences pin the configuration down:

* `x₂` has exactly one nonneighbour `w` in `Y`, and `Y \ {w}` is anticonnected.  Indeed,
  `Y` is anticonnected with at least two elements (it contains `y`, adjacent to `x₂`, and a
  nonneighbour of `x₂`), so two of its vertices `u` have `Y \ {u}` anticonnected
  (`NonCutVertices.exists_two_nonanticut`); for such a `u` other than `y`, `hminhub`
  applied to `Y \ {u}` says that `u` is the *only* nonneighbour of `x₂` in `Y`.  At most
  one of the two can be `y`, so at least one of them is that unique nonneighbour `w`.
* So `w` is a vertex of the hub which the printed claim (1) could have chosen instead of
  `y`: it lies in `Y`, is adjacent to `z`, has `Y \ {w}` anticonnected, and is nonadjacent
  to `x₂`.

Running the printed proof of 19.2 for `w` and a cardinality-minimal `GoodA` set for it —
which is legitimate because every claim of the printed proof is available for `w`, claim
(9) included (`Thm192Claim9NotAdjX2`, the branch `¬ G.Adj (x 2) w`) — reaches claim (11)
and its first sentence *"`z` is not `Y₀`-complete"*, here *"`z` is not
`Y \ {w}`-complete"* (`Thm192Claim9YAdjX2Rerun.z_not_Y0_complete`).  But `x₂` is adjacent
to `y`, so claim (2) gives its second alternative, and in particular `z` **is**
`Y`-complete, hence `Y \ {w}`-complete.  That is the contradiction. -/
theorem minimalHubContradiction (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (h2y : G.Adj (x 2) y)
    (F : Set V) (hFA : F ⊆ A) (hFconn : ConnectedSet G F) (hFne : F ≠ A)
    (hF0 : ∃ a ∈ F, G.Adj (x 0) a) (hF1 : ∃ a ∈ F, G.Adj (x 1) a)
    (hF2 : ∃ a ∈ F, G.Adj (x 2) a)
    (f : V) (hfA : f ∈ A) (hfF : f ∉ F) (hfconn : ConnectedSet G (A \ {f}))
    (hyf : G.Adj y f) (hyuniq : ∀ a ∈ A, G.Adj y a → a = f)
    (hminhub : ∀ Y₀ : Set V, Y₀ ⊆ Y → y ∈ Y₀ → AnticonnectedSet G Y₀ →
      (∃ v ∈ Y₀, ¬ G.Adj v (x 2)) → Y₀ = Y) : False := by
  classical
  -- *"`x₂` is not `Y`-complete"*: some `v ∈ Y` is nonadjacent to `x₂`, and `v ≠ y`.
  obtain ⟨v, hvY, hv2⟩ : ∃ v ∈ Y, ¬ G.Adj v (x 2) := by
    by_contra hcon
    refine hHyp.2.2.2.2.1 (fun q hq => ?_)
    by_contra hnadj
    exact hcon ⟨q, hq, fun hc => hnadj hc.symm⟩
  have hvy : v ≠ y := fun he => hv2 (he ▸ h2y.symm)
  -- so `Y` has at least two elements, and two of its vertices can be deleted from it
  -- without destroying anticonnectedness
  have hns : ¬ Y.Subsingleton := fun hsub => hvy (hsub hvY hyY)
  obtain ⟨a, haY, b, hbY, hab, hAa, hAb⟩ :=
    Workspace.ProofLemmas.NonCutVertices.exists_two_nonanticut hHyp.2.1 hns
  -- for such a vertex other than `y`, `hminhub` forces it to be `v`
  have hforced : ∀ u ∈ Y, u ≠ y → AnticonnectedSet G (Y \ {u}) → u = v := by
    intro u huY huy hanti
    by_contra hne
    have hvu : v ∈ Y \ {u} := ⟨hvY, by simpa using fun hc => hne hc.symm⟩
    have heq : Y \ {u} = Y :=
      hminhub (Y \ {u}) (fun q hq => hq.1) ⟨hyY, by simpa using huy.symm⟩ hanti ⟨v, hvu, hv2⟩
    have : u ∈ Y \ {u} := by rw [heq]; exact huY
    exact this.2 rfl
  -- at most one of the two is `y`, so `Y \ {v}` is anticonnected
  have hvanti : AnticonnectedSet G (Y \ {v}) := by
    by_cases hay : a = y
    · have hby : b ≠ y := fun h => hab (hay.trans h.symm)
      rw [← hforced b hbY hby hAb]
      exact hAb
    · rw [← hforced a haY hay hAa]
      exact hAa
  -- `v` is a vertex the printed claim (1) could have chosen: it is adjacent to `z` and has
  -- a neighbour in `A₁`
  obtain ⟨hvA1, hvz⟩ := hHyp.2.2.2.2.2 v hvY hv2
  obtain ⟨A', hA', hA'min⟩ := Thm192Setup.exists_minimal_goodA hframe hws hHyp hvA1
  -- claim (11) for `v`: *"`z` is not `Y₀`-complete"*
  have hznot : ¬ VertexComplete G z (Y \ {v}) :=
    Thm192Claim9YAdjX2Rerun.z_not_Y0_complete hG hframe hws hHyp ih hvY hvz
      (Or.inr hvanti) hA' hA'min hcex (fun hc => hv2 hc.symm)
  -- but `z` is `Y`-complete, by claim (2): its first alternative needs `x₂` nonadjacent
  -- to `y`, and here `x₂` is adjacent to `y`
  rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
    hleft | ⟨hzY, -⟩
  · exact hleft.2 h2y
  · exact hznot (fun q hq => hzY q hq.1)

/-- The configuration in which `f` is the unique neighbour of `y` in `A` and `x₂` is
adjacent to `y`.

PAPER (19.2, claim (9), printed p. 121): *"… and therefore `f` is the unique neighbour of
`y₀` in `A`. … So `y₀ = y`, and therefore `y` is not adjacent to `x₂`."*

The proof shrinks the hub instead.  Let `Y₀ ⊆ Y` be anticonnected, contain `y`, contain a
vertex nonadjacent to `x₂`, and be smaller than `Y`.  The hypotheses of 19.2 hold for `Y₀`,
so the induction on `|Y|` applies to it, and localized to `A` it returns a wheel with rim
in `{x₀,x₁,z} ∪ A` whose two disjoint `Y₀`-complete edges put two distinct `Y₀`-complete
vertices inside `A` (`Thm192Claim9YAdjX2TwoComplete.two_complete_in_A`).  This is the
printed sentence of claim (1), *"by the minimality of `|Y|` … there is a `Y \ {y₂}`-complete
vertex in `A`"*, read for the hub `Y₀`.  Both vertices are adjacent to `y`, because
`y ∈ Y₀`, so both equal `f`, a contradiction.  So no such `Y₀` is smaller than `Y`, which
is the hypothesis of `minimalHubContradiction`. -/
theorem uniqueNeighbourContradiction (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (h2y : G.Adj (x 2) y)
    (F : Set V) (hFA : F ⊆ A) (hFconn : ConnectedSet G F) (hFne : F ≠ A)
    (hF0 : ∃ a ∈ F, G.Adj (x 0) a) (hF1 : ∃ a ∈ F, G.Adj (x 1) a)
    (hF2 : ∃ a ∈ F, G.Adj (x 2) a)
    (f : V) (hfA : f ∈ A) (hfF : f ∉ F) (hfconn : ConnectedSet G (A \ {f}))
    (hyf : G.Adj y f) (hyuniq : ∀ a ∈ A, G.Adj y a → a = f) : False := by
  classical
  refine minimalHubContradiction G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
    hcex h2y F hFA hFconn hFne hF0 hF1 hF2 f hfA hfF hfconn hyf hyuniq ?_
  rintro Y₀ hsub hyY₀ hanti ⟨v, hvY₀, hv2⟩
  by_contra hneq
  have hcard0 : Y₀.ncard < Y.ncard :=
    Set.ncard_lt_ncard (HasSubset.Subset.ssubset_of_ne hsub hneq) (Set.toFinite Y)
  have hx2c : ¬ VertexComplete G (x 2) Y₀ := fun hc => hv2 (hc v hvY₀).symm
  obtain ⟨c, hcA, d, hdA, hcd, hcY, hdY⟩ :=
    Thm192Claim9YAdjX2TwoComplete.two_complete_in_A G hG z A₀ hframe x hws Y hHyp ih y A hA
      Y₀ hsub hanti hx2c hcard0
  exact hcd ((hyuniq c hcA (hcY y hyY₀).symm).trans (hyuniq d hdA (hdY y hyY₀).symm).symm)

/-- Claim **(9)** of the printed proof of 19.2, in the case `G.Adj (x 2) y`.

Everything here is the printed text: the minimality of `A` produces `f`, the printed
argument *"If `y₀ ∈ Y₀`, then `x₂` is not `Y₀`-complete, and therefore by (2) there are two
`Y₀`-complete vertices in `A`, a contradiction"* rules out `y₀ ∈ Y \ {y}`, and `y₀ = y` is
impossible here because `y` is adjacent to `x₂`.  So the only surviving alternative of
`Thm192Claim9MinimalityWitnessRepaired.minimalityWitness` is that `f` is the unique
neighbour of `y` in `A`, which is `uniqueNeighbourContradiction`. -/
theorem claim9_of_x2_adj_y (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (h2y : G.Adj (x 2) y) :
    ∀ F : Set V, F ⊆ A → ConnectedSet G F →
      (∃ a ∈ F, G.Adj (x 0) a) → (∃ a ∈ F, G.Adj (x 1) a) → (∃ a ∈ F, G.Adj (x 2) a) →
      F = A := by
  classical
  intro F hFA hFconn hF0 hF1 hF2
  by_contra hFne
  -- *"choose `f ∈ A \ F` such that `A \ {f}` is connected"*, and read off which of the two
  -- "has a neighbour" clauses of `GoodA` the set `A \ {f}` loses.
  obtain ⟨f, ⟨hfA, hfF⟩, hfconn, hdisj⟩ :=
    Thm192Claim9MinimalityWitnessRepaired.minimalityWitness G z A₀ x Y y A hA hAmin
      F hFA hFconn hFne hF0 hF1 hF2
  -- The printed alternative — a vertex `y₀ ∈ Y` nonadjacent to `x₂` with no neighbour in
  -- `A \ {f}` — cannot occur here.
  have hy0 : ¬ (∃ y₀ ∈ Y, ¬ G.Adj y₀ (x 2) ∧ VertexAnticomplete G y₀ (A \ {f})) := by
    rintro ⟨y₀, hy₀Y, hy₀2, hy₀anti⟩
    -- *"and therefore `f` is the unique neighbour of `y₀` in `A`"*
    have hy₀uniq : ∀ a ∈ A, G.Adj y₀ a → a = f := by
      intro a haA hadj
      by_contra hne
      exact hy₀anti a ⟨haA, by simpa using hne⟩ hadj
    -- `y₀ ≠ y`, because `y` is adjacent to `x₂` and `y₀` is not.
    have hne : y₀ ≠ y := by
      rintro rfl
      exact hy₀2 h2y.symm
    have hy₀Y0 : y₀ ∈ Y \ {y} := ⟨hy₀Y, by simpa using hne⟩
    -- *"If `y₀ ∈ Y₀`, then `x₂` is not `Y₀`-complete, and therefore by (2) there are two
    -- `Y₀`-complete vertices in `A`, a contradiction."*
    rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
      hleft | ⟨-, P, hP, hPint, hcard⟩
    · exact hy₀2 (hleft.1 y₀ hy₀Y0).symm
    · obtain ⟨c, hcI, d, hdI, hcd, hcY, hdY⟩ :=
        Thm192Infra.two_complete_in_interior hws hA.1 hP hPint hcard
      have hcf : c = f := hy₀uniq c (hPint c hcI) (hcY y₀ hy₀Y0).symm
      have hdf : d = f := hy₀uniq d (hPint d hdI) (hdY y₀ hy₀Y0).symm
      exact hcd (hcf.trans hdf.symm)
  -- So `A \ {f}` loses the clause *"`y` has a neighbour in `A`"*: `f` is the unique
  -- neighbour of `y` in `A`.
  have hanti : VertexAnticomplete G y (A \ {f}) := by
    rcases hdisj with h | h
    · exact absurd h hy0
    · exact h
  obtain ⟨a, haA, hya⟩ := hA.2.2.2.2.2.2
  have haf : a = f := by
    by_contra hne
    exact hanti a ⟨haA, by simpa using hne⟩ hya
  refine uniqueNeighbourContradiction G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
    hAmin hcex h2y F hFA hFconn hFne hF0 hF1 hF2 f hfA hfF hfconn (haf ▸ hya) ?_
  intro b hbA hadj
  by_contra hne
  exact hanti b ⟨hbA, by simpa using hne⟩ hadj

end Workspace.ProofLemmas.Thm192Claim9YAdjX2
