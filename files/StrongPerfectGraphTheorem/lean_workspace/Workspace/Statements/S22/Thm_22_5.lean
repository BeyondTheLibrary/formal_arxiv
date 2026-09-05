import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Statements.S19.Thm_19_1
import Workspace.Statements.S22.Thm_22_1
import Workspace.Statements.S22.Thm_22_3
import Workspace.Statements.S22.Thm_22_4
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.WheelSystemBasics

/-!
# 22.5 — no vertex of the rim of an optimal wheel has a tail

PAPER (printed p. 139), the whole printed proof:

> *"Suppose `z ∈ V(C)` has a tail `T`; let `y` be the neighbour of `z` in `T`, and let
> `x₀, x₁` be the neighbours of `z` in `C`.  Let `A₀ = V(C) \ {z, x₀, x₁}`, so `x₀, x₁` is a
> wheel system with respect to `(z, A₀)`, and `x₀, x₁` are `Y ∪ {y}`-complete.  By 22.1 there
> exist `x₂, …, x_{t+1}` with `t ≥ 1` such that `x₀, …, x_{t+1}` is a wheel system with respect
> to `(z, A₀)`, with hub `Y ∪ {y}`.  Define `Aᵢ, Xᵢ` as usual.  From the construction, all
> members of `Y` have a neighbour in `A₀`.  By 19.1, there exists `r` with `1 ≤ r ≤ t`, such
> that `x₀, …, x_r, x_{t+1}` is a wheel system and `y` has no neighbour in `A_r ∪ {x_{t+1}}`.
> But `Y ∪ {y}` is a hub for this wheel system, and `T` is a tail for `z`.  By 22.3, there is
> no kite for `(C, Y)`; and so by 22.4 applied to this wheel system, `y` has a neighbour in
> `A_r ∪ {x_{t+1}}`, a contradiction.  This proves 22.5."*

Step for step:

| printed sentence | Lean |
|---|---|
| *"let `y` be the neighbour of `z` in `T`, … `x₀, x₁` … `A₀ = V(C) \ {z,x₀,x₁}` … wheel system … `Y ∪ {y}`-complete"* | `KiteTailBasics.tail_opening_move` |
| *"By 22.1 there exist `x₂,…,x_{t+1}` …"* | `thm_22_1 … (s := 1)` |
| *"all members of `Y` have a neighbour in `A₀`"* | last clause of `tail_opening_move`, pushed into `A₁` by `KiteTailBasics.rim_minus_subset_wheelSystemA` |
| *"By 19.1, there exists `r` …"* | `thm_19_1` in contrapositive form: its conclusion *"there is a wheel with hub `Y ∪ {y}`"* is refuted by `KiteTailBasics.no_wheel_hub_union_singleton`, so its `hstep` hypothesis must fail |
| *"By 22.3, there is no kite for `(C,Y)`"* | `thm_22_3` |
| *"by 22.4 applied to this wheel system"* | `thm_22_4` at the truncated sequence `fun j => if j ≤ r then x' j else x' (t+1)` |

Two things the paper leaves implicit:

* 19.1's hypothesis is *"at most one member of `Y ∪ {y}` has no neighbour in `A₁`"*.  Every
  member of `Y` has one (it is adjacent to an end of a `Y`-complete rim edge outside
  `{z, x₀, x₁}`); `y` itself may not, so the exceptional set is `⊆ {y}` — a subsingleton, and
  this is exactly why 19.1 is stated with *"at most one"* rather than *"none"*.
* `A_r` of the truncated system is `A_r` of the given one, because the two have the same `X_r`
  (`KiteTailBasics.wheelSystemA_congr`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S22

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **22.5** (printed p. 139).

PAPER: *"Let `G ∈ F₈`, not admitting a balanced skew partition, and let `(C, Y)` be
an optimal wheel in `G`.  Then no vertex of `C` has a tail."*

(Introduced by: *"We combine the previous result with 19.1 to prove the
following."*)

Encoding notes.  *"`z` has a tail"* means: there is a path `T` which is a tail for
`z` with respect to the wheel `(C, Y)`, where `x₀, x₁` are the neighbours of `z`
in `C` (those two vertices are determined by `z` and `C`, and the requirement that
they are indeed the neighbours of `z` in `C` is part of `IsTail`).  Since the
published definition of a tail no longer contains the clause "no vertex of `G` is
a kite for `(C, Y)`", this statement is strictly stronger than the corresponding
statement of the arXiv draft. -/
theorem thm_22_5 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y) :
    ∀ z ∈ C, ¬ ∃ (x₀ x₁ : V) (T : List V), IsTail G C Y z x₀ x₁ T := by
  rintro z hzC ⟨x₀, x₁, T, hT⟩
  -- Basic data of the wheel and of the rim neighbours.
  have hwheel : IsWheel G C Y := KiteTailBasics.tail_isWheel hT
  have hC : IsHoleList G C := KiteTailBasics.wheel_isHoleList hwheel
  have hlen5 : 5 ≤ C.length := by
    have := KiteTailBasics.wheel_six_le_length hwheel; omega
  obtain ⟨x, hx0, hx1⟩ : ∃ x : ℕ → V, x 0 = x₀ ∧ x 1 = x₁ :=
    ⟨fun i => if i = 0 then x₀ else x₁, by simp, by simp⟩
  have hnb' : KiteTailBasics.IsRimNeighbours G C z (x 0) (x 1) := by
    rw [hx0, hx1]; exact KiteTailBasics.tail_rimNeighbours hT
  -- "let `y` be the neighbour of `z` in `T` … so `x₀, x₁` is a wheel system w.r.t. `(z, A₀)`"
  obtain ⟨u, ⟨R, hTeq⟩, huC, huY, hunc, hframe0, hws0, hY'ne, hY'anti, hzY', hxY',
      hY'disj, hYnbr⟩ := KiteTailBasics.tail_opening_move hT x hx0 hx1
  obtain ⟨A₀, hA₀⟩ : ∃ A : Set V, A = {v : V | v ∈ C} \ ({z, x 0, x 1} : Set V) := ⟨_, rfl⟩
  have hsub0 : A₀ ⊆ wheelSystemA G z A₀ x 1 := by
    rw [hA₀]
    exact KiteTailBasics.rim_minus_subset_wheelSystemA hC hlen5 hzC x hnb'
  rw [← hA₀] at hframe0 hws0 hY'disj hYnbr
  -- "By 22.1 there exist `x₂, …, x_{t+1}` with `t ≥ 1` …"
  obtain ⟨x', n, h1n, hx'eq, hhub⟩ :=
    thm_22_1 G hG hbsp z A₀ hframe0 x 1 hws0 (Y ∪ ({u} : Set V)) hY'disj hY'ne hY'anti
      hzY' hxY'
  have hn1 : 1 ≤ n := le_trans (by omega) h1n
  -- `A₁` is the same for `x` and for its extension `x'`.
  have hA1eq : wheelSystemA G z A₀ x 1 = wheelSystemA G z A₀ x' 1 :=
    KiteTailBasics.wheelSystemA_congr (fun j hj => (hx'eq j hj).symm)
  have hsub0' : A₀ ⊆ wheelSystemA G z A₀ x' 1 := by rw [← hA1eq]; exact hsub0
  -- "there is no wheel with hub `Y ∪ {y}`" — optimality of `(C, Y)`.
  have hnowheel : ¬ ∃ C' : List V, IsWheel G C' (Y ∪ ({u} : Set V)) :=
    KiteTailBasics.no_wheel_hub_union_singleton hopt huY
  -- Only `u` can fail to have a neighbour in `A₁`.
  have hkey : ∀ c : V, c ∈ Y ∪ ({u} : Set V) →
      VertexAnticomplete G c (wheelSystemA G z A₀ x' 1) → c = u := by
    intro c hc hanti
    rcases hc with hcY | hcu
    · exfalso
      obtain ⟨a, ha, hadj⟩ := hYnbr c hcY
      exact hanti a (hsub0' ha) hadj
    · exact Set.mem_singleton_iff.mp hcu
  have hA₁ : {c ∈ Y ∪ ({u} : Set V) |
      VertexAnticomplete G c (wheelSystemA G z A₀ x' 1)}.Subsingleton := by
    intro a ha b hb
    rw [hkey a ha.1 ha.2, hkey b hb.1 hb.2]
  -- "By 19.1, there exists `r` with `1 ≤ r ≤ t` …" — 19.1's `hstep` must fail.
  have hstepfail : ¬ (∀ r : ℕ, 1 ≤ r → r ≤ n →
      IsWheelSystem G z A₀ (fun j => if j ≤ r then x' j else x' (n + 1)) (r + 1) →
      ∀ c ∈ Y ∪ ({u} : Set V),
        ∃ a ∈ (wheelSystemA G z A₀ x' r ∪ {x' (n + 1)} : Set V), G.Adj c a) := by
    intro hs
    exact hnowheel (_root_.Workspace.Statements.S19.SPGT.thm_19_1 G hG z A₀ hframe0 x' n
      (Y ∪ ({u} : Set V)) hhub hn1 hA₁ hs)
  push Not at hstepfail
  obtain ⟨r, hr1, hrn, hwsr, c, hcmem, hcanti⟩ := hstepfail
  -- The member without a neighbour must be `u`.
  have hcu : c = u := by
    refine hkey c hcmem ?_
    intro a ha
    exact hcanti a (Or.inl (WheelSystemBasics.wheelSystemA_mono hr1 ha))
  -- `subst` would eliminate `u` (the right-hand side); rewrite `hcanti` instead.
  rw [hcu] at hcanti
  -- The truncated wheel system `x₀, …, x_r, x_{t+1}`.
  obtain ⟨w, hw⟩ : ∃ f : ℕ → V, f = (fun j => if j ≤ r then x' j else x' (n + 1)) := ⟨_, rfl⟩
  rw [← hw] at hwsr
  have hwj : ∀ j ≤ r, w j = x' j := by
    intro j hj
    rw [hw]
    show (if j ≤ r then x' j else x' (n + 1)) = x' j
    rw [if_pos hj]
  have hwr1 : w (r + 1) = x' (n + 1) := by
    rw [hw]
    show (if r + 1 ≤ r then x' (r + 1) else x' (n + 1)) = x' (n + 1)
    rw [if_neg (by omega)]
  have hw0 : w 0 = x₀ := by rw [hwj 0 (by omega), hx'eq 0 (by omega), hx0]
  have hw1 : w 1 = x₁ := by rw [hwj 1 hr1, hx'eq 1 (by omega), hx1]
  -- `A_r` agrees between the truncated and the given system.
  have hArEq : wheelSystemA G z A₀ w r = wheelSystemA G z A₀ x' r :=
    KiteTailBasics.wheelSystemA_congr hwj
  -- "But `Y ∪ {y}` is a hub for this wheel system."
  have hhub' : IsHubForWheelSystem G z A₀ w (r + 1) (Y ∪ ({u} : Set V)) := by
    refine ⟨hwsr, hhub.2.1, hhub.2.2.1, hhub.2.2.2.1, hhub.2.2.2.2.1, ?_, ?_⟩
    · intro i hi
      rw [hwj i (by omega)]
      exact hhub.2.2.2.2.2.1 i (by omega)
    · rw [hwr1]
      exact hhub.2.2.2.2.2.2
  -- "By 22.3, there is no kite for `(C, Y)`."
  have hnokite : ¬ ∃ v : V, IsKite G C Y v := thm_22_3 G hG hbsp C Y hopt
  -- "and so by 22.4 applied to this wheel system, `y` has a neighbour in `A_r ∪ {x_{t+1}}`"
  have hT' : IsTail G C Y z (w 0) (w 1) T := by rw [hw0, hw1]; exact hT
  have hA₀' : A₀ = {v : V | v ∈ C} \ ({z, w 0, w 1} : Set V) := by
    rw [hw0, hw1, hA₀, hx0, hx1]
  obtain ⟨a, hamem, hadj⟩ :=
    thm_22_4 G hG C Y hopt hnokite z w T hT' u R hTeq A₀ hA₀' r hhub'
  -- "a contradiction."
  rw [hArEq, hwr1] at hamem
  exact hcanti a hamem hadj


end SPGT

end Workspace.Statements.S22
