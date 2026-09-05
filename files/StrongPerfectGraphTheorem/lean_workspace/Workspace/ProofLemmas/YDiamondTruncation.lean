import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# §20 bookkeeping: truncating a `Y`-diamond to a `Y ∪ {x_t}`-diamond

The printed proofs of 20.3 and 20.4 (Chudnovsky–Robertson–Seymour–Thomas,
printed pp. 125–128) repeat one construction three times:

> *"If `x_{t−1}` is `X_{t−3}`-complete, then `x₀,…,x_{t−1}` is a
> `Y ∪ {x_t}`-diamond of height `t − 1`."*

(20.3, step (1), first case; 20.3, final paragraph, second case; and the same
shape with `Y' = {q}` in 20.4.)  Nothing in that sentence is proved in the
paper; it is a routine verification against the definition of `IsYDiamond`.
This module carries the verification, together with the three small facts it
needs:

* `wheelSystem_truncate` — a wheel system of height `t` truncates to one of any
  height `1 ≤ s ≤ t`;
* `anticonnected_union_singleton` — `Y ∪ {w}` is anticonnected whenever `Y` is,
  `w ∉ Y` and `w` is not `Y`-complete (this is `connectedSet_union_singleton`
  read in `Gᶜ`);
* `ydiamond_top_nonadj` — in a `Y`-diamond, `x_t` is **not** adjacent to
  `x_{t−1}`.  The paper uses this silently: `x_t` is `X_{t−2}`-complete but, by
  clause 3 of the wheel-system definition at `i = t`, not `X_{t−1}`-complete.

`YDiamondTruncation.ydiamond_truncate_union` is the sentence quoted above.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.YDiamondTruncation

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Truncating a wheel system: `x₀,…,x_s` is a wheel system whenever `x₀,…,x_t`
is and `1 ≤ s ≤ t`. -/
theorem wheelSystem_truncate {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t s : ℕ} (hws : IsWheelSystem G z A₀ x t) (hs : 1 ≤ s) (hst : s ≤ t) :
    IsWheelSystem G z A₀ x s := by
  obtain ⟨-, hinj, hout, hfr, h2, h3, h4⟩ := hws
  exact ⟨hs, fun j hj k hk h => hinj j (by omega) k (by omega) h,
    fun j hj => hout j (by omega), hfr,
    fun i hi hit => h2 i hi (by omega),
    fun i hi hit => h3 i hi (by omega),
    fun j hj => h4 j (by omega)⟩

/-- `Y ∪ {w}` is anticonnected whenever `Y` is anticonnected, `w ∉ Y` and `w` is
not `Y`-complete.  (In `Gᶜ` the vertex `w` then has a neighbour in `Y`, so this
is `ConnectedSetUnionAttach.connectedSet_union_singleton` applied to `Gᶜ`.) -/
theorem anticonnected_union_singleton {G : SimpleGraph V} {Y : Set V} {w : V}
    (hY : AnticonnectedSet G Y) (hw : w ∉ Y) (hnc : ¬ VertexComplete G w Y) :
    AnticonnectedSet G (Y ∪ {w}) := by
  obtain ⟨y, hyY, hnadj⟩ : ∃ y ∈ Y, ¬ G.Adj w y := by
    by_contra hcon
    push_neg at hcon
    exact hnc (fun y hy => hcon y hy)
  refine ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hY ?_
  refine ⟨y, hyY, ?_⟩
  rw [SimpleGraph.compl_adj]
  exact ⟨fun h => hw (h ▸ hyY), hnadj⟩

/-- In a `Y`-diamond `x₀,…,x_t`, the vertex `x_t` is not adjacent to `x_{t−1}`.

`x_t` is `X_{t−2}`-complete by definition, and clause 3 of the wheel-system
definition (at `i = t`) says `x_t` is not `X_{t−1}`-complete; since
`X_{t−1} = X_{t−2} ∪ {x_{t−1}}`, the missing neighbour can only be `x_{t−1}`. -/
theorem ydiamond_top_nonadj {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (hd : IsYDiamond G z A₀ x t Y) :
    ¬ G.Adj (x t) (x (t - 1)) := by
  obtain ⟨hws, -, -, -, -, -, ht3, hXc, -⟩ := hd
  obtain ⟨-, -, -, -, -, h3, -⟩ := hws
  intro hadj
  refine h3 t (by omega) le_rfl ?_
  intro v hv
  rw [WheelSystemBasics.mem_wheelSystemX] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  rcases Nat.lt_or_ge j (t - 1) with hlt | hge
  · exact hXc (x j) (WheelSystemBasics.mem_wheelSystemX.2 ⟨j, by omega, rfl⟩)
  · have : j = t - 1 := by omega
    subst this
    exact hadj

/-- **The truncation step of §20** (printed pp. 125, 127).

*"If `x_{t−1}` is `X_{t−3}`-complete [and has a neighbour in `A_{t−3}`], then
`x₀,…,x_{t−1}` is a `Y ∪ {x_t}`-diamond of height `t − 1`."* -/
theorem ydiamond_truncate_union {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hcomp : VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)))
    (hnbr : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a) :
    IsYDiamond G z A₀ x (t - 1) (Y ∪ {x t}) := by
  have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := ydiamond_top_nonadj hd
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hA⟩ := hd
  obtain ⟨-, hinj, hout, -, -, -, -⟩ := id hws
  have hidx : t - 1 - 2 = t - 3 := by omega
  refine ⟨wheelSystem_truncate hws (by omega) (by omega), ?_, ?_, ⟨?_, ?_⟩, ?_, ?_,
    by omega, ?_, ?_⟩
  · exact hYne.mono Set.subset_union_left
  · refine anticonnected_union_singleton hYanti (hxY t le_rfl) hnVC
  · rintro (hz | hz)
    · exact hzY hz
    · rw [Set.mem_singleton_iff] at hz
      exact (hout t le_rfl).2 hz.symm
  · rintro i hi (hy | hy)
    · exact hxY i (by omega) hy
    · rw [Set.mem_singleton_iff] at hy
      have := hinj i (by omega) t le_rfl hy
      omega
  · intro i hi y hy
    rcases hy with hy | hy
    · exact hVC i (by omega) y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hXc (x i) (WheelSystemBasics.mem_wheelSystemX.2 ⟨i, by omega, rfl⟩)).symm
  · intro hcon
    exact hnonadj (hcon (x t) (Or.inr rfl)).symm
  · rw [hidx]; exact hcomp
  · rw [hidx]; exact hnbr

end Workspace.ProofLemmas.YDiamondTruncation
