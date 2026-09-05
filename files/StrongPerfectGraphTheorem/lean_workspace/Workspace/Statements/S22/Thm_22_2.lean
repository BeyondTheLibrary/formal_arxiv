import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Statements.S19.Thm_19_1
import Workspace.Statements.S22.Thm_22_1
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.WheelSystemBasics

/-!
# 22.2

PAPER (printed p. 138), the whole printed proof:

> *"By 22.1, there is a sequence `x_{s+1}, …, x_{t+1}` with `t ≥ s` such that `x₀, …, x_{t+1}`
> is a wheel system with respect to the frame `(z, A₀)`, with hub `Y`.  By 19.1, there exists
> `r` with `1 ≤ r ≤ t`, and a member `y ∈ Y`, such that `y` has no neighbour in
> `A_r ∪ {x_{t+1}}`, and `x_{t+1}` has a neighbour in `A_r`, and a non-neighbour in `X_r`.
> Since every member of `Y` has a neighbour in `A_s`, it follows that `r < s`, and the result
> holds (taking `v = x_{t+1}`).  This proves 22.2."*

Step for step:

| printed sentence | Lean |
|---|---|
| *"By 22.1, there is a sequence `x_{s+1}, …, x_{t+1}` …"* | `thm_22_1` |
| *"By 19.1, there exists `r` … `y` has no neighbour in `A_r ∪ {x_{t+1}}`"* | `thm_19_1` in contrapositive form: its conclusion is refuted by the hypothesis `hnowheel`, so its `hstep` must fail |
| *"`x_{t+1}` has a neighbour in `A_r`, and a non-neighbour in `X_r`"* | conditions 2 and 3 of the truncated wheel system that 19.1 hands back, at index `r + 1` |
| *"Since every member of `Y` has a neighbour in `A_s`, it follows that `r < s`"* | `hYAs` plus `WheelSystemBasics.wheelSystemA_mono` |
| *"taking `v = x_{t+1}`"* | `v := x' (t + 1)` |

Three things the paper leaves implicit and that the Lean proof has to supply:

* `A_i` of the extension `x'` agrees with `A_i` of the given `x` for `i ≤ s`, since the two
  sequences agree there (`KiteTailBasics.wheelSystemA_congr`).  This is needed to transport
  the hypotheses `hYAs` and `hone`, which are stated for `x`.
* `v = x_{t+1} ∉ Y`: `KiteTailBasics.hub_last_notMem` — if it were in `Y` then each of
  `x₀, …, x_t` would be `Y`-complete hence adjacent to it, making it `X_t`-complete, which
  condition 3 of a wheel system forbids.
* `v ≠ z` and `v ≠ x i` for `i ≤ s`: from the wheel system's own clauses (`x j ≠ z`, and
  pairwise distinctness together with `s ≤ t < t + 1`).
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


/-- **22.2** (printed p. 137).

PAPER: *"Let `G ∈ F₈`, not admitting a balanced skew partition, let `(z, A₀)` be a
frame, and let `x₀,…,x_s` be a wheel system.  Let
`Y ⊆ V(G) \ (A₀ ∪ {z, x₀,…,x_s})` be nonempty and anticonnected, such that
`z, x₀,…,x_s` are `Y`-complete.  Define `Aᵢ, Xᵢ` as usual, and assume that every
member of `Y` has a neighbour in `A_s`, and at most one member of `Y` has no
neighbour in `A₁`.  Suppose there is no wheel with hub `Y`.  Then there exists `r`
with `1 ≤ r < s`, and a member `y ∈ Y`, and a vertex
`v ∉ Y ∪ {z, x₀,…,x_s}` with the following properties:*

*   *`y` has no neighbour in `A_r ∪ {v}`*
*   *`v` is adjacent to `z`, and has a neighbour in `A_r`, and a non-neighbour in
    `X_r`."* -/
theorem thm_22_2 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (s : ℕ) (hws : IsWheelSystem G z A₀ x s)
    (Y : Set V) (hYdisj : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z ∧ ∀ i ≤ s, y ≠ x i)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hzY : VertexComplete G z Y) (hxY : ∀ i ≤ s, VertexComplete G (x i) Y)
    (hYAs : ∀ y ∈ Y, ∃ a ∈ wheelSystemA G z A₀ x s, G.Adj y a)
    (hone : Set.Subsingleton
      {y ∈ Y | VertexAnticomplete G y (wheelSystemA G z A₀ x 1)})
    (hnowheel : ¬ ∃ C : List V, IsWheel G C Y) :
    ∃ (r : ℕ), 1 ≤ r ∧ r < s ∧ ∃ y ∈ Y, ∃ v : V,
      (v ∉ Y ∧ v ≠ z ∧ ∀ i ≤ s, v ≠ x i) ∧
      VertexAnticomplete G y (wheelSystemA G z A₀ x r ∪ {v}) ∧
      (G.Adj v z ∧ (∃ a ∈ wheelSystemA G z A₀ x r, G.Adj v a) ∧
        ∃ b ∈ wheelSystemX x r, ¬ G.Adj v b) := by
  have hs1 : 1 ≤ s := hws.1
  -- "By 22.1, there is a sequence `x_{s+1}, …, x_{t+1}` with `t ≥ s` …"
  obtain ⟨x', n, hsn, hx'eq, hhub⟩ :=
    thm_22_1 G hG hbsp z A₀ hframe x s hws Y hYdisj hYne hYanti hzY hxY
  have hn1 : 1 ≤ n := le_trans hs1 hsn
  -- `Aᵢ` agrees between `x` and its extension `x'` for every `i ≤ s`.
  have hAeq : ∀ i, i ≤ s → wheelSystemA G z A₀ x i = wheelSystemA G z A₀ x' i := by
    intro i hi
    exact KiteTailBasics.wheelSystemA_congr (fun j hj => (hx'eq j (le_trans hj hi)).symm)
  have hA1eq : wheelSystemA G z A₀ x 1 = wheelSystemA G z A₀ x' 1 := hAeq 1 hs1
  have hAseq : wheelSystemA G z A₀ x s = wheelSystemA G z A₀ x' s := hAeq s (le_refl s)
  have hA₁ : {y ∈ Y | VertexAnticomplete G y (wheelSystemA G z A₀ x' 1)}.Subsingleton := by
    rw [← hA1eq]; exact hone
  -- "By 19.1, there exists `r` …" — 19.1's `hstep` must fail.
  have hstepfail : ¬ (∀ r : ℕ, 1 ≤ r → r ≤ n →
      IsWheelSystem G z A₀ (fun j => if j ≤ r then x' j else x' (n + 1)) (r + 1) →
      ∀ y ∈ Y, ∃ a ∈ (wheelSystemA G z A₀ x' r ∪ {x' (n + 1)} : Set V), G.Adj y a) := by
    intro hstep
    exact hnowheel
      (_root_.Workspace.Statements.S19.SPGT.thm_19_1 G hG z A₀ hframe x' n Y hhub hn1 hA₁ hstep)
  push Not at hstepfail
  obtain ⟨r, hr1, hrn, hwsr, y, hyY, hyanti⟩ := hstepfail
  -- "Since every member of `Y` has a neighbour in `A_s`, it follows that `r < s`."
  have hrs : r < s := by
    by_contra hcon
    obtain ⟨a, ha, hadj⟩ := hYAs y hyY
    rw [hAseq] at ha
    exact hyanti a
      (Or.inl (WheelSystemBasics.wheelSystemA_mono (by omega : s ≤ r) ha)) hadj
  -- The truncated sequence `x₀, …, x_r, x_{t+1}` and its `X_r`, `x_{r+1}`.
  have hxeq : wheelSystemX (fun j => if j ≤ r then x' j else x' (n + 1)) (r + 1 - 1)
      = wheelSystemX x' r := by
    simpa using
      (KiteTailBasics.wheelSystemX_congr
        (x := fun j => if j ≤ r then x' j else x' (n + 1)) (x' := x') (i := r)
        (fun j hj => by simp only []; rw [if_pos hj]))
  have hveq : (fun j => if j ≤ r then x' j else x' (n + 1)) (r + 1) = x' (n + 1) := by
    show (if r + 1 ≤ r then x' (r + 1) else x' (n + 1)) = x' (n + 1)
    rw [if_neg (by omega)]
  have hArs : wheelSystemA G z A₀ x r = wheelSystemA G z A₀ x' r := hAeq r (by omega)
  -- "taking `v = x_{t+1}`".
  refine ⟨r, hr1, hrs, y, hyY, x' (n + 1), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- `v ∉ Y`
    exact KiteTailBasics.hub_last_notMem hhub
  · -- `v ≠ z`
    exact (hhub.1.2.2.1 (n + 1) (le_refl _)).2
  · -- `v ≠ x i` for `i ≤ s`
    intro i hi
    rw [← hx'eq i hi]
    exact KiteTailBasics.hub_last_ne hhub (le_trans hi hsn)
  · -- "`y` has no neighbour in `A_r ∪ {v}`"
    intro a ha
    rcases ha with ha | ha
    · rw [hArs] at ha
      exact hyanti a (Or.inl ha)
    · exact hyanti a (Or.inr ha)
  · -- "`v` is adjacent to `z`"
    exact (hhub.1.2.2.2.2.2.2 (n + 1) (le_refl _)).symm
  · -- "`v` has a neighbour in `A_r`" — condition 2 of the truncated system at index `r + 1`
    obtain ⟨B, hA₀B, hBconn, ⟨b, hbB, hadj⟩, hBz, hBX⟩ :=
      hwsr.2.2.2.2.1 (r + 1) (by omega) (le_refl _)
    have hbA : b ∈ wheelSystemA G z A₀ x' r := by
      refine WheelSystemBasics.mem_wheelSystemA_of_witness hA₀B hBconn hBz ?_ hbB
      intro c hc hcc
      exact hBX c hc (by rw [hxeq]; exact hcc)
    have hbA' : b ∈ wheelSystemA G z A₀ x r := by rw [hArs]; exact hbA
    rw [hveq] at hadj
    exact ⟨b, hbA', hadj⟩
  · -- "`v` has a non-neighbour in `X_r`" — condition 3 of the truncated system
    have hnc := hwsr.2.2.2.2.2.1 (r + 1) (by omega) (le_refl _)
    rw [hxeq, hveq] at hnc
    have hXrs : wheelSystemX x r = wheelSystemX x' r :=
      KiteTailBasics.wheelSystemX_congr (fun j hj => (hx'eq j (by omega)).symm)
    rw [hXrs]
    by_contra hcon
    push Not at hcon
    exact hnc hcon


end SPGT

end Workspace.Statements.S22
