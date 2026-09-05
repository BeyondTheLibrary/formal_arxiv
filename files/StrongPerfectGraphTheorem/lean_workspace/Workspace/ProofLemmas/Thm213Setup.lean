import Mathlib
import Workspace.Types.Core
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.WheelSystemBasics

/-!
# Structural lemmas for the proof of 21.3

The printed proof of 21.3 (perfect.pdf, printed page 133) runs:

> *Suppose there is no such wheel.  Choose `r` with `1 ≤ r ≤ t`, minimum such that `x_{t+1}` has
> a neighbour in `A_r` and a nonneighbour in `X_r`.  By hypothesis, every member of `Y` has a
> neighbour in `A_r ∪ {x_{t+1}}`.  By 19.2, `r > 1`.  ...*

Two things are left implicit there and are supplied here.

* **Such an `r` exists**: `r = t` works, because condition 2 of the wheel-system definition
  applied at `i = t+1` says exactly that `x_{t+1}` has a neighbour in `A_t`, and condition 3
  applied at `i = t+1` says exactly that `x_{t+1}` is not `X_t`-complete
  (`top_property` below).
* **The truncated-and-extended sequence `x₀,…,x_r,x_{t+1}` is again a wheel system**, of height
  `r+1`, precisely when `x_{t+1}` has a neighbour in `A_r` and is not `X_r`-complete
  (`isWheelSystem_of_agrees`).  This is what makes the guard in the hypothesis of 21.3 fire at
  the chosen `r`.

Everything is stated for an arbitrary sequence `x'` that *agrees* with `x` below `r` and takes
the value `x_{t+1}` at `r+1`, so that the caller may instantiate it with the concrete
`fun j => if j ≤ r then x j else x (t+1)` of the frozen statement of 21.3.

Also proved here: the members of the hub `Y` are distinct from `z` and from every `xⱼ`
(`hub_ne`), which the applications of 19.2 and 20.1 in the proof need.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm213Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.ProofLemmas.WheelSystemBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Truncation does not change `Xᵢ` or `Aᵢ` below the truncation point -/

theorem wheelSystemX_agrees {x x' : ℕ → V} {r i : ℕ} (hagree : ∀ j ≤ r, x' j = x j)
    (hi : i ≤ r) : wheelSystemX x' i = wheelSystemX x i := by
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, hagree j (hj.trans hi)⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (hagree j (hj.trans hi)).symm⟩

theorem wheelSystemA_agrees (G : SimpleGraph V) (z : V) (A₀ : Set V) {x x' : ℕ → V} {r i : ℕ}
    (hagree : ∀ j ≤ r, x' j = x j) (hi : i ≤ r) :
    wheelSystemA G z A₀ x' i = wheelSystemA G z A₀ x i := by
  unfold wheelSystemA
  rw [wheelSystemX_agrees hagree hi]

/-! ## `r = t` always satisfies the condition the minimal `r` is chosen for -/

/-- Conditions 2 and 3 of the wheel-system definition, applied at `i = t+1`, say exactly that
`x_{t+1}` has a neighbour in `A_t` and is not `X_t`-complete. -/
theorem top_property {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x (t + 1)) (ht : 1 ≤ t) :
    (∃ a ∈ wheelSystemA G z A₀ x t, G.Adj (x (t + 1)) a) ∧
      ¬ VertexComplete G (x (t + 1)) (wheelSystemX x t) := by
  obtain ⟨-, -, -, -, hcond2, hcond3, -⟩ := hws
  constructor
  · obtain ⟨B, hB0, hBc, ⟨b, hb, hab⟩, hBz, hBX⟩ := hcond2 (t + 1) (by omega) le_rfl
    refine ⟨b, ⟨B, ⟨hB0, hBc, hBz, ?_⟩, hb⟩, hab⟩
    simpa using hBX
  · simpa using hcond3 (t + 1) (by omega) le_rfl

/-! ## The truncated-and-extended sequence is a wheel system -/

/-- `x₀,…,x_r,x_{t+1}` is a wheel system of height `r+1` exactly when `x_{t+1}` has a neighbour
in `A_r` and is not `X_r`-complete. -/
theorem isWheelSystem_of_agrees {G : SimpleGraph V} {z : V} {A₀ : Set V} {x x' : ℕ → V}
    {t r : ℕ} (hws : IsWheelSystem G z A₀ x (t + 1)) (hr1 : 1 ≤ r) (hrt : r ≤ t)
    (hagree : ∀ j ≤ r, x' j = x j) (htop : x' (r + 1) = x (t + 1))
    (hnb : ∃ a ∈ wheelSystemA G z A₀ x r, G.Adj (x (t + 1)) a)
    (hnc : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x r)) :
    IsWheelSystem G z A₀ x' (r + 1) := by
  obtain ⟨-, hdist, hnot, hcond1, hcond2, hcond3, hadjz⟩ := hws
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinctness
    intro j hj k hk hjk
    by_cases hjr : j ≤ r <;> by_cases hkr : k ≤ r
    · rw [hagree j hjr, hagree k hkr] at hjk
      exact hdist j (by omega) k (by omega) hjk
    · have hk' : k = r + 1 := by omega
      subst hk'
      rw [hagree j hjr, htop] at hjk
      have := hdist j (by omega) (t + 1) le_rfl hjk
      omega
    · have hj' : j = r + 1 := by omega
      subst hj'
      rw [hagree k hkr, htop] at hjk
      have := hdist (t + 1) le_rfl k (by omega) hjk
      omega
    · omega
  · -- outside `A₀ ∪ {z}`
    intro j hj
    by_cases hjr : j ≤ r
    · rw [hagree j hjr]; exact hnot j (by omega)
    · have hj' : j = r + 1 := by omega
      subst hj'
      rw [htop]; exact hnot (t + 1) le_rfl
  · -- condition 1 involves only `x₀, x₁`
    rw [hagree 0 (by omega), hagree 1 hr1]
    exact hcond1
  · -- condition 2
    intro i h2 hi
    by_cases hir : i ≤ r
    · obtain ⟨B, hB0, hBc, ⟨b, hb, hab⟩, hBz, hBX⟩ := hcond2 i h2 (by omega)
      refine ⟨B, hB0, hBc, ⟨b, hb, ?_⟩, hBz, ?_⟩
      · rw [hagree i hir]; exact hab
      · intro v hv
        rw [wheelSystemX_agrees hagree (show i - 1 ≤ r by omega)]
        exact hBX v hv
    · have hi' : i = r + 1 := by omega
      subst hi'
      obtain ⟨a, ⟨B, hB, haB⟩, hadj⟩ := hnb
      refine ⟨B, hB.1, hB.2.1, ⟨a, haB, ?_⟩, hB.2.2.1, ?_⟩
      · rw [htop]; exact hadj
      · intro v hv
        rw [show r + 1 - 1 = r from rfl, wheelSystemX_agrees hagree (le_refl r)]
        exact hB.2.2.2 v hv
  · -- condition 3
    intro i h1 hi
    by_cases hir : i ≤ r
    · rw [hagree i hir, wheelSystemX_agrees hagree (show i - 1 ≤ r by omega)]
      exact hcond3 i h1 (by omega)
    · have hi' : i = r + 1 := by omega
      subst hi'
      rw [htop, show r + 1 - 1 = r from rfl, wheelSystemX_agrees hagree (le_refl r)]
      exact hnc
  · -- `z` is adjacent to every term
    intro j hj
    by_cases hjr : j ≤ r
    · rw [hagree j hjr]; exact hadjz j (by omega)
    · have hj' : j = r + 1 := by omega
      subst hj'
      rw [htop]; exact hadjz (t + 1) le_rfl

/-- … and `Y` is a hub for it. -/
theorem isHub_of_agrees {G : SimpleGraph V} {z : V} {A₀ : Set V} {x x' : ℕ → V}
    {t r : ℕ} {Y : Set V} (hhub : IsHubForWheelSystem G z A₀ x (t + 1) Y)
    (hr1 : 1 ≤ r) (hrt : r ≤ t)
    (hagree : ∀ j ≤ r, x' j = x j) (htop : x' (r + 1) = x (t + 1))
    (hnb : ∃ a ∈ wheelSystemA G z A₀ x r, G.Adj (x (t + 1)) a)
    (hnc : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x r)) :
    IsHubForWheelSystem G z A₀ x' (r + 1) Y := by
  obtain ⟨hws, hYne, hYanti, hYsub, hzc, hxc, hxnc⟩ := hhub
  refine ⟨isWheelSystem_of_agrees hws hr1 hrt hagree htop hnb hnc, hYne, hYanti, hYsub, hzc,
    ?_, ?_⟩
  · intro i hi
    rw [hagree i (by omega)]
    exact hxc i (by omega)
  · rw [htop]; exact hxnc

/-! ## The hub avoids `z` and every term of the wheel system -/

/-- Every member of the hub `Y` differs from `z` and from each of `x₀,…,x_{t+1}`.

For `j ≤ t` this is because `xⱼ` is `Y`-complete, hence not adjacent to itself.  For `j = t+1`
it is because if `x_{t+1} ∈ Y` then every `xⱼ` with `j ≤ t`, being `Y`-complete, is adjacent to
`x_{t+1}`, making `x_{t+1}` an `X_t`-complete vertex and contradicting condition 3 of the
wheel-system definition. -/
theorem hub_ne {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) Y) :
    (z ∉ Y) ∧ ∀ j ≤ t + 1, x j ∉ Y := by
  obtain ⟨hws, hYne, hYanti, hYsub, hzc, hxc, hxnc⟩ := hhub
  constructor
  · intro hz
    exact G.irrefl (hzc z hz)
  · intro j hj hmem
    rcases Nat.lt_or_ge j (t + 1) with hlt | hge
    · exact G.irrefl (hxc j hlt (x j) hmem)
    · have hj' : j = t + 1 := by omega
      subst hj'
      refine hws.2.2.2.2.2.1 (t + 1) (by omega) le_rfl ?_
      rintro w ⟨k, hk, rfl⟩
      have hkt : k < t + 1 := by
        have : k ≤ t + 1 - 1 := hk
        omega
      exact (hxc k hkt (x (t + 1)) hmem).symm

end Workspace.ProofLemmas.Thm213Setup
