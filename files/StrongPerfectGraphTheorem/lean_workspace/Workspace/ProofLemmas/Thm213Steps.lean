import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Pseudowheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S19.Thm_19_2
import Workspace.Statements.S20.Thm_20_1
import Workspace.Statements.S21.Thm_21_2
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.Thm213Setup

/-!
# The three citations in the printed proof of 21.3

The printed proof (perfect.pdf, printed page 133) is:

> *Suppose there is no such wheel.  Choose `r` with `1 ≤ r ≤ t`, minimum such that `x_{t+1}` has a
> neighbour in `A_r` and a nonneighbour in `X_r`.  By hypothesis, every member of `Y` has a
> neighbour in `A_r ∪ {x_{t+1}}`.  **By 19.2, `r > 1`.**  Since at most one member of `Y` has no
> neighbour in `A_{r−1}` (because at most one has no neighbour in `A_1`), **it follows from 21.2
> that `x_{t+1}` has a neighbour in `A_{r−1}`**.  Since no wheel has hub `Y`, **20.1 implies that
> `x_0,…,x_r,x_{t+1}` is not a `Y`-diamond**, and so `x_{t+1}` is not `X_{r−1}`-complete.  But that
> contradicts the minimality of `r`.*

The three highlighted appeals are the three theorems below, in the order in which the paper makes
them.  Each is stated for an auxiliary sequence `x'` that agrees with `x` up to `r` and takes the
value `x_{t+1}` at `r+1` — that is the paper's `x_0,…,x_r,x_{t+1}` — so that the caller can
instantiate it with the concrete `fun j => if j ≤ r then x j else x (t+1)` of the frozen statement
of 21.3.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm213Steps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.WheelSystemBasics
open Workspace.ProofLemmas.Thm213Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **"By 19.2, `r > 1`."**  If the minimal `r` were `1`, then `x₀, x₁, x_{t+1}` is a wheel system
of height `2` to which 19.2 applies — its hypothesis *"every `y ∈ Y` nonadjacent to `x₂` has a
neighbour in `A₁`, and is adjacent to `z`"* is exactly what the hypothesis of 21.3 gives at `r = 1`
together with `z` being `Y`-complete — and 19.2 produces a wheel with hub `Y`. -/
theorem wheel_of_r_eq_one {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} {Y : Set V} (hframe : IsFrame G z A₀) (ht : 1 ≤ t)
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) Y)
    (x' : ℕ → V) (hagree : ∀ j ≤ 1, x' j = x j) (htop : x' 2 = x (t + 1))
    (hws' : IsWheelSystem G z A₀ x' 2)
    (hnbr : ∀ y ∈ Y, ∃ a ∈ (wheelSystemA G z A₀ x 1 ∪ {x (t + 1)} : Set V), G.Adj y a) :
    ∃ C : List V, IsWheel G C Y := by
  obtain ⟨hz, hxj⟩ := hub_ne hhub
  obtain ⟨hws, hYne, hYanti, hYsub, hzc, hxc, hxnc⟩ := hhub
  have hA1 : wheelSystemA G z A₀ x' 1 = wheelSystemA G z A₀ x 1 :=
    wheelSystemA_agrees G z A₀ hagree le_rfl
  have hYsub' : ∀ y ∈ Y, y ≠ z ∧ y ≠ x' 0 ∧ y ≠ x' 1 ∧ y ≠ x' 2 := by
    intro y hy
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl; exact hz hy
    · rw [hagree 0 (by omega)]; rintro rfl; exact hxj 0 (by omega) hy
    · rw [hagree 1 le_rfl]; rintro rfl; exact hxj 1 (by omega) hy
    · rw [htop]; rintro rfl; exact hxj (t + 1) le_rfl hy
  have h0 : VertexComplete G (x' 0) Y := by
    rw [hagree 0 (by omega)]; exact hxc 0 (by omega)
  have h1 : VertexComplete G (x' 1) Y := by
    rw [hagree 1 le_rfl]; exact hxc 1 (by omega)
  have h2 : ¬ VertexComplete G (x' 2) Y := by rw [htop]; exact hxnc
  have hnb : ∀ y ∈ Y, ¬ G.Adj y (x' 2) →
      (∃ a ∈ wheelSystemA G z A₀ x' 1, G.Adj y a) ∧ G.Adj y z := by
    intro y hy hne
    rw [htop] at hne
    refine ⟨?_, (hzc y hy).symm⟩
    obtain ⟨a, ha, hya⟩ := hnbr y hy
    rcases ha with ha | ha
    · exact ⟨a, by rw [hA1]; exact ha, hya⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact absurd hya hne
  obtain ⟨C, hC, -⟩ :=
    (Workspace.Statements.S19.SPGT.thm_19_2 G hG z A₀ hframe x' hws' Y hYsub' hYanti h0 h1 h2
      hnb).2
  exact ⟨C, hC⟩

/-- **"it follows from 21.2 that `x_{t+1}` has a neighbour in `A_{r−1}`"**.  Applied to the wheel
system `x₀,…,x_r,x_{t+1}` (whose height is `r+1`, so 21.2 is used with its `t` equal to `r`):
if `x_{t+1}` had no neighbour in `A_{r−1}` then, since at most one member of `Y` has no neighbour
in `A_{r−1} ∪ {x_{t+1}}` (because at most one has no neighbour in `A₁ ⊆ A_{r−1}`) and any such
member has a neighbour in `A_r` (by the hypothesis of 21.3 at `r`), 21.2 would give a wheel with
hub `Y`. -/
theorem nbr_in_prev {G : SimpleGraph V} (hG : InF8 G) {z : V} {A₀ : Set V} {x : ℕ → V}
    {t r : ℕ} {Y : Set V} (hframe : IsFrame G z A₀) (hr2 : 2 ≤ r) (hrt : r ≤ t)
    (x' : ℕ → V) (hagree : ∀ j ≤ r, x' j = x j) (htop : x' (r + 1) = x (t + 1))
    (hhub' : IsHubForWheelSystem G z A₀ x' (r + 1) Y)
    (hone : Set.Subsingleton
      {y ∈ Y | VertexAnticomplete G y (wheelSystemA G z A₀ x 1)})
    (hnbr : ∀ y ∈ Y, ∃ a ∈ (wheelSystemA G z A₀ x r ∪ {x (t + 1)} : Set V), G.Adj y a)
    (hno : ¬ ∃ C : List V, IsWheel G C Y) :
    ∃ a ∈ wheelSystemA G z A₀ x (r - 1), G.Adj (x (t + 1)) a := by
  by_contra hcon
  push_neg at hcon
  have hAprev : wheelSystemA G z A₀ x' (r - 1) = wheelSystemA G z A₀ x (r - 1) :=
    wheelSystemA_agrees G z A₀ hagree (by omega)
  have hAr : wheelSystemA G z A₀ x' r = wheelSystemA G z A₀ x r :=
    wheelSystemA_agrees G z A₀ hagree le_rfl
  have hmono : wheelSystemA G z A₀ x 1 ⊆ wheelSystemA G z A₀ x (r - 1) :=
    wheelSystemA_mono (by omega)
  refine hno (Workspace.Statements.S21.SPGT.thm_21_2 G hG.1 Y ?_ z A₀ hframe x' r hr2 hhub'
    ?_ ?_ ?_)
  · rintro ⟨X, P, hP⟩
    exact hG.2.1 ⟨X, Y, P, hP⟩
  · rw [hAprev, htop]
    intro a ha
    exact hcon a ha
  · intro y hy y' hy'
    refine hone ⟨hy.1, ?_⟩ ⟨hy'.1, ?_⟩
    · intro a ha
      exact hy.2 a (Or.inl (by rw [hAprev]; exact hmono ha))
    · intro a ha
      exact hy'.2 a (Or.inl (by rw [hAprev]; exact hmono ha))
  · intro y hy hanti
    obtain ⟨a, ha, hya⟩ := hnbr y hy
    rcases ha with ha | ha
    · exact ⟨a, by rw [hAr]; exact ha, hya⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact absurd hya (hanti (x (t + 1)) (Or.inr htop.symm))

/-- **"Since no wheel has hub `Y`, 20.1 implies that `x₀,…,x_r,x_{t+1}` is not a `Y`-diamond, and
so `x_{t+1}` is not `X_{r−1}`-complete."**  All the other clauses of the definition of a
`Y`-diamond are already available for `x₀,…,x_r,x_{t+1}` — the height is `r+1 ≥ 3`, `Y` is a hub
for it, and by the previous step `x_{t+1}` has a neighbour in `A_{r−1}` — so `X_{r−1}`-completeness
of `x_{t+1}` is the only thing that could still be missing. -/
theorem not_complete_prev {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V} {x : ℕ → V}
    {t r : ℕ} {Y : Set V} (hframe : IsFrame G z A₀) (hr2 : 2 ≤ r) (hrt : r ≤ t)
    (x' : ℕ → V) (hagree : ∀ j ≤ r, x' j = x j) (htop : x' (r + 1) = x (t + 1))
    (hhub' : IsHubForWheelSystem G z A₀ x' (r + 1) Y)
    (hprev : ∃ a ∈ wheelSystemA G z A₀ x (r - 1), G.Adj (x (t + 1)) a)
    (hno : ¬ ∃ C : List V, IsWheel G C Y) :
    ¬ VertexComplete G (x (t + 1)) (wheelSystemX x (r - 1)) := by
  intro hc
  have hidx : r + 1 - 2 = r - 1 := by omega
  have hAprev : wheelSystemA G z A₀ x' (r + 1 - 2) = wheelSystemA G z A₀ x (r - 1) := by
    rw [hidx]; exact wheelSystemA_agrees G z A₀ hagree (by omega)
  have hXprev : wheelSystemX x' (r + 1 - 2) = wheelSystemX x (r - 1) := by
    rw [hidx]; exact wheelSystemX_agrees hagree (by omega)
  obtain ⟨hz, hxj⟩ := hub_ne hhub'
  obtain ⟨hws', hYne, hYanti, hYsub, hzc, hxc, hxnc⟩ := hhub'
  refine hno (Workspace.Statements.S20.SPGT.thm_20_1 G hG z A₀ hframe Y hYsub hYne hYanti
    (Or.inl ⟨x', r + 1, hws', hYne, hYanti, ⟨hz, hxj⟩, hxc, hxnc, by omega, ?_, ?_⟩)).2
  · rw [hXprev, htop]; exact hc
  · rw [hAprev, htop]; exact hprev

end Workspace.ProofLemmas.Thm213Steps
