import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup

/-!
# The `x₀ ↔ x₁` symmetry of a wheel system, for §19.2

PAPER (printed p. 116): *"Note that this definition is symmetric between `x₀, x₁`, so
`x₁, x₀, x₂,…,x_t` is another wheel system."*

That remark is what licenses the printed *"say"* / *"from the symmetry we may assume"* in
claims (7) (twice), (8), (10) and in the interlude before (11) of the proof of 19.2.  The
transport was first written `private` inside `Workspace/Statements/S19/Thm_19_2.lean`; it is
reproduced here verbatim, without the `private`, so the individual carve-outs can use it too.
`Thm_19_2.lean` is not modified.

`sw x` is the sequence `x₁, x₀, x₂, x₃, …`.  Everything §19.2 predicates of a wheel system —
`IsWheelSystem`, `Hyp192`, `Concl192`, `GoodA`, and `A₁` itself — is invariant under it, and
`sw` is an involution (`sw_sw`), so the transport runs in both directions.

`isWheel_congr` is the companion fact needed whenever the symmetry is applied to a rim: the
hole `z-x₀-P-x₁-z` read backwards is `z-x₁-P̄-x₀-z`, a *different list* with the same vertices
and the same length, and `IsWheel` transports along any such re-listing.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Symmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Transport of `IsWheel` along a re-listing of the rim with the same vertices and the
same length (used for the `x₀ ↔ x₁` symmetry, where the rim `z-x₀-P-x₁-z` is read backwards
as `z-x₁-P̄-x₀-z`). -/
theorem isWheel_congr {G : SimpleGraph V} {W : Set V} {C D : List V}
    (hD : IsHoleList G D) (hlen : C.length = D.length) (hmem : ∀ v : V, v ∈ D ↔ v ∈ C)
    (h : IsWheel G C W) : IsWheel G D W := by
  obtain ⟨⟨-, hC6⟩, ⟨hWne, hWanti, hWdisj⟩, a, b, c, d, ha, hb, hc, hd, hab, hcd,
    hac, had, hbc, hbd⟩ := h
  refine ⟨⟨hD, ?_⟩, ⟨hWne, hWanti, ?_⟩, a, b, c, d, (hmem a).mpr ha, (hmem b).mpr hb,
    (hmem c).mpr hc, (hmem d).mpr hd, hab, hcd, hac, had, hbc, hbd⟩
  · simpa [holeLength, ← hlen] using hC6
  · intro v hv
    exact hWdisj v ((hmem v).mp hv)

/-- The sequence `x₁, x₀, x₂, x₃, …`. -/
def sw (x : ℕ → V) : ℕ → V :=
  fun n => if n = 0 then x 1 else if n = 1 then x 0 else x n

theorem sw_zero (x : ℕ → V) : sw x 0 = x 1 := by simp [sw]

theorem sw_one (x : ℕ → V) : sw x 1 = x 0 := by simp [sw]

theorem sw_two (x : ℕ → V) : sw x 2 = x 2 := by simp [sw]

theorem sw_apply (x : ℕ → V) (n : ℕ) :
    sw x n = x (if n = 0 then 1 else if n = 1 then 0 else n) := by
  simp only [sw]; split_ifs <;> rfl

theorem sw_sw (x : ℕ → V) : sw (sw x) = x := by
  funext n
  by_cases h0 : n = 0
  · subst h0; rw [sw_zero, sw_one]
  by_cases h1 : n = 1
  · subst h1; rw [sw_one, sw_zero]
  · rw [sw_apply, sw_apply]
    simp [h0, h1]

theorem sw_X1 (x : ℕ → V) : wheelSystemX (sw x) 1 = wheelSystemX x 1 := by
  rw [Thm192Setup.wheelSystemX_one, Thm192Setup.wheelSystemX_one, sw_zero, sw_one]
  exact Set.pair_comm _ _

theorem sw_A1 (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) :
    wheelSystemA G z A₀ (sw x) 1 = wheelSystemA G z A₀ x 1 := by
  simp only [wheelSystemA, sw_X1]

/-- *"`x₁, x₀, x₂,…,x_t` is another wheel system"*. -/
theorem sw_ws {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) : IsWheelSystem G z A₀ (sw x) 2 := by
  obtain ⟨h1, hinj, hout, ⟨he0, he1, hnc⟩, hcond2, hcond3, hz⟩ := hws
  refine ⟨h1, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro j hj k hk hjk
    rw [sw_apply, sw_apply] at hjk
    have := hinj _ (by split_ifs <;> omega) _ (by split_ifs <;> omega) hjk
    split_ifs at this <;> omega
  · intro j hj
    rw [sw_apply]
    exact hout _ (by split_ifs <;> omega)
  · rw [sw_zero]; exact he1
  · rw [sw_one]; exact he0
  · intro a ha hcon
    refine hnc a ha ?_
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    refine hcon v ?_
    simp only [sw_zero, sw_one, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · intro i hi2 hi2'
    have hi : i = 2 := by omega
    subst hi
    obtain ⟨B, hB0, hBc, ⟨b, hbB, hadj⟩, hBz, hBX⟩ := hcond2 2 (by omega) (by omega)
    exact ⟨B, hB0, hBc, ⟨b, hbB, by rw [sw_two]; exact hadj⟩, hBz,
      by simp only [show (2 : ℕ) - 1 = 1 from rfl, sw_X1]; exact hBX⟩
  · intro i hi1 hi2
    interval_cases i
    · intro hcon
      refine hcond3 1 (by omega) (by omega) ?_
      intro v hv
      obtain ⟨j, hj, rfl⟩ := hv
      have hj0 : j = 0 := by omega
      subst hj0
      have h := hcon (sw x 0) ⟨0, le_rfl, rfl⟩
      rw [sw_zero, sw_one] at h
      exact h.symm
    · simp only [sw_two, show (2 : ℕ) - 1 = 1 from rfl, sw_X1]
      exact hcond3 2 (by omega) (by omega)
  · intro j hj
    rw [sw_apply]
    exact hz _ (by split_ifs <;> omega)

theorem sw_hyp {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (h : Hyp192 G z A₀ x Y) : Hyp192 G z A₀ (sw x) Y := by
  obtain ⟨hsub, hanti, h0, h1, h2, hnb⟩ := h
  refine ⟨?_, hanti, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨ha, hb, hc, hd⟩ := hsub w hw
    exact ⟨ha, by rw [sw_zero]; exact hc, by rw [sw_one]; exact hb, by rw [sw_two]; exact hd⟩
  · rw [sw_zero]; exact h1
  · rw [sw_one]; exact h0
  · rw [sw_two]; exact h2
  · intro w hw hnadj
    rw [sw_two] at hnadj
    rw [sw_A1]
    exact hnb w hw hnadj

theorem sw_concl {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (h : Concl192 G z A₀ x Y) : Concl192 G z A₀ (sw x) Y := by
  obtain ⟨hz, C, hW, h0, h1, hzC, hCsub⟩ := h
  refine ⟨hz, C, hW, by rw [sw_zero]; exact h1, by rw [sw_one]; exact h0, hzC, ?_⟩
  rw [sw_zero, sw_one, sw_A1]
  intro v hv
  rcases hCsub hv with hh | hh
  · refine Or.inl ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
    tauto
  · exact Or.inr hh

theorem sw_goodA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    {y : V} {A : Set V} (h : GoodA G z A₀ x Y y A) : GoodA G z A₀ (sw x) Y y A := by
  obtain ⟨hsub, hconn, h0, h1, h2, hY, hy⟩ := h
  exact ⟨by rw [sw_A1]; exact hsub, hconn, by rw [sw_zero]; exact h1,
    by rw [sw_one]; exact h0, by rw [sw_two]; exact h2,
    by simpa only [sw_two] using hY, hy⟩

/-- The induction hypothesis of 19.2 transports too: this is the shape every carve-out needs,
since `ih` is one of their binders. -/
theorem sw_ih {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard) :
    (∀ Y' : Set V, Y'.ncard < Y.ncard →
      Hyp192 G z A₀ (sw x) Y' → Concl192 G z A₀ (sw x) Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard := by
  refine ⟨?_, ih.2⟩
  intro Y' hlt hH
  have hH' : Hyp192 G z A₀ x Y' := by
    have hh := sw_hyp hH
    rwa [sw_sw] at hh
  exact sw_concl (ih.1 Y' hlt hH')

/-- Minimality of `A` transports as well. -/
theorem sw_goodA_min {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    {y : V} {A : Set V}
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard) :
    ∀ B : Set V, GoodA G z A₀ (sw x) Y y B → A.ncard ≤ B.ncard := by
  intro B hB
  refine hAmin B ?_
  have hh := sw_goodA hB
  rwa [sw_sw] at hh

end Workspace.ProofLemmas.Thm192Symmetry
