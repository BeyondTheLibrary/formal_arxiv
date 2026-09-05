import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S22.Thm_22_2
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# 23.3 — the descent step (proof attempt)

PAPER (printed p. 141, proof of 23.3), the part implemented here:

> *"By 22.2, there exists `r` with `1 ≤ r < s`, and a vertex `v` such that `y` has no
> neighbour in `A_r ∪ {v}`, and `v` is adjacent to `z`, and has a neighbour in `A_r`, and a
> non-neighbour in `X_r`.  Then `(y, A₀)` is a frame, and `x₀,…,x_r` is a wheel system with
> respect to it, and `z` is `{y,x₀,…,x_r}`-complete, and has a neighbour in `A'_r` (namely
> `v`), where `A'_r` is the maximal connected subset of `V(G)` including `A₀` and containing
> no neighbour of `y` and no `X_r`-complete vertex."*

22.2 is applied with hub `Y := {y}` — the singleton is nonempty and (trivially) anticonnected,
`z, x₀,…,x_s` are `{y}`-complete exactly because `y` is `{z,x₀,…,x_s}`-complete, its unique
member has a neighbour in `A_s` by hypothesis, "at most one member has no neighbour in `A₁`" is
vacuous for a singleton, and "there is no wheel with hub `Y`" is `G ∈ F₉`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm233Descent

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The descent step of 23.3, as printed: apply 22.2 to the configuration
`(z,A₀), x₀,…,x_s, y` and read off the new configuration `(y,A₀), x₀,…,x_r, z`,
whose height `r` satisfies `1 ≤ r < s`. -/
theorem descent (G : SimpleGraph V) (hG : InF9 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (s : ℕ) (hws : IsWheelSystem G z A₀ x s)
    (y : V)
    (hy₁ : y ∉ insert z (wheelSystemX x s))
    (hy₂ : VertexComplete G y (insert z (wheelSystemX x s)))
    (hy₃ : ∃ a ∈ wheelSystemA G z A₀ x s, G.Adj y a) :
    ∃ r : ℕ, 1 ≤ r ∧ r < s ∧
      IsFrame G y A₀ ∧ IsWheelSystem G y A₀ x r ∧
      z ∉ insert y (wheelSystemX x r) ∧
      VertexComplete G z (insert y (wheelSystemX x r)) ∧
      (∃ a ∈ wheelSystemA G y A₀ x r, G.Adj z a) := by
  classical
  -- the seven clauses of the given wheel system
  have hs1 : 1 ≤ s := hws.1
  have hdist := hws.2.1
  have hxA₀ := hws.2.2.1
  have hcond1 := hws.2.2.2.1
  have hcond2 := hws.2.2.2.2.1
  have hcond3 := hws.2.2.2.2.2.1
  have hzx := hws.2.2.2.2.2.2
  -- `y ∉ {z, x₀,…,x_s}` in the two forms used below
  have hyz : y ≠ z := by
    intro h; exact hy₁ (by rw [h]; exact Set.mem_insert _ _)
  have hyx : ∀ i ≤ s, y ≠ x i := by
    intro i hi h
    exact hy₁ (Set.mem_insert_of_mem _ ⟨i, hi, h⟩)
  -- `y` is `{z, x₀,…,x_s}`-complete
  have hyzadj : G.Adj y z := hy₂ z (Set.mem_insert _ _)
  have hyxadj : ∀ i ≤ s, G.Adj y (x i) :=
    fun i hi => hy₂ (x i) (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩)
  -- `y ∉ A₀`, since `A₀` contains no neighbour of `z`
  have hyA₀ : y ∉ A₀ := fun h => hframe.2.2.2 y h hyzadj.symm
  -- no vertex of `A₀` is `Xᵢ`-complete, for any `i ≥ 1` — clause 1 of the wheel system
  have hncA₀ : ∀ i, 1 ≤ i → ∀ w ∈ A₀, ¬ VertexComplete G w (wheelSystemX x i) := by
    intro i hi w hw hc
    refine hcond1.2.2 w hw ?_
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hc (x 0) ⟨0, by omega, rfl⟩
    · exact hc (x 1) ⟨1, hi, rfl⟩
  -- ### 22.2 applied with the singleton hub `Y = {y}`
  have hYdisj : ∀ w ∈ ({y} : Set V), w ∉ A₀ ∧ w ≠ z ∧ ∀ i ≤ s, w ≠ x i := by
    rintro w rfl
    exact ⟨hyA₀, hyz, hyx⟩
  have hYne : ({y} : Set V).Nonempty := ⟨y, rfl⟩
  have hYanti : AnticonnectedSet G ({y} : Set V) := by
    intro a b
    have hab : a = b := Subtype.ext (a.2.trans b.2.symm)
    rw [hab]
  have hzY : VertexComplete G z ({y} : Set V) := by
    intro w hw
    have hw' : w = y := hw
    subst hw'
    exact hyzadj.symm
  have hxY : ∀ i ≤ s, VertexComplete G (x i) ({y} : Set V) := by
    intro i hi w hw
    have hw' : w = y := hw
    subst hw'
    exact (hyxadj i hi).symm
  have hYAs : ∀ w ∈ ({y} : Set V), ∃ a ∈ wheelSystemA G z A₀ x s, G.Adj w a := by
    rintro w rfl
    exact hy₃
  have hone : Set.Subsingleton
      {w ∈ ({y} : Set V) | VertexAnticomplete G w (wheelSystemA G z A₀ x 1)} := by
    intro p hp q hq
    have hp' : p = y := hp.1
    have hq' : q = y := hq.1
    rw [hp', hq']
  have hnowheel : ¬ ∃ C : List V, Workspace.Types.Wheels.SPGT.IsWheel G C ({y} : Set V) := by
    rintro ⟨C', hC'⟩
    exact hG.2.1 ⟨C', ({y} : Set V), hC'⟩
  obtain ⟨r, hr1, hrs, y', hy'Y, v, -, hvanti, hvzadj, ⟨a₀, ha₀, hva₀⟩, b, hbX, hvb⟩ :=
    _root_.Workspace.Statements.S22.SPGT.thm_22_2 G hG.1 hbsp z A₀ hframe x s hws
      ({y} : Set V) hYdisj hYne hYanti hzY hxY hYAs hone hnowheel
  have hy'eq : y' = y := hy'Y
  rw [hy'eq] at hvanti
  -- `A₀ ⊆ A_r`, and `y` has no neighbour in `A_r ∪ {v}`
  have hA₀Ar : A₀ ⊆ wheelSystemA G z A₀ x r :=
    WheelSystemBasics.A₀_subset_wheelSystemA hframe (hncA₀ r hr1)
  have hyAr : ∀ w ∈ wheelSystemA G z A₀ x r, ¬ G.Adj y w :=
    fun w hw => hvanti w (Or.inl hw)
  refine ⟨r, hr1, hrs, ?_, ?_, ?_, ?_, ?_⟩
  · -- *"Then `(y, A₀)` is a frame"*
    exact ⟨hframe.1, hframe.2.1, hyA₀, fun w hw => hyAr w (hA₀Ar hw)⟩
  · -- *"and `x₀,…,x_r` is a wheel system with respect to it"*
    refine ⟨hr1, ?_, ?_, hcond1, ?_, ?_, ?_⟩
    · intro j hj k hk h
      exact hdist j (by omega) k (by omega) h
    · intro j hj
      exact ⟨(hxA₀ j (by omega)).1, (hyx j (by omega)).symm⟩
    · -- clause 2: the witness is `A_{i-1}`, which avoids the neighbours of `y` because
      -- `A_{i-1} ⊆ A_r`
      intro i h2 hir
      refine ⟨wheelSystemA G z A₀ x (i - 1),
        WheelSystemBasics.A₀_subset_wheelSystemA hframe (hncA₀ (i - 1) (by omega)),
        WheelSystemBasics.connectedSet_wheelSystemA hframe.1, ?_, ?_, ?_⟩
      · obtain ⟨B, hA₀B, hBc, hbB, hBz, hBX⟩ := hcond2 i h2 (by omega)
        exact WheelSystemBasics.exists_adj_wheelSystemA_of_witness hA₀B hBc hBz hBX hbB
      · intro w hw
        exact hyAr w (WheelSystemBasics.wheelSystemA_mono (by omega) hw)
      · intro w hw
        exact WheelSystemBasics.wheelSystemA_no_complete hw
    · intro i h1 hir
      exact hcond3 i h1 (by omega)
    · intro j hj
      exact hyxadj j (by omega)
  · -- `z ∉ {y, x₀,…,x_r}`
    intro h
    simp only [Set.mem_insert_iff] at h
    rcases h with h | ⟨j, hj, hzj⟩
    · exact hyz h.symm
    · exact (hxA₀ j (by omega)).2 hzj.symm
  · -- *"and `z` is `{y,x₀,…,x_r}`-complete"*
    intro w hw
    simp only [Set.mem_insert_iff] at hw
    rcases hw with rfl | ⟨j, hj, rfl⟩
    · exact hyzadj.symm
    · exact hzx j (by omega)
  · -- *"and has a neighbour in `A'_r` (namely `v`)"*: the witness set is `A_r ∪ {v}`
    refine ⟨v, ?_, hvzadj.symm⟩
    refine WheelSystemBasics.mem_wheelSystemA_of_witness
      (B := wheelSystemA G z A₀ x r ∪ {v})
      (fun w hw => Or.inl (hA₀Ar hw)) ?_ ?_ ?_ (Or.inr rfl)
    · exact ConnectedSetUnionAttach.connectedSet_union_singleton
        (WheelSystemBasics.connectedSet_wheelSystemA hframe.1) ⟨a₀, ha₀, hva₀⟩
    · intro w hw
      exact hvanti w hw
    · rintro w (hw | hw)
      · exact WheelSystemBasics.wheelSystemA_no_complete hw
      · have hw' : w = v := hw
        subst hw'
        intro hc
        exact hvb (hc b hbX)

end Workspace.ProofLemmas.Thm233Descent
