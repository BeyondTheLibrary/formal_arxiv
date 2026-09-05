import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.ExtremalChoice

/-!
# Choosing an optimal wheel with as few `Y`-complete rim edges as possible

The opening move of §§22–23 is always the same sentence.  Printed proof of **23.2**
(printed p. 139):

> *"Suppose there is a wheel in `G`, and choose an optimal wheel `(C, Y)` such that `C`
> contains as few `Y`-complete edges as possible."*

`Workspace.Types.WheelSystems.OptimalWheel` is the paper's *optimal* — a wheel whose hub `Y`
cannot be enlarged to the hub of another wheel — so "choose an optimal wheel" is a maximum
taken over `Y.ncard`, and "as few `Y`-complete edges as possible" is a subsequent minimum
taken over the rim with `Y` held fixed.

This module is the plain-wheel twin of `WheelBasics.exists_optimal_odd_wheel` (which does the
same for *odd* wheels, for 16.3); the argument is identical, with `IsWheel` in place of
`IsOddWheel`.  It is needed by 23.2 and is the standing hypothesis `OptimalWheel G C Y` of
23.1, 22.3, 22.4 and 22.5, none of which says where the optimal wheel comes from.

Note the two extremal clauses are taken in the paper's order and are **not** symmetric: the
minimum over rims is taken with the *same* hub `Y`, which is exactly what step (1) of 23.2
needs — it builds a second hole `C'` with two fewer `Y`-complete edges and concludes that
`(C', Y)` cannot be a wheel.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.OptimalWheelChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.ProofLemmas.ExtremalChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of `Y`-complete edges carried by the rim `C` — the quantity the paper
minimises in *"such that `C` contains as few `Y`-complete edges as possible"*.

Spelled exactly as in `WheelBasics.even_ncard_yEdges_of_wheel` and
`WheelParity.ncard_yEdges_eq_cycCount`, so those lemmas apply to it after `rw [yEdgeCount]`. -/
noncomputable def yEdgeCount (G : SimpleGraph V) (Y : Set V) (C : List V) : ℕ :=
  {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard

theorem yEdgeCount_def (G : SimpleGraph V) (Y : Set V) (C : List V) :
    yEdgeCount G Y C =
      {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard := rfl

/-- PAPER (23.2, printed p. 139): *"Suppose there is a wheel in `G`, and choose an optimal
wheel `(C, Y)` such that `C` contains as few `Y`-complete edges as possible."*

The hub is maximised first (that is `OptimalWheel`), then the rim is chosen to carry as few
`Y`-complete edges as possible **among rims with the same hub `Y`**. -/
theorem exists_optimal_wheel (G : SimpleGraph V)
    (hex : ∃ (C : List V) (Y : Set V), IsWheel G C Y) :
    ∃ (C : List V) (Y : Set V), OptimalWheel G C Y ∧
      ∀ C' : List V, IsWheel G C' Y → yEdgeCount G Y C ≤ yEdgeCount G Y C' := by
  classical
  obtain ⟨⟨C₁, Y₁⟩, hw₁, hmaxY⟩ :=
    exists_max_nat (fun t : List V × Set V => IsWheel G t.1 t.2) (fun t => t.2.ncard)
      (Fintype.card V) (fun t _ => ncard_le_card t.2)
      (by obtain ⟨C, Y, h⟩ := hex; exact ⟨⟨C, Y⟩, h⟩)
  obtain ⟨C, hwC, hminC⟩ :=
    exists_min_nat (fun C' : List V => IsWheel G C' Y₁) (fun C' => yEdgeCount G Y₁ C')
      ⟨C₁, hw₁⟩
  refine ⟨C, Y₁, ⟨hwC, ?_⟩, fun C' hw' => hminC C' hw'⟩
  rintro ⟨C', Y', hw', hss⟩
  have h1 := hmaxY ⟨C', Y'⟩ hw'
  have h2 : Y₁.ncard < Y'.ncard := Set.ncard_lt_ncard hss (Set.toFinite _)
  simp only at h1
  omega

/-- The unpacked form: the hub of the chosen wheel is nonempty and anticonnected, the rim is
a hole of length `≥ 6` disjoint from the hub, and no rim with the same hub carries fewer
`Y`-complete edges.  This is the shape the proof of 23.2 consumes. -/
theorem exists_optimal_wheel' (G : SimpleGraph V)
    (hex : ∃ (C : List V) (Y : Set V), IsWheel G C Y) :
    ∃ (C : List V) (Y : Set V),
      IsWheel G C Y ∧
      (¬ ∃ (C' : List V) (Y' : Set V), IsWheel G C' Y' ∧ Y ⊂ Y') ∧
      IsHoleList G C ∧ 6 ≤ holeLength C ∧
      Y.Nonempty ∧ AnticonnectedSet G Y ∧ (∀ v ∈ C, v ∉ Y) ∧
      ∀ C' : List V, IsWheel G C' Y → yEdgeCount G Y C ≤ yEdgeCount G Y C' := by
  obtain ⟨C, Y, ⟨hw, hopt⟩, hmin⟩ := exists_optimal_wheel G hex
  exact ⟨C, Y, hw, hopt, hw.1.1, hw.1.2, hw.2.1.1, hw.2.1.2.1, hw.2.1.2.2, hmin⟩

end Workspace.ProofLemmas.OptimalWheelChoice
