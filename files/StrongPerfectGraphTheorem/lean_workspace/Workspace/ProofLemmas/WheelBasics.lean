import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.Statements.S02.Thm_2_3

/-!
# Basic facts about wheels

Two facts that §16 uses without comment.

* `even_cycCount_of_wheel` — *"there are an even number of `Y`-complete edges in `C`"*
  (printed p. 101, inside the proof of 16.3).  This is the second bullet of 2.3 applied to the
  rim: 2.3 leaves the alternative *"there are exactly two `X`-complete vertices and they are
  adjacent"*, which a wheel excludes because its two disjoint `Y`-complete edges already supply
  four distinct `Y`-complete rim vertices.  It is the hypothesis of
  `WheelParity.sameWheelParity_iff`, so it is what makes wheel-parity two-valued at all.

* `exists_optimal_odd_wheel` — *"Suppose `(C,Y)` is an odd wheel with `Y` maximal, and subject
  to that, such that the number of `Y`-complete edges in `C` is minimum"* (printed p. 101, the
  opening sentence of the proof of 16.3).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.WheelBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.ExtremalChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rim of a wheel carries an even number of `Y`-complete edges. -/
theorem even_ncard_yEdges_of_wheel {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) :
    Even {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard := by
  obtain ⟨⟨hhole, -⟩, ⟨-, hYanti, hCY⟩, a, b, c, d, haC, hbC, hcC, hdC, hab, hcd,
    hac, had, hbc, hbd⟩ := hw
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti C
    (Or.inr hhole) hCY).2 hhole
  rcases h23 with h | ⟨x, y, hset, hxy, -⟩
  · exact h
  · exfalso
    have hmem : ∀ w : V, w ∈ C → VertexComplete G w Y → w = x ∨ w = y := by
      intro w hwC hwY
      have hw' : w ∈ ({x, y} : Set V) := by rw [← hset]; exact ⟨hwC, hwY⟩
      simpa using hw'
    have ha := hmem a haC hab.2.1
    have hb := hmem b hbC hab.2.2
    have hc := hmem c hcC hcd.2.1
    have hab' : a ≠ b := hab.1.ne
    have hsub : ({a, b, c} : Set V) ⊆ ({x, y} : Set V) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have e1 : a ∉ ({b, c} : Set V) := by simp [hab', hac]
    have e2 : b ∉ ({c} : Set V) := by simp [hbc]
    have h3 : ({a, b, c} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem e1 (Set.toFinite _),
        Set.ncard_insert_of_notMem e2 (Set.toFinite _), Set.ncard_singleton]
    have h2 : ({x, y} : Set V).ncard = 2 := Set.ncard_pair hxy
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

/-- The same fact in the `cycCount` bookkeeping of `WheelParity` — this is exactly the
hypothesis of `WheelParity.sameWheelParity_iff`. -/
theorem even_cycCount_of_wheel {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) :
    Even (WheelParity.cycCount G Y C C.length) := by
  rw [← WheelParity.ncard_yEdges_eq_cycCount hw.1.1]
  exact even_ncard_yEdges_of_wheel hBerge hw

/-- PAPER (16.3, printed p. 101): *"Suppose `(C,Y)` is an odd wheel with `Y` maximal, and
subject to that, such that the number of `Y`-complete edges in `C` is minimum."* -/
theorem exists_optimal_odd_wheel (G : SimpleGraph V)
    (hex : ∃ (C : List V) (Y : Set V), IsOddWheel G C Y) :
    ∃ (C : List V) (Y : Set V), IsOddWheel G C Y ∧
      (¬ ∃ (C' : List V) (Y' : Set V), IsOddWheel G C' Y' ∧ Y ⊂ Y') ∧
      (∀ C' : List V, IsOddWheel G C' Y →
        {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard ≤
          {e : Sym2 V | ∃ u ∈ C', ∃ v ∈ C', e = s(u, v) ∧ EdgeComplete G Y u v}.ncard) := by
  classical
  obtain ⟨⟨C₁, Y₁⟩, hw₁, hmaxY⟩ :=
    exists_max_nat (fun t : List V × Set V => IsOddWheel G t.1 t.2) (fun t => t.2.ncard)
      (Fintype.card V) (fun t _ => ncard_le_card t.2)
      (by obtain ⟨C, Y, h⟩ := hex; exact ⟨⟨C, Y⟩, h⟩)
  obtain ⟨C, hwC, hminC⟩ :=
    exists_min_nat (fun C' : List V => IsOddWheel G C' Y₁)
      (fun C' => {e : Sym2 V | ∃ u ∈ C', ∃ v ∈ C', e = s(u, v) ∧ EdgeComplete G Y₁ u v}.ncard)
      ⟨C₁, hw₁⟩
  refine ⟨C, Y₁, hwC, ?_, fun C' hw' => hminC C' hw'⟩
  rintro ⟨C', Y', hw', hss⟩
  have h1 := hmaxY ⟨C', Y'⟩ hw'
  have h2 : Y₁.ncard < Y'.ncard := Set.ncard_lt_ncard hss (Set.toFinite _)
  simp only at h1
  omega

end Workspace.ProofLemmas.WheelBasics
