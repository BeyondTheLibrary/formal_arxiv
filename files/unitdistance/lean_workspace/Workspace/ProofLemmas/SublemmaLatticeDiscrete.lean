import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaSeparation
import Workspace.ProofLemmas.SublemmaPacking

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeDiscrete (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) (R : ℝ) :
    (∀ a : Fin f → ℂ, (Xset sel DD R a).Finite) ∧
      (∀ (U : Finset (Fin f → ℂ)) (a : Fin f → ℂ),
        {p : (Fin f → ℂ) × (Fin f → ℂ) |
            p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U}.Finite) := by
  -- Every window intersection is finite.
  have hXfin : ∀ a : Fin f → ℂ, (Xset sel DD R a).Finite := by
    intro a
    by_cases hR : R ≤ 0
    · -- If `R ≤ 0` the window is contained in `{0}` (each coordinate norm is forced to `0`),
      -- so the coset intersection is finite.
      have hwin : (window (f := f) R).Finite := by
        apply Set.Finite.subset (Set.finite_singleton (0 : Fin f → ℂ))
        intro z hz
        simp only [window, Set.mem_setOf_eq] at hz
        rw [Set.mem_singleton_iff]
        funext r
        have hzr : ‖z r‖ = 0 := le_antisymm (le_trans (hz r) hR) (norm_nonneg _)
        simpa using norm_eq_zero.mp hzr
      exact Set.Finite.subset hwin (fun z hz => hz.2)
    · -- If `R > 0`, use the lattice separation bound and the packing count.
      rw [not_le] at hR
      have hsep := Workspace.ProofLemmas.SublemmaSeparation hcm sel DD hDD R a
      exact (SublemmaPacking sel DD hDD R hR a hsep).1
  refine ⟨hXfin, ?_⟩
  -- The `Ecount` index set is a subset of `Xset × Xset`, hence finite.
  intro U a
  apply Set.Finite.subset ((hXfin a).prod (hXfin a))
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

end MinkowskiLemmas
