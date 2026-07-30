import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaLatticeDiscreteTopology
import Workspace.ProofLemmas.SublemmaLatticeRankFull

set_option maxHeartbeats 4000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaMinkowskiMapIsFullLattice (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    DiscreteTopology ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) ∧
      @IsZLattice ℝ _ _ _ _ (AddSubgroup.toIntSubmodule (lattice sel DD))
        (SublemmaLatticeDiscreteTopology hcm sel DD hDD) := by
  haveI hdisc : DiscreteTopology ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) :=
    SublemmaLatticeDiscreteTopology hcm sel DD hDD
  refine ⟨hdisc, ?_⟩
  set Lsub : Submodule ℤ (Fin f → ℂ) := AddSubgroup.toIntSubmodule (lattice sel DD) with hLsub
  set s : Set (Fin f → ℂ) := (↑Lsub : Set (Fin f → ℂ)) with hs
  -- `span ℤ s = Lsub` since `Lsub` is already a `ℤ`-submodule.
  have hspanZ : Submodule.span ℤ s = Lsub := Submodule.span_eq Lsub
  haveI hdisc' : DiscreteTopology ↥(Submodule.span ℤ s) := by rw [hspanZ]; exact hdisc
  -- discreteness ⇒ `dim_ℝ (span ℝ s) = rank_ℤ (span ℤ s)`.
  have hfr : Set.finrank ℝ s = Set.finrank ℤ s :=
    Real.finrank_eq_int_finrank_of_discrete hdisc'
  -- `rank_ℤ = 2f`.
  have hZ : Set.finrank ℤ s = 2 * f := by
    show Module.finrank ℤ ↥(Submodule.span ℤ s) = 2 * f
    rw [hspanZ]; exact SublemmaLatticeRankFull hcm sel DD hDD
  -- ambient dimension is also `2f`.
  have hfrankE : Module.finrank ℝ (Fin f → ℂ) = 2 * f := by
    rw [Module.finrank_pi_fintype ℝ]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  -- Hence `span ℝ s = ⊤`.
  have hspanR_top : Submodule.span ℝ s = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    show Module.finrank ℝ ↥(Submodule.span ℝ s) = Module.finrank ℝ (Fin f → ℂ)
    rw [← Set.finrank, hfr, hZ, hfrankE]
  exact IsZLattice.mk hspanR_top

end MinkowskiLemmas
