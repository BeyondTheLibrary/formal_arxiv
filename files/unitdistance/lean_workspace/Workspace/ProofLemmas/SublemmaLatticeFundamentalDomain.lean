import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaMinkowskiMapIsFullLattice

set_option maxHeartbeats 4000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeFundamentalDomain (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    ∃ F : Set (Fin f → ℂ),
      MeasureTheory.IsAddFundamentalDomain (↥(lattice sel DD)) F volume ∧
        0 < volume F ∧ volume F < ⊤ := by
  obtain ⟨hdisc, hzl⟩ := SublemmaMinkowskiMapIsFullLattice hcm sel DD hDD
  letI := hdisc
  letI := hzl
  set Lsub : Submodule ℤ (Fin f → ℂ) := AddSubgroup.toIntSubmodule (lattice sel DD) with hLsub
  haveI : Module.Free ℤ ↥Lsub := ZLattice.module_free ℝ Lsub
  haveI : Module.Finite ℤ ↥Lsub := ZLattice.module_finite ℝ Lsub
  set b : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥Lsub) ℤ ↥Lsub :=
    Module.Free.chooseBasis ℤ ↥Lsub with hb
  set bR : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥Lsub) ℝ (Fin f → ℂ) :=
    Module.Basis.ofZLatticeBasis ℝ Lsub b with hbR
  refine ⟨ZSpan.fundamentalDomain bR, ?_, ?_, ?_⟩
  · exact ZLattice.isAddFundamentalDomain b volume
  · exact pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero bR)
  · exact (ZSpan.fundamentalDomain_isBounded bR).measure_lt_top

end MinkowskiLemmas
