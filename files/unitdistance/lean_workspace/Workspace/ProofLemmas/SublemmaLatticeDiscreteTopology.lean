import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaLatticeNormBound

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeDiscreteTopology (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    DiscreteTopology ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) := by
  have hbound := SublemmaLatticeNormBound hcm sel DD hDD
  have hDD0 : (0 : ℝ) < (DD : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hDD
  have hDDpos : (0 : ℝ) < (DD : ℝ)⁻¹ := inv_pos.mpr hDD0
  apply discreteTopology_of_isOpen_singleton_zero
  have hset : {(0 : ↥(AddSubgroup.toIntSubmodule (lattice sel DD)))}
      = Subtype.val ⁻¹' (Metric.ball (0 : Fin f → ℂ) ((DD : ℝ)⁻¹)) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl; simpa using hDDpos
    · intro hx
      by_contra hne
      have hxne : (x : Fin f → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
      have hxlat : (x : Fin f → ℂ) ∈ lattice sel DD := x.2
      exact absurd hx (not_lt.mpr (hbound (x : Fin f → ℂ) hxlat hxne))
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

end MinkowskiLemmas
