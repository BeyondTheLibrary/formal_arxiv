import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaNcountEqTsum (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) (R : ℝ)
    (a : Fin f → ℂ) :
    (Ncount sel DD R a : ℝ) = ∑' l : ↥(lattice sel DD),
      (window R).indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) := by
  classical
  -- The lattice points landing in the window.
  set T : Set (↥(lattice sel DD)) :=
    {l | a + (l : Fin f → ℂ) ∈ window R} with hTdef
  have he_inj : Function.Injective (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) :=
    fun l1 l2 h => Subtype.ext (add_left_cancel h)
  -- The window-indicator periodization equals `T.indicator 1`.
  have hT : ∀ l : ↥(lattice sel DD),
      (window R).indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ))
        = T.indicator (fun _ => (1 : ℝ)) l := by
    intro l
    simp only [Set.indicator_apply, hTdef, Set.mem_setOf_eq]
  -- Collapse the tsum to the cardinality of `T`.
  rw [tsum_congr hT, ← tsum_subtype]
  simp only [tsum_const, nsmul_eq_mul, mul_one, Nat.card_coe_set_eq]
  -- `T.ncard = (Xset ...).ncard`.
  have himg : (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) '' T = Xset sel DD R a := by
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨?_, hl⟩
      show (a + (l : Fin f → ℂ)) - a ∈ lattice sel DD
      rw [add_sub_cancel_left]; exact l.2
    · rintro ⟨hz1, hz2⟩
      refine ⟨⟨z - a, hz1⟩, ?_, ?_⟩
      · show a + (z - a) ∈ window R
        rw [show a + (z - a) = z from by abel]; exact hz2
      · show a + (z - a) = z
        abel
  have hncard : (Xset sel DD R a).ncard = T.ncard := by
    rw [← himg]; exact Set.ncard_image_of_injective T he_inj
  show ((Xset sel DD R a).ncard : ℝ) = (T.ncard : ℝ)
  exact_mod_cast hncard

end MinkowskiLemmas
