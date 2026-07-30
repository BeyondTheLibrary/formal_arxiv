import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaHaarUnfolding (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (F : Set (Fin f → ℂ))
    (hF : IsAddFundamentalDomain (↥(lattice sel DD)) F)
    (S : Set (Fin f → ℂ)) (hS : MeasurableSet S) (hSbdd : Bornology.IsBounded S) :
    ∫ a in F, (∑' l : ↥(lattice sel DD),
        (S.indicator (fun _ => (1 : ℝ))) (a + (l : Fin f → ℂ)))
      = (volume S).toReal := by
  classical
  -- Countability of the lattice (needed by the unfolding lemmas).
  haveI hcountOK : Countable (𝓞 K) := by
    have b := Module.Free.chooseBasis ℤ (𝓞 K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI hcountLat : Countable (↥(lattice sel DD)) := by
    have hc : ((lattice sel DD : Set (Fin f → ℂ))).Countable := by
      rw [lattice, AddMonoidHom.coe_range]; exact Set.countable_range _
    exact hc.to_subtype
  set g : (Fin f → ℂ) → ℝ := S.indicator (fun _ => (1 : ℝ)) with hgdef
  have hgmeas : Measurable g := by rw [hgdef]; exact measurable_const.indicator hS
  have hSvol : volume S ≠ ⊤ := hSbdd.measure_lt_top.ne
  -- `g` is integrable.
  have hgint : Integrable g volume := by
    rw [hgdef, integrable_indicator_iff hS]
    exact integrableOn_const hSvol (by simp)
  -- `∫ g = vol S`.
  have hInt : ∫ x, g x = (volume S).toReal := by
    have hg1 : g = S.indicator (1 : (Fin f → ℂ) → ℝ) := by rw [hgdef, Pi.one_def]
    rw [hg1, integral_indicator_one hS]; rfl
  -- The unfolding identity `∫ g = ∑' l, ∫_F g (l +ᵥ x)`.
  have hUnfold := hF.integral_eq_tsum'' g hgint
  -- AE-strong measurability of each shifted summand.
  have haemeas : ∀ l : ↥(lattice sel DD),
      AEStronglyMeasurable (fun a => g (l +ᵥ a)) (volume.restrict F) :=
    fun l => (hgmeas.comp (measurable_const_vadd l)).aestronglyMeasurable
  -- Summability bound for swapping the sum and the integral.
  have hsum_ne : ∑' l : ↥(lattice sel DD),
      ∫⁻ a, ‖g (l +ᵥ a)‖ₑ ∂(volume.restrict F) ≠ ⊤ := by
    rw [← hF.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)]
    have hnorm : (fun x => ‖g x‖ₑ) = S.indicator (1 : (Fin f → ℂ) → ENNReal) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hgdef, Set.indicator_apply, hx]
    rw [hnorm, lintegral_indicator_one hS]
    exact hSvol
  -- Convert the goal's `a + ↑l` into the `+ᵥ` action, then unfold.
  have hpt : ∀ (a : Fin f → ℂ) (l : ↥(lattice sel DD)),
      g (a + (l : Fin f → ℂ)) = g (l +ᵥ a) := by
    intro a l
    rw [show (l +ᵥ a) = (l : Fin f → ℂ) + a from rfl, add_comm]
  simp only [hpt]
  rw [integral_tsum haemeas hsum_ne, ← hUnfold]
  exact hInt

end MinkowskiLemmas
