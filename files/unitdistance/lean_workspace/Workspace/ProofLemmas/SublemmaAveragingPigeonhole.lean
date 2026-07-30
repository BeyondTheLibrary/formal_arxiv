import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory

section MinkowskiLemmas

variable {f : ℕ}

theorem SublemmaAveragingPigeonhole
    (F : Set (Fin f → ℂ)) (hFpos : 0 < volume F) (hFfin : volume F < ⊤)
    (N E : (Fin f → ℂ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hNmeas : Measurable N) (hEmeas : Measurable E)
    (hNnonneg : ∀ a, 0 ≤ N a) (hEnonneg : ∀ a, 0 ≤ E a)
    (hNint : MeasureTheory.IntegrableOn N F volume)
    (hEint : MeasureTheory.IntegrableOn E F volume)
    (hempty : ∀ a, N a = 0 → E a = 0)
    (hEq : ∫ a in F, E a = c * ∫ a in F, N a)
    (hNpos : 0 < ∫ a in F, N a) :
    ∃ a, 0 < N a ∧ c * N a ≤ E a := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a, 0 < N a → E a < c * N a`
  set g : (Fin f → ℂ) → ℝ := fun a => c * N a - E a with hgdef
  have hgnonneg : ∀ a, 0 ≤ g a := by
    intro a
    rcases eq_or_lt_of_le (hNnonneg a) with h0 | hpos
    · have hE0 := hempty a h0.symm
      simp [hgdef, ← h0, hE0]
    · have hlt := hcon a hpos
      simp only [hgdef]; linarith
  have hgint : IntegrableOn g F volume := by
    simpa [hgdef] using (hNint.const_mul c).sub hEint
  -- `∫_F g = 0`.
  have hgint0 : ∫ a in F, g a = 0 := by
    have h1 : ∫ a in F, g a = (∫ a in F, c * N a) - ∫ a in F, E a :=
      integral_sub (hNint.const_mul c) hEint
    rw [integral_const_mul] at h1
    rw [h1, hEq]; ring
  -- Support of `N` (within `F`) has positive measure.
  have hNae : (0 : (Fin f → ℂ) → ℝ) ≤ᶠ[ae (volume.restrict F)] N := ae_of_all _ hNnonneg
  have hNsupp : 0 < volume (Function.support N ∩ F) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNae hNint).mp hNpos
  -- `support N ⊆ support g` (within `F`).
  have hsubset : Function.support N ∩ F ⊆ Function.support g ∩ F := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ha2⟩
    rw [Function.mem_support] at ha1 ⊢
    have hNa : 0 < N a := lt_of_le_of_ne (hNnonneg a) (Ne.symm ha1)
    have hlt := hcon a hNa
    simp only [hgdef]
    intro hg0; linarith
  -- Hence `∫_F g > 0`, contradicting `∫_F g = 0`.
  have hgae : (0 : (Fin f → ℂ) → ℝ) ≤ᶠ[ae (volume.restrict F)] g := ae_of_all _ hgnonneg
  have hgpos : 0 < ∫ a in F, g a := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hgae hgint]
    exact lt_of_lt_of_le hNsupp (measure_mono hsubset)
  linarith

end MinkowskiLemmas
