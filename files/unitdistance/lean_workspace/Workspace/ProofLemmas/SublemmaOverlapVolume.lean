import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory Pointwise

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaOverlapVolume (hcm : IsAdjoinI L K)
    (R : ℝ) (u : Fin f → ℂ) (hU_coord : ∀ r, ‖u r‖ = 1) :
    volume (window (f := f) R ∩ (window (f := f) R - {u})) =
      ENNReal.ofReal (overlapArea R ^ f) := by
  -- Per-coordinate: the overlap of two radius-`R` discs at centre distance `1`
  -- has the same volume as the reference pair `(0, 1)`, by rotation invariance.
  have hcoordVol : ∀ c : ℂ, ‖c‖ = 1 →
      volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R)
        = ENNReal.ofReal (overlapArea R) := by
    intro c hc
    set a : Circle := ⟨c, mem_sphere_zero_iff_norm.mpr hc⟩ with ha
    have hac : (a : ℂ) = c := rfl
    have hiso : Isometry (rotation a) := (rotation a).isometry
    have h0 : (rotation a) 0 = 0 := by rw [rotation_apply, mul_zero]
    have h1 : (rotation a) 1 = c := by rw [rotation_apply, mul_one, hac]
    have e0 : (rotation a) ⁻¹' Metric.closedBall (0 : ℂ) R = Metric.closedBall (0 : ℂ) R := by
      have h := hiso.preimage_closedBall 0 R
      rwa [h0] at h
    have e1 : (rotation a) ⁻¹' Metric.closedBall c R = Metric.closedBall (1 : ℂ) R := by
      have h := hiso.preimage_closedBall 1 R
      rwa [h1] at h
    have hpre : (rotation a) ⁻¹' (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R)
        = Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R := by
      rw [Set.preimage_inter, e0, e1]
    have hmeas : MeasurableSet (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R) :=
      measurableSet_closedBall.inter measurableSet_closedBall
    have hmp := (rotation a).measurePreserving
    have hcoord : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R)
        = volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) := by
      have hh := hmp.measure_preimage
        (s := Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R) hmeas.nullMeasurableSet
      rw [hpre] at hh
      exact hh.symm
    have hfin1 : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
      rw [Complex.volume_closedBall]; finiteness
    rw [hcoord, overlapArea, ENNReal.ofReal_toReal hfin1]
  -- `window R` and its `u`-translate as products of discs.
  have hwin : window (f := f) R = Set.univ.pi (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
    ext z
    simp only [window, Set.mem_setOf_eq, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  have hwinu : window (f := f) R - {u}
      = Set.univ.pi (fun r : Fin f => Metric.closedBall (-u r) R) := by
    ext z
    constructor
    · rw [Set.mem_sub]
      rintro ⟨x, hx, y, hy, hxy⟩
      rw [Set.mem_singleton_iff] at hy
      subst y
      subst hxy
      simp only [window, Set.mem_setOf_eq] at hx
      simp only [Set.mem_univ_pi, Metric.mem_closedBall]
      intro r
      rw [Complex.dist_eq, Pi.sub_apply]
      have hxx : x r - u r - -u r = x r := by ring
      rw [hxx]; exact hx r
    · intro hz
      simp only [Set.mem_univ_pi, Metric.mem_closedBall] at hz
      rw [Set.mem_sub]
      refine ⟨z + u, ?_, u, Set.mem_singleton u, by ring⟩
      simp only [window, Set.mem_setOf_eq]
      intro r
      have hzr := hz r
      rw [Complex.dist_eq] at hzr
      rw [Pi.add_apply]
      have hzz : z r - -u r = z r + u r := by ring
      rw [hzz] at hzr
      exact hzr
  -- Assemble via Fubini.
  rw [hwinu, hwin, ← Set.pi_inter_distrib, volume_pi, Measure.pi_pi]
  have hfactor : ∀ r : Fin f,
      volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (-u r) R)
        = ENNReal.ofReal (overlapArea R) :=
    fun r => hcoordVol (-u r) (by rw [norm_neg]; exact hU_coord r)
  simp only [hfactor]
  have hnn : (0 : ℝ) ≤ overlapArea R := ENNReal.toReal_nonneg
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hnn]

end MinkowskiLemmas
