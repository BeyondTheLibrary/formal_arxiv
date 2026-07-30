import Mathlib
import Workspace.Types.MinkowskiWindow

open scoped NumberField
open MeasureTheory
open Workspace.Types.MinkowskiWindow

set_option maxHeartbeats 800000

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaPacking
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 0 < R) (a : Fin f → ℂ)
    (hsep : ∀ x ∈ Xset sel DD R a, ∀ x' ∈ Xset sel DD R a, x ≠ x' →
      (DD : ℝ)⁻¹ ≤ ‖x - x'‖) :
    (Xset sel DD R a).Finite ∧
      (Ncount sel DD R a : ℝ) ≤ (1 + 2 * R * (DD : ℝ)) ^ (2 * f) := by
  have hDD0 : (0 : ℝ) < (DD : ℝ) := by exact_mod_cast hDD
  set ρ : ℝ := (DD : ℝ)⁻¹ / 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  -- Volume constants.
  set V : ENNReal := (ENNReal.ofReal ρ ^ 2 * (NNReal.pi : ENNReal)) ^ f with hV_def
  set Vbig : ENNReal := (ENNReal.ofReal (R + ρ) ^ 2 * (NNReal.pi : ENNReal)) ^ f with hVbig_def
  have hV_ne : V ≠ ⊤ := by rw [hV_def]; finiteness
  have hVbig_ne : Vbig ≠ ⊤ := by rw [hVbig_def]; finiteness
  have hVtoReal : V.toReal = (ρ ^ 2 * Real.pi) ^ f := by
    rw [hV_def, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hρ.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hVbigtoReal : Vbig.toReal = ((R + ρ) ^ 2 * Real.pi) ^ f := by
    rw [hVbig_def, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ R + ρ), ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hVtoReal_pos : 0 < V.toReal := by rw [hVtoReal]; positivity
  -- Volume of a small ball (constant, translation-invariant).
  have hballvol : ∀ x : Fin f → ℂ, volume (Metric.ball x ρ) = V := by
    intro x
    rw [ball_pi x hρ, volume_pi, Measure.pi_pi]
    simp only [Complex.volume_ball]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hV_def]
  -- Volume of the enlarged window ball.
  have hbigvol : volume (Metric.ball (0 : Fin f → ℂ) (R + ρ)) = Vbig := by
    rw [ball_pi (0 : Fin f → ℂ) (by positivity : (0:ℝ) < R + ρ), volume_pi, Measure.pi_pi]
    simp only [Complex.volume_ball]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hVbig_def]
  -- The core packing bound on every finite subset.
  have hbound : ∀ S : Finset (Fin f → ℂ), (↑S ⊆ Xset sel DD R a) →
      (S.card : ℝ) ≤ (1 + 2 * R * (DD : ℝ)) ^ (2 * f) := by
    intro S hSsub
    -- Disjointness of the balls of radius ρ.
    have hdisj : (↑S : Set (Fin f → ℂ)).PairwiseDisjoint (fun x => Metric.ball x ρ) := by
      intro x hx y hy hxy
      apply Metric.ball_disjoint_ball
      rw [dist_eq_norm]
      have hs := hsep x (hSsub hx) y (hSsub hy) hxy
      have hρsum : ρ + ρ = (DD : ℝ)⁻¹ := by rw [hρ_def]; ring
      rw [hρsum]; exact hs
    have hmeas : ∀ b ∈ S, MeasurableSet (Metric.ball b ρ) := fun b _ => measurableSet_ball
    -- Containment in the enlarged window ball.
    have hsub : (⋃ x ∈ S, Metric.ball x ρ) ⊆ Metric.ball (0 : Fin f → ℂ) (R + ρ) := by
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨x, hxS, hyx⟩ := hy
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball, dist_eq_norm] at hyx
      have hxwin : ‖x‖ ≤ R := by
        have hxX : x ∈ Xset sel DD R a := hSsub hxS
        rw [pi_norm_le_iff_of_nonneg hR.le]
        intro i
        exact hxX.2 i
      have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
        have := norm_add_le x (y - x)
        simpa using this
      linarith
    -- Packing inequality in ENNReal.
    have hpack : (S.card : ENNReal) * V ≤ Vbig := by
      calc (S.card : ENNReal) * V
          = ∑ _x ∈ S, V := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ x ∈ S, volume (Metric.ball x ρ) := by
            exact (Finset.sum_congr rfl (fun x _ => (hballvol x).symm))
        _ = volume (⋃ x ∈ S, Metric.ball x ρ) := (measure_biUnion_finset hdisj hmeas).symm
        _ ≤ volume (Metric.ball (0 : Fin f → ℂ) (R + ρ)) := measure_mono hsub
        _ = Vbig := hbigvol
    -- Convert to reals.
    have hpackR : (S.card : ℝ) * V.toReal ≤ Vbig.toReal := by
      have hle : ((S.card : ENNReal) * V).toReal ≤ Vbig.toReal :=
        (ENNReal.toReal_le_toReal (by finiteness) hVbig_ne).mpr hpack
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle
    -- Ratio identity.
    have hkey : (1 + 2 * R * (DD : ℝ)) * ρ = R + ρ := by
      rw [hρ_def]; field_simp; ring
    have hratio : Vbig.toReal = (1 + 2 * R * (DD : ℝ)) ^ (2 * f) * V.toReal := by
      rw [hVbigtoReal, hVtoReal, pow_mul, ← mul_pow]
      congr 1
      have hsq : ((1 + 2 * R * (DD : ℝ)) ^ 2) * ρ ^ 2 = (R + ρ) ^ 2 := by
        rw [← mul_pow, hkey]
      rw [← hsq]; ring
    rw [hratio] at hpackR
    exact le_of_mul_le_mul_right hpackR hVtoReal_pos
  -- Finiteness from the uniform bound.
  have hfin : (Xset sel DD R a).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨S, hSsub, hScard⟩ :=
      hinf.exists_subset_card_eq (⌈(1 + 2 * R * (DD : ℝ)) ^ (2 * f)⌉₊ + 1)
    have hb := hbound S hSsub
    rw [hScard] at hb
    have hceil : (1 + 2 * R * (DD : ℝ)) ^ (2 * f) ≤ (⌈(1 + 2 * R * (DD : ℝ)) ^ (2 * f)⌉₊ : ℝ) :=
      Nat.le_ceil _
    push_cast at hb
    linarith
  refine ⟨hfin, ?_⟩
  -- Cardinality bound.
  have hcard_eq : Ncount sel DD R a = hfin.toFinset.card := by
    rw [Ncount, Set.ncard_eq_toFinset_card _ hfin]
  rw [hcard_eq]
  exact hbound hfin.toFinset (Set.Finite.coe_toFinset hfin).subset

end MinkowskiLemmas
