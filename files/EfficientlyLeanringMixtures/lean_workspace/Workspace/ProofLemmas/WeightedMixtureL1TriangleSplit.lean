import Mathlib
import Workspace.Types.L1AndTVDistance

namespace Workspace.ProofLemmas

open MeasureTheory

/-- Helper: L1Norm is non-negative. -/
private lemma L1Norm_nonneg' (f : ℝ → ℝ) :
    0 ≤ Workspace.Types.L1AndTVDistance.L1Norm f := by
  unfold Workspace.Types.L1AndTVDistance.L1Norm
  exact integral_nonneg (fun x => abs_nonneg _)

/-- Helper: L1Norm of a constant multiple. -/
private lemma L1Norm_const_mul' (c : ℝ) (f : ℝ → ℝ) :
    Workspace.Types.L1AndTVDistance.L1Norm (fun x => c * f x)
      = |c| * Workspace.Types.L1AndTVDistance.L1Norm f := by
  unfold Workspace.Types.L1AndTVDistance.L1Norm
  simp only [abs_mul]
  rw [← integral_const_mul]

/-- Helper: triangle inequality for L1Norm. -/
private lemma L1Norm_add_le' (f g : ℝ → ℝ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Workspace.Types.L1AndTVDistance.L1Norm (fun x => f x + g x)
      ≤ Workspace.Types.L1AndTVDistance.L1Norm f
        + Workspace.Types.L1AndTVDistance.L1Norm g := by
  unfold Workspace.Types.L1AndTVDistance.L1Norm
  have h1 : Integrable (fun x => |f x|) volume := hf.abs
  have h2 : Integrable (fun x => |g x|) volume := hg.abs
  rw [← integral_add h1 h2]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun x => abs_nonneg _)
  · exact h1.add h2
  · exact Filter.Eventually.of_forall (fun x => abs_add_le (f x) (g x))

/-- Reverse triangle: L1Norm f ≤ L1Norm (f+g) + L1Norm g. -/
private lemma L1Norm_rev_tri' (f g : ℝ → ℝ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Workspace.Types.L1AndTVDistance.L1Norm f
      ≤ Workspace.Types.L1AndTVDistance.L1Norm (fun x => f x + g x)
        + Workspace.Types.L1AndTVDistance.L1Norm g := by
  have h1 := L1Norm_add_le' (fun x => f x + g x) (fun x => -g x)
    (hf.add hg) hg.neg
  have heq : (fun x => (f x + g x) + (-g x)) = f := by
    funext x; ring
  rw [heq] at h1
  have hneg : Workspace.Types.L1AndTVDistance.L1Norm (fun x => -g x)
      = Workspace.Types.L1AndTVDistance.L1Norm g := by
    unfold Workspace.Types.L1AndTVDistance.L1Norm
    simp [abs_neg]
  rw [hneg] at h1
  exact h1

theorem WeightedMixtureL1TriangleSplit
    (w₁ w₂ w'₁ w'₂ : ℝ) (G₁ G₂ G'₁ G'₂ : ℝ → ℝ)
    (hG₁ : MeasureTheory.Integrable G₁ MeasureTheory.volume)
    (hG₂ : MeasureTheory.Integrable G₂ MeasureTheory.volume)
    (hG'₁ : MeasureTheory.Integrable G'₁ MeasureTheory.volume)
    (hG'₂ : MeasureTheory.Integrable G'₂ MeasureTheory.volume)
    (hw₁ : 0 ≤ w₁) :
    Workspace.Types.L1AndTVDistance.L1Norm
        (fun x => w₂ * G₂ x - w'₂ * G'₂ x)
      - w₁ * Workspace.Types.L1AndTVDistance.L1Norm (fun x => G₁ x - G'₁ x)
      - |w₁ - w'₁| *
          (Workspace.Types.L1AndTVDistance.L1Norm G'₁
            + Workspace.Types.L1AndTVDistance.L1Norm G'₂)
      ≤ Workspace.Types.L1AndTVDistance.L1Norm
          (fun x => (w₁ * G₁ x + w₂ * G₂ x) - (w'₁ * G'₁ x + w'₂ * G'₂ x)) := by
  -- Set abbreviations
  set A := fun x => w₂ * G₂ x - w'₂ * G'₂ x with hA
  set B := fun x => w₁ * G₁ x - w'₁ * G'₁ x with hB
  set D := fun x => G₁ x - G'₁ x with hD
  -- The full sum = A + B
  have hsum_eq : (fun x => (w₁ * G₁ x + w₂ * G₂ x) - (w'₁ * G'₁ x + w'₂ * G'₂ x))
      = (fun x => A x + B x) := by
    funext x; simp [hA, hB]; ring
  rw [hsum_eq]
  -- Decompose B = w₁ * D + (w₁ - w'₁) * G'₁
  have hB_eq : B = (fun x => w₁ * D x + (w₁ - w'₁) * G'₁ x) := by
    funext x; simp [hB, hD]; ring
  -- Integrability of various pieces
  have hA_int : Integrable A volume := by
    apply Integrable.sub
    · exact hG₂.const_mul w₂
    · exact hG'₂.const_mul w'₂
  have hD_int : Integrable D volume := hG₁.sub hG'₁
  have hB_int : Integrable B volume := by
    apply Integrable.sub
    · exact hG₁.const_mul w₁
    · exact hG'₁.const_mul w'₁
  -- Reverse triangle: L1Norm A ≤ L1Norm (A + B) + L1Norm B
  have hrev := L1Norm_rev_tri' A B hA_int hB_int
  -- Triangle bound on B: L1Norm B ≤ |w₁| * L1Norm D + |w₁ - w'₁| * L1Norm G'₁
  have hBbound : Workspace.Types.L1AndTVDistance.L1Norm B
      ≤ |w₁| * Workspace.Types.L1AndTVDistance.L1Norm D
        + |w₁ - w'₁| * Workspace.Types.L1AndTVDistance.L1Norm G'₁ := by
    rw [hB_eq]
    have h := L1Norm_add_le' (fun x => w₁ * D x) (fun x => (w₁ - w'₁) * G'₁ x)
      (hD_int.const_mul w₁) (hG'₁.const_mul (w₁ - w'₁))
    rw [L1Norm_const_mul' w₁ D, L1Norm_const_mul' (w₁ - w'₁) G'₁] at h
    exact h
  -- Using hw₁ : 0 ≤ w₁, we have |w₁| = w₁.
  have habs_w₁ : |w₁| = w₁ := abs_of_nonneg hw₁
  rw [habs_w₁] at hBbound
  -- Non-negativity facts
  have hD_nonneg := L1Norm_nonneg' D
  have hG'₁_nonneg := L1Norm_nonneg' G'₁
  have hG'₂_nonneg := L1Norm_nonneg' G'₂
  have habs_diff_nonneg : 0 ≤ |w₁ - w'₁| := abs_nonneg _
  -- Combine: L1Norm A ≤ L1Norm(A+B) + w₁ * L1Norm D + |w₁-w'₁| * L1Norm G'₁
  --                  ≤ L1Norm(A+B) + w₁ * L1Norm D + |w₁-w'₁| * (L1Norm G'₁ + L1Norm G'₂)
  nlinarith [hrev, hBbound, hD_nonneg, hG'₁_nonneg, hG'₂_nonneg,
             habs_diff_nonneg,
             mul_nonneg habs_diff_nonneg hG'₂_nonneg]

end Workspace.ProofLemmas
