import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.ConvFamilyDiagonalThresholdConcrete
import Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded
import Workspace.ProofLemmas.ConvolveWithGaussianBounded
import Workspace.ProofLemmas.SublemmaSGCDensityIsAnalytic
import Workspace.PriorWork.HummelGidasZeroCount

/-!
# `MainCaseSimpleTransport` — analytic core of the §6.1 main case (`c im ≠ 0`).

Packages the diagonal §6.1 finish for a SIMPLE deconvolution base `S'` together with
its width-`αrec` recovery into a clean count bound, abstracting away the genericity /
coefficient-perturbation linkage (which the caller supplies as `h_rec`/`h_transport`).

Given a simple base `S'` (the perturbed deconvolution preimage `g̃₀'`) with
`≤ 2(k-1)` zeros, somewhere nonzero, nonzero at the near-delta centre `ν`, a nonzero
near-delta coefficient `A`, and:

* `h_rec` : for every small width `v ∈ (0, w_im)`, convolving the diagonal slice
  `conv(S'.density, v) + A·N(ν, v)` at the recovery width `w_im - v` reproduces the
  perturbed target `fp`;
* `h_transport` : the perturbed target has at least as many zeros as the original
  target `f` (`zeroCount f ≤ zeroCount fp`);

then `f` has at most `2k` zeros.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.ZeroCount

set_option maxHeartbeats 4000000

/-- **Analytic core of the §6.1 main case.**  Transports the diagonal near-delta
threshold of a simple base through the recovery convolution to a `≤ 2k` zero count
of the original target. -/
theorem mainCaseSimpleTransport
    (k : ℕ) (hk : 1 ≤ k)
    (S' : SignedGaussianCombination)
    (hS'_simple : ∀ x, S'.density x = 0 → deriv S'.density x ≠ 0)
    (hS'_ne : ∃ x : ℝ, S'.density x ≠ 0)
    (hS'_count : Workspace.Types.ZeroCount.hasAtMostNZeros S'.density (2 * (k - 1)))
    (ν : ℝ) (hS'_ν : S'.density ν ≠ 0)
    (A : ℝ) (hA : A ≠ 0)
    (w_im : ℝ) (hw_im : 0 < w_im)
    (f fp : ℝ → ℝ)
    (hfp_analytic : AnalyticOnNhd ℝ fp Set.univ)
    (h_rec : ∀ (v : ℝ) (hv : 0 < v) (hvlt : v < w_im),
      Workspace.Types.GaussianConvolution.convolveWithGaussian
          (fun x => Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv x
            + A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x)
          (w_im - v) (by linarith)
        = fp)
    (h_transport : zeroCount f ≤ zeroCount fp) :
    Workspace.Types.ZeroCount.hasAtMostNZeros f (2 * k) := by
  -- STEP-1-concrete on the simple base `S'`: a small diagonal width `v₀`.
  obtain ⟨v_diag, hv_diag_pos, hv_diag_spec⟩ :=
    convFamily_diagonal_threshold_concrete S' hS'_simple hS'_ne ν hS'_ν
      (2 * (k - 1)) hS'_count A hA
  -- Pick `v` in `(0, min v_diag (w_im/2)]`, so `0 < v < w_im` and `v ≤ v_diag`.
  set v : ℝ := min v_diag (w_im / 2) with hv_def
  have hv_pos : 0 < v := lt_min hv_diag_pos (by linarith)
  have hv_le_diag : v ≤ v_diag := min_le_left _ _
  have hv_lt_wim : v < w_im := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- The diagonal slice has `≤ 2(k-1)+2 = 2k` zeros (using `fFamU S' v = conv(S'.density, v)`).
  have hslice_fFamU : Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => fFamU S' v x +
        A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x)
      (2 * (k - 1) + 2) := hv_diag_spec v hv_pos hv_le_diag
  -- Rewrite `fFamU S' v = conv(S'.density, v)`.
  have hslice_eq : (fun x => fFamU S' v x +
        A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x)
      = (fun x => Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv_pos x
        + A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x) := by
    funext x; rw [fFamU_eq_convolve S' v hv_pos x]
  rw [hslice_eq] at hslice_fFamU
  -- `2(k-1)+2 = 2k`.
  have h2k : 2 * (k - 1) + 2 = 2 * k := by omega
  rw [h2k] at hslice_fFamU
  -- The diagonal slice function.
  set hfun : ℝ → ℝ :=
    (fun x => Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv_pos x
      + A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x) with hhfun_def
  -- Analyticity of `hfun`: it equals the diagonal slice; but we only need `hfun`'s
  -- recovery target `fp`'s analyticity for Hummel–Gidas, supplied as `hfp_analytic`.
  -- Hummel–Gidas applied to `hfun` requires `hfun` analytic.  We get it from `h_rec`:
  -- `conv(hfun, w_im - v) = fp`, but Hummel–Gidas needs `hfun` analytic directly.
  -- `hfun` is a signed Gaussian mixture (conv of a mixture + a Gaussian), hence analytic.
  have hconv_analytic : AnalyticOnNhd ℝ
      (Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv_pos) Set.univ := by
    have heq : Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv_pos
        = (fun x => fFamU S' v x) := by
      funext x; rw [fFamU_eq_convolve S' v hv_pos x]
    rw [heq]; exact gFam_analytic_pos S' v hv_pos
  have hNimv_analytic : AnalyticOnNhd ℝ
      (fun x => A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x) Set.univ := by
    refine analyticOnNhd_const.mul ?_
    have hdfun : (fun x => Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x)
        = (fun x => (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - ν) ^ 2 / (2 * v))) := by
      funext y; rw [GaussianPDF.density_eq]
    simp only [hdfun]
    refine analyticOnNhd_const.mul ?_
    refine analyticOnNhd_rexp.comp ?_ (fun _ _ => Set.mem_univ _)
    apply AnalyticOnNhd.div_const
    apply AnalyticOnNhd.neg
    apply AnalyticOnNhd.pow
    exact analyticOnNhd_id.sub analyticOnNhd_const
  have hhfun_analytic : AnalyticOnNhd ℝ hfun Set.univ := by
    rw [hhfun_def]
    exact fun x hx => (hconv_analytic x hx).add (hNimv_analytic x hx)
  -- Boundedness of `hfun`: convolution term + scaled-Gaussian term, each bounded.
  have hf_bdd : ∃ C : ℝ, ∀ x : ℝ, |hfun x| ≤ C := by
    -- (1) The convolution term `conv(S'.density, v)` is bounded.
    have hS'_cont : Continuous S'.density :=
      (Workspace.ProofLemmas.SublemmaSGCDensityIsAnalytic S').continuous
    obtain ⟨C1, hC1⟩ := Workspace.ProofLemmas.ConvolveWithGaussianBounded
      S'.density hS'_cont (Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded S')
      v hv_pos
    -- (2) The scaled-Gaussian term `A * N(ν, v, x)` is bounded.  Express it as the
    -- density of the singleton signed Gaussian combination `[(A, ⟨ν, v, hv_pos⟩)]`.
    obtain ⟨C2, hC2⟩ := Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded
      (⟨[(A, ⟨ν, v, hv_pos⟩)]⟩ : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    have hC2' : ∀ x : ℝ,
        |A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x| ≤ C2 := by
      intro x
      have hden := hC2 x
      rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq] at hden
      simpa using hden
    -- (3) Combine.
    refine ⟨C1 + C2, fun x => ?_⟩
    rw [hhfun_def]
    calc |Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv_pos x
            + A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x|
        ≤ |Workspace.Types.GaussianConvolution.convolveWithGaussian S'.density v hv_pos x|
            + |A * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv_pos⟩ x| :=
          abs_add_le _ _
      _ ≤ C1 + C2 := add_le_add (hC1 x) (hC2' x)
  -- Hummel–Gidas on `hfun` at width `w_im - v`: `conv(hfun, w_im - v)` has `≤ 2k` zeros.
  have h_conv_bound : Workspace.Types.ZeroCount.hasAtMostNZeros
      (Workspace.Types.GaussianConvolution.convolveWithGaussian hfun (w_im - v) (by linarith))
      (2 * k) :=
    Workspace.PriorWork.HummelGidasZeroCount hfun hhfun_analytic hf_bdd (2 * k) hslice_fFamU
      (w_im - v) (by linarith)
  -- Recovery: `conv(hfun, w_im - v) = fp`.
  have hrec_v := h_rec v hv_pos hv_lt_wim
  rw [hrec_v] at h_conv_bound
  -- Transport `count f ≤ count fp ≤ 2k`.
  rw [Workspace.Types.ZeroCount.hasAtMostNZeros]
  rw [Workspace.Types.ZeroCount.hasAtMostNZeros] at h_conv_bound
  exact le_trans h_transport h_conv_bound

end Workspace.ProofLemmas
