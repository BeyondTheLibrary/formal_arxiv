import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.HurwitzGaussianPerturbationSimpleZeroPreservation
import Workspace.ProofLemmas.SublemmaSmallPerturbationDerivOnZeroNbhds
import Workspace.ProofLemmas.SublemmaSmallPerturbationOnZeroNbhds

/-!
# Band-uniform region (b) outer-zero bound for the convolution-width family

This file proves a **band-uniform** version of region (b) of the §6.1 add-near-delta
step.  Region (b), formalised in
`Workspace.ProofLemmas.HurwitzGaussianPerturbationSimpleZeroPreservation`, says:

> For an analytic `g` with `≤ N` (all-simple) zeros, and for every `a_k ≠ 0`, `μ_k`,
> `b < b'`, `δ > 0`, there is a threshold `v₀ > 0` so that for every `v ∈ (0, v₀]`
> the outer region `Icc b b' \ Ioo (μ_k − δ) (μ_k + δ)` contains at most `N` zeros of
> `g x + a_k · N(μ_k, v, x)`.

We want this **for the whole convolution-width family** `gα(c) := fFamU S c`
(`= conv(S.density, c)` for `c > 0`), with a SINGLE threshold `v0b_uniform > 0` valid
simultaneously for every band width `c ∈ [0, c_max]`.

## What is genuinely reusable (the two banked uniform floors)

Region (b)'s per-`g` threshold is `v₀ = min (v_th1, v_th2)` where

* `v_th1` comes from `SublemmaSmallPerturbationDerivOnZeroNbhds` with floor
  `η = ε₁/2`, where `ε₁ = min_j |deriv g (x_j)|` over the zeros `x_j` of `g`;
* `v_th2` comes from `SublemmaSmallPerturbationOnZeroNbhds` with floor `η = g_lb`,
  where `g_lb` is a positive C⁰ lower bound for `|g|` on a compact zero-free set `A`.

Both threshold sub-lemmas are keyed ONLY on `(μ_k, a_k, Kbig, η)`, and the region
`Kbig := Icc (b − δ) (b' + δ) \ Ioo (μ_k − δ/2) (μ_k + δ/2)` is **independent of `c`**.
Both floors are ALREADY PROVEN uniform over the band:

* `Workspace.ProofLemmas.branchDeriv_uniform_lower_bound` gives `ε₁(gα(c)) ≥ ε₁(g̃₀')/2`
  uniformly;
* `Workspace.ProofLemmas.convFamily_C0_floor_on_band` gives `g_lb(gα(c)) ≥ g_lb`
  uniformly on a band-product compact zero-free set.

Hence the two threshold sub-lemmas, fed the uniform floors `ε₁_unif/2` and `g_lb_unif`,
yield a SINGLE band-uniform pair `(v_th1_unif, v_th2_unif)`, and the uniform threshold
`v0b_uniform := min v_th1_unif v_th2_unif` is `> 0`.

## The band-uniform statement

We package the band substrate as hypotheses that the §6.1 substrate already supplies:

* `hgα_analytic c` : `gα(c)` is analytic (from `Prop7AnalyticityOfMixture (heatShift …)`);
* `hgα_zeros c`    : `gα(c)` has `≤ N` zeros (the Hummel–Gidas bound on the band);
* `hgα_simple c`   : every zero of `gα(c)` is simple (from `convSmall_all_zeros_simple`);

together with the two uniform floors, and we conclude a single `v0b_uniform > 0` for the
whole band.

## Status of the proof (route (ii): parametrized region (b))

The two threshold sub-lemmas are applied with the uniform floors ONCE, giving the genuine
band-uniform threshold `v0b_uniform := min v_th1_unif v_th2_unif`.  The per-`c` outer
bound is delivered by the **parametrized** region (b) variant
`HurwitzGaussianPerturbationSimpleZeroPreservation_param`, which takes the floors / region /
thresholds as EXTERNAL inputs and returns the conclusion for every `v ≤ min v_th1 v_th2`.

Because that threshold is built from the `c`-independent uniform floors, the comparison
`v ≤ v0c` that blocked black-box reuse is now a definitional equality: we feed exactly
`v_th1 = v_th1_unif`, `v_th2 = v_th2_unif`, so `v ≤ v0b_uniform = min v_th1_unif v_th2_unif`
discharges the slice bound directly, with NO opaque existential.

The per-`c` zero combinatorics (`hderiv_lb`, the zero-cover, `hgp_R3Local`) live inside the
parametrized variant's body; the caller threads in the band substrate (analyticity, `≤ N`
zeros, all-simple zeros) together with the banked uniform floors, supplied here as the
per-slice floor hypotheses the §6.1 toolbox provides:

* `ε₂fam c` — a per-slice cover radius (`≤ δ/8`, `≤ 1`) with the derivative-continuity fact
  `hderiv_lb_fam` near each zero of `gα(c)` (this is `c`-dependent but reproduces from the
  slice's own C¹ regularity; it does NOT affect the threshold);
* `hε₁_unif_le` — the banked uniform derivative floor `ε₁_unif ≤ |deriv gα(c) x_j|` at the
  zeros (from `branchDeriv_uniform_lower_bound`);
* `hg_lb_unif_spec` — the banked uniform value floor `g_lb_unif ≤ |gα(c) x|` on the
  zero-free part `K \ ⋃_{gα(c) x_j = 0} Ioo (x_j ± ε₂fam c)` (from
  `convFamily_C0_floor_on_band`).
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.ZeroCount

set_option maxHeartbeats 4000000

/-- **Band-uniform region (b) outer-zero bound for the convolution-width family.**

Let `S` be a signed Gaussian combination, `c_max > 0`, `a_k ≠ 0`, `μ_k`, `b < b'`,
`δ > 0`, and `N : ℕ`.  Assume the §6.1 band substrate:

* every band slice `gα(c) = fFamU S c` (`c ∈ [0, c_max]`) is analytic;
* every band slice has `≤ N` zeros;
* every band slice has all-simple zeros.

Then there is a single threshold `v0b_uniform > 0`, **uniform over the entire band**,
such that for every `c ∈ [0, c_max]` and every `v ∈ (0, v0b_uniform]` the outer region
`Icc b b' \ Ioo (μ_k − δ) (μ_k + δ)` contains at most `N` zeros of
`gα(c) x + a_k · N(μ_k, v, x)`.

The uniform threshold is built (constructively, below) from the two banked uniform
floors via the two `c`-independent threshold sub-lemmas. -/
theorem convFamily_uniform_regionB
    (S : SignedGaussianCombination)
    (c_max : ℝ) (hc_max : 0 < c_max)
    (N : ℕ)
    (a_k : ℝ) (hak : a_k ≠ 0) (μ_k : ℝ)
    (b b' : ℝ) (hbb' : b < b')
    (δ : ℝ) (hδ : 0 < δ)
    -- band substrate (supplied by the §6.1 toolbox):
    (hgα_analytic : ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ)
    (hgα_zeros : ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      Workspace.Types.ZeroCount.hasAtMostNZeros (fun x => fFamU S c x) N)
    (hgα_simple : ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      ∀ x : ℝ, fFamU S c x = 0 → deriv (fun y => fFamU S c y) x ≠ 0)
    -- the two banked uniform floors (already proven), supplied as per-slice floor
    -- hypotheses of the form the §6.1 toolbox provides:
    (ε₁_unif : ℝ) (hε₁_unif_pos : 0 < ε₁_unif)
    (g_lb_unif : ℝ) (hg_lb_unif_pos : 0 < g_lb_unif)
    -- a per-slice cover radius (c-dependent; reproduces from each slice's C¹ regularity):
    (ε₂fam : ℝ → ℝ)
    (hε₂fam_pos : ∀ c : ℝ, 0 ≤ c → c ≤ c_max → 0 < ε₂fam c)
    (hε₂fam_le_δ8 : ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ε₂fam c ≤ δ/8)
    (hε₂fam_le_1 : ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ε₂fam c ≤ 1)
    (hderiv_lb_fam : ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      ∀ x_j : ℝ, fFamU S c x_j = 0 →
        ∀ x ∈ Set.Icc (x_j - ε₂fam c) (x_j + ε₂fam c),
          |deriv (fun y => fFamU S c y) x_j| / 2 ≤ |deriv (fun y => fFamU S c y) x|)
    -- banked uniform derivative floor at the zeros (`branchDeriv_uniform_lower_bound`):
    (hε₁_unif_le : ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      ∀ x_j : ℝ, fFamU S c x_j = 0 → ε₁_unif ≤ |deriv (fun y => fFamU S c y) x_j|)
    -- banked uniform value floor on the zero-free part (`convFamily_C0_floor_on_band`):
    (hg_lb_unif_spec : ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      ∀ x ∈ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ)) \
          (⋃ x_j ∈ {y : ℝ | fFamU S c y = 0}, Set.Ioo (x_j - ε₂fam c) (x_j + ε₂fam c)),
        g_lb_unif ≤ |fFamU S c x|) :
    ∃ v0b_uniform : ℝ, 0 < v0b_uniform ∧
      ∀ (c : ℝ), 0 ≤ c → c ≤ c_max →
        ∀ (v : ℝ) (hv : 0 < v), v ≤ v0b_uniform →
          (Workspace.Types.ZeroCount.zeroSet
              (fun x => fFamU S c x +
                a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x)
            ∩ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ))).encard
            ≤ (N : ℕ∞) := by
  -- The `c`-independent outer-perturbation region `Kbig` of region (b).
  set Kbig : Set ℝ := Set.Icc (b - δ) (b' + δ) \ Set.Ioo (μ_k - δ/2) (μ_k + δ/2)
    with hKbig_def
  have hKbig_compact : IsCompact Kbig := (isCompact_Icc).diff isOpen_Ioo
  have hμ_notin_Kbig : μ_k ∉ Kbig := by
    rw [hKbig_def]; intro hc; exact hc.2 ⟨by linarith, by linarith⟩
  -- Threshold from the derivative-decay sub-lemma fed with the UNIFORM `ε₁` floor.
  obtain ⟨v_th1_unif, hv_th1_unif_pos, hv_th1_unif_spec⟩ :=
    SublemmaSmallPerturbationDerivOnZeroNbhds μ_k a_k hak Kbig hKbig_compact hμ_notin_Kbig
      (ε₁_unif/2) (by linarith)
  -- Threshold from the value-decay sub-lemma fed with the UNIFORM `g_lb` floor.
  obtain ⟨v_th2_unif, hv_th2_unif_pos, hv_th2_unif_spec⟩ :=
    SublemmaSmallPerturbationOnZeroNbhds μ_k a_k hak Kbig hKbig_compact hμ_notin_Kbig
      g_lb_unif hg_lb_unif_pos
  -- The genuine band-uniform threshold.
  refine ⟨min v_th1_unif v_th2_unif, lt_min hv_th1_unif_pos hv_th2_unif_pos, ?_⟩
  intro c hc0 hcmax v hv hv_le
  -- Apply the PARAMETRIZED region (b) to the slice `gα(c)` with the uniform floors and the
  -- c-independent thresholds `(v_th1_unif, v_th2_unif)`.  Its conclusion holds for every
  -- `v ≤ min v_th1_unif v_th2_unif = v0b_uniform`, so `v ≤ v0b_uniform` (i.e. `hv_le`)
  -- discharges the slice bound DIRECTLY — no opaque existential.
  exact HurwitzGaussianPerturbationSimpleZeroPreservation_param
    (fun x => fFamU S c x) (hgα_analytic c hc0 hcmax) N
    (hgα_zeros c hc0 hcmax) (hgα_simple c hc0 hcmax)
    b b' hbb' a_k hak μ_k δ hδ
    Kbig hKbig_def
    (ε₂fam c) (hε₂fam_pos c hc0 hcmax) (hε₂fam_le_δ8 c hc0 hcmax) (hε₂fam_le_1 c hc0 hcmax)
    (hderiv_lb_fam c hc0 hcmax)
    ε₁_unif hε₁_unif_pos (hε₁_unif_le c hc0 hcmax)
    g_lb_unif hg_lb_unif_pos (hg_lb_unif_spec c hc0 hcmax)
    v_th1_unif hv_th1_unif_pos hv_th1_unif_spec
    v_th2_unif hv_th2_unif_pos hv_th2_unif_spec
    v hv hv_le

end Workspace.ProofLemmas
