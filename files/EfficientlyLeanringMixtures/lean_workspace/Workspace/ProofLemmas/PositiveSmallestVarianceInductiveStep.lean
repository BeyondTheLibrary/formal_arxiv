import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.MixtureDeconvolution
import Workspace.ProofLemmas.FormalToNormalizedBridge
import Workspace.ProofLemmas.FormalGaussianNontriviality
import Workspace.ProofLemmas.FormalGaussianTailEnvelope
import Workspace.ProofLemmas.SublemmaAbstractFormalGaussianAnalytic
import Workspace.ProofLemmas.Prop7AddGaussianAddsAtMostTwoZeros
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.Prop7ConvolutionRecoversOriginalDensity
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.MainCaseSimpleTransport
import Workspace.ProofLemmas.BareMainCaseDualGenericity
import Workspace.ProofLemmas.FirstReductionSimpleZeros
import Workspace.ProofLemmas.FirstReductionCountNonDecrease
import Workspace.ProofLemmas.SublemmaGenericSimpleZeros
import Workspace.ProofLemmas.FinitenessOfSignedGaussianZeros
import Workspace.PriorWork.HummelGidasZeroCount
import Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded

/-!
# PositiveSmallestVarianceInductiveStep

Steps 1–7 assembled (Moitra–Valiant §6.1) — the inductive step when the smallest
variance is strictly positive (the detailed proof's `PositiveVarianceCaseComplete`).

Fix `k ≥ 1` and assume the bare-exponential induction hypothesis: every
`a' μ' τ' : Fin k → ℝ` with `τ' i ≠ 0` for all `i`, `τ'` pairwise distinct, and
some `a' i ≠ 0` has at most `2(k-1)` zeros of
`x ↦ Σ_{i ∈ Fin k} a' i · exp(-(x - μ' i)² / (2 · τ' i))`.

Let `a μ τ : Fin (k+1) → ℝ` with `τ` pairwise distinct, all `τ i ≠ 0`, some
`a i ≠ 0`, and ALL `τ i > 0` (every variance strictly positive). Then
`x ↦ Σ_{i ∈ Fin (k+1)} a i · exp(-(x - μ i)² / (2 · τ i))` has at most `2k`
zeros.

## Assembly route (proof_detailed.md, Steps 1–7)

Outer reduction (Step 7, this file, fully wired):

* Build the normalized `(k+1)`-component `SignedGaussianCombination` `S_f` whose
  density equals the target `f` (`FormalToNormalizedBridge`, all variances
  positive).
* Pick `β` with `0 < β < min_i τ_sq_i`.  The deconvolved combination
  `hα := (deconvSigned S_f β).density` shifts every variance DOWN by `β`,
  keeping the (normalized) coefficients.  By
  `Prop7ConvolutionRecoversOriginalDensity` (with the deconvolution shift and
  the convolution width both equal to `β`),
  `convolveWithGaussian hα β = S_f.density = f` pointwise.
* `hα` is analytic (`Prop7AnalyticityOfMixture`).  Granting the inner bound
  `hasAtMostNZeros hα (2k)`, `HummelGidasZeroCount` (Theorem 8) gives
  `hasAtMostNZeros (convolveWithGaussian hα β) (2k) = hasAtMostNZeros f (2k)`.

Inner bound (Steps 1–6, packaged as `innerHAlphaBound`):

* `hα` has one component of small variance `β` (the smallest-variance component,
  shifted to `τ_sq_{i_min} − β = σ_k² − β`, wait — in the deconvolved picture the
  smallest becomes the *narrowest*); separate it off as a near-delta, bound the
  remaining `k`-component combination by the IH (≤ 2(k−1)), apply
  `Prop7AddGaussianAddsAtMostTwoZeros` (+2) and `AnalyticIFTZeroBranchTracking`
  to raise the width parameter, giving ≤ 2k.

The inner bound is the genuinely heavy analytic assembly (Steps 1–6).  It is
organised in two layers:

* `innerHAlphaBound` — converts the abstract `SignedGaussianCombination` to the
  bare-exponential `Fin (k+1)` model and re-derives its side conditions
  (positivity, distinctness, nonzero coefficient, nontriviality).  This layer is
  fully proven and reduces the bound to `bareModelSixStepBound`.
* `bareModelSixStepBound` — the §6.1 argument in the bare model, realized with TWO
  POSITIVE-width Gaussian convolutions (`αp = w im / 2`).  Fully proven: Step 1
  (smallest-variance split), the `c im = 0` sub-case (IH on the rest), Step 3 (the
  IH `≤ 2(k-1)` bound on the proper deconvolution pre-image `g̃₀`, plus its
  analyticity and tail envelope), Step 5a (`g_α := conv(g̃₀, αp)` has `≤ 2(k-1)`
  zeros by HummelGidas at positive width, and is analytic), and Step 7 (the exact,
  normalization-correct recovery `conv(g_α + A·N(ν im, αp), αp) = f` via the heat
  semigroup, then HummelGidas again).  A SINGLE precise `sorry` remains for Step 5b
  (`hh_bound`): the add-near-delta `+2` step needs SIMPLE zeros (and a transported
  tail envelope) of the *convolved* family `g_α`, which no workspace lemma supplies.
-/

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open Workspace.Types.ZeroCount
open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.MixtureDeconvolution

/-- **Bare-exponential core of Steps 1–6 (Moitra–Valiant §6.1).**

This is the inner bound *expressed in the bare-exponential `Fin (k+1)` model* —
the model used by the IH and by the formal-Gaussian black boxes
`FormalGaussianTailEnvelope`, `FirstReductionSimpleZeros`,
`Prop7AddGaussianAddsAtMostTwoZeros`, `SublemmaZeroStructureContinuityInVariance`.

Given coefficients `c`, means `ν`, strictly-positive pairwise-distinct variances
`w` on `Fin (k+1)`, with some `c i ≠ 0` and the sum not identically zero, the
function `x ↦ Σ_i c i · exp(-(x-ν i)²/(2 w i))` has at most `2k` distinct real
zeros.

The proof realizes Steps 1–7 with TWO POSITIVE-width Gaussian convolutions
(no negative-variance object ever appears):

* **Step 1** — pick the smallest-variance index `im` (`Finset.exists_min_image`)
  and split `f = c im·exp(-(·-ν im)²/(2·w im)) + (rest)`.
* `c im = 0` sub-case — `f` is the `k`-component rest at the actual variances,
  bounded by the IH (`≤ 2(k-1) ≤ 2k`).  Fully proven.
* **Step 3** — the PROPER width-`w im` deconvolution pre-image `g̃₀` of the bare
  rest (variances `w(succAbove i) − w im > 0`, bare coefficients rescaled by
  `√(2π·w(succAbove i))/√(2π·(w(succAbove i)−w im))` so that the heat flow
  restores the bare rest exactly).  IH ⇒ `≤ 2(k-1)` zeros; analytic; tail
  envelope (`hg0_bound`, `hg0_analytic`, `hg0_tail`).  Fully proven.
* **Step 5a** — `g_α := conv(g̃₀, αp)`, `αp := w im / 2 > 0`.  HummelGidas
  (POSITIVE width) ⇒ `g_α` has `≤ 2(k-1)` zeros and is analytic (`hgα_bound`,
  `hgα_analytic`).  Fully proven.
* **Step 5b** — add the last Gaussian as a near-delta of width `αp`:
  `h := g_α + A·N(ν im, αp)`, `A := c im·√(2π·w im) ≠ 0`, giving `≤ 2k` zeros.
  This is the ONE remaining analytic input (`Prop7AddGaussianAddsAtMostTwoZeros`
  needs SIMPLE zeros + a tail envelope of the *convolved* `g_α`); see the
  `hh_bound` comment for the precise three missing facts.  The single `sorry`.
* **Step 7** — recover `f = conv(h, αp)` (a SECOND positive-width convolution;
  `heat_semigroup_density` ⇒ rest variances `wg i + 2αp = w(succAbove i)`, last
  `2αp = w im`; normalization-correct, `h_recover`), then HummelGidas again ⇒
  `f` has `≤ 2k` zeros.  Fully proven.

The single `sorry` is `hh_bound` (Step 5b); everything else is proven.  The earlier
"irreducible negative-variance crossing" claim was a convention error: with the
proper deconvolution pre-image `g̃₀` and `αp = w im / 2` both convolutions use the
positive width `αp` and both endpoints are honest positive-variance combinations. -/
private theorem bareModelSixStepBound
    (k : ℕ) (hk : 1 ≤ k)
    (IH : ∀ (a' : Fin k → ℝ)
            (μ' : Fin k → ℝ)
            (τ_sq' : Fin k → ℝ),
          (∀ i : Fin k, 0 < τ_sq' i) →
          (∀ i j : Fin k, i ≠ j → τ_sq' i ≠ τ_sq' j) →
          (∃ i : Fin k, a' i ≠ 0) →
          Workspace.Types.ZeroCount.hasAtMostNZeros
            (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => a' i * Real.exp (-(x - μ' i)^2 / (2 * τ_sq' i))))
            (2 * (k - 1)))
    (c : Fin (k + 1) → ℝ)
    (ν : Fin (k + 1) → ℝ)
    (w : Fin (k + 1) → ℝ)
    (hw_pos : ∀ i : Fin (k + 1), 0 < w i)
    (hw_distinct : ∀ i j : Fin (k + 1), i ≠ j → w i ≠ w j)
    (hc_nonzero : ∃ i : Fin (k + 1), c i ≠ 0)
    (h_nontrivial : ∃ x : ℝ,
      (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))) ≠ 0) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))))
      (2 * k) := by
  classical
  -- ===== Step 1: identify the smallest-variance index and split it off. =====
  obtain ⟨im, _, him⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (k + 1))) w Finset.univ_nonempty
  -- `him : ∀ j, w im ≤ w j` — the index `im` carries the minimal variance `σ_k²`.
  have him_pos : 0 < w im := hw_pos im
  -- Pointwise split: smallest-variance term + the remaining `k` components.
  have hsplit : ∀ x : ℝ,
      (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))
      = c im * Real.exp (-(x - ν im)^2 / (2 * w im))
        + (Finset.univ : Finset (Fin k)).sum
          (fun i => c (im.succAbove i)
            * Real.exp (-(x - ν (im.succAbove i))^2 / (2 * w (im.succAbove i)))) := by
    intro x
    exact Fin.sum_univ_succAbove
      (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))) im
  -- The remaining `k` components carry strictly LARGER variances than `w im`.
  have hrem_larger : ∀ i : Fin k, w im < w (im.succAbove i) := by
    intro i
    have hne : im.succAbove i ≠ im := Fin.succAbove_ne im i
    have hle : w im ≤ w (im.succAbove i) := him _ (Finset.mem_univ _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd h.symm (hw_distinct _ _ hne)
  -- ===== Case split on whether any remaining coefficient is nonzero. =====
  by_cases hrem_coeff : ∃ i : Fin k, c (im.succAbove i) ≠ 0
  · -- Main case: a remaining component is nonzero.
    -- Step 3: the variance-shifted `k`-component combination
    --   g₀(x) = Σ_{i<k} c(im.succAbove i)·exp(-(·-ν(...))²/(2·(w(...)-w im)))
    -- has ≤ 2(k-1) zeros by the induction hypothesis.
    -- The shifted variances `w(im.succAbove i) - w im` are pairwise distinct
    -- and strictly positive.
    have hrem_distinct : ∀ i j : Fin k, i ≠ j →
        w (im.succAbove i) - w im ≠ w (im.succAbove j) - w im := by
      intro i j hij
      have hne : im.succAbove i ≠ im.succAbove j := by
        intro h; exact hij (im.succAbove_right_injective h)
      have := hw_distinct _ _ hne
      intro heq; apply this; linarith
    have hrem_pos : ∀ i : Fin k, 0 < w (im.succAbove i) - w im := by
      intro i; have := hrem_larger i; linarith
    -- ===== Step 3: the PROPER deconvolution pre-image g̃₀ of the rest of f. =====
    -- Convolution preserves NORMALIZED (probability) coefficients, not bare
    -- exponential coefficients.  So the function whose width-`w im` convolution
    -- reproduces the bare rest of `f` (`Σ c(succAbove i)·exp(-(·)²/(2·w(succAbove i)))`)
    -- is NOT the naive bare-coefficient shift, but the family with the SAME bare
    -- means / shifted variances `w(succAbove i) − w im` and bare coefficients
    --   `cg i := c(succAbove i)·√(2π·w(succAbove i)) / √(2π·(w(succAbove i)−w im))`.
    -- (Its width-`w im` heat flow restores the normalization `√(2π·w(succAbove i))`
    -- and the bare coefficient `c(succAbove i)`.)  The IH applies to g̃₀ for ANY
    -- coefficient vector, so the `√`-rescaled coefficients are fine.
    set cg : Fin k → ℝ := fun i =>
      c (im.succAbove i) * Real.sqrt (2 * Real.pi * w (im.succAbove i))
        / Real.sqrt (2 * Real.pi * (w (im.succAbove i) - w im)) with hcg_def
    set νg : Fin k → ℝ := fun i => ν (im.succAbove i) with hνg_def
    set wg : Fin k → ℝ := fun i => w (im.succAbove i) - w im with hwg_def
    -- A nonzero rest coefficient gives a nonzero `cg`.
    have hcg_nonzero : ∃ i : Fin k, cg i ≠ 0 := by
      obtain ⟨i, hi⟩ := hrem_coeff
      refine ⟨i, ?_⟩
      rw [hcg_def]; simp only
      have h1 : Real.sqrt (2 * Real.pi * w (im.succAbove i)) ≠ 0 := by
        apply ne_of_gt; apply Real.sqrt_pos.mpr; have := hw_pos (im.succAbove i); positivity
      have h2 : Real.sqrt (2 * Real.pi * (w (im.succAbove i) - w im)) ≠ 0 := by
        apply ne_of_gt; apply Real.sqrt_pos.mpr; have := hrem_pos i; positivity
      exact div_ne_zero (mul_ne_zero hi h1) h2
    -- g̃₀ has ≤ 2(k-1) zeros by the IH (any coefficients, distinct positive vars).
    have hg0_bound :
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => (Finset.univ : Finset (Fin k)).sum
            (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))) (2 * (k - 1)) := by
      apply IH cg νg wg
      · intro i; rw [hwg_def]; exact hrem_pos i
      · intro i j hij; rw [hwg_def]; exact hrem_distinct i j hij
      · exact hcg_nonzero
    -- g̃₀ is real-analytic.
    have hg0_analytic :
        AnalyticOnNhd ℝ
          (fun x => (Finset.univ : Finset (Fin k)).sum
            (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))) Set.univ :=
      abstract_formal_gaussian_analytic k cg νg wg
        (fun i => by rw [hwg_def]; exact ne_of_gt (hrem_pos i))
    -- g̃₀ admits the Gaussian tail envelope consumed by Step 5.
    have hg0_tail :
        ∃ (b b' a a' s s' : ℝ),
          b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
          (∀ x : ℝ, x < b →
            ((Finset.univ : Finset (Fin k)).sum
                (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))).sign = a.sign ∧
            |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x ^ 2 / (2 * s)) <
              |(Finset.univ : Finset (Fin k)).sum
                (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))|) ∧
          (∀ x : ℝ, x > b' →
            ((Finset.univ : Finset (Fin k)).sum
                (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))).sign = a'.sign ∧
            |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x ^ 2 / (2 * s')) <
              |(Finset.univ : Finset (Fin k)).sum
                (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))|) :=
      FormalGaussianTailEnvelope k cg νg wg
        (fun i => by rw [hwg_def]; exact hrem_pos i)
        (fun i j hij => by rw [hwg_def]; exact hrem_distinct i j hij)
        hcg_nonzero
    -- ===== Steps 5–7 via TWO POSITIVE-WIDTH Gaussian convolutions. =====
    --
    -- The prior "irreducible negative-variance crossing" diagnosis was a
    -- convention error.  The variance-shifted family g₀ (variances
    -- `w(succAbove i) − w im = σ_i² − σ_min² > 0`) is a GAUSSIAN CONVOLUTION
    -- pre-image of the rest of `f`, so the whole recovery is carried out with
    -- POSITIVE widths only.  Pick `αp := w im / 2`, so `0 < αp` and
    -- `2·αp = w im` (the smallest variance).  Then:
    --   * g_α := convolveWithGaussian g₀ αp  has ≤ 2(k-1) zeros by HummelGidas
    --     (POSITIVE width αp); g_α is analytic (a signed Gaussian mixture).
    --   * h := g_α + A·N(ν im, αp)  has ≤ 2k zeros by the add-near-delta `+2`
    --     step (`Prop7AddGaussianAddsAtMostTwoZeros`), `A := c im·√(2π·w im) ≠ 0`.
    --   * convolveWithGaussian h αp = f  (a SECOND positive-width convolution:
    --     rest variances `(σ_i²−σ_min²+αp)+αp = σ_i²`, last `αp+αp = w im`),
    --     so HummelGidas again gives  f ≤ 2k.
    -- All widths are `αp = w im / 2 > 0`; no negative-variance object appears.
    classical
    -- The g̃₀ function (matches `hg0_bound`/`hg0_analytic`/`hg0_tail`).
    set g0 : ℝ → ℝ :=
      (fun x => (Finset.univ : Finset (Fin k)).sum
        (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))) with hg0_def
    -- ===== WIDTH DECOUPLING (the §6.1 finish). =====
    -- The earlier route PINNED the add-Gaussian/convolution width and the recovery
    -- width to be EQUAL (`αp = w im / 2`, `2·αp = w im`).  That is too rigid: the
    -- simple-zeros input `convSmall_all_zeros_simple` and the
    -- `Prop7AddGaussianAddsAtMostTwoZeros` threshold `v₀` both need the width SMALL,
    -- but it was pinned to `w im / 2`.  DECOUPLE the two widths:
    --   * add-Gaussian / convolution width:  a FREE small `v` with `0 < v < w im`;
    --   * recovery width:  `w im − v` (positive since `v < w im`).
    -- The convolution semigroup keeps recovery EXACT:
    --   conv(conv(g̃₀, v), (w im − v)) = conv(g̃₀, w im)   (variances
    --     (w_i − w im) + v + (w im − v) = w_i), and the bump
    --   N(ν im, v) conv N(0, w im − v) = N(ν im, w im).
    -- So `conv(h, w im − v) = f` with `h = conv(g̃₀, v) + A·N(ν im, v)` for ANY small v.
    -- Normalize g₀ to a signed Gaussian combination S_g0 with S_g0.density = g0.
    obtain ⟨S_g0, hS_g0_comp, hS_g0_density, _, _⟩ :=
      FormalToNormalizedBridge k cg νg wg hrem_pos
    have hg0_eq : g0 = S_g0.density := by
      funext x; rw [hg0_def]; exact hS_g0_density x
    -- Sub-case split on the smallest-variance coefficient `c im`.
    by_cases hcim : c im = 0
    · -- `c im = 0`: `f` is the `k`-component sum at the ACTUAL variances
      -- `w (succAbove i)` (positive, distinct, some coeff nonzero), so the IH
      -- gives ≤ 2(k-1) ≤ 2k directly.
      have hf_eq_rest :
          (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
            (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))))
          = (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => c (im.succAbove i)
                * Real.exp (-(x - ν (im.succAbove i))^2 / (2 * w (im.succAbove i))))) := by
        funext x; rw [hsplit x, hcim, zero_mul, zero_add]
      rw [hf_eq_rest]
      -- IH on the rest at the actual variances.
      have hrest_bound :
          Workspace.Types.ZeroCount.hasAtMostNZeros
            (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => c (im.succAbove i)
                * Real.exp (-(x - ν (im.succAbove i))^2 / (2 * w (im.succAbove i)))))
            (2 * (k - 1)) := by
        apply IH (fun i => c (im.succAbove i)) (fun i => ν (im.succAbove i))
                 (fun i => w (im.succAbove i))
        · intro i; exact hw_pos _
        · intro i j hij
          have hne : im.succAbove i ≠ im.succAbove j := by
            intro h; exact hij (im.succAbove_right_injective h)
          exact hw_distinct _ _ hne
        · exact hrem_coeff
      -- 2(k-1) ≤ 2k.
      have hle : ((2 * (k - 1) : ℕ) : ℕ∞) ≤ ((2 * k : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : 2 * (k - 1) ≤ 2 * k)
      exact le_trans hrest_bound hle
    · -- `c im ≠ 0`: the DECOUPLED-WIDTH two-positive-convolution route.
      -- Normalized last-component coefficient `A := c im·√(2π·w im) ≠ 0`.
      set A : ℝ := c im * Real.sqrt (2 * Real.pi * w im) with hA_def
      have hA_ne : A ≠ 0 := by
        rw [hA_def]
        have hsq : 0 < Real.sqrt (2 * Real.pi * w im) := by
          apply Real.sqrt_pos.mpr; positivity
        exact mul_ne_zero hcim (ne_of_gt hsq)
      -- ===== Choose the FREE small convolution/add-Gaussian width `v`. =====
      -- We package the entire §6.1 add-near-delta step in one existential: there is a
      -- small width `v` with `0 < v < w im` such that the small-variance object
      --   h_v := conv(g̃₀, v) + A·N(ν im, v)
      -- has at most `2k` zeros.  The recovery width is then `w im − v > 0`, and the
      -- convolution semigroup recovers `f` EXACTLY (variances
      --   (w_i − w im) + v + (w im − v) = w_i,   last  v + (w im − v) = w im).
      --
      -- Inside the existential the route is `Prop7AddGaussianAddsAtMostTwoZeros`
      -- applied to `gα := conv(g̃₀, v)`:
      --   * analyticity (`Prop7AnalyticityOfMixture`),
      --   * `≤ 2(k-1)` zeros (HummelGidas on g̃₀, positive width v),
      --   * SIMPLE ZEROS (input (i)) of `gα` via `convSmall_all_zeros_simple` after a
      --     first-reduction of `g̃₀` to a simple-zero base `g̃₀'` (needs `v < α_pers`),
      --   * TAIL ENVELOPE (input (ii)) of `gα` via `SublemmaTailDomination` on
      --     `heatShift S_g0 v`,
      --   * THRESHOLD (input (iii)) `v ≤ v₀`: now satisfiable because `v` is FREE —
      --     pick it in a min including `v₀`.
      -- The DECOUPLING removes the OLD false obstruction (`αp = w im/2 ≤ v₀`), where
      -- the width was pinned too large for both (i) and (iii).
      -- ===== §6.1 FINISH: dual-genericity transport (STEP 2). =====
      -- The branch goal `hasAtMostNZeros f (2k)` is discharged by the standalone
      -- dual-genericity main-case lemma, which supplies a SIMPLE deconvolution base,
      -- the recovery to the perturbed target, and the count transport, feeding the
      -- analytic engine `mainCaseSimpleTransport` (= STEP-1-concrete + Hummel–Gidas).
      exact bareMainCaseDualGenericity k hk IH c ν w hw_pos hw_distinct im
        (fun j => him j (Finset.mem_univ j)) hcim hrem_coeff
  · -- Degenerate case: every remaining coefficient is zero, so the whole sum
    -- collapses to the single smallest-variance Gaussian term.
    simp only [not_exists, not_not] at hrem_coeff
    -- The function equals `c im · exp(-(·-ν im)²/(2 w im))`.
    have hsimp :
        (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
          (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))))
        = (fun x => c im * Real.exp (-(x - ν im)^2 / (2 * w im))) := by
      funext x
      rw [hsplit x]
      have hz : (Finset.univ : Finset (Fin k)).sum
            (fun i => c (im.succAbove i)
              * Real.exp (-(x - ν (im.succAbove i))^2 / (2 * w (im.succAbove i)))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _; rw [hrem_coeff i]; ring
      rw [hz, add_zero]
    rw [hsimp]
    by_cases hcim : c im = 0
    · -- Then the function is identically zero, contradicting nontriviality.
      exfalso
      obtain ⟨x, hx⟩ := h_nontrivial
      apply hx
      rw [hsplit x, hcim, zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro i _; rw [hrem_coeff i]; ring
    · -- A single nonzero scaled Gaussian never vanishes: zero distinct zeros ≤ 2k.
      have hzs :
          Workspace.Types.ZeroCount.zeroSet
            (fun x => c im * Real.exp (-(x - ν im)^2 / (2 * w im))) = ∅ := by
        rw [Workspace.Types.ZeroCount.zeroSet]
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact mul_ne_zero hcim (ne_of_gt (Real.exp_pos _)) h
      rw [Workspace.Types.ZeroCount.hasAtMostNZeros,
          Workspace.Types.ZeroCount.zeroCount, hzs]
      simp

/-- **Inner bound (Steps 1–6).**  Any normalized `(k+1)`-component signed Gaussian
combination `S`, with at least one nonzero coefficient, density not identically
zero, distinct positive variances, has at most `2k` distinct real zeros.

This is the deconvolved target of Step 7: applied to `S = deconvSigned S_f β` it
provides the `≤ 2k` bound that Hummel–Gidas transports back to `f`.

The abstract `SignedGaussianCombination` `S` is converted to the bare-exponential
`Fin (k+1)` model — `S.density x = Σ_i (p_i.1/√(2π·varSq_i))·exp(-(x-mean_i)²/(2·varSq_i))`
— its hypotheses are re-derived in that model, and `bareModelSixStepBound` (the
§6.1 analytic core) is applied. -/
private theorem innerHAlphaBound
    (k : ℕ) (hk : 1 ≤ k)
    (IH : ∀ (a' : Fin k → ℝ)
            (μ' : Fin k → ℝ)
            (τ_sq' : Fin k → ℝ),
          (∀ i : Fin k, 0 < τ_sq' i) →
          (∀ i j : Fin k, i ≠ j → τ_sq' i ≠ τ_sq' j) →
          (∃ i : Fin k, a' i ≠ 0) →
          Workspace.Types.ZeroCount.hasAtMostNZeros
            (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => a' i * Real.exp (-(x - μ' i)^2 / (2 * τ_sq' i))))
            (2 * (k - 1)))
    (S : SignedGaussianCombination)
    (hlen : S.components.length = k + 1)
    (h_coeff : ∃ p ∈ S.components, p.1 ≠ 0)
    (h_density_ne : ∃ x : ℝ, S.density x ≠ 0)
    (h_var_distinct :
      (S.components.map (fun p => p.2.varSq)).Nodup)
    -- All component variances are strictly positive.  This is the hypothesis the
    -- §6.1 first-reduction / add-near-delta / analytic-IFT-homotopy argument needs
    -- (every variance must stay a genuine positive Gaussian width throughout the
    -- homotopy).  It is supplied at the unique call site below: the components of
    -- `deconvSigned S_f β` have variances `τ_sq i − β > 0` because `β < τ_sq i`.
    -- (Note: `GaussianPDF.varSq_pos` already guarantees this per-component; this
    -- hypothesis is the packaged statement the assembly references directly.)
    (h_var_pos : ∀ p ∈ S.components, 0 < p.2.varSq) :
    Workspace.Types.ZeroCount.hasAtMostNZeros S.density (2 * k) := by
  classical
  -- Extract the bare-exponential `Fin (k+1)` model from the component list:
  --   c i = (coeff_i) / √(2π·varSq_i),  ν i = mean_i,  w i = varSq_i.
  set c : Fin (k + 1) → ℝ := fun i =>
    (S.components.get (Fin.cast hlen.symm i)).1
      / Real.sqrt (2 * Real.pi * (S.components.get (Fin.cast hlen.symm i)).2.varSq)
    with hc_def
  set ν : Fin (k + 1) → ℝ := fun i =>
    (S.components.get (Fin.cast hlen.symm i)).2.mean with hν_def
  set w : Fin (k + 1) → ℝ := fun i =>
    (S.components.get (Fin.cast hlen.symm i)).2.varSq with hw_def
  -- `S.density` equals the bare-exponential sum in this model.
  have hdens : S.density = (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
      (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))) := by
    funext x
    rw [SignedGaussianCombination.density_eq]
    have hconv : ∀ (l : List ℝ) (hl : l.length = k + 1),
        l.sum = ∑ i : Fin (k + 1), l.get (Fin.cast hl.symm i) := by
      intro l hl
      rw [← List.sum_ofFn]; congr 1
      apply List.ext_getElem
      · simp [hl]
      · intro n h1 h2; simp only [List.getElem_ofFn]; rfl
    rw [hconv (S.components.map (fun p => p.1 * p.2.density x))
        (by rw [List.length_map]; exact hlen)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hc_def, hν_def, hw_def, List.get_eq_getElem, List.getElem_map]
    rw [GaussianPDF.density_eq]
    rw [div_mul_eq_mul_div, one_mul, mul_div_assoc']
    exact mul_div_right_comm _ _ _
  -- Re-derive the bare-model side conditions.
  have hw_pos : ∀ i : Fin (k + 1), 0 < w i := by
    intro i; rw [hw_def]; apply h_var_pos; exact List.get_mem _ _
  have hw_distinct : ∀ i j : Fin (k + 1), i ≠ j → w i ≠ w j := by
    intro i j hij
    rw [hw_def]; simp only
    have hnd := h_var_distinct
    rw [List.nodup_iff_injective_get] at hnd
    intro heq
    apply hij
    have hmapeq : (S.components.map (fun p => p.2.varSq)).get
            (Fin.cast (by rw [List.length_map]; exact hlen.symm) i)
          = (S.components.map (fun p => p.2.varSq)).get
            (Fin.cast (by rw [List.length_map]; exact hlen.symm) j) := by
      simp only [List.get_eq_getElem, List.getElem_map]; exact heq
    have hcast := hnd hmapeq
    exact (Fin.cast_inj _).mp hcast
  have hc_nonzero : ∃ i : Fin (k + 1), c i ≠ 0 := by
    obtain ⟨p, hp_mem, hp_ne⟩ := h_coeff
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp hp_mem
    refine ⟨Fin.cast hlen n, ?_⟩
    rw [hc_def]; simp only
    have hcast : Fin.cast hlen.symm (Fin.cast hlen n) = n := by apply Fin.ext; simp
    rw [hcast, hn]
    have hpos : 0 < p.2.varSq := h_var_pos p hp_mem
    have hsqrt : 0 < Real.sqrt (2 * Real.pi * p.2.varSq) := by
      apply Real.sqrt_pos.mpr; positivity
    exact div_ne_zero hp_ne (ne_of_gt hsqrt)
  have h_nontrivial : ∃ x : ℝ,
      (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))) ≠ 0 := by
    obtain ⟨x, hx⟩ := h_density_ne
    refine ⟨x, ?_⟩
    have := congrFun hdens x
    rw [this] at hx
    exact hx
  -- Apply the §6.1 bare-model core (Steps 1–6).
  rw [hdens]
  exact bareModelSixStepBound k hk IH c ν w hw_pos hw_distinct hc_nonzero h_nontrivial

theorem PositiveSmallestVarianceInductiveStep
    (k : ℕ) (hk : 1 ≤ k)
    (IH : ∀ (a' : Fin k → ℝ)
            (μ' : Fin k → ℝ)
            (τ_sq' : Fin k → ℝ),
          (∀ i : Fin k, 0 < τ_sq' i) →
          (∀ i j : Fin k, i ≠ j → τ_sq' i ≠ τ_sq' j) →
          (∃ i : Fin k, a' i ≠ 0) →
          Workspace.Types.ZeroCount.hasAtMostNZeros
            (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => a' i * Real.exp (-(x - μ' i)^2 / (2 * τ_sq' i))))
            (2 * (k - 1)))
    (a : Fin (k + 1) → ℝ)
    (μ : Fin (k + 1) → ℝ)
    (τ_sq : Fin (k + 1) → ℝ)
    (h_τ_nonzero : ∀ i : Fin (k + 1), τ_sq i ≠ 0)
    (h_τ_distinct : ∀ i j : Fin (k + 1), i ≠ j → τ_sq i ≠ τ_sq j)
    (h_a_nonzero : ∃ i : Fin (k + 1), a i ≠ 0)
    (h_τ_pos : ∀ i : Fin (k + 1), 0 < τ_sq i) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))))
      (2 * k) := by
  classical
  -- Abbreviation for the target bare-exponential sum.
  set f : ℝ → ℝ :=
    (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
      (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i)))) with hf_def
  -- Step 7a: the normalized signed combination S_f whose density is f.
  obtain ⟨S_f, hS_f_comp, hS_f_density, hS_f_coeff_iff, hS_f_exists_iff⟩ :=
    FormalToNormalizedBridge (k + 1) a μ τ_sq h_τ_pos
  -- f = S_f.density.
  have hf_eq : f = S_f.density := by
    funext x; rw [hf_def]; exact hS_f_density x
  -- The component list of S_f has length k+1.
  have hS_f_len : S_f.components.length = k + 1 := by
    rw [hS_f_comp]; simp
  -- Pick the smallest variance σ_k² = min_i τ_sq i (>0).
  obtain ⟨imin, _, himin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (k + 1))) τ_sq
      Finset.univ_nonempty
  have hσk_pos : 0 < τ_sq imin := h_τ_pos imin
  -- Choose a deconvolution shift β with 0 < β < every variance.
  set β : ℝ := τ_sq imin / 2 with hβ_def
  have hβ_pos : 0 < β := by rw [hβ_def]; linarith
  have hβ_lt_all : ∀ i : Fin (k + 1), β < τ_sq i := by
    intro i
    have hmin_le : τ_sq imin ≤ τ_sq i := himin i (Finset.mem_univ i)
    rw [hβ_def]; linarith
  -- Translate β < every variance into the deconvSigned hypothesis on S_f.components.
  have hβ_lt_comp : ∀ p ∈ S_f.components, β < p.snd.varSq := by
    intro p hp
    rw [hS_f_comp] at hp
    rw [List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    -- the i-th component's variance is τ_sq i.
    show β < τ_sq i
    exact hβ_lt_all i
  -- hα := the deconvolved density (variances shifted DOWN by β).
  set hα : ℝ → ℝ := (deconvSigned S_f β hβ_lt_comp).density with hhα_def
  -- Step 7b: convolving hα by N(0, β) recovers f.
  have hαβ_pos : 0 < β + β := by linarith
  have h_recover :
      ∀ x : ℝ, convolveWithGaussian hα β hβ_pos x = S_f.density x := by
    intro x
    have hconv :=
      Prop7ConvolutionRecoversOriginalDensity S_f β hβ_lt_comp β hβ_pos hαβ_pos x
    -- hconv : convolveWithGaussian S_α.density β x = S'.density x where
    --   S_α = deconvSigned S_f β, S' = S_f with each variance shifted by β-β = 0.
    -- Reduce S'.density to S_f.density.
    simp only at hconv
    rw [hhα_def]
    rw [hconv]
    -- Now show the shifted-by-0 combination's density equals S_f.density.
    rw [SignedGaussianCombination.density_eq, SignedGaussianCombination.density_eq]
    -- Both are sums over S_f.components; the shifted variance is varSq + (β - β) = varSq.
    rw [List.map_map]
    -- Convert RHS `map h S_f.components` to attach form, then match termwise.
    rw [← List.attach_map_val (l := S_f.components)
        (f := fun q : ℝ × GaussianPDF => q.1 * q.2.density x)]
    apply congrArg
    apply List.map_congr_left
    intro q _
    show q.val.1 * (GaussianPDF.density ⟨q.val.2.mean, q.val.2.varSq + (β - β), _⟩) x
        = q.val.1 * q.val.2.density x
    congr 1
    rw [GaussianPDF.density_eq, GaussianPDF.density_eq]
    have : q.val.2.varSq + (β - β) = q.val.2.varSq := by ring
    simp only [this]
  -- f is not identically zero (distinct-variance nontriviality).
  have hf_nontrivial : ∃ x : ℝ, f x ≠ 0 := by
    obtain ⟨x, hx⟩ :=
      FormalGaussianNontriviality (k + 1) (by omega) a μ τ_sq h_τ_nonzero
        h_τ_distinct h_a_nonzero
    exact ⟨x, by rw [hf_def]; exact hx⟩
  -- Step 7c: bound hα by the inner lemma (Steps 1–6).
  have h_hα_coeff : ∃ p ∈ (deconvSigned S_f β hβ_lt_comp).components, p.1 ≠ 0 := by
    -- deconvSigned preserves coefficients; lift a nonzero coeff of S_f.
    obtain ⟨p₀, hp₀_mem, hp₀_ne⟩ := hS_f_exists_iff.mp h_a_nonzero
    refine ⟨(p₀.1, shiftGaussian p₀.2 β (hβ_lt_comp p₀ hp₀_mem)), ?_, hp₀_ne⟩
    rw [deconvSigned]
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨p₀, hp₀_mem, rfl⟩
  have h_hα_var_distinct :
      ((deconvSigned S_f β hβ_lt_comp).components.map (fun p => p.2.varSq)).Nodup := by
    -- The variance list equals `List.ofFn (fun i => τ_sq i - β)`; Nodup since τ_sq distinct.
    have hvar_eq :
        (deconvSigned S_f β hβ_lt_comp).components.map (fun p => p.2.varSq)
          = List.ofFn (fun i : Fin (k + 1) => τ_sq i - β) := by
      simp only [deconvSigned, List.map_map]
      simp only [Function.comp_def, shiftGaussian_varSq]
      rw [List.attach_map_val (l := S_f.components)
          (f := fun q : ℝ × GaussianPDF => q.2.varSq - β), hS_f_comp, List.map_ofFn]
      rfl
    rw [hvar_eq]
    rw [List.nodup_ofFn]
    intro i j hij
    by_contra hne
    have : τ_sq i = τ_sq j := by have := hij; simp only at this; linarith [this]
    exact h_τ_distinct i j hne this
  have h_hα_density_ne : ∃ x : ℝ, hα x ≠ 0 := by
    -- If hα ≡ 0 then its convolution (= f) would be ≡ 0, contradicting nontriviality.
    by_contra h
    simp only [not_exists, not_not] at h
    obtain ⟨x₀, hx₀⟩ := hf_nontrivial
    apply hx₀
    rw [← (by funext x; rw [h_recover x, ← hf_eq] : convolveWithGaussian hα β hβ_pos = f)]
    rw [convolveWithGaussian_def]
    have : ∀ y : ℝ, hα y * (GaussianPDF.density ⟨0, β, hβ_pos⟩ (x₀ - y)) = 0 := by
      intro y; rw [h y]; ring
    simp only [this]
    exact MeasureTheory.integral_zero ℝ ℝ
  have h_hα_len : (deconvSigned S_f β hβ_lt_comp).components.length = k + 1 := by
    rw [deconvSigned_components_length]; exact hS_f_len
  -- Every deconvolved variance `τ_sq i − β` is strictly positive (since `β < τ_sq i`).
  have h_hα_var_pos :
      ∀ p ∈ (deconvSigned S_f β hβ_lt_comp).components, 0 < p.2.varSq := by
    intro p hp
    -- Components of `deconvSigned` are `shiftGaussian` of the originals; their
    -- variance positivity is the structure field `varSq_pos`.
    exact p.2.varSq_pos
  have h_hα_bound :
      Workspace.Types.ZeroCount.hasAtMostNZeros hα (2 * k) :=
    innerHAlphaBound k hk IH (deconvSigned S_f β hβ_lt_comp) h_hα_len
      h_hα_coeff h_hα_density_ne h_hα_var_distinct h_hα_var_pos
  -- Step 7d: hα is analytic.
  have h_hα_analytic : AnalyticOnNhd ℝ hα Set.univ := by
    rw [hhα_def]; exact Prop7AnalyticityOfMixture _
  -- Apply Hummel–Gidas: convolution does not increase zeros.
  have h_hα_bdd : ∃ C : ℝ, ∀ x : ℝ, |hα x| ≤ C := by
    rw [hhα_def]
    exact Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded (deconvSigned S_f β hβ_lt_comp)
  have h_conv_bound :
      Workspace.Types.ZeroCount.hasAtMostNZeros
        (convolveWithGaussian hα β hβ_pos) (2 * k) :=
    Workspace.PriorWork.HummelGidasZeroCount hα h_hα_analytic h_hα_bdd (2 * k) h_hα_bound β hβ_pos
  -- The convolution equals f, so f has ≤ 2k zeros.
  have h_funext : convolveWithGaussian hα β hβ_pos = f := by
    funext x; rw [h_recover x, ← hf_eq]
  rw [h_funext, hf_def] at h_conv_bound
  -- h_conv_bound : hasAtMostNZeros f (2*k); the goal is the unfolded f.
  exact h_conv_bound

end Workspace.ProofLemmas
