import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.SublemmaRegionPartitionZeroCount

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

/-!
# `Prop7AddGaussianAddsAtMostTwoZeros` — Attempt 5

Closes the proof using `SublemmaRegionPartitionZeroCount`, which is the
proved version of the Step 5 region-partition zero-count lemma.

We do NOT use `Workspace.PriorWork.Prop7AddGaussianAddsAtMostTwoZerosPaper`
directly: instead we destructure the envelope hypothesis, shift its tail
endpoints so that they straddle `μ_k`, and then invoke
`SublemmaRegionPartitionZeroCount`.
-/

open Workspace.Types.ZeroCount
open Workspace.Types.GaussianPDF
open scoped Real

/-- Bridge `b < b'` to `b < μ_k < b'` by shrinking the tail endpoints. -/
private lemma aux_shift_envelope_to_straddle_mu_k
    (g : ℝ → ℝ) (b b' a a' s s' : ℝ) (h_b_lt : b < b')
    (_ha : a ≠ 0) (_ha' : a' ≠ 0) (_hs : 0 < s) (_hs' : 0 < s')
    (h_left  : ∀ x : ℝ, x < b →
        (g x).sign = a.sign ∧
        |a|  * (1 / Real.sqrt (2 * Real.pi * s )) * Real.exp (-x^2 / (2 * s )) < |g x|)
    (h_right : ∀ x : ℝ, x > b' →
        (g x).sign = a'.sign ∧
        |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) < |g x|)
    (μ_k : ℝ) :
    ∃ b_new b'_new : ℝ, b_new < b'_new ∧ b_new < μ_k ∧ μ_k < b'_new ∧
      (∀ x : ℝ, x < b_new →
          (g x).sign = a.sign ∧
          |a|  * (1 / Real.sqrt (2 * Real.pi * s )) * Real.exp (-x^2 / (2 * s )) < |g x|) ∧
      (∀ x : ℝ, x > b'_new →
          (g x).sign = a'.sign ∧
          |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) < |g x|) := by
  refine ⟨min b (μ_k - 1), max b' (μ_k + 1), ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : min b (μ_k - 1) ≤ b := min_le_left _ _
    have h2 : b' ≤ max b' (μ_k + 1) := le_max_left _ _
    linarith
  · have : min b (μ_k - 1) ≤ μ_k - 1 := min_le_right _ _
    linarith
  · have : μ_k + 1 ≤ max b' (μ_k + 1) := le_max_right _ _
    linarith
  · intro x hx
    apply h_left
    have h1 : min b (μ_k - 1) ≤ b := min_le_left _ _
    linarith
  · intro x hx
    apply h_right
    have h1 : b' ≤ max b' (μ_k + 1) := le_max_left _ _
    linarith

/-- **Main theorem.** -/
theorem Prop7AddGaussianAddsAtMostTwoZeros :
    ∀ (g : ℝ → ℝ),
      AnalyticOnNhd ℝ g Set.univ →
      ∀ (N : ℕ),
        Workspace.Types.ZeroCount.hasAtMostNZeros g N →
        (∀ x : ℝ, g x = 0 → deriv g x ≠ 0) →
        -- Tail-Gaussian envelope hypothesis (paper §6.1 Step 1)
        (∃ b b' a a' s s' : ℝ, b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
          (∀ x : ℝ, x < b →
              (g x).sign = a.sign ∧
              |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) < |g x|) ∧
          (∀ x : ℝ, x > b' →
              (g x).sign = a'.sign ∧
              |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) < |g x|)) →
        ∀ (a_k : ℝ), a_k ≠ 0 →
        ∀ (μ_k : ℝ),
          ∃ v₀ : ℝ, 0 < v₀ ∧
            ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
              Workspace.Types.ZeroCount.hasAtMostNZeros
                (fun x => g x +
                  a_k *
                    Workspace.Types.GaussianPDF.GaussianPDF.density
                      ⟨μ_k, v, hv⟩ x)
                (N + 2) := by
  intro g hg N hN_g hg_simple h_envelope a_k ha_k μ_k
  obtain ⟨b, b', a, a', s, s', h_b_lt, ha, ha', hs, hs', h_left, h_right⟩ :=
    h_envelope
  -- Shift the tail endpoints so that the envelope straddles μ_k.
  obtain ⟨b₀, b₀', hb_lt', hb_mu, hmu_b', h_left', h_right'⟩ :=
    aux_shift_envelope_to_straddle_mu_k g b b' a a' s s' h_b_lt
      ha ha' hs hs' h_left h_right μ_k
  -- Invoke the proved region-partition zero-count sub-lemma.
  exact SublemmaRegionPartitionZeroCount g hg N hN_g hg_simple
          a_k ha_k μ_k b₀ b₀' a a' s s' hb_lt' hb_mu hmu_b'
          ha ha' hs hs' h_left' h_right'

end Workspace.ProofLemmas
