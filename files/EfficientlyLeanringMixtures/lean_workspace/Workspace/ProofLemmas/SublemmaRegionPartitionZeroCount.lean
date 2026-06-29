import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.HurwitzGaussianPerturbationTailDominance
import Workspace.ProofLemmas.HurwitzGaussianPerturbationSimpleZeroPreservation
import Workspace.ProofLemmas.HurwitzGaussianPerturbationCenterTwoZeros
import Workspace.ProofLemmas.SublemmaAddGaussianTailRegionNoZeros

namespace Workspace.ProofLemmas

theorem SublemmaRegionPartitionZeroCount
    (g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ)
    (N : ℕ) (h_zeros : Workspace.Types.ZeroCount.hasAtMostNZeros g N)
    (h_simple : ∀ x : ℝ, g x = 0 → deriv g x ≠ 0)
    (a_k : ℝ) (ha_k : a_k ≠ 0) (μ_k : ℝ)
    (b b' a a' s s' : ℝ) (hb_lt : b < b')
    (h_b_mu : b < μ_k) (h_mu_b' : μ_k < b')
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hs : 0 < s) (hs' : 0 < s')
    (h_env_left : ∀ x < b,
        (g x).sign = a.sign ∧
        |a| * (1 / Real.sqrt (2 * Real.pi * s)) *
          Real.exp (-x^2 / (2 * s)) < |g x|)
    (h_env_right : ∀ x > b',
        (g x).sign = a'.sign ∧
        |a'| * (1 / Real.sqrt (2 * Real.pi * s')) *
          Real.exp (-x^2 / (2 * s')) < |g x|) :
    ∃ v_threshold : ℝ, 0 < v_threshold ∧
      ∀ v : ℝ, ∀ hv : 0 < v, v ≤ v_threshold →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => g x + a_k *
            Workspace.Types.GaussianPDF.GaussianPDF.density
              ⟨μ_k, v, hv⟩ x)
          (N + 2) := by
  -- We assemble the three PROVEN region ProofLemmas (Moitra–Valiant §6.1) instead
  -- of delegating to the paper axiom:
  --   region (a)  `HurwitzGaussianPerturbationTailDominance`        : zeroSet h ⊆ Icc b b'
  --   region (b)  `HurwitzGaussianPerturbationSimpleZeroPreservation`: outer-window zeros ≤ N
  --   region (c)  `HurwitzGaussianPerturbationCenterTwoZeros`        : inner-window zeros ≤ 2
  -- fused by `SublemmaAddGaussianTailRegionNoZeros` ((a)+(b)+(c) ⇒ hasAtMostNZeros h (N+2)).
  --
  -- Region (c) FIXES the central-window radius `δ` (it is existentially produced),
  -- so we extract `δ` from (c) first and thread the SAME `δ` into region (b).
  -- Region (a) needs the straddle `b < μ_k < b'`, which this wrapper supplies.
  -- The added Gaussian's variance threshold is the min of the three regional ones.
  --
  -- Region (c): inner-window ≤2 zeros.  Produces δ and its own threshold v₀_c.
  obtain ⟨δ, hδ_pos, v0c, hv0c_pos, hcenter⟩ :=
    HurwitzGaussianPerturbationCenterTwoZeros g hg a_k ha_k μ_k
  -- Region (a): tail dominance ⇒ zeroSet h ⊆ Icc b b'.  Needs b < μ_k < b'.
  obtain ⟨v0a, hv0a_pos, htail⟩ :=
    HurwitzGaussianPerturbationTailDominance g b b' a a' s s' hb_lt ha ha' hs hs'
      μ_k h_b_mu h_mu_b' h_env_left h_env_right a_k ha_k
  -- Region (b): outer-window ≤N zeros, using the δ produced by region (c).
  obtain ⟨v0b, hv0b_pos, houter⟩ :=
    HurwitzGaussianPerturbationSimpleZeroPreservation g hg N h_zeros h_simple
      b b' hb_lt a_k ha_k μ_k δ hδ_pos
  -- Combined variance threshold.
  refine ⟨min v0a (min v0b v0c), lt_min hv0a_pos (lt_min hv0b_pos hv0c_pos), ?_⟩
  intro v hv hv_le
  have hv_le_a : v ≤ v0a := le_trans hv_le (min_le_left _ _)
  have hv_le_b : v ≤ v0b := le_trans hv_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hv_le_c : v ≤ v0c := le_trans hv_le (le_trans (min_le_right _ _) (min_le_right _ _))
  -- The perturbed function.
  set h : ℝ → ℝ := fun x => g x + a_k *
      Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x with hh_def
  -- Feed the three regional bounds into the encard glue.
  exact SublemmaAddGaussianTailRegionNoZeros h b b' μ_k δ N
    (htail v hv hv_le_a)
    (houter v hv hv_le_b)
    (hcenter v hv hv_le_c)

end Workspace.ProofLemmas
