-- Cited from (classical real analysis / general topology):
--   * Munkres, J. R. (2000). *Topology* (2nd ed.), Prentice Hall, Ch. 3
--     §27 (compactness; continuous and lower-semicontinuous functions on
--     a compact set attain their infimum).
--   * Rudin, W. (1976). *Principles of Mathematical Analysis* (3rd ed.),
--     McGraw-Hill, Ch. 2 (compactness) and Ch. 4 §4.16 (extreme value
--     theorem; extension to lower-semicontinuous functions on a compact
--     set).
--   * Bourbaki, N. *General Topology*, Ch. IV §6 (lower-semicontinuous
--     functions on a compact set attain their infimum).
--
-- Paper label: [Munkres §27 / Rudin Principles §4.16 / Bourbaki Top. IV §6]
--
-- NL statement (compactness extraction of a uniform positive infimum):
-- Let `K ⊆ ℝ` be a compact set and let `f : ℝ → ℝ` be a function which
-- is lower-semicontinuous on `K` and strictly positive on `K` (i.e.
-- `f c > 0` for every `c ∈ K`). Then there exists a strictly positive
-- constant `m > 0` such that `f c ≥ m` for every `c ∈ K`.
--
-- (If `K = ∅` the conclusion holds vacuously with, e.g., `m := 1`. The
-- nontrivial content is the case `K ≠ ∅`, where the classical extreme
-- value theorem for lower-semicontinuous functions on a compact set
-- yields `m := inf_{c ∈ K} f c > 0`.)
--
-- This is the pure compactness/EVT ingredient used to upgrade the
-- lower-semicontinuous threshold `v₀ : ℝ → ℝ` produced by
-- `GaussianPerturbationThresholdLSC` to a single uniform constant
-- `v_K > 0` valid for every `c ∈ K`.
import Mathlib

namespace Workspace.ProofLemmas

theorem CompactPositiveLSCInfimum
    (K : Set ℝ) (hK_compact : IsCompact K)
    (f : ℝ → ℝ)
    (hf_lsc : LowerSemicontinuousOn f K)
    (hf_pos : ∀ c ∈ K, 0 < f c) :
    ∃ m : ℝ, 0 < m ∧ ∀ c ∈ K, m ≤ f c := by
  by_cases hK_empty : K.Nonempty
  · -- Nonempty case: the LSC function on the compact set attains its minimum.
    obtain ⟨a, ha_mem, ha_min⟩ :=
      hf_lsc.exists_isMinOn hK_empty hK_compact
    refine ⟨f a, hf_pos a ha_mem, ?_⟩
    intro c hc
    exact (isMinOn_iff.mp ha_min) c hc
  · -- Empty case: pick m := 1, the conclusion ∀ c ∈ K, m ≤ f c is vacuous.
    refine ⟨1, by norm_num, ?_⟩
    intro c hc
    exact absurd ⟨c, hc⟩ hK_empty

end Workspace.ProofLemmas
