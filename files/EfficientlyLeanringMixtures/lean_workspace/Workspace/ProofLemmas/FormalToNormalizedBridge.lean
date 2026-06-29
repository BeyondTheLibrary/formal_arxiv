import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination

/-!
# FormalToNormalizedBridge

Model-bridge (Steps 4,5,7): a bare-exponential formal Gaussian sum equals a
`SignedGaussianCombination` density.

For any finite index family `Fin n` with means `ν i`, strictly positive
variances `w i > 0` and coefficients `c i`, the bare-exponential sum
`g x = Σ_i c i · exp(-(x - ν i)² / (2 · w i))`
equals, pointwise for every `x`, the density of the `SignedGaussianCombination`
`S_g` whose `i`-th component is
`(c i · √(2π · w i),  GaussianPDF ⟨ν i, w i, _⟩)`.
That is `∀ x, g x = S_g.density x`.

The `i`-th coefficient `c i · √(2π · w i)` is nonzero iff `c i ≠ 0`, so `S_g`
has a nonzero coefficient iff `g` does.

The `SignedGaussianCombination` is assembled from the `Fin n` data via
`List.ofFn`, so its `components` list has length `n` and its `i`-th entry is the
declared `(coefficient, Gaussian)` pair.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

theorem FormalToNormalizedBridge
    (n : ℕ)
    (c : Fin n → ℝ)
    (ν : Fin n → ℝ)
    (w : Fin n → ℝ)
    (hw : ∀ i : Fin n, 0 < w i) :
    ∃ S : SignedGaussianCombination,
      S.components =
        List.ofFn (fun i : Fin n =>
          (c i * Real.sqrt (2 * Real.pi * w i),
            (⟨ν i, w i, hw i⟩ : GaussianPDF))) ∧
      (∀ x : ℝ,
        (Finset.univ : Finset (Fin n)).sum
          (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))
        = S.density x) ∧
      (∀ i : Fin n,
        (c i * Real.sqrt (2 * Real.pi * w i) ≠ 0) ↔ (c i ≠ 0)) ∧
      ((∃ i : Fin n, c i ≠ 0) ↔ (∃ p ∈ S.components, p.1 ≠ 0)) := by
  -- Build the signed combination from the Fin n data.
  refine ⟨⟨List.ofFn (fun i : Fin n =>
        (c i * Real.sqrt (2 * Real.pi * w i),
          (⟨ν i, w i, hw i⟩ : GaussianPDF)))⟩, rfl, ?_, ?_, ?_⟩
  · -- Density equality.
    intro x
    rw [SignedGaussianCombination.density_eq]
    -- RHS: (List.ofFn ... ).map (fun p => p.1 * p.2.density x)).sum
    -- Convert the list sum over List.ofFn into a Finset.univ sum.
    rw [List.map_ofFn]
    rw [List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    -- LHS coefficient term: c i * exp(...). RHS: (c i * √(2π w i)) * density x.
    simp only [Function.comp, GaussianPDF.density_eq]
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * w i) := by
      apply Real.sqrt_pos.mpr
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact mul_pos this (hw i)
    have hsqrt_ne : Real.sqrt (2 * Real.pi * w i) ≠ 0 := ne_of_gt hsqrt_pos
    -- LHS: c i * exp(...).  RHS: √ * c i * (√⁻¹ * exp(...)).
    rw [one_div]
    rw [show c i * Real.sqrt (2 * Real.pi * w i)
          * ((Real.sqrt (2 * Real.pi * w i))⁻¹
              * Real.exp (-(x - ν i) ^ 2 / (2 * w i)))
        = (Real.sqrt (2 * Real.pi * w i) * (Real.sqrt (2 * Real.pi * w i))⁻¹)
          * (c i * Real.exp (-(x - ν i) ^ 2 / (2 * w i))) from by ring]
    rw [mul_inv_cancel₀ hsqrt_ne, one_mul]
  · -- Coefficient nonzero iff c i nonzero.
    intro i
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * w i) := by
      apply Real.sqrt_pos.mpr
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact mul_pos this (hw i)
    have hsqrt_ne : Real.sqrt (2 * Real.pi * w i) ≠ 0 := ne_of_gt hsqrt_pos
    constructor
    · intro h hc; exact h (by rw [hc]; ring)
    · intro hc; exact mul_ne_zero hc hsqrt_ne
  · -- Existence of nonzero coefficient iff existence of nonzero c i.
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨(c i * Real.sqrt (2 * Real.pi * w i),
          (⟨ν i, w i, hw i⟩ : GaussianPDF)), ?_, ?_⟩
      · rw [List.mem_ofFn]; exact ⟨i, rfl⟩
      · have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * w i) := by
          apply Real.sqrt_pos.mpr
          have : (0 : ℝ) < 2 * Real.pi := by positivity
          exact mul_pos this (hw i)
        exact mul_ne_zero hi (ne_of_gt hsqrt_pos)
    · rintro ⟨p, hp_mem, hp_ne⟩
      rw [List.mem_ofFn] at hp_mem
      obtain ⟨i, rfl⟩ := hp_mem
      refine ⟨i, ?_⟩
      intro hc
      apply hp_ne
      simp [hc]

end Workspace.ProofLemmas
