import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.FormalGaussianNontriviality
import Workspace.ProofLemmas.FormalToNormalizedBridge
import Workspace.ProofLemmas.SublemmaTailDomination

/-!
# FormalGaussianTailEnvelope

Step 4 (Moitra–Valiant §6.1) — Gaussian tail envelope for a distinct-positive-
variance formal Gaussian sum.

Let `g x = Σ_{i ∈ Fin k} c i · exp(-(x - ν i)² / (2 · w i))` with all `w i > 0`
pairwise distinct and some `c i ≠ 0`. Then there exist reals `b < b'`,
`a_env ≠ 0`, `a'_env ≠ 0`, `s > 0`, `s' > 0` such that:

* for all `x < b`, `sign (g x) = sign a_env` and
  `|a_env| · (1/√(2π s)) · exp(-x²/(2s)) < |g x|`;
* for all `x > b'`, `sign (g x) = sign a'_env` and
  `|a'_env| · (1/√(2π s')) · exp(-x²/(2s')) < |g x|`.

This is exactly the tail-envelope existential consumed by
`Prop7AddGaussianAddsAtMostTwoZeros` (cf. `SublemmaTailDomination`), transported
to the bare-exponential model via `FormalToNormalizedBridge`.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

theorem FormalGaussianTailEnvelope
    (k : ℕ)
    (c : Fin k → ℝ)
    (ν : Fin k → ℝ)
    (w : Fin k → ℝ)
    (hw_pos : ∀ i : Fin k, 0 < w i)
    (hw_distinct : ∀ i j : Fin k, i ≠ j → w i ≠ w j)
    (hc_nonzero : ∃ i : Fin k, c i ≠ 0) :
    ∃ (b b' a a' s s' : ℝ),
      b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
      (∀ x : ℝ, x < b →
        ((Finset.univ : Finset (Fin k)).sum
            (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))).sign = a.sign ∧
        |a| * (1 / Real.sqrt (2 * Real.pi * s)) *
            Real.exp (-x ^ 2 / (2 * s)) <
          |(Finset.univ : Finset (Fin k)).sum
            (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))|) ∧
      (∀ x : ℝ, x > b' →
        ((Finset.univ : Finset (Fin k)).sum
            (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))).sign = a'.sign ∧
        |a'| * (1 / Real.sqrt (2 * Real.pi * s')) *
            Real.exp (-x ^ 2 / (2 * s')) <
          |(Finset.univ : Finset (Fin k)).sum
            (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))|) := by
  classical
  -- k ≥ 1 since some coefficient is nonzero.
  have hk : 1 ≤ k := by
    obtain ⟨i, _⟩ := hc_nonzero
    exact i.pos
  -- Variances are nonzero (they are strictly positive).
  have hw_ne : ∀ i : Fin k, w i ≠ 0 := fun i => ne_of_gt (hw_pos i)
  -- Bridge: the bare-exponential sum equals a SignedGaussianCombination density.
  obtain ⟨S, _hcomp, hdens, _hcoeff, _hex⟩ :=
    FormalToNormalizedBridge k c ν w hw_pos
  -- Nontriviality: the formal sum is somewhere nonzero.
  obtain ⟨x₀, hx₀⟩ :=
    FormalGaussianNontriviality k hk c ν w hw_ne hw_distinct hc_nonzero
  -- Transport nontriviality across the bridge to the density.
  have hS : ∃ x, S.density x ≠ 0 := ⟨x₀, by rw [← hdens x₀]; exact hx₀⟩
  -- Apply the sound tail-domination lemma.
  obtain ⟨b, b', a, a', s, s', hbb', ha, ha', hs, hs', hL, hR⟩ :=
    SublemmaTailDomination S hS
  refine ⟨b, b', a, a', s, s', hbb', ha, ha', hs, hs', ?_, ?_⟩
  · intro x hx
    obtain ⟨hsign, hmag⟩ := hL x hx
    rw [hdens x]
    exact ⟨hsign, hmag⟩
  · intro x hx
    obtain ⟨hsign, hmag⟩ := hR x hx
    rw [hdens x]
    exact ⟨hsign, hmag⟩

end Workspace.ProofLemmas
