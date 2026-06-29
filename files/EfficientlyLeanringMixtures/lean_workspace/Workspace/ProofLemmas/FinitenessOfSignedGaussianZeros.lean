import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.SublemmaSignedGaussianDensityZerosFinite
import Workspace.ProofLemmas.SublemmaTailDomination

/-!
# Sub-lemma A (Step 1, Finiteness)

A nonzero signed Gaussian combination has finitely many distinct real zeros.

If `S.density ≢ 0` (witnessed by some `x` with `S.density x ≠ 0`), then the zero
set `{x | S.density x = 0}` is finite — equivalently `zeroCount S.density < ⊤` in
`ℕ∞`.

Proof idea (for the eventual proof, not needed for the statement): factor out the
everywhere-positive prefactor `exp(-x²/(2σ_max²))` so the zero set coincides with
that of a nonzero exponential-quadratic combination, then transfer the finiteness
from the proved `ExponentialSumZeroBound`.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.SignedGaussianCombination
open Workspace.Types.ZeroCount

/-- **Finiteness of the zero set of a nonzero signed Gaussian combination.**

If `S.density` is not identically zero, then its zero set is finite; equivalently
`zeroCount S.density < ⊤`. -/
theorem FinitenessOfSignedGaussianZeros
    (S : SignedGaussianCombination)
    (hne : ∃ x : ℝ, S.density x ≠ 0) :
    (zeroSet S.density).Finite ∧ zeroCount S.density < ⊤ := by
  -- Tail domination: outside `[b, b']` the density keeps a fixed nonzero sign.
  -- (The corrected hypothesis of `SublemmaTailDomination` is exactly `hne`.)
  obtain ⟨b, b', a, a', s, s', hbb', ha, ha', hs, hs', hleft, hright⟩ :=
    SublemmaTailDomination S hne
  -- On the compact interval `[b, b']` the zero set is finite (analyticity).
  have hfinIcc : Set.Finite {x ∈ Set.Icc b b' | S.density x = 0} :=
    SublemmaSignedGaussianDensityZerosFinite S hne b b'
  -- Every zero must lie inside `[b, b']`, since the tails are sign-definite.
  have hsub : zeroSet S.density ⊆ {x ∈ Set.Icc b b' | S.density x = 0} := by
    intro x hx
    rw [zeroSet_def, Set.mem_setOf_eq] at hx
    refine ⟨?_, hx⟩
    rw [Set.mem_Icc]
    constructor
    · by_contra hlt
      push_neg at hlt
      have hsign := (hleft x hlt).1
      rw [hx] at hsign
      simp only [Real.sign_zero] at hsign
      exact ha (by have := hsign.symm; simpa [Real.sign_eq_zero_iff] using this)
    · by_contra hgt
      push_neg at hgt
      have hsign := (hright x hgt).1
      rw [hx] at hsign
      simp only [Real.sign_zero] at hsign
      exact ha' (by have := hsign.symm; simpa [Real.sign_eq_zero_iff] using this)
  -- Finite subset of a finite set is finite; finiteness gives `encard < ⊤`.
  have hfin : (zeroSet S.density).Finite := hfinIcc.subset hsub
  exact ⟨hfin, by rw [zeroCount_def]; exact hfin.encard_lt_top⟩

end Workspace.ProofLemmas
