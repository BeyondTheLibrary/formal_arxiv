import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.SublemmaTailDominationSoundCore

namespace Workspace.ProofLemmas

open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianPDF

/-
SOUND proof of `SublemmaTailDomination`.

The body now delegates to `SublemmaTailDominationSound` (in
`Workspace.ProofLemmas.SublemmaTailDominationSoundCore`), which is built ENTIRELY
from Mathlib and the already-proven, axiom-clean building blocks
(`SublemmaEnvIsLittleODom`, `SublemmaRestIsLittleODom`,
`SublemmaTailDominanceSoundPieces`).  It does NOT route through the FALSE-RISK
axioms `MaxVarianceGaussianTailEstimate` / `MaxVarianceGaussianTailDominanceCoreMagnitude`
(nor `SublemmaTailDominationPaper`, which imported them).

This is now FULLY PROVEN (0 `sorry`, only Mathlib's standard axioms) under the
correct hypothesis `∃ x, S.density x ≠ 0` (the density is not identically zero).
The earlier `topCoeffSum G S ≠ 0` gaps are discharged by the finite reduction
`exists_reduced_right/left` in `SublemmaTailDominationSoundCore.lean`, which drops
cancelling identical-Gaussian top groups (each drop preserves the density and
shortens the component list) until a surviving lex-max group has nonzero
coefficient sum.  The old hypothesis `∃ p ∈ S.components, p.1 ≠ 0` was too weak —
`S = [(1,G), (-1,G)]` satisfies it yet has `S.density ≡ 0`, making the required
strictly-positive envelope impossible; `∃ x, S.density x ≠ 0` correctly excludes
that case.
-/
theorem SublemmaTailDomination
    (S : SignedGaussianCombination)
    (hS : ∃ x, S.density x ≠ 0) :
    ∃ (b b' a a' s s' : ℝ),
      b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
      (∀ x : ℝ, x < b →
        (S.density x).sign = a.sign ∧
        |a| * (1 / Real.sqrt (2 * Real.pi * s)) *
            Real.exp (-x ^ 2 / (2 * s)) < |S.density x|) ∧
      (∀ x : ℝ, x > b' →
        (S.density x).sign = a'.sign ∧
        |a'| * (1 / Real.sqrt (2 * Real.pi * s')) *
            Real.exp (-x ^ 2 / (2 * s')) < |S.density x|) :=
  SublemmaTailDominationSound S hS

end Workspace.ProofLemmas
