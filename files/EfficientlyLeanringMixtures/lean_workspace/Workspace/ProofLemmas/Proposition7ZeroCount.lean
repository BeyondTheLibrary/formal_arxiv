import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.Prop7Induction

namespace Workspace.ProofLemmas

/--
Proposition 7 of Moitra–Valiant: a signed linear combination of `k ≥ 1` Gaussian
densities with pairwise distinct variances and not-all-zero coefficients has at
most `2(k - 1)` real zeros (`k - 1` is natural subtraction; for `k ≥ 1` it
coincides with the mathematical `k - 1`).
-/
theorem Proposition7ZeroCount :
    ∀ (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination),
      let k := S.components.length
      1 ≤ k →
      (S.components.map (fun p => p.snd.varSq)).Nodup →
      (∃ p ∈ S.components, p.fst ≠ 0) →
      Workspace.Types.ZeroCount.hasAtMostNZeros S.density (2 * (k - 1)) :=
  Prop7Induction

end Workspace.ProofLemmas
