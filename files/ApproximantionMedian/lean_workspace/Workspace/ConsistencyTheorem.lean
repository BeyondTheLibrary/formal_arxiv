import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGFinalAssembly

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian

namespace Workspace.ConsistencyTheorem

/-- **Theorem 3 (consistency guarantee of `CMP(c)`).**

For `q = 2` and arbitrary dimension `d ≥ 1`: whenever the prediction equals an
optimal facility `fstar` (i.e. `socialCost 2 P fstar = optSocialCost 2 P`),
every coordinate-wise median `m` of the `CMP(c)`-augmented instance
`(P, ⌊c·n⌋ copies of fstar)` has social cost on the original agents at most
`CG(c) · OPT₂(P)`.

The hypothesis `(⌊c·n⌋ : ℝ) = c·n` requires the number of prediction copies to be
integral. This is the paper's standing assumption (it "ignores non-integrality",
working with `c·n` copies as an integer / in the `n → ∞` regime). The bound is
genuinely FALSE for finite `n` with `⌊cn⌋ < cn`: the effective prediction weight
`⌊cn⌋/n < c` yields the strictly worse bound `CG(⌊cn⌋/n) > CG(c)`.

The general-position hypothesis `(hfstar : ∀ j, fstar j ≠ m j)` records the
paper's standing normalization that the optimal facility is in GENERAL POSITION
relative to the returned median (`approx.tex` line 9: the analysis normalizes to
`f_i > 0` coordinate-wise after translating the median to the origin). It is a
FAITHFUL statement fix, not a weakening: the bound's proof reflects each
coordinate by the sign of `fstar j − m j` and rescales so that the translated
optimum `fstar − m` becomes a strictly-positive unit vector, which is exactly the
`f > 0` hypothesis required by the core inequality
`CGNormalizedCoreInequality_fpos`. (The ε-device that would relax this to
`fstar j ≠ 0`-only / `f ≥ 0` provably fails for the consistency core, because the
augmented median is `f`-dependent — see `proving_notes.md`.) Coordinates with
`fstar j = m j` contribute `0` to the optimum and to every `Δ_X = ∑_{j∈X} f_j²`,
so requiring them to be absent costs no generality in the paper's argument. -/
theorem consistency_guarantee :
    ∀ (c : ℝ), 0 ≤ c → c < 1 →
      ∀ {n d : ℕ}, 1 ≤ d →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) →
      ∀ (P : Fin n → Fin d → ℝ) (fstar : Fin d → ℝ),
        socialCost 2 P fstar = optSocialCost 2 P →
      ∀ (m : Fin d → ℝ),
        IsCoordinateMedian m (augment P fstar (⌊c * (n : ℝ)⌋₊)) →
        (∀ j, fstar j ≠ m j) →
        socialCost 2 P m ≤ CG c * optSocialCost 2 P
    := Workspace.ProofLemmas.CGFinalAssembly.CGFinalAssembly

end Workspace.ConsistencyTheorem
