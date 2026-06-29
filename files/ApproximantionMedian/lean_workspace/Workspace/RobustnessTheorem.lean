import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.RGFinalAssembly

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem

namespace Workspace.RobustnessTheorem

/-- **Theorem 4 (robustness guarantee of `CMP(c)`).**

For `q = 2` and arbitrary dimension `d ≥ 1`: for EVERY prediction `pred ∈ ℝ^d`,
every coordinate-wise median `m` of the `CMP(c)`-augmented instance
`(P, ⌊c·n⌋ copies of pred)` has social cost on the original agents at most
`RG(c) · OPT₂(P)`. Robustness is the WORST case over ALL predictions: the extra
universal binder `∀ (pred : Fin d → ℝ)` is the only structural difference from the
consistency theorem (Theorem 3), which fixes `pred = fstar`. Here `pred` is
arbitrary while `fstar` remains an optimal facility — it defines `optSocialCost`
and the general-position condition. The bound holds for every prediction because
the worst-case prediction (signature `(−1,…,−1)`) already attains the maximum
`RG(c)`, and every other prediction gives a value `≤ RG(c)`.

The hypothesis `(⌊c·n⌋ : ℝ) = c·n` requires the number of prediction copies to be
integral. This is the paper's standing assumption (it "ignores non-integrality",
working with `c·n` copies as an integer / in the `n → ∞` regime) — the SAME
faithful fix as in consistency (Theorem 3).

The general-position hypothesis `(hgp : ∀ j, fstar j ≠ m j)` records the paper's
standing normalization that the optimal facility is in GENERAL POSITION relative
to the returned median (`approx.tex` line 9: the analysis normalizes to `f_i > 0`
coordinate-wise after translating the median to the origin). It is the SAME
faithful statement fix as in consistency (Theorem 3) — see the
`consistency_guarantee` docstring and `theorem_robustness_text.md`: the bound's
proof reflects each coordinate by the sign of `fstar j − m j` and rescales so that
the translated optimum becomes a strictly-positive unit vector. Coordinates with
`fstar j = m j` contribute `0` to the optimum and to every `Δ_X = ∑_{j∈X} f_j²`,
so requiring them absent costs no generality.

Like `fstar`, the prediction `pred` is assumed in general position relative to the
returned median (`hgp_pred : ∀ j, pred j ≠ m j`): the worst-case-prediction
analysis (`prediction.tex` Lemma `lm:optimal solution for sigma(pred)`) ranges over
predictions with a DEFINITE signature `σ(pred) ∈ {±1}^d` — i.e. `pred_j ≠ m_j` after
translating the median to the origin — so a degenerate `pred_j = m_j` lies outside
the paper's argument. This is the exact analog of the `fstar` general-position fix. -/
theorem robustness_guarantee :
    ∀ (c : ℝ), 0 ≤ c → c < 1 →
      ∀ {n d : ℕ}, 1 ≤ d →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) →
      ∀ (P : Fin n → Fin d → ℝ) (pred : Fin d → ℝ) (fstar : Fin d → ℝ),
        socialCost 2 P fstar = optSocialCost 2 P →
      ∀ (m : Fin d → ℝ),
        IsCoordinateMedian m (augment P pred (⌊c * (n : ℝ)⌋₊)) →
        (∀ j, fstar j ≠ m j) →
        (∀ j, pred j ≠ m j) →
        socialCost 2 P m ≤ RG c * optSocialCost 2 P
    := Workspace.ProofLemmas.RGFinalAssembly.RGFinalAssembly

end Workspace.RobustnessTheorem
