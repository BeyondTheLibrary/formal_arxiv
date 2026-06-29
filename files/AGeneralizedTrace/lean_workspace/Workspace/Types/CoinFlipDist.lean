import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec

open Workspace.Types.ProbVec Workspace.Types.BinVec

namespace Workspace.Types.CoinFlipDist

/--
The coin-flip distribution on `BinVec n` induced by a probability vector
`S : ProbVec n`.

For a probability string `S = (p_1, ..., p_n)`, this is the probability
measure on `{0,1}^n` where the `i`-th bit is independently `1` with
probability `p_i` and `0` with probability `1 - p_i`.

The only data carried is a `PMF` on `BinVec n`, and the only axiom is the
product-factorisation formula: for every `b : BinVec n`, the probability of
`b` under the PMF equals the product over coordinates of
`p_i` (when `b.bit i = true`) or `1 - p_i` (when `b.bit i = false`).
Total mass being `1` is automatic by `PMF`.
-/
structure CoinFlipDist (n : ℕ) (S : ProbVec n) where
  /-- The underlying probability mass function on `BinVec n`. -/
  toPMF : PMF (BinVec n)
  /-- Product-factorisation axiom: the probability of each binary vector
  equals the product of per-coordinate Bernoulli factors. -/
  prod_factorisation :
    ∀ b : BinVec n,
      toPMF b =
        ∏ i : Fin n,
          ENNReal.ofReal (if b.bit i then S.p i else 1 - S.p i)

end Workspace.Types.CoinFlipDist
