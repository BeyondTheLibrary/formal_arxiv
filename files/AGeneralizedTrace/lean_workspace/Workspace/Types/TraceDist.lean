import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.DeletionChannel

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.CoinFlipDist
open Workspace.Types.DeletionChannel

namespace Workspace.Types.TraceDist

/--
The full trace distribution `TraceDist n S δ`.

This is the PMF on `Trace n` obtained by composing the two components of the
trace-generation process:

1. Sample a binary vector `b : BinVec n` from the coin-flip distribution
   `CoinFlipDist n S` (i.e. the product of independent `Bernoulli(p_i)`'s
   described by the probability string `S : ProbVec n`).
2. Sample a trace `τ : Trace n` from the deletion-channel distribution
   `DeletionChannel n b δ` with deletion probability `δ : DelProb`.

Formally, for every trace `τ`, the probability assigned by `TraceDist n S δ`
to `τ` equals the iterated sum
`∑' b : BinVec n, (cfd.toPMF b) * ((dc b).toPMF τ)` where `cfd` is any
`CoinFlipDist n S` and `dc` any family of `DeletionChannel n b δ`.

The axiom is quantified over *all* choices of component distributions
`cfd` and `dc`, since a `CoinFlipDist n S` and `DeletionChannel n b δ` are
parameterised structures that abstract the underlying PMFs — the composition
law is thus stated as a universal property relating `toPMF` to any pair of
component distributions.

Total mass being `1` is automatic by `PMF`.
-/
structure TraceDist (n : ℕ) (S : ProbVec n) (δ : DelProb) where
  /-- The underlying probability mass function on traces of length at most `n`. -/
  toPMF : PMF (Trace n)
  /-- Composition-law axiom: the probability assigned to each trace `τ` equals
  the iterated sum over binary vectors `b` of the coin-flip probability of `b`
  times the deletion-channel probability of `τ` given `b`, for every choice
  of component coin-flip distribution `cfd` and per-`b` deletion-channel
  family `dc`. -/
  composition_law :
    ∀ (cfd : CoinFlipDist n S) (dc : ∀ b : BinVec n, DeletionChannel n b δ),
      ∀ τ : Trace n,
        (toPMF : Trace n → ENNReal) τ =
          ∑' b : BinVec n, (cfd.toPMF b) * ((dc b).toPMF τ)

end Workspace.Types.TraceDist
