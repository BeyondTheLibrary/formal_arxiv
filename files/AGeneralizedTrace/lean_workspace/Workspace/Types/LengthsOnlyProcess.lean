import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess

open scoped Classical

namespace Workspace.Types.LengthsOnlyProcess

/--
The probability that an iid sequence of `len` Bernoulli(`1 - δ`) trials
produces exactly `z` "kept" outcomes.

Concretely this is `Bin(len, 1 - δ, z) = (len choose z) * (1 - δ)^z * δ^(len - z)`.

Used to model the trace LENGTH produced by passing a binary string of
length `len` through a deletion channel at rate `δ`: each bit is
independently kept with probability `1 - δ`, so the output length is
`Binomial(len, 1 - δ)` regardless of the actual bit values.

If `z > len`, the binomial coefficient `len choose z` is `0`, so this
correctly evaluates to `0` in that case as well.
-/
noncomputable def binomialPMF (len : ℕ) (δ : DelProb) (z : ℕ) : ENNReal :=
  (Nat.choose len z : ENNReal) *
    ENNReal.ofReal ((1 - δ.val) ^ z) *
    ENNReal.ofReal (δ.val ^ (len - z))

/--
The PMF on the LENGTH of the trace produced by passing the prefix
`b[0 .. n/4 + r)` of `b : BinVec n` through the deletion channel at
rate `δ`. Because each bit is kept independently with probability
`1 - δ` regardless of its value, this is a `Binomial(n/4 + r, 1 - δ)`
distribution that does NOT depend on `b`.

For out-of-range offsets `r`, where `r + n/4` falls outside `[0, n/2]`,
the PMF is set to `0`. (The offset weight is also `0` on those `r`,
so the composition law is consistent.) -/
noncomputable def prefixLengthWeight (n : ℕ) (δ : DelProb) (r : ℤ)
    (z : ℕ) : ENNReal :=
  let k : ℤ := r + (n / 4 : ℕ)
  if h : 0 ≤ k ∧ k ≤ (n / 2 : ℕ) then
    -- length of the prefix is `n/4 + r`, written as a `ℕ`.
    binomialPMF k.toNat δ z
  else
    0

/--
The PMF on the LENGTH of the trace produced by passing the suffix
`b[3n/4 + r .. n)` of `b : BinVec n` through the deletion channel at
rate `δ`. Symmetric to `prefixLengthWeight`: each bit is kept
independently with probability `1 - δ`, so the output length is
`Binomial(n - 3*(n/4) - r, 1 - δ)`, again independent of `b`.

The suffix `b[3*(n/4) + r .. n)` has exactly `n - 3*(n/4) - r` indices,
which equals `n - 2*(n/4) - k.toNat` (where `k = r + n/4`). When `n` is
divisible by `4` this simplifies to `n/2 - k.toNat`, but for `n` not
divisible by `4` (e.g. `n % 8 = 1`) the correct length is
`n - 2*(n/4) - k.toNat`, which can exceed `n/2 - k.toNat` by up to one.

For out-of-range offsets `r`, the PMF is `0`. -/
noncomputable def suffixLengthWeight (n : ℕ) (δ : DelProb) (r : ℤ)
    (z : ℕ) : ENNReal :=
  let k : ℤ := r + (n / 4 : ℕ)
  if h : 0 ≤ k ∧ k ≤ (n / 2 : ℕ) then
    -- length of the suffix is `n - (n/4 + n/2) - r = n - n/2 - k.toNat`,
    -- written as a `ℕ`.
    binomialPMF (n - n / 2 - k.toNat) δ z
  else
    0

/--
The **lengths-only process** `LengthsOnlyProcess n S δ`.

Given a length parameter `n`, a probability vector `S : ProbVec n`, and
a deletion probability `δ : DelProb`, this is the joint distribution
over 3-tuples `(M, z₋, z₊)` where:

* `M : BinVec (n/2)` is the (un-deleted) middle segment of the
  underlying binary string `b : BinVec n` at offset `r`,
* `z₋ : ℕ` is the LENGTH of the trace produced by passing the prefix
  `b[0 .. n/4 + r)` through the deletion channel at rate `δ`,
* `z₊ : ℕ` is the LENGTH of the trace produced by passing the suffix
  `b[3n/4 + r .. n)` through the deletion channel at rate `δ`,

with the offset `r : ℤ` (sampled so that `r + n/4` is `Binomial(n/2, 1/2)`)
**marginalised out** of the output. Per Rivkin–Valiant–Valiant (2024),
§3.1 — *"$r$ is crucially **not** returned in this process; instead, $z_-$
and $z_+$ are returned as fuzzy proxies for $r$"*.

This is a simplification of `Workspace.Types.PartialDeletionProcess`:
instead of carrying the full traces `T_init`, `T_final`, the process
records only their LENGTHS. The LENGTH of a trace is sufficient for
the §3.1 analysis of Rivkin–Valiant–Valiant 2024 because — in the
witness construction — the prefix/suffix bits are mostly `0`, making
the trace lengths nearly sufficient statistics. Crucially, the trace
length depends only on the LENGTH of the input segment (not its bit
values), since each bit is deleted independently — so the length-PMFs
factor out of the sum over `b`.

The structure carries a `PMF` on `BinVec (n/2) × ℕ × ℕ` together
with one axiom — `composition_law` — defining its value in terms of
the underlying `CoinFlipDist`, the offset PMF, the prefix-length and
suffix-length binomial PMFs, and the middle-segment indicator. The
auxiliary expressions `offsetWeight` and `middleIndicator` are reused
verbatim from `Workspace.Types.PartialDeletionProcess`. Total mass
being `1` is automatic by `PMF`.
-/
structure LengthsOnlyProcess (n : ℕ) (S : ProbVec n) (δ : DelProb) where
  /-- The underlying probability mass function on the joint output space. -/
  toPMF : PMF (BinVec (n / 2) × ℕ × ℕ)
  /-- Composition-law axiom: the probability of each output 3-tuple
  `(m, z₋, z₊)` is the sum over underlying binary vectors `b` and
  offsets `r : ℤ` of the product of (a) the coin-flip probability of
  `b`, (b) the offset probability of `r`, (c) the prefix-trace-length
  probability that the prefix produces a trace of length `z₋`,
  (d) the suffix-trace-length probability that the suffix produces a
  trace of length `z₊`, and (e) the middle-segment indicator that the
  bits of `b` at positions `n/4 + r, …, 3n/4 + r - 1` equal `m`.

  Since the prefix- and suffix-trace-length PMFs do NOT depend on `b`
  (each bit is kept with probability `1 - δ` regardless of its value),
  the dependence on `b` enters only through the coin-flip PMF and the
  middle-segment indicator. The offset `r` is summed over (marginalised). -/
  composition_law :
    ∀ (cfd : CoinFlipDist n S),
      ∀ (m : BinVec (n / 2)) (zMinus zPlus : ℕ),
        (toPMF : (BinVec (n / 2) × ℕ × ℕ) → ENNReal)
            (m, zMinus, zPlus) =
          ∑' (b : BinVec n) (r : ℤ),
            cfd.toPMF b *
              (offsetWeight n r *
                (prefixLengthWeight n δ r zMinus *
                  (suffixLengthWeight n δ r zPlus *
                    middleIndicator n b m r)))

end Workspace.Types.LengthsOnlyProcess
