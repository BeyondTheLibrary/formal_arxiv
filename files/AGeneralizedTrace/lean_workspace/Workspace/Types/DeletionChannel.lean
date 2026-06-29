import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb

namespace Workspace.Types.DeletionChannel

/--
Given a `BinVec n` `b` and a mask `m : Fin n → Bool`, return the list of bits
of `b` at positions where `m` is true, in the original order.

This is the "restriction of `b` to the keep-set `K = {i | m i = true}`", i.e.,
what the deletion channel outputs when the keep-set is `K`.
-/
def restrict {n : ℕ} (b : BinVec n) (m : Fin n → Bool) : List Bool :=
  (List.finRange n).filterMap (fun i => if m i then some (b.bit i) else none)

/--
The deletion-channel Markov kernel.

Given:
* a length-`n` binary vector `b : BinVec n`,
* a deletion probability `δ : DelProb`,

`DeletionChannel n b δ` packages
* a `PMF (Trace n)` describing the distribution over observed traces, and
* an axiom characterising that PMF as a sum over keep-sets (encoded as masks
  `m : Fin n → Bool`):

    toPMF τ =
      ∑_{m : Fin n → Bool}
        (if restrict b m = τ.bits then 1 else 0) *
        ∏_{i : Fin n}
          (if m i
             then ENNReal.ofReal (1 - δ.val)
             else ENNReal.ofReal δ.val)

Semantically: independently for each `i : Fin n`, keep `b.bit i` with
probability `1 - δ` and drop it with probability `δ`, then concatenate the
kept bits in their original order.

The axiom is a `Prop`-valued field; instantiation does not require proving
it — it is stated as the defining property of the kernel. -/
structure DeletionChannel (n : ℕ) (b : BinVec n) (δ : DelProb) where
  /-- The output distribution over traces. -/
  toPMF : PMF (Trace n)
  /-- The defining keep-set sum formula for the PMF of each trace. -/
  pmf_eq_keep_set_sum :
    ∀ τ : Trace n,
      (toPMF : Trace n → ENNReal) τ =
        ∑ m : Fin n → Bool,
          (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
            ∏ i : Fin n,
              (if m i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)

end Workspace.Types.DeletionChannel
