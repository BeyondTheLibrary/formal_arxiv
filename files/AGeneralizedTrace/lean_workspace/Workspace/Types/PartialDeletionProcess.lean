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

open scoped Classical

namespace Workspace.Types.PartialDeletionProcess

/--
The offset PMF used by the partial-deletion process.

Given a length parameter `n`, the offset `r : ℤ` is sampled so that
`r + n/4` is `Binomial(n/2, 1/2)`. Concretely, the probability assigned
to `r` is

  `(n/2 choose (r + n/4))_+ * (1/2)^(n/2)`

where the binomial coefficient is `0` whenever `r + n/4` falls outside
`{0, …, n/2}`.

This is expressed inline (not as a separate type) — it is only ever
referenced by `composition_law`. -/
noncomputable def offsetWeight (n : ℕ) (r : ℤ) : ENNReal :=
  let k : ℤ := r + (n / 4 : ℕ)
  if h : 0 ≤ k ∧ k ≤ (n / 2 : ℕ) then
    (Nat.choose (n / 2) k.toNat : ENNReal) * (ENNReal.ofReal (1 / 2)) ^ (n / 2)
  else
    0

/--
For an output `m : BinVec (n/2)` and an offset `r : ℤ`, this is the
indicator (as `ENNReal` `0`/`1`) that the middle segment of the
underlying string `b : BinVec n` — namely the bits at positions
`n/4 + r + 1, …, 3n/4 + r` — equals `m`.

We require that the integer index `n/4 + r + j` (for `j : Fin (n/2)`)
lies in the range `[0, n)`. If not — i.e. `r` is out of range — the
indicator is `0`, since the middle segment isn't well-defined and the
offset PMF assigns weight `0` to such `r` anyway.
-/
noncomputable def middleIndicator (n : ℕ) (b : BinVec n) (m : BinVec (n / 2))
    (r : ℤ) : ENNReal :=
  if h : ∀ j : Fin (n / 2),
      0 ≤ ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) ∧
      ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) then
    if (∀ j : Fin (n / 2),
        b.bit ⟨(((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat,
          by
            have hj := h j
            have hlt := hj.2
            have hnonneg := hj.1
            -- toNat of a nonneg integer is < n.
            have : (((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat < n := by
              have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
                  = ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hnonneg
              have : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by
                rw [h0]; exact hlt
              exact_mod_cast this
            exact this⟩
        = m.bit j) then 1 else 0
  else 0

/--
The "prefix-deletion" mask predicate: a mask `μ : Fin n → Bool` is a
valid prefix mask for offset `r` if it is `false` everywhere on indices
`i ≥ n/4 + r`. (When `r` is out of range we make it the always-false
predicate so the corresponding sum vanishes against the offset weight.)

Together with the keep-set-sum formula (see `prefixWeight`), this models
sending the prefix `b[0 .. n/4 + r)` through the deletion channel.
-/
noncomputable def isPrefixMask (n : ℕ) (r : ℤ) (μ : Fin n → Bool) : Prop :=
  ∀ i : Fin n, ((i : ℤ) ≥ ((n / 4 : ℕ) : ℤ) + r) → μ i = false

/--
Symmetrically, the "suffix-deletion" mask predicate: a mask is a valid
suffix mask for offset `r` if it is `false` everywhere on indices
`i < 3n/4 + r`. Models sending `b[3n/4 + r .. n)` through the deletion
channel.
-/
noncomputable def isSuffixMask (n : ℕ) (r : ℤ) (μ : Fin n → Bool) : Prop :=
  ∀ i : Fin n, ((i : ℤ) < ((n / 4 + n / 2 : ℕ) : ℤ) + r) → μ i = false

/--
The keep-set sum giving the probability that the prefix
`b[0 .. n/4 + r)` produces trace `t₁` after independent deletion at
rate `δ`. We use the same formulation as `DeletionChannel`'s
`pmf_eq_keep_set_sum`, restricting the mask to the prefix range.

Bits outside the prefix range are forced to `false` in the mask, so
they contribute a factor `δ` per coordinate (they are "deleted") — we
divide that systematic contribution out by also requiring that mask
equals `false` outside, but we additionally need the mask to behave as
a kept-or-dropped indicator only inside the prefix. The cleanest
expression is:

  ∑_{μ : Fin n → Bool, isPrefixMask r μ}
    (if restrict b μ = t₁.bits then 1 else 0) *
    ∏_{i : Fin n, (i : ℤ) < n/4 + r}
      (if μ i then ofReal (1 - δ) else ofReal δ)

with the product taken only over the prefix indices (the indices outside
contribute a factor of `1`, since their `μ i` is forced `false` but they
don't count toward the deletion probability of the prefix segment).
-/
noncomputable def prefixWeight (n : ℕ) (b : BinVec n) (δ : DelProb)
    (r : ℤ) (t₁ : Trace n) : ENNReal :=
  ∑ μ : Fin n → Bool,
    (if isPrefixMask n r μ ∧ restrict b μ = t₁.bits then (1 : ENNReal) else 0) *
      ∏ i : Fin n,
        (if ((i : ℤ) < ((n / 4 : ℕ) : ℤ) + r) then
            (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)
          else 1)

/-- Symmetric to `prefixWeight`, for the suffix `b[3n/4 + r .. n)`. -/
noncomputable def suffixWeight (n : ℕ) (b : BinVec n) (δ : DelProb)
    (r : ℤ) (t₂ : Trace n) : ENNReal :=
  ∑ μ : Fin n → Bool,
    (if isSuffixMask n r μ ∧ restrict b μ = t₂.bits then (1 : ENNReal) else 0) *
      ∏ i : Fin n,
        (if ((i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r) then
            (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)
          else 1)

/--
The **partial-deletion process** `PartialDeletionProcess n S δ`.

Given a length parameter `n`, a probability vector `S : ProbVec n`, and
a deletion probability `δ : DelProb`, this is the joint distribution
over 3-tuples `(M, T_init, T_final)` where:

* `M : BinVec (n/2)` is the (un-deleted) middle segment of the
  underlying binary string `b : BinVec n` at offset `r`,
* `T_init : Trace n` is the trace produced by passing the prefix
  `b[0 .. n/4 + r)` through the deletion channel at rate `δ`,
* `T_final : Trace n` is the trace produced by passing the suffix
  `b[3n/4 + r .. n)` through the deletion channel at rate `δ`,

with the offset `r : ℤ` (sampled so that `r + n/4` is `Binomial(n/2, 1/2)`)
**marginalised out** of the output. Per Rivkin–Valiant–Valiant (2024),
§3.1 — `r` is not returned by the process.

(See §3.1 of Rivkin–Valiant–Valiant 2024 for context.)

The structure carries a `PMF` on `BinVec (n/2) × Trace n × Trace n`
together with one axiom — `composition_law` — defining its value in
terms of the underlying `CoinFlipDist`, the offset PMF, the two
deletion-channel-style sums on the prefix and suffix, and the middle-
segment indicator. The components `CoinFlipDist`, `prefixWeight`,
`suffixWeight`, `offsetWeight`, and `middleIndicator` are kept as
auxiliary expressions: only `CoinFlipDist` is itself a structure (since
it appears as a parameter of the axiom).

Total mass being `1` is automatic by `PMF`.
-/
structure PartialDeletionProcess (n : ℕ) (S : ProbVec n) (δ : DelProb) where
  /-- The underlying probability mass function on the joint output space. -/
  toPMF : PMF (BinVec (n / 2) × Trace n × Trace n)
  /-- Composition-law axiom: the probability of each output 3-tuple
  `(m, t₁, t₂)` is the sum over underlying binary vectors `b` and
  offsets `r : ℤ` of the product of (a) the coin-flip probability of
  `b`, (b) the offset probability of `r`, (c) the prefix-deletion-
  channel probability that `b[0 .. n/4 + r)` becomes `t₁`, (d) the
  suffix-deletion-channel probability that `b[3n/4 + r .. n)` becomes
  `t₂`, and (e) the middle-segment indicator that the bits of `b` at
  positions `n/4 + r, …, 3n/4 + r - 1` equal `m`.

  The axiom is universally quantified over the coin-flip-distribution
  parameter, since `CoinFlipDist n S` is a parameterised structure
  abstracting an underlying PMF; the law is thus stated as a universal
  property relating `toPMF` to any choice of underlying coin-flip
  distribution. The offset `r` is summed over (marginalised). -/
  composition_law :
    ∀ (cfd : CoinFlipDist n S),
      ∀ (m : BinVec (n / 2)) (t₁ t₂ : Trace n),
        (toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal)
            (m, t₁, t₂) =
          ∑' (b : BinVec n) (r : ℤ),
            cfd.toPMF b *
              (offsetWeight n r *
                (prefixWeight n b δ r t₁ *
                  (suffixWeight n b δ r t₂ *
                    middleIndicator n b m r)))

end Workspace.Types.PartialDeletionProcess
