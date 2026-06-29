import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.PriorWork.DataProcessingTV
import Workspace.ProofLemmas.TraceDeletionKernel
import Workspace.ProofLemmas.PartialDominatesAssembly

/-!
# Kernel-side convolution collapse toward the bind identity

This file continues the assembly toward de-axiomatizing
`partial_dominates_traceDist`.  `PartialDominatesAssembly` built the
reconstruction kernel `reconstructKernel` (`K`) and the fixed-offset
three-segment factorization `channel_sum_factor3`.

The remaining bind identity `part.toPMF.bind K = trace.toPMF` is a
**convolution over decompositions** (F14's diagnosis): the target trace
`τ`'s split point is data-dependent, so the channel mass at `τ` is a sum
over decompositions `τ.bits = pre ++ mid ++ suf`, not a product.

This file lands the **kernel-side** half of that convolution sorry-free:

* `concatTrace_eq_of_bits` — the unconditional backward direction: if the
  three bit lists concatenate to `τ.bits`, the reconstruction equals `τ`
  (the length bound is automatic from `τ.bits.length ≤ n`).
* `concatTrace_eq_target_iff` — under the in-range hypothesis, the
  reconstruction `concatTrace pre mid suf` equals `τ` iff the bit lists
  agree.  This is the bridge collapsing the kernel's `concatTrace`-indicator
  to a list equation.
* `concatTrace_eq_unique_mid` — when the prefix/suffix bits match `τ`'s
  outer slices and lengths are compatible, the matching middle bit list is
  the **unique** inner slice `τ.bits.extract t₁.length (τ.length - t₂.length)`.
  This pins the data-dependent boundary that makes the partial process
  (which records the boundary via `r` and `M`) more informative than the
  trace.
* `reconstructKernel_collapse` — the kernel mass at `τ` written as a `tsum`
  over the deleted middle `mid : Trace (n/2)` against the list indicator
  `t₁.bits ++ mid.bits ++ t₂.bits = τ.bits`, **valid when** the prefix and
  suffix already fit inside `τ` (`t₁.bits.length + t₂.bits.length ≤ n`),
  which holds on the partial-deletion process support.  This is exactly the
  convolution form the offset marginalization must match.

The genuinely remaining step (documented at the bottom) is the **offset
marginalization**: re-summing the per-`r` `channel_sum_factor3` against the
binomial `offsetWeight` to match `part.toPMF.bind K` at each `τ`, followed
by `DataProcessingTV reconstructKernel part.toPMF part'.toPMF`.
-/

namespace PartialDominatesConvolution

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open TraceDeletionKernel
open PartialDominatesAssembly

open scoped Classical

/-! ### Collapsing the `concatTrace` indicator to a list equation -/

/-- **Backward direction (unconditional).**  If the concatenated bit lists
equal the target's bits, the reconstructed trace equals the target.  The
length bound on the concatenation is automatic from `τ.bits.length ≤ n`. -/
lemma concatTrace_eq_of_bits {n : ℕ} (pre mid suf : List Bool) (τ : Trace n)
    (hbits : pre ++ mid ++ suf = τ.bits) :
    concatTrace (n := n) pre mid suf = τ := by
  have hlen : (pre ++ mid ++ suf).length ≤ n := by
    rw [hbits]; exact τ.length_le
  unfold concatTrace
  rw [dif_pos hlen]
  cases τ with
  | mk bits length_le =>
    simp only [Trace.mk.injEq]
    exact hbits

/-- **`concatTrace` matches a target iff the bit lists agree**, given the
concatenation is in range.  This is the bridge that collapses the
reconstruction kernel's `concatTrace`-indicator (`reconstructKernel_apply`)
to the list-level decomposition equation. -/
lemma concatTrace_eq_target_iff {n : ℕ} (pre mid suf : List Bool) (τ : Trace n)
    (h : (pre ++ mid ++ suf).length ≤ n) :
    concatTrace (n := n) pre mid suf = τ ↔ pre ++ mid ++ suf = τ.bits := by
  constructor
  · intro heq
    have := congrArg Trace.bits heq
    rwa [concatTrace_bits _ _ _ h] at this
  · intro hbits
    exact concatTrace_eq_of_bits pre mid suf τ hbits

/-- **The matching middle bit list is unique and data-dependent.**  If
`pre ++ mid ++ suf = τ.bits`, then `mid` is determined as the inner slice of
`τ.bits` between the prefix and the suffix.  Concretely `mid` is the sublist
obtained by dropping the first `pre.length` bits and the last `suf.length`
bits of `τ.bits`.  This pins the boundary that the trace alone does not
expose (whence the partial process is strictly more informative). -/
lemma concatTrace_eq_unique_mid {n : ℕ} (pre mid suf : List Bool) (τ : Trace n)
    (hbits : pre ++ mid ++ suf = τ.bits) :
    mid = (τ.bits.drop pre.length).take mid.length := by
  -- `τ.bits = pre ++ (mid ++ suf)`, so dropping `pre.length` yields `mid ++ suf`.
  have hassoc : pre ++ (mid ++ suf) = τ.bits := by
    rw [← List.append_assoc]; exact hbits
  have hdrop : τ.bits.drop pre.length = mid ++ suf := by
    rw [← hassoc, List.drop_left]
  rw [hdrop, List.take_left]

/-! ### The kernel-side convolution -/

/-- **Kernel-side convolution collapse.**  The reconstruction kernel's mass
at an output trace `τ`, written as a `tsum` over the deleted middle
`mid : Trace (n/2)`, weighted by the middle-deletion mass and the indicator
that the three pieces concatenate to `τ`.

The hypothesis `hfit : t₁.bits.length + (n / 2) + t₂.bits.length ≤ n` ensures
every candidate middle (of length `≤ n/2`, by its `Trace (n/2)` type) keeps
the concatenation in range, so the `concatTrace`-indicator collapses to the
list equation.  On the partial-deletion process support the prefix `t₁`,
the `n/2`-length middle `M`, and the suffix `t₂` are disjoint segments of a
single length-`n` string, so this fits.

Combined with the offset marginalization (the remaining step), this matches
`part.toPMF.bind K` at each `τ`. -/
lemma reconstructKernel_collapse {n : ℕ} (δ : DelProb)
    (M : BinVec (n / 2)) (t₁ t₂ : Trace n) (τ : Trace n)
    (hfit : t₁.bits.length + (n / 2) + t₂.bits.length ≤ n) :
    (reconstructKernel δ (M, t₁, t₂) : Trace n → ENNReal) τ
      = ∑' mid : Trace (n / 2),
          (traceDelete δ.val δ.pos.le δ.lt_one.le (fullTrace M) : Trace (n / 2) → ENNReal) mid
            * (if t₁.bits ++ mid.bits ++ t₂.bits = τ.bits then (1 : ENNReal) else 0) := by
  rw [reconstructKernel_apply]
  apply tsum_congr
  intro mid
  congr 1
  -- Every middle has `mid.bits.length ≤ n/2`, so the concat is in range.
  have hmidlen : mid.bits.length ≤ n / 2 := mid.length_le
  have hlen : (t₁.bits ++ mid.bits ++ t₂.bits).length ≤ n := by
    rw [List.length_append, List.length_append]
    omega
  by_cases hb : t₁.bits ++ mid.bits ++ t₂.bits = τ.bits
  · rw [if_pos hb, if_pos ((concatTrace_eq_target_iff _ _ _ _ hlen).mpr hb)]
  · rw [if_neg hb, if_neg (fun hc => hb ((concatTrace_eq_target_iff _ _ _ _ hlen).mp hc))]

/-! ### Precise remaining step toward the full bind identity

With the **kernel side** now reduced (`reconstructKernel_collapse`) to a
`tsum` over the deleted middle against the list-decomposition indicator, the
two halves of the bind identity `part.toPMF.bind K = trace.toPMF` are:

1. **Kernel side (DONE here).**  `K (M, t₁, t₂) τ` is the convolution
   `∑' mid, (middle deletion mass) · [t₁.bits ++ mid.bits ++ t₂.bits = τ.bits]`,
   and the contributing `mid` is the *unique* inner slice of `τ` between the
   prefix and suffix (`concatTrace_eq_unique_mid`).

2. **Offset marginalization (the remaining genuine `tsum`).**  `trace.toPMF τ`
   (after `traceDist_canonical` + `deletionChannel_eq_traceDelete` from
   `TVMonotoneInDelta`) is `∑' b, cfd b · (whole-string deletion at τ)`.  The
   whole-string channel sum at a *fixed* offset `r` factors by
   `PartialDominatesAssembly.channel_sum_factor3` into prefix·middle·suffix
   segment sums with `n₁ = n/4 + r`, `n₂ = n/2`, `n₃ = n - 3n/4 - r`.  The
   partial process carries the boundary data: `offsetWeight n r` (binomial
   over `r`), `prefixWeight`/`suffixWeight` (the segment channel sums against
   `t₁`/`t₂`), and `middleIndicator` (the un-deleted middle `M`).  The
   remaining identity is the `tsum`-over-`r : ℤ` that re-sums the per-`r`
   three-segment factorization against `offsetWeight` and matches it, via the
   kernel-side convolution of step 1, to `part.toPMF.bind K`.  The boundary
   index arithmetic aligning `n₁ + n₂ + n₃ = n` needs the `lenEquiv` /
   `finRange_cast` length cast already used in
   `TVMonotoneInDelta.keep_fullTrace_eq_restrict`.

3. **DPI conclusion.**  Once step 2 yields `part.toPMF.bind reconstructKernel
   = trace.toPMF` (and likewise for `part'` / `trace'`), apply
   `Workspace.PriorWork.DataProcessingTV reconstructKernel part.toPMF
   part'.toPMF` to obtain `TV(trace) ≤ TV(part)` — the conclusion of the
   axiom `partial_dominates_traceDist`.  (`Countable` instances for the trace
   and partial sample spaces are available — `Trace n` via the injective
   `bits`, products of countables.)
-/

end PartialDominatesConvolution
