import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.ProbVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.DeletionChannel
import Workspace.Types.TraceDist
import Workspace.Types.PartialDeletionProcess
import Workspace.PriorWork.DataProcessingTV
import Workspace.ProofLemmas.TraceDeletionKernel
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.DeletionChannelExists
import Workspace.ProofLemmas.TVMonotoneInDelta
import Workspace.ProofLemmas.PartialDominatesAssembly
import Workspace.ProofLemmas.PartialDominatesConvolution

/-!
# Explicit two-sided form of the bind identity (sorry-free reductions)

This file continues the assembly toward de-axiomatizing
`partial_dominates_traceDist`.  `PartialDominatesAssembly` built the
reconstruction kernel and the fixed-offset three-segment factorization;
`PartialDominatesConvolution` collapsed the kernel side to a convolution.

The genuine remaining wall is the **bind identity**
`part.toPMF.bind reconstructKernel = trace.toPMF`.  Closing it via
`Workspace.PriorWork.DataProcessingTV` requires matching, at every output
trace `τ`, the two explicit `tsum` expressions for the two sides.

This file lands, **sorry-free**, both sides written in their most explicit
form, so that the only remaining task is the per-`τ` algebraic/combinatorial
matching of the two `tsum`s:

* `traceDist_toPMF_eq` — the **trace side**: `td.toPMF τ` equals
  `∑' b, cfd b · (traceDelete δ (fullTrace b)) τ`, obtained from
  `TVMonotoneInDelta.traceDist_canonical` and
  `TVMonotoneInDelta.deletionChannel_eq_traceDelete` against canonical
  coin-flip / deletion-channel witnesses (which exist by
  `CoinFlipDistExists` / `DeletionChannelExists`).

* `bind_reconstruct_apply` — the **bind side**: the value of
  `part.toPMF.bind reconstructKernel` at `τ`, expanded by `PMF.bind_apply`
  into `∑' s, part.toPMF s · (reconstructKernel δ s) τ`.

* `partial_toPMF_eq` — the **partial-process mass** at a sample
  `(m, t₁, t₂)`, rewritten via `composition_law` against a canonical
  coin-flip witness into the explicit `∑' b ∑' r` form with `offsetWeight`,
  `prefixWeight`, `suffixWeight`, `middleIndicator`.

* `bind_reconstruct_explicit` — the bind side fully expanded by substituting
  `partial_toPMF_eq` and `reconstructKernel_apply`: the precise nested
  `tsum` (over `s = (m, t₁, t₂)`, then `b`, `r`, then the deleted middle)
  that the offset marginalization must collapse to the trace side.

After these, the SOLE remaining step (documented at the bottom) is the
per-`τ` identity equating `bind_reconstruct_explicit` to
`traceDist_toPMF_eq`; then `DataProcessingTV` closes the axiom.
-/

namespace PartialDominatesBindForm

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.ProbVec
open Workspace.Types.CoinFlipDist
open Workspace.Types.DeletionChannel
open Workspace.Types.TraceDist
open Workspace.Types.PartialDeletionProcess
open TraceDeletionKernel
open TVMonotoneInDelta
open PartialDominatesAssembly

open scoped Classical

/-! ### Trace side -/

/-- **Trace side, canonical deletion-kernel form.**  The trace distribution's
mass at `τ` is the coin-flip-weighted sum, over underlying strings `b`, of the
rate-`δ` whole-string deletion kernel applied to the full trace of `b`.  This is
the right-hand side that the bind of the partial process through the
reconstruction kernel must reproduce. -/
lemma traceDist_toPMF_eq {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (td : TraceDist n S δ) (cfd : CoinFlipDist n S) (τ : Trace n) :
    (td.toPMF : Trace n → ENNReal) τ
      = ∑' b : BinVec n,
          cfd.toPMF b
            * (traceDelete δ.val δ.pos.le δ.lt_one.le (TVMonotoneInDelta.fullTrace b) : Trace n → ENNReal) τ := by
  -- Canonical deletion-channel family witness.
  let dc : ∀ b : BinVec n, DeletionChannel n b δ := fun b => (DeletionChannelExists b δ).some
  rw [traceDist_canonical td cfd dc, PMF.bind_apply]
  apply tsum_congr
  intro b
  rw [deletionChannel_eq_traceDelete b δ (dc b)]

/-! ### Bind side -/

/-- **Bind side, raw `PMF.bind_apply` expansion.**  The pushforward of the
partial-deletion process through the reconstruction kernel, evaluated at `τ`. -/
lemma bind_reconstruct_apply {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (part : PartialDeletionProcess n S δ) (τ : Trace n) :
    ((part.toPMF.bind (reconstructKernel δ)) : Trace n → ENNReal) τ
      = ∑' s : BinVec (n / 2) × Trace n × Trace n,
          (part.toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal) s
            * (reconstructKernel δ s : Trace n → ENNReal) τ := by
  rw [PMF.bind_apply]

/-- **Partial-process mass, explicit form.**  Using `composition_law` against a
canonical coin-flip witness, the partial process's mass at a sample
`(m, t₁, t₂)` is the explicit double `tsum` over underlying strings `b` and
offsets `r`, weighted by the offset PMF, the prefix/suffix segment channel
sums, and the middle-segment indicator. -/
lemma partial_toPMF_eq {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (part : PartialDeletionProcess n S δ) (cfd : CoinFlipDist n S)
    (m : BinVec (n / 2)) (t₁ t₂ : Trace n) :
    (part.toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal) (m, t₁, t₂)
      = ∑' (b : BinVec n) (r : ℤ),
          cfd.toPMF b *
            (offsetWeight n r *
              (prefixWeight n b δ r t₁ *
                (suffixWeight n b δ r t₂ *
                  middleIndicator n b m r))) := by
  rw [part.composition_law cfd m t₁ t₂]

/-- **Bind side, fully explicit nested-`tsum` form.**  Substituting both the
partial-process mass (`partial_toPMF_eq`) and the reconstruction-kernel value
(`reconstructKernel_apply`) into the raw bind expansion, the bind side at `τ`
is the explicit nested sum: over the sample `(m, t₁, t₂)`, over underlying
strings `b` and offsets `r` (the partial-process structure), times the kernel's
sum over the deleted middle.  This is the precise left-hand side the offset
marginalization must collapse to `traceDist_toPMF_eq`. -/
lemma bind_reconstruct_explicit {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (part : PartialDeletionProcess n S δ) (cfd : CoinFlipDist n S) (τ : Trace n) :
    ((part.toPMF.bind (reconstructKernel δ)) : Trace n → ENNReal) τ
      = ∑' s : BinVec (n / 2) × Trace n × Trace n,
          (∑' (b : BinVec n) (r : ℤ),
            cfd.toPMF b *
              (offsetWeight n r *
                (prefixWeight n b δ r s.2.1 *
                  (suffixWeight n b δ r s.2.2 *
                    middleIndicator n b s.1 r))))
          * (∑' mid : Trace (n / 2),
              (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1) : Trace (n / 2) → ENNReal) mid
                * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)) := by
  rw [bind_reconstruct_apply]
  apply tsum_congr
  rintro ⟨m, t₁, t₂⟩
  rw [partial_toPMF_eq part cfd m t₁ t₂, reconstructKernel_apply]

/-! ### Trace side, whole-string `restrict`/`wfac` keep-set form -/

/-- **Whole-string keep-set form of the trace side's inner kernel.**  The
rate-`δ` whole-string deletion kernel applied to the full trace of `b`, at output
`τ`, equals the single mask sum over `Fin n → Bool` of the keep indicator
`[restrict b m = τ.bits]` times the per-coordinate Bernoulli weight product
`∏ i, wfac δ (m i)`.  This is the `restrict`/`wfac` normal form that the offset
marginalization of the bind side must reproduce.  Obtained from
`traceDelete_apply` by reindexing the mask domain `Fin (fullTrace b).bits.length`
to `Fin n` through `lenEquiv` (exactly as in
`TVMonotoneInDelta.deletionChannel_eq_traceDelete`). -/
lemma traceDelete_fullTrace_restrict_form {n : ℕ} (b : BinVec n) (δ : DelProb) (τ : Trace n) :
    (traceDelete δ.val δ.pos.le δ.lt_one.le (TVMonotoneInDelta.fullTrace b) : Trace n → ENNReal) τ
      = ∑ m : Fin n → Bool,
          (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
            ∏ i : Fin n, RestrictSegmentFactorization.wfac δ.val (m i) := by
  rw [traceDelete_apply δ.val δ.pos.le δ.lt_one.le (TVMonotoneInDelta.fullTrace b) τ]
  rw [← Equiv.sum_comp (Equiv.arrowCongr (TVMonotoneInDelta.lenEquiv b).symm (Equiv.refl Bool))
        (fun m => (if keep (TVMonotoneInDelta.fullTrace b) m = τ.bits then (1 : ENNReal) else 0) *
          ∏ i : Fin (TVMonotoneInDelta.fullTrace b).bits.length,
            (if m i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val))]
  apply Finset.sum_congr rfl
  intro m _
  have heq : (Equiv.arrowCongr (TVMonotoneInDelta.lenEquiv b).symm (Equiv.refl Bool)) m
      = (fun j => m ((TVMonotoneInDelta.lenEquiv b) j)) := by
    funext j; rfl
  rw [heq]
  rw [TVMonotoneInDelta.keep_fullTrace_eq_restrict b m]
  congr 1
  rw [← Equiv.prod_comp (TVMonotoneInDelta.lenEquiv b)
        (fun i => RestrictSegmentFactorization.wfac δ.val (m i))]
  apply Finset.prod_congr rfl
  intro i _
  unfold RestrictSegmentFactorization.wfac
  rfl

/-! ### Fubini reorder: pull the underlying-string sum `∑' b` outermost -/

/-- **Fubini reorder of the bind side.**  Everything is `ENNReal`, so the nested
`tsum`s of `bind_reconstruct_explicit` may be freely reordered (no summability
side-conditions).  We pull the underlying-string sum `∑' b` to the outside and
factor out the coin-flip weight `cfd b`, leaving — per `b` — the offset sum
`∑' r` of the offset weight times the three segment factors times the
kernel-side middle convolution, summed over the partial-process sample
`s = (m, t₁, t₂)`.  This is the form on which the per-`(b, r)` three-segment
factorization (`channel_sum_factor3`) and the offset marginalization act. -/
lemma bind_reconstruct_fubini {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (part : PartialDeletionProcess n S δ) (cfd : CoinFlipDist n S) (τ : Trace n) :
    ((part.toPMF.bind (reconstructKernel δ)) : Trace n → ENNReal) τ
      = ∑' b : BinVec n,
          cfd.toPMF b *
            ∑' (s : BinVec (n / 2) × Trace n × Trace n) (r : ℤ),
              (offsetWeight n r *
                (prefixWeight n b δ r s.2.1 *
                  (suffixWeight n b δ r s.2.2 *
                    middleIndicator n b s.1 r)))
              * (∑' mid : Trace (n / 2),
                  (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1) : Trace (n / 2) → ENNReal) mid
                    * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)) := by
  rw [bind_reconstruct_explicit]
  -- Name the kernel-side convolution factor `K s` (depends only on `s`).
  set K : (BinVec (n / 2) × Trace n × Trace n) → ENNReal :=
    fun s => ∑' mid : Trace (n / 2),
        (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1) : Trace (n / 2) → ENNReal) mid
          * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)
    with hK
  -- Name the per-(b,r,s) inner weight `W b r s`.
  set W : BinVec n → ℤ → (BinVec (n / 2) × Trace n × Trace n) → ENNReal :=
    fun b r s =>
      offsetWeight n r *
        (prefixWeight n b δ r s.2.1 *
          (suffixWeight n b δ r s.2.2 *
            middleIndicator n b s.1 r))
    with hW
  -- LHS after naming: ∑' s, (∑' b, cfd b * ∑' r, W b r s) * K s.
  have hlhs : (∑' s : BinVec (n / 2) × Trace n × Trace n,
        (∑' (b : BinVec n) (r : ℤ), cfd.toPMF b * W b r s) * K s)
      = ∑' s : BinVec (n / 2) × Trace n × Trace n,
          ∑' b : BinVec n, (cfd.toPMF b * (∑' r : ℤ, W b r s)) * K s := by
    apply tsum_congr; intro s
    rw [ENNReal.tsum_mul_right]
    congr 1
    apply tsum_congr; intro b
    rw [← ENNReal.tsum_mul_left]
  rw [hlhs]
  -- Swap ∑' s and ∑' b.
  rw [ENNReal.tsum_comm]
  -- Per b: factor cfd b out of the s-sum.
  apply tsum_congr; intro b
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr; intro s
  -- (cfd b * (∑' r, W b r s)) * K s = cfd b * ((∑' r, W b r s) * K s).
  rw [mul_assoc, ENNReal.tsum_mul_right]

/-! ### Reduction of the bind identity to a single per-`b` scalar identity -/

/-- **Bind identity from the per-`b` core identity.**  Combining the trace side
(`traceDist_toPMF_eq` + `traceDelete_fullTrace_restrict_form`) and the bind side
(`bind_reconstruct_fubini`), the full bind identity `part.toPMF.bind K =
trace.toPMF` (as PMFs) follows from the SINGLE remaining per-`b` scalar identity
`hcore`: for every underlying string `b` and every output trace `τ`, the
offset-marginalized three-segment convolution of the partial process equals the
whole-string keep-set sum.  This isolates the genuine combinatorial wall (offset
marginalization + three-segment factorization) into one explicit equation, with
all the `tsum`/Fubini/PMF plumbing discharged sorry-free. -/
lemma bind_identity_of_per_b {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (td : TraceDist n S δ) (part : PartialDeletionProcess n S δ) (cfd : CoinFlipDist n S)
    (hcore : ∀ (b : BinVec n) (τ : Trace n),
      (∑' (s : BinVec (n / 2) × Trace n × Trace n) (r : ℤ),
          (offsetWeight n r *
            (prefixWeight n b δ r s.2.1 *
              (suffixWeight n b δ r s.2.2 *
                middleIndicator n b s.1 r)))
          * (∑' mid : Trace (n / 2),
              (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1) : Trace (n / 2) → ENNReal) mid
                * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)))
        = ∑ m : Fin n → Bool,
            (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
              ∏ i : Fin n, RestrictSegmentFactorization.wfac δ.val (m i)) :
    part.toPMF.bind (reconstructKernel δ) = td.toPMF := by
  apply PMF.ext
  intro τ
  rw [bind_reconstruct_fubini part cfd τ, traceDist_toPMF_eq td cfd τ]
  apply tsum_congr
  intro b
  rw [traceDelete_fullTrace_restrict_form b δ τ, hcore b τ]

/-! ### Precise remaining step toward the bind identity

**STATUS.**  The bind identity `part.toPMF.bind reconstructKernel = trace.toPMF`
is now reduced — *sorry-free, only Mathlib axioms* — to a SINGLE explicit
per-`b` scalar equation by `bind_identity_of_per_b`.  The plumbing discharged
sorry-free here:

* `bind_reconstruct_fubini` — Fubini-reorders the bind side, pulling `∑' b`
  outermost and factoring `cfd b` out (pure `ENNReal` `tsum` algebra, no
  summability side-goals).
* `traceDelete_fullTrace_restrict_form` — rewrites the trace side's inner kernel
  value into the whole-string `restrict`/`wfac` keep-set sum (via the `lenEquiv`
  mask-domain reindex).
* `bind_identity_of_per_b` — combines the two with `traceDist_toPMF_eq` and
  reduces the whole PMF identity to the per-`b` hypothesis `hcore`.

**THE EXACT REMAINING `have`** (the hypothesis `hcore` of
`bind_identity_of_per_b`):  for every `b : BinVec n` and `τ : Trace n`,
```
∑' (s : BinVec (n/2) × Trace n × Trace n) (r : ℤ),
    (offsetWeight n r *
      (prefixWeight n b δ r s.2.1 *
        (suffixWeight n b δ r s.2.2 * middleIndicator n b s.1 r)))
    * (∑' mid, traceDelete δ (fullTrace s.1) mid
         * [concatTrace s.2.1.bits mid.bits s.2.2.bits = τ])
  = ∑ m : Fin n → Bool, [restrict b m = τ.bits] * ∏ i, wfac δ (m i).
```
This is the genuine combinatorial wall (offset marginalization + three-segment
factorization). Its proof still needs new offset-cast infrastructure mapping the
`ℤ`-offset masked `prefixWeight`/`suffixWeight` (sums over `Fin n → Bool` with
`ℤ` index comparisons) to the fixed-width segment sums `segSum δ _ _` over
`BinVec (n/4+r)` / `BinVec (n - 3n/4 - r)`, then `channel_sum_factor3` with cut
points `n₁ = n/4+r`, `n₂ = n/2`, `n₃ = n - 3n/4 - r`, then the binomial
`offsetWeight`-against-`r` marginalization. Once `hcore` is proved,
`bind_identity_of_per_b` yields the bind identity, and
`Workspace.PriorWork.DataProcessingTV reconstructKernel part.toPMF part'.toPMF`
closes `partial_dominates_traceDist`.

---

For reference, both sides of the bind identity
`part.toPMF.bind reconstructKernel = trace.toPMF` are now in fully explicit
`tsum` form (per output trace `τ`):

* **Trace side** (`traceDist_toPMF_eq`):
  `∑' b, cfd b · (traceDelete δ (fullTrace b)) τ`, where (by
  `TraceDeletionKernel.traceDelete_apply`) the inner kernel value is the
  single whole-string keep-set sum
  `∑_{m : Fin n → Bool} [keep (fullTrace b) m = τ.bits] · ∏ i, wfac δ (m i)`.

* **Bind side** (`bind_reconstruct_explicit`): the sample sum `∑' (m,t₁,t₂)`
  of `(∑' b ∑' r  cfd b · offsetWeight · prefixWeight · suffixWeight ·
  middleIndicator) · (∑' mid, middle-deletion mass · [t₁ ++ mid ++ t₂ = τ])`.

The SOLE remaining task is the per-`τ` identity equating these two `tsum`s.
The combinatorial heart is:

1. **Fubini / reorder** the bind side to pull the `∑' b` outermost (everything
   is `ENNReal`, so `ENNReal.tsum_comm` / `ENNReal.tsum_mul_left` apply with no
   summability side-conditions), giving, per `b`,
   `cfd b · ∑' r, offsetWeight n r · (∑'_{(m,t₁,t₂)} prefixWeight · suffixWeight
   · middleIndicator · (middle-deletion convolution at τ))`.

2. **Per-`(b, r)` three-segment factorization.**  At a fixed offset `r`, the
   inner sample sum is the convolution over decompositions
   `τ.bits = t₁.bits ++ mid.bits ++ t₂.bits` of the product of the prefix
   channel sum (against `t₁`), the middle-deletion mass (re-deleting the
   un-deleted middle `M = m` recorded by `middleIndicator`), and the suffix
   channel sum (against `t₂`).  This is exactly
   `PartialDominatesAssembly.channel_sum_factor3` with cut points
   `n₁ = n/4 + r`, `n₂ = n/2`, `n₃ = n - 3n/4 - r`, applied to the
   point-indicator `g = (· = τ.bits)` (whose factorization across the two cuts
   is reintroduced by summing over the decomposition, per
   `PartialDominatesConvolution.concatTrace_eq_unique_mid`).

3. **Offset marginalization.**  Summing the per-`r` factorization against
   `offsetWeight n r` collapses the offset to recover the single whole-string
   keep-set sum of the trace side.  The boundary-index arithmetic aligning
   `n₁ + n₂ + n₃ = n` uses the `lenEquiv` / `finRange_cast` length cast already
   established in `TVMonotoneInDelta`.

Once this per-`τ` identity is proved — i.e.
`part.toPMF.bind reconstructKernel = trace.toPMF` (and the same for
`part'` / `trace'`) — the axiom's conclusion follows immediately from
`Workspace.PriorWork.DataProcessingTV reconstructKernel part.toPMF
part'.toPMF`: its left side is `TVDistance` of the two bound (= trace)
PMFs, its right side is the partial-process TV in the axiom's statement.
`Countable` instances for `Trace n` and the product sample space are
available (the former via injective `bits`).
-/

end PartialDominatesBindForm
