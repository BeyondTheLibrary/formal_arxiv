import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.DeletionChannel
import Workspace.PriorWork.DataProcessingTV
import Workspace.ProofLemmas.TraceDeletionKernel
import Workspace.ProofLemmas.RestrictSegmentFactorization
import Workspace.ProofLemmas.DeletionSegmentFactorization

/-!
# Assembly toward de-axiomatizing `partial_dominates_traceDist`

This file builds the **reconstruction (post-processing) kernel** and the
**fixed-offset three-segment factorization** that the paper's Lemma 6 DPI step
(TV(trace) ≤ TV(partial-deletion process)) rests on.

The paper's argument (Rivkin–Valiant–Valiant 2024, §3.1, Lemma 6): the
partial-deletion process retains MORE information than the trace.  From a
partial-process sample `(M, T_init, T_final)` one reconstructs a genuine trace
by deleting `M`'s bits at rate `δ` and concatenating `T_init ++ (middle) ++
T_final`.  Hence there is a stochastic post-processing kernel `K` with
`part.toPMF.bind K = trace.toPMF`, and the data-processing inequality
(`Workspace.PriorWork.DataProcessingTV`) gives the bound.

What this file lands sorry-free:

* `concatTrace` — the safe three-way list concatenation into a `Trace n`
  (total on the product type, faithful on the in-range support).
* `reconstructKernel` (`K`) — the reconstruction Markov kernel
  `BinVec (n/2) × Trace n × Trace n → PMF (Trace n)`.
* `channel_sum_factor3` — the **fixed-offset three-segment factorization** of
  the deletion-channel keep-set sum: for any observable `g` that factors
  multiplicatively over the two segment cuts (`g (s₁ ++ s₂ ++ s₃) = g₁ s₁ · g₂
  s₂ · g₃ s₃`), the single-mask channel sum over the full string
  `b : BinVec (n₁+n₂+n₃)` factors as the product of the three per-segment
  keep-set sums.  Proved by iterating
  `RestrictSegmentFactorization.restrict_channel_sum_factor`.

**Important modelling note.**  The keep-set sum at a *fixed* target `τ` (point
indicator `g = (· = τ.bits)`) does *not* factor as a product — it is a
*convolution* over the decompositions `τ.bits = pre ++ mid ++ suf`, because the
three segment outputs have random (data-dependent) lengths.  This is exactly why
the partial-deletion process — which records the segment boundary via the offset
`r` and the un-deleted middle `M` — retains strictly more information than the
trace.  The factorization here is therefore stated for a *general factoring
observable*; the point-indicator specialisation is recovered only after the
offset `r` and middle `M` pin the boundary, which is the remaining `tsum`-over-`r`
step (documented at the bottom and in the report).
-/

namespace PartialDominatesAssembly

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.DeletionChannel
open TraceDeletionKernel
open RestrictSegmentFactorization
open DeletionSegmentFactorization

open scoped Classical

/-! ### Safe three-way concatenation into a `Trace n` -/

/-- The "full trace" of a binary vector: its bits in order. -/
def fullTrace {n : ℕ} (b : BinVec n) : Trace n :=
  ⟨List.ofFn b.bit, by rw [List.length_ofFn]⟩

@[simp] lemma fullTrace_bits {n : ℕ} (b : BinVec n) :
    (fullTrace b).bits = List.ofFn b.bit := rfl

/-- Concatenate a prefix, middle and suffix bit list into a `Trace n`.  If the
total length exceeds `n` we fall back to the empty trace (this never happens on
the in-range support of the partial-deletion process, where the three pieces are
the prefix/middle/suffix segments of a single length-`n` string).  Total on the
whole product type, which is what `PMF.map` / `PMF.bind` require. -/
noncomputable def concatTrace {n : ℕ} (pre mid suf : List Bool) : Trace n :=
  if h : (pre ++ mid ++ suf).length ≤ n then
    ⟨pre ++ mid ++ suf, h⟩
  else
    ⟨[], by simp⟩

lemma concatTrace_bits {n : ℕ} (pre mid suf : List Bool)
    (h : (pre ++ mid ++ suf).length ≤ n) :
    (concatTrace (n := n) pre mid suf).bits = pre ++ mid ++ suf := by
  unfold concatTrace
  rw [dif_pos h]

/-- `concatTrace` is injective in its arguments once the segment lengths are
fixed (used to relate the reconstruction kernel to the partial process on its
support).  Concretely: if all three lengths agree and stay in range, equal
concatenations force equal pieces. -/
lemma concatTrace_eq_iff {n : ℕ} (pre mid suf pre' mid' suf' : List Bool)
    (h : (pre ++ mid ++ suf).length ≤ n) (h' : (pre' ++ mid' ++ suf').length ≤ n)
    (hpre : pre.length = pre'.length) (hmid : mid.length = mid'.length) :
    concatTrace (n := n) pre mid suf = concatTrace (n := n) pre' mid' suf'
      ↔ pre = pre' ∧ mid = mid' ∧ suf = suf' := by
  constructor
  · intro heq
    have hb : pre ++ mid ++ suf = pre' ++ mid' ++ suf' := by
      have := congrArg Trace.bits heq
      rwa [concatTrace_bits _ _ _ h, concatTrace_bits _ _ _ h'] at this
    -- Split off the prefix (lengths agree), then the middle.
    rw [List.append_assoc, List.append_assoc] at hb
    have hp : pre = pre' := (List.append_inj_left hb hpre)
    subst hp
    have hms : mid ++ suf = mid' ++ suf' := List.append_cancel_left hb
    have hm : mid = mid' := List.append_inj_left hms hmid
    subst hm
    exact ⟨rfl, rfl, List.append_cancel_left hms⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-! ### The reconstruction kernel `K` -/

/-- **Reconstruction (post-processing) kernel.**  Given a partial-process sample
`(M, T_init, T_final)`, delete `M`'s bits independently at rate `δ` (via the
rate-`δ` trace-deletion kernel applied to the full trace of `M`) and output the
concatenation `T_init ++ (deleted middle) ++ T_final`.  This is the kernel `K`
of the paper's Lemma 6 with `part.toPMF.bind K = trace.toPMF`. -/
noncomputable def reconstructKernel {n : ℕ} (δ : DelProb)
    (s : BinVec (n / 2) × Trace n × Trace n) : PMF (Trace n) :=
  (traceDelete δ.val δ.pos.le δ.lt_one.le (fullTrace s.1)).map
    (fun mid => concatTrace s.2.1.bits mid.bits s.2.2.bits)

/-- Keep-set-sum value of the reconstruction kernel at an output trace `τ`. -/
lemma reconstructKernel_apply {n : ℕ} (δ : DelProb)
    (s : BinVec (n / 2) × Trace n × Trace n) (τ : Trace n) :
    (reconstructKernel δ s : Trace n → ENNReal) τ
      = ∑' mid : Trace (n / 2),
          (traceDelete δ.val δ.pos.le δ.lt_one.le (fullTrace s.1) : Trace (n / 2) → ENNReal) mid
            * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0) := by
  unfold reconstructKernel
  rw [PMF.map_apply]
  apply tsum_congr
  intro mid
  by_cases h : concatTrace (n := n) s.2.1.bits mid.bits s.2.2.bits = τ
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun hc => h hc.symm), mul_zero]

/-! ### Fixed-offset three-segment factorization of the channel keep-set sum -/

/-- The per-segment keep-set sum: the deletion-channel mass that the segment
`c : BinVec k` produces output exactly `target`, weighted by an observable `g`. -/
noncomputable def segSum {k : ℕ} (δ : ℝ) (c : BinVec k) (g : List Bool → ENNReal) :
    ENNReal :=
  ∑ m : Fin k → Bool, g (restrict c m) * ∏ i, wfac δ (m i)

/-- **Two-segment factorization** (re-export of `restrict_channel_sum_factor`).
For a string `b : BinVec (n₁+n₂)` and an observable `g` factoring over the cut,
the full keep-set sum factors as the product of the prefix and suffix segment
sums. -/
theorem channel_sum_factor2 {n₁ n₂ : ℕ} (δ : ℝ) (b : BinVec (n₁ + n₂))
    (g : List Bool → ENNReal) (g₁ g₂ : List Bool → ENNReal)
    (hg : ∀ s₁ s₂ : List Bool, g (s₁ ++ s₂) = g₁ s₁ * g₂ s₂) :
    (∑ m : Fin (n₁ + n₂) → Bool, g (restrict b m) * ∏ i, wfac δ (m i))
      = segSum δ (⟨fun i => b.bit (Fin.castAdd n₂ i)⟩ : BinVec n₁) g₁
        * segSum δ (⟨fun i => b.bit (Fin.natAdd n₁ i)⟩ : BinVec n₂) g₂ := by
  unfold segSum
  exact restrict_channel_sum_factor δ b g g₁ g₂ hg

/-- The per-position weight product over a triple of segment masks factors. -/
private lemma wfac_prod_append3 {n₁ n₂ n₃ : ℕ} (δ : ℝ)
    (m₁ : Fin n₁ → Bool) (m₂ : Fin n₂ → Bool) (m₃ : Fin n₃ → Bool) :
    (∏ i, wfac δ (Fin.append (Fin.append m₁ m₂) m₃ i))
      = (∏ i, wfac δ (m₁ i)) * ((∏ i, wfac δ (m₂ i)) * (∏ i, wfac δ (m₃ i))) := by
  rw [Fin.prod_univ_add (fun i => wfac δ (Fin.append (Fin.append m₁ m₂) m₃ i))]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_add (fun i => wfac δ (Fin.append m₁ m₂ i))]
  simp only [Fin.append_left, Fin.append_right]
  ring

theorem channel_sum_factor3 {n₁ n₂ n₃ : ℕ} (δ : ℝ)
    (b : BinVec (n₁ + n₂ + n₃))
    (g : List Bool → ENNReal) (g₁ g₂ g₃ : List Bool → ENNReal)
    (hg : ∀ s₁ s₂ s₃ : List Bool, g (s₁ ++ s₂ ++ s₃) = g₁ s₁ * (g₂ s₂ * g₃ s₃)) :
    (∑ m : Fin (n₁ + n₂ + n₃) → Bool, g (restrict b m) * ∏ i, wfac δ (m i))
      = segSum δ (⟨fun i => b.bit (Fin.castAdd n₃ (Fin.castAdd n₂ i))⟩ : BinVec n₁) g₁
        * (segSum δ (⟨fun i => b.bit (Fin.castAdd n₃ (Fin.natAdd n₁ i))⟩ : BinVec n₂) g₂
          * segSum δ (⟨fun i => b.bit (Fin.natAdd (n₁ + n₂) i)⟩ : BinVec n₃) g₃) := by
  -- Composite equivalence reindexing the full mask domain as a triple of
  -- per-segment masks, in one shot.
  set e : (((Fin n₁ → Bool) × (Fin n₂ → Bool)) × (Fin n₃ → Bool))
      ≃ (Fin (n₁ + n₂ + n₃) → Bool) :=
    ((Fin.appendEquiv (α := Bool) n₁ n₂).prodCongr (Equiv.refl (Fin n₃ → Bool))).trans
      (Fin.appendEquiv (α := Bool) (n₁ + n₂) n₃) with he
  rw [← e.sum_comp (fun m => g (restrict b m) * ∏ i, wfac δ (m i))]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold segSum
  -- RHS: factor the triple product of segment sums into a triple sum.
  rw [Finset.sum_mul, Finset.sum_mul_sum]
  -- Match termwise over (m₁, m₂, m₃), distributing the per-factor sums.
  apply Finset.sum_congr rfl; intro m₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m₂ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m₃ _
  -- Evaluate `e (m₁, m₂, m₃) = append (append m₁ m₂) m₃`.
  have hinner : (Fin.appendEquiv (α := Bool) n₁ n₂) (m₁, m₂) = Fin.append m₁ m₂ := by
    funext a; rw [Fin.appendEquiv_apply]
  have hem : e ((m₁, m₂), m₃) = Fin.append (Fin.append m₁ m₂) m₃ := by
    rw [he]
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
      id_eq]
    funext a
    rw [Fin.appendEquiv_apply, hinner]
  rw [hem]
  -- restrict b (append (append m₁ m₂) m₃) = pre ++ mid ++ suf.
  have hsplit1 := restrict_split (n₁ := n₁ + n₂) (n₂ := n₃) b
      (Fin.append (Fin.append m₁ m₂) m₃)
  simp only [Fin.append_left, Fin.append_right] at hsplit1
  -- The prefix-middle part `restrict (bPM) (append m₁ m₂)` splits again.
  have hsplit2 := restrict_split (n₁ := n₁) (n₂ := n₂)
      (⟨fun i => b.bit (Fin.castAdd n₃ i)⟩ : BinVec (n₁ + n₂)) (Fin.append m₁ m₂)
  simp only [Fin.append_left, Fin.append_right] at hsplit2
  rw [hsplit1, hsplit2, hg, wfac_prod_append3]
  ring

/-! ### Precise remaining step toward the full bind identity

With `reconstructKernel` (`K`) defined and `channel_sum_factor3` proved, the
remaining work to obtain `part.toPMF.bind K = trace.toPMF` (and hence the DPI
bound via `Workspace.PriorWork.DataProcessingTV`) is:

1. **Offset marginalization (the genuine remaining `tsum`).**  `trace.toPMF τ`
   (after `traceDist_canonical` + `deletionChannel_eq_traceDelete` from
   `TVMonotoneInDelta`) is `∑' b, cfd b * (deletion-channel of the whole string
   b at τ)`.  The whole-string channel sum at a *fixed* offset `r` factors by
   `channel_sum_factor3` into prefix·middle·suffix segment sums with
   `n₁ = n/4 + r`, `n₂ = n/2`, `n₃ = n - 3n/4 - r`.  The partial process
   carries the boundary data: `offsetWeight n r` (binomial over `r`),
   `prefixWeight`/`suffixWeight` (the segment channel sums against `t₁`/`t₂`),
   and `middleIndicator` (the un-deleted middle `M`).  The remaining identity is
   a `tsum`-over-`r : ℤ` that re-sums the per-`r` three-segment factorization
   against the binomial `offsetWeight` and matches it to `part.toPMF.bind K`.

2. **Boundary-index arithmetic.**  `channel_sum_factor3` is stated for the type
   `BinVec (n₁ + n₂ + n₃)`, whereas `b : BinVec n`; aligning `n₁ + n₂ + n₃ = n`
   for the offset-dependent cut points (`n/4 + r`, `n/2`, remainder) requires a
   length cast (the `lenEquiv`/`finRange_cast` pattern already used in
   `TVMonotoneInDelta.keep_fullTrace_eq_restrict`).

3. **Kernel-side convolution.**  `K (M, t₁, t₂) τ` (`reconstructKernel_apply`)
   sums over the deleted middle `mid` of `M` and demands
   `t₁.bits ++ mid.bits ++ t₂.bits = τ.bits`.  Matching this to the middle
   segment sum `segSum δ (middle b) (· = mid)` is exactly the point-indicator
   specialisation `g = (· = τ.bits)` of `channel_sum_factor3`, valid *once the
   offset `r` and middle `M` pin the segment boundary* — which is why the
   factorization is stated for a general factoring observable and the
   point-indicator only appears after step 1's marginalization.
-/

end PartialDominatesAssembly
