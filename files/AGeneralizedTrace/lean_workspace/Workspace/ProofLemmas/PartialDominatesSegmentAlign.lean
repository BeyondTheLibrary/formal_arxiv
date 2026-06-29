import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.DeletionChannel
import Workspace.ProofLemmas.TraceDeletionListCompose
import Workspace.ProofLemmas.DeletionSegmentFactorization
import Workspace.ProofLemmas.RestrictSegmentFactorization
import Workspace.ProofLemmas.PartialDominatesAssembly
import Workspace.ProofLemmas.PartialDominatesSegmentCast

/-!
# Segment-alignment lemmas (a) and (b) for the `hcore` offset cast

This file lands, **sorry-free**, the two genuine "weight-product alignment"
steps the `hcore` reduction of `PartialDominatesBindForm.bind_identity_of_per_b`
requires:

* **(a) prefix alignment** (`prefixWindow_eq_segSum`): the offset-`r` masked
  prefix sum — a sum over masks `μ : Fin (k + m) → Bool` constrained to be
  `false` outside the prefix window `Fin k`, with the per-index weight product
  gated `if i < k then bernoulli else 1` — equals the fixed-width segment sum
  `segSum δ (prefix-segment of b) g` over `BinVec k`.

* **(b) suffix mirror** (`suffixWindow_eq_segSum`): the mirror image — a sum over
  masks constrained to be `false` on the prefix block `Fin k`, with the per-index
  weight product gated `if i ≥ k then bernoulli else 1` (i.e. active only on the
  suffix window `Fin m`) — equals the fixed-width segment sum
  `segSum δ (suffix-segment of b) g` over `BinVec m`.

Both are stated in the **cast-free `k + m` shape** (matching
`channel_sum_factor3`, which is phrased for `BinVec (n₁ + n₂ + n₃)`), so no
`ℤ → ℕ` `Fin.cast` is needed at this layer.  Together with
`PartialDominatesSegmentCast.{restrict_truncate_add, false_tail_mask_sum_collapse}`
(F56) and `restrict_truncate_prefix` / `prefix_false_mask_sum_collapse` proved
here as the suffix-side mirrors, these are exactly the masked-sum → `segSum`
bridges that feed `channel_sum_factor3` once the integer window length is fixed.

The genuine still-open remainder (the binomial `offsetWeight`-vs-`r:ℤ`
marginalization, plus the `ℤ → ℕ` alignment `(n/4 + r).toNat = k`) is documented
at the bottom and in `lean_knowledge.md`.
-/

namespace PartialDominatesSegmentAlign

open Workspace.Types.BinVec
open Workspace.Types.DeletionChannel
open TraceDeletionListCompose
open DeletionSegmentFactorization
open RestrictSegmentFactorization
open PartialDominatesSegmentCast

open scoped Classical

/-! ### (a) Prefix-window weight equals the prefix segment sum -/

/-- **Per-index weight product collapses to the prefix block (prefix case).**
For a mask `μ : Fin (k + m) → Bool` that is `false` on the suffix block
(`Fin.natAdd k`), the full per-index Bernoulli product gated `if i < k` equals
the clean product of `wfac δ` over the prefix masks `μ ∘ Fin.castAdd m`.  The
gate `if i < k` is `true` exactly on the prefix block `Fin.castAdd m i` and
`false` on the suffix block, where the mask is forced `false` (contributing the
neutral factor `wfac δ false`'s gate value `1`). -/
lemma wfac_prod_prefix_gate {k m : ℕ} (δ : ℝ) (μ : Fin (k + m) → Bool) :
    (∏ i : Fin (k + m),
        (if (i : ℕ) < k then wfac δ (μ i) else 1))
      = ∏ i : Fin k, wfac δ (μ (Fin.castAdd m i)) := by
  rw [Fin.prod_univ_add
        (f := fun i : Fin (k + m) => if (i : ℕ) < k then wfac δ (μ i) else 1)]
  have hpre : (∏ i : Fin k,
        (if ((Fin.castAdd m i : Fin (k + m)) : ℕ) < k then wfac δ (μ (Fin.castAdd m i)) else 1))
      = ∏ i : Fin k, wfac δ (μ (Fin.castAdd m i)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos]
    simpa using i.isLt
  have hsuf : (∏ i : Fin m,
        (if ((Fin.natAdd k i : Fin (k + m)) : ℕ) < k then wfac δ (μ (Fin.natAdd k i)) else 1))
      = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [if_neg]
    simp [Fin.natAdd]
  rw [hpre, hsuf, mul_one]

/-- **(a) Prefix-window weight equals the prefix segment sum.**  The offset-`r`
masked prefix sum — over masks `μ : Fin (k + m) → Bool` constrained to be `false`
on the suffix block, with the keep-indicator `g (restrict b μ)` and the per-index
weight product gated `if i < k` — equals the fixed-width segment sum
`segSum δ (prefix-segment of b) g` over `BinVec k`.

This is the prefix half of casting `prefixWeight`'s `Fin n → Bool` masked sum
(constrained `false` outside the prefix window) to a clean `BinVec k` segment
sum, the form `channel_sum_factor3` consumes.  It combines F56's
`false_tail_mask_sum_collapse` (mask-domain reindex), `restrict_truncate_add`
(restrict drops the false tail), and `wfac_prod_prefix_gate` (weight product
collapse). -/
theorem prefixWindow_eq_segSum {k m : ℕ} (δ : ℝ) (b : BinVec (k + m))
    (g : List Bool → ENNReal) :
    (∑ μ : Fin (k + m) → Bool,
        (if (∀ i : Fin m, μ (Fin.natAdd k i) = false) then
            g (restrict b μ) *
              ∏ i : Fin (k + m), (if (i : ℕ) < k then wfac δ (μ i) else 1)
          else 0))
      = PartialDominatesAssembly.segSum δ
          (⟨fun i => b.bit (Fin.castAdd m i)⟩ : BinVec k) g := by
  -- Collapse the false-tail mask sum to a sum over prefix masks `ν : Fin k → Bool`.
  rw [false_tail_mask_sum_collapse
        (fun μ => g (restrict b μ) *
          ∏ i : Fin (k + m), (if (i : ℕ) < k then wfac δ (μ i) else 1))]
  unfold PartialDominatesAssembly.segSum
  apply Finset.sum_congr rfl
  intro ν _
  -- The extended mask `Fin.append ν (fun _ => false)` is `false` on the tail.
  have hfalse : ∀ i : Fin m, (Fin.append ν (fun _ => false)) (Fin.natAdd k i) = false := by
    intro i; rw [Fin.append_right]
  -- restrict drops the false tail, leaving the prefix restrict.
  rw [restrict_truncate_add b (Fin.append ν (fun _ => false)) hfalse]
  -- The prefix-part of the extended mask is `ν`.
  have hpref : (fun i => (Fin.append ν (fun _ => false)) (Fin.castAdd m i)) = ν := by
    funext i; rw [Fin.append_left]
  rw [hpref]
  -- The weight product collapses to the clean prefix `wfac` product.
  rw [wfac_prod_prefix_gate δ (Fin.append ν (fun _ => false))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.append_left]

/-! ### (b) Suffix-window weight equals the suffix segment sum -/

/-- **`restrict` drops a `false` prefix (cast-free segment form).**  Mirror of
`PartialDominatesSegmentCast.restrict_truncate_add`: if the mask `μ` is `false`
on the entire first segment (`Fin k`, indexed by `Fin.castAdd m`), then
restricting the full `BinVec (k + m)` to `μ` equals restricting just the second
`m`-bit segment of `b` to `μ`'s suffix part. -/
lemma restrict_truncate_prefix {k m : ℕ} (b : BinVec (k + m)) (μ : Fin (k + m) → Bool)
    (hfalse : ∀ i : Fin k, μ (Fin.castAdd m i) = false) :
    restrict b μ
      = restrict (⟨fun i => b.bit (Fin.natAdd k i)⟩ : BinVec m)
          (fun i => μ (Fin.natAdd k i)) := by
  rw [restrict_split (n₁ := k) (n₂ := m) b μ]
  have hpre : restrict (⟨fun i => b.bit (Fin.castAdd m i)⟩ : BinVec k)
        (fun i => μ (Fin.castAdd m i)) = [] := by
    rw [restrict_eq_keepWith]
    apply keepWith_false_eq_nil
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfalse i
  rw [hpre, List.nil_append]

/-- **The false-prefix mask sum collapses to a sum over the suffix block.**
Mirror of `PartialDominatesSegmentCast.false_tail_mask_sum_collapse`: a `Fintype`
sum over masks `μ : Fin (k + m) → Bool`, gated by the indicator that `μ` is
`false` on the first segment `Fin k`, equals the sum over suffix masks
`ν : Fin m → Bool` of the integrand evaluated at the extension of `ν` by the
constant-`false` prefix (`Fin.append (fun _ => false) ν`). -/
lemma prefix_false_mask_sum_collapse {k m : ℕ} (F : (Fin (k + m) → Bool) → ENNReal) :
    (∑ μ : Fin (k + m) → Bool,
       (if (∀ i : Fin k, μ (Fin.castAdd m i) = false) then F μ else 0))
      = ∑ ν : Fin m → Bool, F (Fin.append (fun _ => false) ν) := by
  rw [← (Fin.appendEquiv (α := Bool) k m).sum_comp
        (fun μ => if (∀ i : Fin k, μ (Fin.castAdd m i) = false) then F μ else 0)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  have happ : ∀ w : Fin k → Bool, (Fin.appendEquiv (α := Bool) k m) (w, ν) = Fin.append w ν := by
    intro w; funext a; rw [Fin.appendEquiv_apply]
  rw [Finset.sum_eq_single (fun _ : Fin k => false)]
  · rw [happ, if_pos]
    intro i; rw [Fin.append_left]
  · intro w _ hw
    rw [happ, if_neg]
    intro hcon
    apply hw
    funext i
    have := hcon i
    rwa [Fin.append_left] at this
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- **Per-index weight product collapses to the suffix block (suffix case).**
For a mask `μ : Fin (k + m) → Bool` that is `false` on the prefix block
(`Fin.castAdd m`), the full per-index Bernoulli product gated `if i ≥ k` equals
the clean product of `wfac δ` over the suffix masks `μ ∘ Fin.natAdd k`. -/
lemma wfac_prod_suffix_gate {k m : ℕ} (δ : ℝ) (μ : Fin (k + m) → Bool) :
    (∏ i : Fin (k + m),
        (if (i : ℕ) ≥ k then wfac δ (μ i) else 1))
      = ∏ i : Fin m, wfac δ (μ (Fin.natAdd k i)) := by
  rw [Fin.prod_univ_add
        (f := fun i : Fin (k + m) => if (i : ℕ) ≥ k then wfac δ (μ i) else 1)]
  have hpre : (∏ i : Fin k,
        (if ((Fin.castAdd m i : Fin (k + m)) : ℕ) ≥ k then wfac δ (μ (Fin.castAdd m i)) else 1))
      = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [if_neg]
    simp only [Fin.coe_castAdd, not_le]
    exact i.isLt
  have hsuf : (∏ i : Fin m,
        (if ((Fin.natAdd k i : Fin (k + m)) : ℕ) ≥ k then wfac δ (μ (Fin.natAdd k i)) else 1))
      = ∏ i : Fin m, wfac δ (μ (Fin.natAdd k i)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos]
    simp [Fin.natAdd]
  rw [hpre, hsuf, one_mul]

/-- **(b) Suffix-window weight equals the suffix segment sum.**  Mirror of
`prefixWindow_eq_segSum`: the offset-`r` masked suffix sum — over masks
`μ : Fin (k + m) → Bool` constrained to be `false` on the prefix block, with the
keep-indicator `g (restrict b μ)` and the per-index weight product gated
`if i ≥ k` — equals the fixed-width segment sum `segSum δ (suffix-segment of b) g`
over `BinVec m`.  This is the suffix half of casting `suffixWeight`'s
`Fin n → Bool` masked sum to a clean `BinVec m` segment sum. -/
theorem suffixWindow_eq_segSum {k m : ℕ} (δ : ℝ) (b : BinVec (k + m))
    (g : List Bool → ENNReal) :
    (∑ μ : Fin (k + m) → Bool,
        (if (∀ i : Fin k, μ (Fin.castAdd m i) = false) then
            g (restrict b μ) *
              ∏ i : Fin (k + m), (if (i : ℕ) ≥ k then wfac δ (μ i) else 1)
          else 0))
      = PartialDominatesAssembly.segSum δ
          (⟨fun i => b.bit (Fin.natAdd k i)⟩ : BinVec m) g := by
  rw [prefix_false_mask_sum_collapse
        (fun μ => g (restrict b μ) *
          ∏ i : Fin (k + m), (if (i : ℕ) ≥ k then wfac δ (μ i) else 1))]
  unfold PartialDominatesAssembly.segSum
  apply Finset.sum_congr rfl
  intro ν _
  have hfalse : ∀ i : Fin k, (Fin.append (fun _ => false) ν) (Fin.castAdd m i) = false := by
    intro i; rw [Fin.append_left]
  rw [restrict_truncate_prefix b (Fin.append (fun _ => false) ν) hfalse]
  have hsuff : (fun i => (Fin.append (fun _ => false) ν) (Fin.natAdd k i)) = ν := by
    funext i; rw [Fin.append_right]
  rw [hsuff]
  rw [wfac_prod_suffix_gate δ (Fin.append (fun _ => false) ν)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.append_right]

/-! ### Precise remaining step (d) — characterized

With (a) `prefixWindow_eq_segSum` and (b) `suffixWindow_eq_segSum` proved
sorry-free (both in the cast-free `k + m` window shape), the `hcore` hypothesis
of `PartialDominatesBindForm.bind_identity_of_per_b` reduces to the following
**still-open** chain.  For a fixed underlying string `b : BinVec n` and output
trace `τ`:

1. **Integer window alignment (`ℤ → ℕ` cast).**  `prefixWeight n b δ r t₁` is a
   sum over `μ : Fin n → Bool` with the prefix-window gate `if (i:ℤ) < n/4 + r`.
   To apply (a) one must:
   * fix `k := (n/4 + r).toNat`, `m := n - k`, and the length cast `BinVec n ≃
     BinVec (k + m)` (the `lenEquiv`/`Fin.cast` pattern from `TVMonotoneInDelta`);
   * show the `ℤ`-comparison `(i : ℤ) < n/4 + r` matches the `ℕ`-comparison
     `(i : ℕ) < k` under that cast (needs `0 ≤ n/4 + r` and `n/4 + r ≤ n`, i.e.
     `r` in the `offsetWeight`-support range — outside it both sides vanish);
   * identify `isPrefixMask n r μ` (false past `n/4 + r`) with the `false`-tail
     hypothesis of (a).
   Then `prefixWeight n b δ r t₁ = segSum δ (prefix b at offset r) (· = t₁.bits)`.
   The suffix is symmetric via (b) with cut `3n/4 + r`.

2. **Three-segment factorization.**  With the three cuts `n₁ = n/4 + r`,
   `n₂ = n/2`, `n₃ = n - 3n/4 - r` aligned (`n₁ + n₂ + n₃ = n`),
   `PartialDominatesAssembly.channel_sum_factor3` factors the whole-string
   keep-set sum (for a factoring observable) into the three segment sums.  The
   middle segment sum, pinned by `middleIndicator` (`M = b`'s middle) and the
   kernel's re-deletion, matches via
   `PartialDominatesConvolution.concatTrace_eq_unique_mid`.

3. **Binomial offset marginalization (the genuine combinatorial wall).**  The RHS
   of `hcore`, `∑ m : Fin n → Bool, [restrict b m = τ.bits] · ∏ wfac δ (m i)`,
   carries **no offset `r`**.  Summing the per-`r` three-segment factorization
   against `offsetWeight n r` (the `Bin(n/2, 1/2)`-shifted-by-`n/4` weight) over
   all valid `r : ℤ` must reproduce that single unconstrained whole-string
   deletion sum.  Concretely: each whole-string mask `m` corresponds to a unique
   decomposition `(offset r, prefix/middle/suffix segment masks)` determined by
   where the kept-bit boundary of the middle window falls; the bijection /
   reindex turning `∑ m` into `∑_r offsetWeight(r) · (segment-factored)` is the
   paper's Lemma-6 measure-preservation argument.  This is the multi-day
   combinatorial remainder — it is NOT reachable in a bounded lemma budget, and
   is the sole content still standing between (a)+(b) and a sorry-free `hcore`.
-/

end PartialDominatesSegmentAlign
