import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.DeletionChannel
import Workspace.ProofLemmas.TraceDeletionListCompose
import Workspace.ProofLemmas.DeletionSegmentFactorization

/-!
# Segment factorization at the `BinVec` / `restrict` level

This file lifts the list-level segment factorization
(`DeletionSegmentFactorization.keepWith_append`) up to the `restrict` operator on
`BinVec`, which is the form the deletion channel
(`Workspace.Types.DeletionChannel`) actually consumes.

The deletion channel's defining sum (`DeletionChannel.pmf_eq_keep_set_sum`) is
indexed by masks `m : Fin n → Bool` and uses
`restrict b m = (List.finRange n).filterMap (fun i => if m i then some (b.bit i) else none)`
as the kept output.  To realise the paper's Lemma 6 reduction ("apply the
deletion process to the middle segment and concatenate prefix / middle / last")
we need `restrict` to factor over a split of the index set
`Fin (n₁ + n₂) ≃ Fin n₁ ⊕ Fin n₂`.

We provide:

* `restrict_eq_keepWith` — the bridge identifying `restrict b m` with the
  reindexing-free list-level `keepWith (List.ofFn b.bit) (List.ofFn m)`.
* `restrict_append` — the central **restrict-respects-append** lemma: for a
  vector and mask materialised by `Fin.append`, `restrict` of the concatenation
  is the concatenation of the two segment `restrict`s.
* `restrict_split` — the same fact phrased for an *arbitrary* `b : BinVec (n₁+n₂)`
  and `m : Fin (n₁+n₂) → Bool`, splitting them at `n₁` via
  `Fin.castAdd` / `Fin.natAdd`.  This is the form Lemma 6 uses directly.

Everything is proved sorry-free.  The PMF-level product reindex (turning the
deletion PMF of a concatenation into `PMF.map (· ++ ·)` of the product of the
per-segment deletion PMFs) is set up via the marginalization engine
`segment_mask_sum_factor`; see `restrict_channel_sum_factor` below and the
report for the precise remaining step.
-/

namespace RestrictSegmentFactorization

open Workspace.Types.BinVec
open Workspace.Types.DeletionChannel
open TraceDeletionListCompose
open DeletionSegmentFactorization

/-! ### Bridge: `restrict` is the list-level `keepWith` -/

/-- Auxiliary: the position-wise zip of two `ofFn` lists is the `finRange`-indexed
map of the paired functions. -/
private lemma ofFn_zip_ofFn {n : ℕ} (f g : Fin n → Bool) :
    (List.ofFn f).zip (List.ofFn g) = (List.finRange n).map (fun i => (f i, g i)) := by
  apply List.ext_getElem?
  intro i
  rw [List.zip_eq_zipWith, List.getElem?_zipWith', List.getElem?_map,
    List.getElem?_ofFn, List.getElem?_ofFn]
  rcases lt_or_ge i n with hi | hi
  · rw [List.getElem?_eq_getElem (by simpa using hi : i < (List.finRange n).length)]
    simp [hi, List.getElem_finRange]
  · rw [List.getElem?_eq_none (by simpa using hi : (List.finRange n).length ≤ i)]
    simp [Nat.not_lt.mpr hi]

/-- **`restrict` equals list-level `keepWith` on the bit list.**  The
`Fin`-indexed `filterMap` defining `restrict b m` coincides with the
reindexing-free `keepWith` applied to the bit list `List.ofFn b.bit` and the
decision list `List.ofFn m`.  This is the analogue of
`TraceDeletionKernel.keep_eq_keepWith`, but on `BinVec` instead of `Trace`. -/
theorem restrict_eq_keepWith {n : ℕ} (b : BinVec n) (m : Fin n → Bool) :
    restrict b m = keepWith (List.ofFn b.bit) (List.ofFn m) := by
  unfold restrict keepWith
  -- `keepWith` zips the bit list with the decision list; rewrite that zip as a
  -- `finRange`-indexed map, then both sides are the same `filterMap`.
  rw [ofFn_zip_ofFn, List.filterMap_map]
  rfl

/-! ### Restrict respects append (segment factorization) -/

/-- **Restrict respects `Fin.append` (segment factorization).**
For a vector built as `Fin.append b₁ b₂ : Fin (n₁+n₂) → Bool` and a mask built as
`Fin.append m₁ m₂`, the restriction of the concatenation is the concatenation of
the two segment restrictions.  This is the `BinVec`-level form of
`DeletionSegmentFactorization.keepWith_append`. -/
theorem restrict_append {n₁ n₂ : ℕ}
    (b₁ : Fin n₁ → Bool) (b₂ : Fin n₂ → Bool)
    (m₁ : Fin n₁ → Bool) (m₂ : Fin n₂ → Bool) :
    restrict (n := n₁ + n₂) ⟨Fin.append b₁ b₂⟩ (Fin.append m₁ m₂)
      = restrict (⟨b₁⟩ : BinVec n₁) m₁ ++ restrict (⟨b₂⟩ : BinVec n₂) m₂ := by
  rw [restrict_eq_keepWith, restrict_eq_keepWith, restrict_eq_keepWith]
  -- The bit list and the decision list both split as `ofFn _ ++ ofFn _`.
  show keepWith (List.ofFn (Fin.append b₁ b₂)) (List.ofFn (Fin.append m₁ m₂))
      = keepWith (List.ofFn b₁) (List.ofFn m₁) ++ keepWith (List.ofFn b₂) (List.ofFn m₂)
  rw [List.ofFn_fin_append, List.ofFn_fin_append]
  exact keepWith_append (List.ofFn b₁) (List.ofFn b₂) (List.ofFn m₁) (List.ofFn m₂)
    (by simp)

/-- **Restrict splits at an arbitrary cut point `n₁` (segment factorization).**
For an arbitrary `b : BinVec (n₁+n₂)` and mask `m : Fin (n₁+n₂) → Bool`, the
restriction splits as the prefix restriction (over `Fin.castAdd`) concatenated
with the suffix restriction (over `Fin.natAdd`).  This is the form the Lemma 6
"prefix / middle / last" reduction consumes: cut the index set at `n₁`, restrict
each segment independently, and concatenate. -/
theorem restrict_split {n₁ n₂ : ℕ}
    (b : BinVec (n₁ + n₂)) (m : Fin (n₁ + n₂) → Bool) :
    restrict b m
      = restrict (⟨fun i => b.bit (Fin.castAdd n₂ i)⟩ : BinVec n₁)
          (fun i => m (Fin.castAdd n₂ i))
        ++ restrict (⟨fun i => b.bit (Fin.natAdd n₁ i)⟩ : BinVec n₂)
            (fun i => m (Fin.natAdd n₁ i)) := by
  -- Reassemble `b.bit` and `m` from their prefix / suffix parts.
  have hb : b = ⟨Fin.append (fun i => b.bit (Fin.castAdd n₂ i))
      (fun i => b.bit (Fin.natAdd n₁ i))⟩ := by
    cases b with
    | mk bit => simp only [BinVec.mk.injEq]; rw [Fin.append_castAdd_natAdd]
  have hm : m = Fin.append (fun i => m (Fin.castAdd n₂ i))
      (fun i => m (Fin.natAdd n₁ i)) := by
    rw [Fin.append_castAdd_natAdd]
  conv_lhs => rw [hb, hm]
  exact restrict_append _ _ _ _

/-! ### PMF-level (channel-mass) segment factorization

The deletion-channel mass at a trace is the keep-set sum
`∑ m, (if restrict b m = τ.bits then 1 else 0) * ∏ i, (if m i then ofReal(1-δ) else ofReal δ)`
(`DeletionChannel.pmf_eq_keep_set_sum`).  Replacing the indicator `if · = τ.bits`
by an arbitrary observable `g : List Bool → ENNReal`, the channel mass factors
over a segment split exactly when `g` factors over the concatenation point — this
is the probabilistic statement "the two segments are deleted independently".

We prove the channel-mass factorization directly at the `BinVec` level (it does
NOT route through `segment_mask_sum_factor`, which is phrased with list-level
`keepWith`; instead we reindex the single `Fin (n₁+n₂) → Bool` mask sum through
`Fin.appendEquiv` and split the per-position weight product with
`Fin.prod_univ_add`, then apply `restrict_append`). -/

/-- The per-position Bernoulli keep/drop weight used by the deletion channel. -/
noncomputable def wfac (δ : ℝ) (bit : Bool) : ENNReal :=
  if bit then ENNReal.ofReal (1 - δ) else ENNReal.ofReal δ

/-- **Channel-mass segment factorization.**  For an observable `g` that factors
multiplicatively over the concatenation point (`g (s₁ ++ s₂) = g₁ s₁ * g₂ s₂`),
the deletion-channel keep-set sum over `b : BinVec (n₁+n₂)` factors as the
product of the two per-segment keep-set sums.  Taking `g = if · = τ.bits then 1
else 0` (which factors whenever `τ.bits` splits at the segment boundary)
specialises this to the channel-PMF statement that the concatenated channel is
the independent product of the prefix and suffix channels. -/
theorem restrict_channel_sum_factor {n₁ n₂ : ℕ} (δ : ℝ)
    (b : BinVec (n₁ + n₂))
    (g : List Bool → ENNReal) (g₁ g₂ : List Bool → ENNReal)
    (hg : ∀ s₁ s₂ : List Bool, g (s₁ ++ s₂) = g₁ s₁ * g₂ s₂) :
    (∑ m : Fin (n₁ + n₂) → Bool, g (restrict b m) * ∏ i, wfac δ (m i))
      = (∑ m₁ : Fin n₁ → Bool,
            g₁ (restrict (⟨fun i => b.bit (Fin.castAdd n₂ i)⟩ : BinVec n₁) m₁)
              * ∏ i, wfac δ (m₁ i))
        * (∑ m₂ : Fin n₂ → Bool,
            g₂ (restrict (⟨fun i => b.bit (Fin.natAdd n₁ i)⟩ : BinVec n₂) m₂)
              * ∏ i, wfac δ (m₂ i)) := by
  -- Reindex the single mask sum through `Fin.appendEquiv`.
  rw [← (Fin.appendEquiv (α := Bool) n₁ n₂).sum_comp
        (fun m => g (restrict b m) * ∏ i, wfac δ (m i))]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m₁ _
  apply Finset.sum_congr rfl
  intro m₂ _
  -- The reindexed mask is `Fin.append m₁ m₂`.
  have happ : (Fin.appendEquiv (α := Bool) n₁ n₂) (m₁, m₂) = Fin.append m₁ m₂ := by
    funext a; rw [Fin.appendEquiv_apply]
  rw [happ]
  -- Split the weight product.
  rw [Fin.prod_univ_add (fun i => wfac δ (Fin.append m₁ m₂ i))]
  -- Identify `restrict b (append m₁ m₂)` via `restrict_split`, with `g` factoring.
  have hsplit := restrict_split (n₁ := n₁) (n₂ := n₂) b (Fin.append m₁ m₂)
  -- `restrict_split` produced the castAdd/natAdd parts of `Fin.append m₁ m₂`,
  -- which reduce to `m₁` / `m₂`.
  simp only [Fin.append_left, Fin.append_right] at hsplit ⊢
  rw [hsplit, hg]
  ring

end RestrictSegmentFactorization
