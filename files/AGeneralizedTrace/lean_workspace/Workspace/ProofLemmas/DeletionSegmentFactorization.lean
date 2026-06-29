import Mathlib
import Workspace.ProofLemmas.TraceDeletionListCompose

/-!
# Deletion channel factors over concatenated segments

This file proves the **segment / concatenation factorization** of the
independent-bit deletion process: deleting the bits of a *concatenation*
`l₁ ++ l₂` (under a decision mask that is itself a concatenation `m₁ ++ m₂`,
aligned so that `|m₁| = |l₁|`) is exactly the concatenation of the independent
deletions of the two segments:

    keepWith (l₁ ++ l₂) (m₁ ++ m₂) = keepWith l₁ m₁ ++ keepWith l₂ m₂.

This is the list-level core of the paper's Lemma 6 reduction
("apply the deletion process to the middle bits and concatenate the first,
middle, and last bits"): the deletion channel splits over a partition of the
input bits into consecutive segments, with each segment deleted independently.

It is the foundation for both `partial_dominates_traceDist` and
`TVPartialBoundedByLengthsPlusBad`, which rely on the deletion channel
factoring over a first / middle / last segmentation.

We build on the reindexing-free list model from
`TraceDeletionListCompose` (`keepWith`, `dWeight`).  Everything here is proved
sorry-free by structural induction on the first segment.
-/

namespace DeletionSegmentFactorization

open TraceDeletionListCompose

/-! ### List-level segment factorization of `keepWith`

The key reusable lemma.  When the first segment's mask `m₁` exactly covers the
first segment `l₁` (`m₁.length = l₁.length`), the keep operation distributes over
the concatenation. The length hypothesis is essential: `keepWith` zips its two
arguments position-wise, so the split point of the mask must coincide with the
split point of the list. -/

/-- **Deletion respects concatenation (list level).**
`keepWith` of a concatenation, under a mask split aligned with the list split,
is the concatenation of the per-segment `keepWith`s. Proved by induction on the
first segment `l₁`, with `m₁` generalized. -/
theorem keepWith_append (l₁ l₂ m₁ m₂ : List Bool) (hlen : m₁.length = l₁.length) :
    keepWith (l₁ ++ l₂) (m₁ ++ m₂) = keepWith l₁ m₁ ++ keepWith l₂ m₂ := by
  induction l₁ generalizing m₁ with
  | nil =>
    -- l₁ = [] forces m₁ = [] by the length hypothesis.
    simp only [List.length_nil] at hlen
    rw [List.length_eq_zero_iff.mp hlen]
    simp
  | cons a l₁ ih =>
    cases m₁ with
    | nil => simp at hlen
    | cons b m₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      cases b with
      | false =>
        -- both sides drop the head a; recurse.
        simp only [List.cons_append, keepWith_cons_false]
        exact ih m₁ hlen
      | true =>
        -- both sides keep the head a; recurse.
        simp only [List.cons_append, keepWith_cons_true]
        rw [ih m₁ hlen]

/-! ### Three-way segmentation (first / middle / last)

The paper's Lemma 6 partitions the input bits into three consecutive segments —
the first bits, the middle bits, and the last bits — applies the deletion
process to each, and concatenates the results.  This is the iterated
two-segment factorization. -/

/-- **Deletion respects a three-way concatenation (list level).**
With masks aligned to each segment (`|mF| = |lF|`, `|mM| = |lM|`), deletion of
`lF ++ lM ++ lL` is the concatenation of the three independent segment
deletions.  This is exactly the first/middle/last decomposition used in the
Lemma 6 reduction. -/
theorem keepWith_append3 (lF lM lL mF mM mL : List Bool)
    (hF : mF.length = lF.length) (hM : mM.length = lM.length) :
    keepWith (lF ++ lM ++ lL) (mF ++ mM ++ mL)
      = keepWith lF mF ++ keepWith lM mM ++ keepWith lL mL := by
  rw [List.append_assoc lF lM lL, List.append_assoc mF mM mL,
      keepWith_append lF (lM ++ lL) mF (mM ++ mL) hF,
      keepWith_append lM lL mM mL hM, List.append_assoc]

/-! ### Weight factorization over segments

The multiplicative weight of a concatenated decision mask factors as the
product of the per-segment weights — independently of any length alignment, by
`List.map_append` + `List.prod_append`.  Together with `keepWith_append`, this
shows the *joint* (keep-pattern, weight) of the two-segment process is the
independent product of the per-segment processes — the probabilistic content of
"each segment is deleted independently". -/

variable {M : Type*} [CommMonoid M]

/-- **Decision-weight factors over concatenation.** The per-position Bernoulli
weight of a concatenated mask is the product of the two segment weights. -/
theorem dWeight_append (w : Bool → M) (m₁ m₂ : List Bool) :
    dWeight w (m₁ ++ m₂) = dWeight w m₁ * dWeight w m₂ := by
  unfold dWeight
  rw [List.map_append, List.prod_append]

/-- **Joint two-segment factorization.** The combined (kept-output, weight) data
of deleting `l₁ ++ l₂` under a length-aligned concatenated mask is the product
of the per-segment kept outputs (concatenated) and per-segment weights
(multiplied). This packages `keepWith_append` and `dWeight_append` into the
single statement the PMF-level pushforward consumes. -/
theorem keepWith_dWeight_append (w : Bool → M) (l₁ l₂ m₁ m₂ : List Bool)
    (hlen : m₁.length = l₁.length) :
    keepWith (l₁ ++ l₂) (m₁ ++ m₂) = keepWith l₁ m₁ ++ keepWith l₂ m₂
      ∧ dWeight w (m₁ ++ m₂) = dWeight w m₁ * dWeight w m₂ :=
  ⟨keepWith_append l₁ l₂ m₁ m₂ hlen, dWeight_append w m₁ m₂⟩

/-! ### PMF-level lift: the segment-product marginalization (ENNReal)

The probabilistic content of the factorization. Working with `ENNReal`
per-position weights `w` (e.g. `factor q`), the *joint* mask sum over the two
segments — weighting each output by an arbitrary observable `g` of the
concatenated kept list — splits into a product of the two per-segment sums when
`g` itself factors as `g (s₁ ++ s₂) = g₁ s₁ * g₂ s₂`.  This is exactly the step
that turns the deletion channel on `l₁ ++ l₂` into the *independent* product of
the two per-segment channels at the PMF (pushforward) level: the double mask sum
over `(Fin |l₁| → Bool) × (Fin |l₂| → Bool)` factors as the product of the two
single-segment mask sums.

This is stated with `Fin`-indexed masks (`List.ofFn`) so it plugs directly into
the kernel layer (`TraceDeletionKernel.traceDelete_apply`, whose sums are over
`Fin t.bits.length → Bool`). -/

/-- The two-segment mask sum (over `Fin |l₁|→Bool × Fin |l₂|→Bool`), weighting
each joint outcome by the `ENNReal` per-position weight and an observable `g` of
the concatenated kept list, factors into the product of the two single-segment
mask sums whenever `g` factors multiplicatively over the concatenation point. -/
theorem segment_mask_sum_factor
    (w : Bool → ENNReal) (l₁ l₂ : List Bool)
    (g : List Bool → ENNReal) (g₁ g₂ : List Bool → ENNReal)
    (hg : ∀ s₁ s₂ : List Bool, g (s₁ ++ s₂) = g₁ s₁ * g₂ s₂) :
    (∑ m₁ : Fin l₁.length → Bool, ∑ m₂ : Fin l₂.length → Bool,
        g (keepWith l₁ (List.ofFn m₁) ++ keepWith l₂ (List.ofFn m₂))
          * (dWeight w (List.ofFn m₁) * dWeight w (List.ofFn m₂)))
      = (∑ m₁ : Fin l₁.length → Bool, g₁ (keepWith l₁ (List.ofFn m₁)) * dWeight w (List.ofFn m₁))
        * (∑ m₂ : Fin l₂.length → Bool, g₂ (keepWith l₂ (List.ofFn m₂)) * dWeight w (List.ofFn m₂)) := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m₁ _
  apply Finset.sum_congr rfl
  intro m₂ _
  rw [hg]
  ring

/-- **Segment-product marginalization in the merged form.** When the joint mask
is materialised as a single concatenated decision list `List.ofFn m₁ ++ List.ofFn m₂`
applied to `l₁ ++ l₂`, the kept output is `keepWith l₁ (ofFn m₁) ++ keepWith l₂ (ofFn m₂)`
and its weight is the product of the two segment weights.  This is the bridge
identity that rewrites a single-mask channel sum over `l₁ ++ l₂` into the
two-segment product form consumed by `segment_mask_sum_factor`. -/
theorem keepWith_dWeight_append_ofFn
    (w : Bool → ENNReal) (l₁ l₂ : List Bool)
    (m₁ : Fin l₁.length → Bool) (m₂ : Fin l₂.length → Bool) :
    keepWith (l₁ ++ l₂) (List.ofFn m₁ ++ List.ofFn m₂)
        = keepWith l₁ (List.ofFn m₁) ++ keepWith l₂ (List.ofFn m₂)
      ∧ dWeight w (List.ofFn m₁ ++ List.ofFn m₂)
        = dWeight w (List.ofFn m₁) * dWeight w (List.ofFn m₂) := by
  refine ⟨?_, dWeight_append w _ _⟩
  apply keepWith_append
  simp

end DeletionSegmentFactorization
