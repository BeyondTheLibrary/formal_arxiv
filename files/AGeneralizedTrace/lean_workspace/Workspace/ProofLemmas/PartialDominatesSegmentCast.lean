import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.DeletionChannel
import Workspace.ProofLemmas.TraceDeletionListCompose
import Workspace.ProofLemmas.DeletionSegmentFactorization
import Workspace.ProofLemmas.RestrictSegmentFactorization

/-!
# Segment-cast building blocks for the `hcore` offset cast

This file lands, **sorry-free**, the two genuinely-mechanical building blocks of
the per-`r` segment cast that `PartialDominatesBindForm.bind_identity_of_per_b`'s
remaining hypothesis `hcore` requires.

`hcore` must rewrite the offset-`r` masked `prefixWeight`/`suffixWeight` (sums
over `Fin n → Bool` masks constrained to be `false` outside the segment window,
with the per-index weight product `if i < window then bernoulli else 1`) into the
fixed-width segment sums `segSum δ (segment of b) (· = t.bits)` over
`BinVec k` (`k` = the integer window length, here in its cast-free `k + m` form),
so that `PartialDominatesAssembly.channel_sum_factor3` can be applied with cut
points `n₁ = n/4 + r`, `n₂ = n/2`, `n₃ = remainder`.

The two pieces here are the mask-level core of that cast:

* `restrict_truncate_add` — **the restrict drops a false tail**: for a mask `μ`
  that is `false` everywhere on the second segment `Fin m` (the part the prefix
  channel does not act on), `restrict b μ` equals the restriction of the first
  `k`-bit segment of `b` to `μ`'s prefix part.  Proved by `restrict_split`
  followed by collapsing the suffix `restrict` to `[]` via
  `keepWith_false_eq_nil`.

* `false_tail_mask_sum_collapse` — **the false-tail mask sum collapses**: a
  `Fintype` sum over `Fin (k + m) → Bool` of an integrand gated by the
  "tail is `false`" indicator collapses to a sum over `Fin k → Bool`, via the
  `Fin.appendEquiv` reindex and `Finset.sum_eq_single` pinning the tail block to
  the constant-`false` function.

Both are stated in the cast-free `k + m` shape (matching `channel_sum_factor3`,
which is itself phrased for `BinVec (n₁ + n₂ + n₃)`), so no `ℤ → ℕ` `Fin.cast`
is needed at this layer; the integer alignment `n/4 + r = k` and the binomial
`offsetWeight`-vs-`r` marginalization are the still-open remainder (see the
report and `lean_knowledge.md`).
-/

namespace PartialDominatesSegmentCast

open Workspace.Types.BinVec
open Workspace.Types.DeletionChannel
open TraceDeletionListCompose
open DeletionSegmentFactorization
open RestrictSegmentFactorization

open scoped Classical

/-- **An all-`false` decision list keeps nothing.**  `keepWith l m` with every
entry of `m` equal to `false` is the empty list.  (List-level helper for the
restrict truncation.) -/
lemma keepWith_false_eq_nil (l₂ m₂ : List Bool) (hfalse : ∀ x ∈ m₂, x = false) :
    keepWith l₂ m₂ = [] := by
  unfold keepWith
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  have hp2 : p.2 ∈ m₂ := (List.of_mem_zip hp).2
  rw [hfalse p.2 hp2]; simp

/-- **`restrict` drops a `false` tail (cast-free segment form).**  If the mask
`μ` is `false` on the entire second segment (`Fin m`, indexed by `Fin.natAdd k`),
then restricting the full `BinVec (k + m)` to `μ` equals restricting just the
first `k`-bit segment of `b` to `μ`'s prefix part.  This is the mask-level core
of casting `prefixWeight`'s `Fin n → Bool` mask sum to a fixed-width `BinVec k`
segment sum. -/
lemma restrict_truncate_add {k m : ℕ} (b : BinVec (k + m)) (μ : Fin (k + m) → Bool)
    (hfalse : ∀ i : Fin m, μ (Fin.natAdd k i) = false) :
    restrict b μ
      = restrict (⟨fun i => b.bit (Fin.castAdd m i)⟩ : BinVec k)
          (fun i => μ (Fin.castAdd m i)) := by
  rw [restrict_split (n₁ := k) (n₂ := m) b μ]
  have hsuf : restrict (⟨fun i => b.bit (Fin.natAdd k i)⟩ : BinVec m)
        (fun i => μ (Fin.natAdd k i)) = [] := by
    rw [restrict_eq_keepWith]
    apply keepWith_false_eq_nil
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfalse i
  rw [hsuf, List.append_nil]

/-- **The false-tail mask sum collapses to a sum over the prefix block.**  A
`Fintype` sum over masks `μ : Fin (k + m) → Bool`, gated by the indicator that
`μ` is `false` on the second segment, equals the sum over prefix masks
`ν : Fin k → Bool` of the integrand evaluated at the extension of `ν` by the
constant-`false` tail (`Fin.append ν (fun _ => false)`).  This is the
mask-domain reindex half of the segment cast: the offset-`r` prefix mask sum
(constrained `false` outside the window) becomes a clean `Fin k → Bool` sum. -/
lemma false_tail_mask_sum_collapse {k m : ℕ} (F : (Fin (k + m) → Bool) → ENNReal) :
    (∑ μ : Fin (k + m) → Bool,
       (if (∀ i : Fin m, μ (Fin.natAdd k i) = false) then F μ else 0))
      = ∑ ν : Fin k → Bool, F (Fin.append ν (fun _ => false)) := by
  rw [← (Fin.appendEquiv (α := Bool) k m).sum_comp
        (fun μ => if (∀ i : Fin m, μ (Fin.natAdd k i) = false) then F μ else 0)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ν _
  have happ : ∀ w : Fin m → Bool, (Fin.appendEquiv (α := Bool) k m) (ν, w) = Fin.append ν w := by
    intro w; funext a; rw [Fin.appendEquiv_apply]
  rw [Finset.sum_eq_single (fun _ : Fin m => false)]
  · rw [happ, if_pos]
    intro i; rw [Fin.append_right]
  · intro w _ hw
    rw [happ, if_neg]
    intro hcon
    apply hw
    funext i
    have := hcon i
    rwa [Fin.append_right] at this
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

end PartialDominatesSegmentCast
