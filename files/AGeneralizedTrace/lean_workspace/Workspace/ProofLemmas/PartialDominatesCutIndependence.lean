import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.ProofLemmas.RestrictSegmentFactorization
import Workspace.ProofLemmas.PartialDominatesAssembly
import Workspace.ProofLemmas.TraceDeletionKernel
import Workspace.ProofLemmas.TVMonotoneInDelta
import Workspace.ProofLemmas.PartialDominatesBindForm

/-!
# Cut-independence of the whole-string deletion keep-set sum (sorry-free)

This file lands, **sorry-free**, the mathematical heart of the per-`r` identity
that closes `PartialDominatesBindForm.bind_identity_of_per_b`'s `hcore`
hypothesis (F59 reframing: `hcore` = per-`r` identity × `offsetWeight_tsum = 1`).

The per-`r` identity asserts that the cut location `r` is irrelevant: the
whole-string keep-set sum at a point target `τ` equals, for *every* three-way
split `n = n₁ + n₂ + n₃`, the convolution over decompositions
`τ = t₁ ++ mid ++ t₂` of the three per-segment point-indicator segment sums.

What this file proves:

* `whole_string_triple_split` — the whole-string keep-set sum factors into a
  triple sum over the three segment masks (this is `channel_sum_factor3`'s
  proof body, stopped before the factoring-observable hypothesis is used, so it
  applies to the *point* indicator `[· = τ]`).
* `concat_indicator_as_conv` — the point indicator `[r₁ ++ r₂ ++ r₃ = τ]`
  expands as a `tsum` over decompositions `(t₁, mid, t₂)` of `τ`, picking out
  the unique matching one.
* `whole_string_eq_segConv` — **the cut-independence identity**: the
  whole-string keep-set sum equals
  `∑'(t₁,mid,t₂) segSum_pre(·=t₁) · segSum_mid(·=mid) · segSum_suf(·=t₂) ·
   [t₁++mid++t₂=τ]`, for ANY cut `(n₁,n₂,n₃)`.  The RHS depends only on
  `b, δ, τ` (and `n = n₁+n₂+n₃`); the cut is irrelevant.

This is the cut-independence made formal — exactly the fact that makes the
per-`r` term a constant (independent of `r`), so summing it against
`offsetWeight` and using `OffsetWeightSumOne.offsetWeight_tsum_eq_one` collapses
the offset.

**Exact remaining `have` toward `hcore`** (documented at the bottom).
-/

namespace PartialDominatesCutIndependence

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.DeletionChannel
open RestrictSegmentFactorization
open PartialDominatesAssembly
open TraceDeletionKernel

open scoped Classical

/-- Triple-segment whole-string keep-set sum at a point target `τ`, expanded
into a triple sum over the three segment masks via `restrict_split`. -/
theorem whole_string_triple_split {n₁ n₂ n₃ : ℕ} (δ : ℝ)
    (b : BinVec (n₁ + n₂ + n₃)) (τ : List Bool) :
    (∑ m : Fin (n₁ + n₂ + n₃) → Bool,
        (if restrict b m = τ then (1 : ENNReal) else 0) * ∏ i, wfac δ (m i))
      = ∑ m₁ : Fin n₁ → Bool, ∑ m₂ : Fin n₂ → Bool, ∑ m₃ : Fin n₃ → Bool,
          (if restrict (⟨fun i => b.bit (Fin.castAdd n₃ (Fin.castAdd n₂ i))⟩ : BinVec n₁) m₁
               ++ restrict (⟨fun i => b.bit (Fin.castAdd n₃ (Fin.natAdd n₁ i))⟩ : BinVec n₂) m₂
               ++ restrict (⟨fun i => b.bit (Fin.natAdd (n₁ + n₂) i)⟩ : BinVec n₃) m₃ = τ
            then (1 : ENNReal) else 0)
          * ((∏ i, wfac δ (m₁ i)) * ((∏ i, wfac δ (m₂ i)) * (∏ i, wfac δ (m₃ i)))) := by
  set e : (((Fin n₁ → Bool) × (Fin n₂ → Bool)) × (Fin n₃ → Bool))
      ≃ (Fin (n₁ + n₂ + n₃) → Bool) :=
    ((Fin.appendEquiv (α := Bool) n₁ n₂).prodCongr (Equiv.refl (Fin n₃ → Bool))).trans
      (Fin.appendEquiv (α := Bool) (n₁ + n₂) n₃) with he
  rw [← e.sum_comp (fun m => (if restrict b m = τ then (1 : ENNReal) else 0) * ∏ i, wfac δ (m i))]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro m₁ _
  apply Finset.sum_congr rfl; intro m₂ _
  apply Finset.sum_congr rfl; intro m₃ _
  have hinner : (Fin.appendEquiv (α := Bool) n₁ n₂) (m₁, m₂) = Fin.append m₁ m₂ := by
    funext a; rw [Fin.appendEquiv_apply]
  have hem : e ((m₁, m₂), m₃) = Fin.append (Fin.append m₁ m₂) m₃ := by
    rw [he]
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq]
    funext a
    rw [Fin.appendEquiv_apply, hinner]
  rw [hem]
  have hsplit1 := restrict_split (n₁ := n₁ + n₂) (n₂ := n₃) b
      (Fin.append (Fin.append m₁ m₂) m₃)
  simp only [Fin.append_left, Fin.append_right] at hsplit1
  have hsplit2 := restrict_split (n₁ := n₁) (n₂ := n₂)
      (⟨fun i => b.bit (Fin.castAdd n₃ i)⟩ : BinVec (n₁ + n₂)) (Fin.append m₁ m₂)
  simp only [Fin.append_left, Fin.append_right] at hsplit2
  rw [hsplit1, hsplit2]
  congr 1
  rw [Fin.prod_univ_add (fun i => wfac δ (Fin.append (Fin.append m₁ m₂) m₃ i))]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_add (fun i => wfac δ (Fin.append m₁ m₂ i))]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-- Point-indicator decomposition: a three-way concatenation equals `τ` iff
there is a (necessarily unique) decomposition of `τ` matching the three pieces.
Phrased as an `ENNReal` tsum over `List Bool × List Bool × List Bool`. -/
theorem concat_indicator_as_conv (r₁ r₂ r₃ τ : List Bool) :
    (if r₁ ++ r₂ ++ r₃ = τ then (1 : ENNReal) else 0)
      = ∑' p : List Bool × List Bool × List Bool,
          (if r₁ = p.1 then (1 : ENNReal) else 0)
            * ((if r₂ = p.2.1 then (1 : ENNReal) else 0)
              * ((if r₃ = p.2.2 then (1 : ENNReal) else 0)
                * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1 : ENNReal) else 0))) := by
  rw [tsum_eq_single (r₁, r₂, r₃)]
  · simp
  · rintro ⟨t₁, t₂, t₃⟩ hne
    by_cases h1 : r₁ = t₁
    · by_cases h2 : r₂ = t₂
      · by_cases h3 : r₃ = t₃
        · exact absurd (by rw [h1, h2, h3]) hne
        · simp [h3]
      · simp [h2]
    · simp [h1]

/-- **Cut-independent convolution form of the whole-string keep-set sum.**
For any three-way split `n = n₁ + n₂ + n₃`, the whole-string keep-set sum at a
point target `τ` equals the convolution, over decompositions
`τ = t₁ ++ mid ++ t₂`, of the three per-segment point-indicator segment sums.
The cut location `(n₁, n₂, n₃)` is irrelevant: the value depends only on `b`,
`δ`, `τ` (and `n = n₁+n₂+n₃`). -/
theorem whole_string_eq_segConv {n₁ n₂ n₃ : ℕ} (δ : ℝ)
    (b : BinVec (n₁ + n₂ + n₃)) (τ : List Bool) :
    (∑ m : Fin (n₁ + n₂ + n₃) → Bool,
        (if restrict b m = τ then (1 : ENNReal) else 0) * ∏ i, wfac δ (m i))
      = ∑' p : List Bool × List Bool × List Bool,
          segSum δ (⟨fun i => b.bit (Fin.castAdd n₃ (Fin.castAdd n₂ i))⟩ : BinVec n₁)
              (fun s => if s = p.1 then 1 else 0)
            * (segSum δ (⟨fun i => b.bit (Fin.castAdd n₃ (Fin.natAdd n₁ i))⟩ : BinVec n₂)
                  (fun s => if s = p.2.1 then 1 else 0)
              * (segSum δ (⟨fun i => b.bit (Fin.natAdd (n₁ + n₂) i)⟩ : BinVec n₃)
                  (fun s => if s = p.2.2 then 1 else 0)
                * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1 : ENNReal) else 0))) := by
  rw [whole_string_triple_split]
  -- Abbreviate the three segments.
  set c₁ : BinVec n₁ := ⟨fun i => b.bit (Fin.castAdd n₃ (Fin.castAdd n₂ i))⟩ with hc₁
  set c₂ : BinVec n₂ := ⟨fun i => b.bit (Fin.castAdd n₃ (Fin.natAdd n₁ i))⟩ with hc₂
  set c₃ : BinVec n₃ := ⟨fun i => b.bit (Fin.natAdd (n₁ + n₂) i)⟩ with hc₃
  -- Rewrite each finite sum over Fintype masks as a tsum, and the indicator via
  -- the convolution form; then reorder everything to pull `∑' p` outermost.
  -- Step 1: substitute the indicator decomposition inside the triple finite sum.
  have hstep : ∀ (m₁ : Fin n₁ → Bool) (m₂ : Fin n₂ → Bool) (m₃ : Fin n₃ → Bool),
      (if restrict c₁ m₁ ++ restrict c₂ m₂ ++ restrict c₃ m₃ = τ then (1 : ENNReal) else 0)
        * ((∏ i, wfac δ (m₁ i)) * ((∏ i, wfac δ (m₂ i)) * (∏ i, wfac δ (m₃ i))))
      = ∑' p : List Bool × List Bool × List Bool,
          ((if restrict c₁ m₁ = p.1 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₁ i))
          * (((if restrict c₂ m₂ = p.2.1 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₂ i))
            * (((if restrict c₃ m₃ = p.2.2 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₃ i))
              * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1:ENNReal) else 0))) := by
    intro m₁ m₂ m₃
    rw [concat_indicator_as_conv (restrict c₁ m₁) (restrict c₂ m₂) (restrict c₃ m₃) τ,
        ← ENNReal.tsum_mul_right]
    apply tsum_congr; intro p; ring
  -- Rewrite each finite summand via hstep.
  have hLHS : (∑ m₁ : Fin n₁ → Bool, ∑ m₂ : Fin n₂ → Bool, ∑ m₃ : Fin n₃ → Bool,
        (if restrict c₁ m₁ ++ restrict c₂ m₂ ++ restrict c₃ m₃ = τ then (1:ENNReal) else 0)
          * ((∏ i, wfac δ (m₁ i)) * ((∏ i, wfac δ (m₂ i)) * (∏ i, wfac δ (m₃ i)))))
      = ∑ m₁ : Fin n₁ → Bool, ∑ m₂ : Fin n₂ → Bool, ∑ m₃ : Fin n₃ → Bool,
          ∑' p : List Bool × List Bool × List Bool,
            ((if restrict c₁ m₁ = p.1 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₁ i))
            * (((if restrict c₂ m₂ = p.2.1 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₂ i))
              * (((if restrict c₃ m₃ = p.2.2 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₃ i))
                * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1:ENNReal) else 0))) := by
    apply Finset.sum_congr rfl; intro m₁ _
    apply Finset.sum_congr rfl; intro m₂ _
    apply Finset.sum_congr rfl; intro m₃ _
    exact hstep m₁ m₂ m₃
  rw [hLHS]
  -- Define the per-(m₁,m₂,m₃,p) summand.
  set G : (Fin n₁ → Bool) → (Fin n₂ → Bool) → (Fin n₃ → Bool) →
      (List Bool × List Bool × List Bool) → ENNReal :=
    fun m₁ m₂ m₃ p =>
      ((if restrict c₁ m₁ = p.1 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₁ i))
      * (((if restrict c₂ m₂ = p.2.1 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₂ i))
        * (((if restrict c₃ m₃ = p.2.2 then (1:ENNReal) else 0) * ∏ i, wfac δ (m₃ i))
          * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1:ENNReal) else 0))) with hG
  -- LHS: ∑ m₁ ∑ m₂ ∑ m₃ ∑' p, G  →  ∑' p ∑ m₁ ∑ m₂ ∑ m₃, G  (finite/tsum interchange).
  rw [show (∑ m₁ : Fin n₁ → Bool, ∑ m₂ : Fin n₂ → Bool, ∑ m₃ : Fin n₃ → Bool,
          ∑' p : List Bool × List Bool × List Bool, G m₁ m₂ m₃ p)
      = ∑' p : List Bool × List Bool × List Bool,
          ∑ m₁ : Fin n₁ → Bool, ∑ m₂ : Fin n₂ → Bool, ∑ m₃ : Fin n₃ → Bool, G m₁ m₂ m₃ p from ?_]
  · -- Per p, RHS segSum triple product = the inner triple finite sum of G.
    apply tsum_congr; intro p
    unfold PartialDominatesAssembly.segSum
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m₁ _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m₂ _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  · -- Finite/tsum interchange (ENNReal): pull ∑' p outermost.
    rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    apply Finset.sum_congr rfl; intro m₁ _
    rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    apply Finset.sum_congr rfl; intro m₂ _
    rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]

/-! ### Middle identification (piece 2): `traceDelete (fullTrace M)` is a segSum -/

/-- **The middle-deletion mass is the middle segment's point-indicator segment
sum.**  At width `n/2` (the middle window), the rate-`δ` whole-string deletion
of the full trace of `M`, evaluated at output `mid`, equals
`segSum δ M (· = mid.bits)`.  This identifies the `hcore` LHS middle factor
`∑'mid, traceDelete δ (fullTrace M) mid · [t₁++mid++t₂=τ]` with the middle factor
of `whole_string_eq_segConv`.  Proved by re-exporting
`PartialDominatesBindForm.traceDelete_fullTrace_restrict_form` (the `lenEquiv`
mask-domain reindex) and folding the result into `segSum`. -/
theorem traceDelete_fullTrace_eq_segSum {k : ℕ} (M : BinVec k) (δ : DelProb)
    (mid : Trace k) :
    (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace M)
        : Trace k → ENNReal) mid
      = PartialDominatesAssembly.segSum δ.val M (fun s => if s = mid.bits then 1 else 0) := by
  have h := PartialDominatesBindForm.traceDelete_fullTrace_restrict_form M δ mid
  rw [show (PartialDominatesAssembly.fullTrace M) = (TVMonotoneInDelta.fullTrace M) from rfl]
  rw [h]
  unfold PartialDominatesAssembly.segSum
  rfl

/-! ### Exact remaining `have` toward `hcore`

With `whole_string_eq_segConv` (sorry-free), the **RHS of `hcore`** — the
whole-string keep-set sum `∑ m : Fin n → Bool, [restrict b m = τ.bits] · ∏ wfac`
— is now, for the offset-`r` cut `(n₁,n₂,n₃) = (n/4+r, n/2, n-3n/4-r)`, equal to
the segment-convolution
`∑'(t₁,mid,t₂) segSum_pre(·=t₁) · segSum_mid(·=mid) · segSum_suf(·=t₂) ·
 [t₁++mid++t₂=τ.bits]`, INDEPENDENT of `r`.

The remaining work to close `hcore` (the hypothesis of
`PartialDominatesBindForm.bind_identity_of_per_b`) is the **per-`r` LHS↔segment
identification**, i.e. proving that the `hcore` LHS per-`r` summand equals this
constant segment-convolution.  Three pieces remain:

1. **ℤ→ℕ window cast (prefix/suffix).**  Identify
   `prefixWeight n b δ r t₁ = segSum_pre (· = t₁.bits)` and
   `suffixWeight n b δ r t₂ = segSum_suf (· = t₂.bits)`.  Each is a sum over
   `Fin n → Bool` with a `ℤ`-gate (`(i:ℤ) < n/4+r` / `(i:ℤ) ≥ 3n/4+r`); the
   target is a fixed-width `BinVec k` segment sum.  The mask→`segSum` bridges
   are already proved in `PartialDominatesSegmentAlign.{prefixWindow_eq_segSum,
   suffixWindow_eq_segSum}` (cast-free `k+m` form); what is missing is only the
   length cast `BinVec n ≃ BinVec (k+m)` (with `k = (n/4+r).toNat`) matching the
   `ℤ`-gate to the `ℕ`-gate (needs `0 ≤ n/4+r ≤ n`, i.e. `r` in the
   `offsetWeight`-support — outside it `offsetWeight n r = 0`, both sides vanish)
   and identifying `isPrefixMask`/`isSuffixMask` with the false-tail/false-prefix
   hypotheses of (a)/(b).

2. **Middle identification.**  `middleIndicator n b s.1 r · (∑'mid,
   traceDelete δ (fullTrace s.1) mid · [t₁++mid++t₂=τ])`: when
   `middleIndicator` pins `s.1 = b`'s middle window (the segment of `b` between
   the two cuts), `traceDelete δ (fullTrace s.1) mid` is the `n/2`-segment
   point-indicator segment sum `segSum_mid (· = mid.bits)` (by the
   `traceDelete_fullTrace_restrict_form` reindex at width `n/2`), so the inner
   `∑'mid` convolution is exactly the middle factor of `whole_string_eq_segConv`.

3. **Offset marginalization (now trivial).**  Summing the per-`r` identity (LHS
   = the constant segment-convolution = RHS) against `offsetWeight n r` over all
   `r : ℤ` multiplies the `r`-independent RHS by
   `∑' r, offsetWeight n r = 1` (`OffsetWeightSumOne.offsetWeight_tsum_eq_one`),
   recovering the single whole-string RHS of `hcore`.

Once 1+2 land (the genuine remaining work — the ℤ→ℕ length cast and the middle
`traceDelete = segSum` reindex), `hcore` closes, and
`PartialDominatesBindForm.bind_identity_of_per_b` + `DataProcessingTV` close
`partial_dominates_traceDist`.
-/

end PartialDominatesCutIndependence
