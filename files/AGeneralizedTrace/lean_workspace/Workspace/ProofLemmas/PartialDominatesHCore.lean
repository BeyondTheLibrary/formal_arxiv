import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.ProbVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.TraceDist
import Workspace.Types.TVDistance
import Workspace.Types.PartialDeletionProcess
import Workspace.PriorWork.DataProcessingTV
import Workspace.ProofLemmas.TVMonotoneInDelta
import Workspace.ProofLemmas.RestrictSegmentFactorization
import Workspace.ProofLemmas.TraceDeletionKernel
import Workspace.ProofLemmas.PartialDominatesAssembly
import Workspace.ProofLemmas.PartialDominatesConvolution
import Workspace.ProofLemmas.PartialDominatesCutIndependence
import Workspace.ProofLemmas.PartialDominatesOffsetCast
import Workspace.ProofLemmas.OffsetWeightSumOne
import Workspace.ProofLemmas.PartialDominatesBindForm
import Workspace.ProofLemmas.DeletionLengthMarginal

/-!
# Closing `hcore`: the per-`b` core identity of `bind_identity_of_per_b`

This file lands, **sorry-free**, the remaining `hcore` hypothesis of
`PartialDominatesBindForm.bind_identity_of_per_b`, under the arithmetic gate
`2 * (n / 4) = n / 2` (which holds whenever `n % 4 ∈ {0, 1}`, in particular under
the paper's global gate `n % 8 = 1`).

It then assembles the full de-axiomatization:
`bind_identity_of_per_b` + `DataProcessingTV` give the conclusion of
`Workspace.Types.PartialDeletionAxioms.partial_dominates_traceDist` as a
*theorem* (under the gate `2*(n/4)=n/2`), so the structural axiom can be
replaced.
-/

namespace PartialDominatesHCore

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.ProbVec
open Workspace.Types.CoinFlipDist
open Workspace.Types.TraceDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.DeletionChannel
open RestrictSegmentFactorization
open TraceDeletionKernel
open PartialDominatesAssembly
open PartialDominatesConvolution
open PartialDominatesCutIndependence
open PartialDominatesOffsetCast
open OffsetWeightSumOne
open PartialDominatesBindForm

open scoped Classical

/-! ### Middle-window pin

For an offset `r` in the `offsetWeight` support (`0 ≤ r + n/4 ≤ n/2`, hence the
middle indices `n/4 + r + j` for `j : Fin (n/2)` lie in `[0, n)`), the
`middleIndicator n b · r` is the point indicator at the *middle window*
`midWindow n b r`, the `BinVec (n/2)` whose `j`-th bit is `b.bit` at integer
position `n/4 + r + j`. -/

/-- The middle window of `b` at offset `r` (only meaningful when `r` is in the
offset support so that the indices stay in `[0, n)`). -/
noncomputable def midWindow {n : ℕ} (b : BinVec n) (r : ℤ)
    (hr0 : 0 ≤ r + (n / 4 : ℕ)) (hr2 : r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)) : BinVec (n / 2) :=
  ⟨fun j => b.bit ⟨(((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat, by
    have hj : (j : ℕ) < n / 2 := j.isLt
    have hjn : ((j : ℕ) : ℤ) < (n / 2 : ℕ) := by exact_mod_cast hj
    have hlt : ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) := by
      have h1 : ((n / 4 : ℕ) : ℤ) + r ≤ (n / 2 : ℕ) := by
        have := hr2; linarith
      have hn2 : (n / 2 : ℕ) + (n / 2 : ℕ) ≤ (n : ℕ) := by omega
      have : (n / 2 : ℕ) + ((j : ℕ) : ℤ) < (n : ℤ) := by
        have : ((n / 2 : ℕ) : ℤ) + ((n / 2 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
        linarith
      linarith
    have hge : 0 ≤ ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := by
      have : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
      have hr0' : 0 ≤ ((n / 4 : ℕ) : ℤ) + r := by linarith [hr0]
      linarith
    have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
        = ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hge
    have : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by rw [h0]; exact hlt
    exact_mod_cast this⟩⟩

/-- For a valid offset `r`, the middle indicator is the point indicator at
`midWindow n b r`. -/
lemma middleIndicator_eq_point {n : ℕ} (b : BinVec n) (m : BinVec (n / 2)) (r : ℤ)
    (hr0 : 0 ≤ r + (n / 4 : ℕ)) (hr2 : r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)) :
    middleIndicator n b m r
      = if m = midWindow b r hr0 hr2 then (1 : ENNReal) else 0 := by
  unfold middleIndicator
  -- The range hypothesis holds for valid `r`.
  have hrange : ∀ j : Fin (n / 2),
      0 ≤ ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) ∧
      ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) := by
    intro j
    constructor
    · have : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
      have hr0' : 0 ≤ ((n / 4 : ℕ) : ℤ) + r := by linarith [hr0]
      linarith
    · have hj : (j : ℕ) < n / 2 := j.isLt
      have hjn : ((j : ℕ) : ℤ) < (n / 2 : ℕ) := by exact_mod_cast hj
      have h1 : ((n / 4 : ℕ) : ℤ) + r ≤ (n / 2 : ℕ) := by linarith [hr2]
      have hn2 : (n / 2 : ℕ) + (n / 2 : ℕ) ≤ (n : ℕ) := by omega
      have : ((n / 2 : ℕ) : ℤ) + ((n / 2 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
      linarith
  rw [dif_pos hrange]
  -- Now compare the inner indicator (pointwise bit equality) to `m = midWindow`.
  by_cases hm : m = midWindow b r hr0 hr2
  · rw [if_pos hm]
    rw [if_pos]
    intro j
    -- both sides are `b.bit` at the same index, against `m.bit j`.
    rw [hm]
    rfl
  · rw [if_neg hm]
    rw [if_neg]
    intro hbit
    apply hm
    -- pointwise bit equality forces `m = midWindow`.
    apply congrArg BinVec.mk
    funext j
    rw [← hbit j]

/-! ### Cast invariance of the whole-string keep-set sum -/

/-- The whole-string keep-set sum is invariant under a length-`cast` reindex of
the underlying vector. -/
lemma wholeStringSum_cast {N n : ℕ} (h : N = n) (b : BinVec n) (δ : ℝ) (τ : List Bool) :
    (∑ m : Fin N → Bool,
        (if restrict (⟨fun j => b.bit (Fin.cast h j)⟩ : BinVec N) m = τ then (1 : ENNReal) else 0)
          * ∏ i, wfac δ (m i))
      = ∑ m : Fin n → Bool,
          (if restrict b m = τ then (1 : ENNReal) else 0) * ∏ i, wfac δ (m i) := by
  rw [← Equiv.sum_comp ((finCongr h).arrowCongr (Equiv.refl Bool))
        (fun m : Fin n → Bool =>
          (if restrict b m = τ then (1 : ENNReal) else 0) * ∏ i, wfac δ (m i))]
  apply Finset.sum_congr rfl
  intro μ _
  have hμ : ((finCongr h).arrowCongr (Equiv.refl Bool)) μ
      = (fun j : Fin n => μ (Fin.cast h.symm j)) := by
    funext j; simp [Equiv.arrowCongr, finCongr]
  rw [hμ]
  have hrestrict : restrict (⟨fun j => b.bit (Fin.cast h j)⟩ : BinVec N) μ
      = restrict b (fun j => μ (Fin.cast h.symm j)) := by
    have hc := restrict_cast h b (fun j => μ (Fin.cast h.symm j))
    -- hc : restrict ⟨b.bit∘cast h⟩ ((μ∘cast h.symm)∘cast h) = restrict b (μ∘cast h.symm)
    have hid : (fun j : Fin N => (fun j' : Fin n => μ (Fin.cast h.symm j')) (Fin.cast h j)) = μ := by
      funext j; simp
    rw [hid] at hc
    exact hc
  rw [hrestrict]
  congr 1
  rw [← Equiv.prod_comp (finCongr h) (fun i : Fin n => wfac δ (μ (Fin.cast h.symm i)))]
  apply Finset.prod_congr rfl
  intro i _
  congr 1

/-! ### Trace ↔ List reindexing of a segment-convolution -/

/-- If a point-indicator segment sum `segSum δ c (· = s)` is nonzero, then `s` is
the `restrict` of `c` by some mask, hence of length `≤ k`. -/
lemma segSum_point_ne_zero_length {k : ℕ} (δ : ℝ) (c : BinVec k) (s : List Bool)
    (hs : segSum δ c (fun t => if t = s then (1 : ENNReal) else 0) ≠ 0) :
    s.length ≤ k := by
  unfold segSum at hs
  -- some summand is nonzero: there is m with restrict c m = s.
  by_contra hlen
  rw [not_le] at hlen
  apply hs
  apply Finset.sum_eq_zero
  intro m _
  have hne : restrict c m ≠ s := by
    intro heq
    have := DeletionLengthMarginalProof.length_restrict_le c m
    rw [heq] at this
    omega
  simp only [if_neg hne, zero_mul]

/-- The injection `Trace n × Trace n × Trace (n/2) → List³` sending each component
to its bit list (in the order prefix, middle, suffix). -/
def traceTripleEmb (n : ℕ) :
    (Trace n × Trace n × Trace (n / 2)) → (List Bool × List Bool × List Bool) :=
  fun s => (s.1.bits, s.2.2.bits, s.2.1.bits)

lemma traceTripleEmb_injective (n : ℕ) : Function.Injective (traceTripleEmb n) := by
  rintro ⟨t₁, t₂, mid⟩ ⟨t₁', t₂', mid'⟩ heq
  simp only [traceTripleEmb, Prod.mk.injEq] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  have e1 : t₁ = t₁' := DeletionLengthMarginalProof.trace_ext h1
  have e2 : mid = mid' := DeletionLengthMarginalProof.trace_ext h2
  have e3 : t₂ = t₂' := DeletionLengthMarginalProof.trace_ext h3
  subst e1; subst e2; subst e3; rfl

/-- Reindex `whole_string_eq_segConv`'s `List³` convolution into the `Trace³`
form matching the `hcore` LHS.  The three point-indicator segment sums vanish
outside lengths `n₁ ≤ n`, `n₂ ≤ n/2`, `n₃ ≤ n`, so the `List³` sum restricts to
the image of `traceTripleEmb`. -/
lemma segConv_list_eq_trace {n n₁ n₂ n₃ : ℕ} (δ : ℝ)
    (c₁ : BinVec n₁) (c₂ : BinVec n₂) (c₃ : BinVec n₃) (τ : List Bool)
    (h1 : n₁ ≤ n) (h2 : n₂ ≤ n / 2) (h3 : n₃ ≤ n) :
    (∑' p : List Bool × List Bool × List Bool,
        segSum δ c₁ (fun s => if s = p.1 then 1 else 0)
          * (segSum δ c₂ (fun s => if s = p.2.1 then 1 else 0)
            * (segSum δ c₃ (fun s => if s = p.2.2 then 1 else 0)
              * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1 : ENNReal) else 0))))
      = ∑' s : Trace n × Trace n × Trace (n / 2),
          segSum δ c₁ (fun t => if t = s.1.bits then 1 else 0)
            * (segSum δ c₂ (fun t => if t = s.2.2.bits then 1 else 0)
              * (segSum δ c₃ (fun t => if t = s.2.1.bits then 1 else 0)
                * (if s.1.bits ++ s.2.2.bits ++ s.2.1.bits = τ then (1 : ENNReal) else 0))) := by
  rw [← Function.Injective.tsum_eq (traceTripleEmb_injective n)
        (f := fun p : List Bool × List Bool × List Bool =>
          segSum δ c₁ (fun s => if s = p.1 then 1 else 0)
            * (segSum δ c₂ (fun s => if s = p.2.1 then 1 else 0)
              * (segSum δ c₃ (fun s => if s = p.2.2 then 1 else 0)
                * (if p.1 ++ p.2.1 ++ p.2.2 = τ then (1 : ENNReal) else 0))))]
  · apply tsum_congr
    rintro ⟨t₁, t₂, mid⟩
    rfl
  · -- support ⊆ range traceTripleEmb
    intro p hp
    rw [Function.mem_support] at hp
    -- p.1, p.2.1, p.2.2 lengths bounded.
    have hne1 : segSum δ c₁ (fun s => if s = p.1 then (1:ENNReal) else 0) ≠ 0 := by
      intro h; rw [h, zero_mul] at hp; exact hp rfl
    have hne2 : segSum δ c₂ (fun s => if s = p.2.1 then (1:ENNReal) else 0) ≠ 0 := by
      intro h; rw [h] at hp; simp only [zero_mul, mul_zero] at hp; exact hp rfl
    have hne3 : segSum δ c₃ (fun s => if s = p.2.2 then (1:ENNReal) else 0) ≠ 0 := by
      intro h; rw [h] at hp; simp only [zero_mul, mul_zero] at hp; exact hp rfl
    have hl1 : p.1.length ≤ n := le_trans (segSum_point_ne_zero_length δ c₁ p.1 hne1) h1
    have hl2 : p.2.1.length ≤ n / 2 := le_trans (segSum_point_ne_zero_length δ c₂ p.2.1 hne2) h2
    have hl3 : p.2.2.length ≤ n := le_trans (segSum_point_ne_zero_length δ c₃ p.2.2 hne3) h3
    refine ⟨(⟨p.1, hl1⟩, ⟨p.2.2, hl3⟩, ⟨p.2.1, hl2⟩), ?_⟩
    simp only [traceTripleEmb]

/-- `segSum` depends only on the underlying bit function, so two `BinVec`s with
equal bit functions give the same segment sum. -/
lemma segSum_congr_bit {k : ℕ} (δ : ℝ) (c c' : BinVec k) (g : List Bool → ENNReal)
    (h : ∀ i, c.bit i = c'.bit i) :
    segSum δ c g = segSum δ c' g := by
  have : c = c' := by apply congrArg BinVec.mk; funext i; exact h i
  rw [this]

/-! ### The per-`r` identity (valid offset) -/

/-- **Per-`r` identity.**  For an offset `r` in the `offsetWeight` support
(`0 ≤ r + n/4 ≤ n/2`) and under the gate `2*(n/4) = n/2`, the inner three-segment
convolution of the partial process (summed over the sample `s`, with the offset
fixed at `r`) equals the whole-string keep-set sum — independent of `r`. -/
lemma per_r_identity {n : ℕ} (b : BinVec n) (δ : DelProb) (τ : Trace n) (r : ℤ)
    (hr0 : 0 ≤ r + (n / 4 : ℕ)) (hr2 : r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)) :
    (∑' (s : BinVec (n / 2) × Trace n × Trace n),
        (prefixWeight n b δ r s.2.1 *
          (suffixWeight n b δ r s.2.2 *
            middleIndicator n b s.1 r))
        * (∑' mid : Trace (n / 2),
            (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1)
                : Trace (n / 2) → ENNReal) mid
              * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)))
      = ∑ m : Fin n → Bool,
          (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
            ∏ i : Fin n, RestrictSegmentFactorization.wfac δ.val (m i) := by
  -- Cut sizes.
  set K₁ : ℕ := (((n / 4 : ℕ) : ℤ) + r).toNat with hK₁
  set K₃ : ℕ := n - (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat with hK₃
  -- Prefix/suffix range bounds for `prefixWeight_eq_segSum` / `suffixWeight_eq_segSum`.
  have hpre0 : 0 ≤ ((n / 4 : ℕ) : ℤ) + r := by linarith [hr0]
  have hpren : ((n / 4 : ℕ) : ℤ) + r ≤ (n : ℤ) := by
    have h1 : ((n / 4 : ℕ) : ℤ) + r ≤ (n / 2 : ℕ) := by linarith [hr2]
    have : (n / 2 : ℕ) ≤ (n : ℕ) := Nat.div_le_self n 2
    have : ((n / 2 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast this
    linarith
  -- Suffix start = n/4 + n/2 + r = (n/4+r) + n/2.  Gate-free bounds.
  have hsuf0 : 0 ≤ ((n / 4 + n / 2 : ℕ) : ℤ) + r := by
    have hle : ((n / 4 : ℕ) : ℤ) ≤ ((n / 4 + n / 2 : ℕ) : ℤ) := by push_cast; omega
    linarith [hpre0]
  have hsufn : ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (n : ℤ) := by
    -- n/4+n/2+r = (n/4+r) + n/2 ≤ n/2 + n/2 ≤ n
    have he : ((n / 4 + n / 2 : ℕ) : ℤ) + r = (((n / 4 : ℕ) : ℤ) + r) + ((n / 2 : ℕ) : ℤ) := by
      push_cast; ring
    rw [he]
    have h1 : ((n / 4 : ℕ) : ℤ) + r ≤ (n / 2 : ℕ) := by linarith [hr2]
    have hn2 : (n / 2 : ℕ) + (n / 2 : ℕ) ≤ (n : ℕ) := by omega
    have : ((n / 2 : ℕ) : ℤ) + ((n / 2 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
    linarith
  -- The three-cut sum, gate-free.
  have hsum3 : K₁ + n / 2 + K₃ = n := by
    have hK₁Z : (K₁ : ℤ) = ((n / 4 : ℕ) : ℤ) + r := Int.toNat_of_nonneg hpre0
    have hK₃term : ((((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat : ℤ) = ((n / 4 + n / 2 : ℕ) : ℤ) + r :=
      Int.toNat_of_nonneg hsuf0
    have hsuf_le_n : (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat ≤ n := by
      have := Int.toNat_le.mpr hsufn; simpa using this
    -- K₁ + n/2 = (n/4+n/2+r).toNat, since (K₁:ℤ) + n/2 = (n/4+r) + n/2 = n/4+n/2+r.
    have hkey : K₁ + n / 2 = (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat := by
      have hZ : (K₁ : ℤ) + (n / 2 : ℕ) = ((((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat : ℤ) := by
        rw [hK₁Z, hK₃term]; push_cast; ring
      exact_mod_cast hZ
    omega
  -- The cast vector `b'` over `BinVec (K₁ + n/2 + K₃)`.
  set b' : BinVec (K₁ + n / 2 + K₃) := ⟨fun i => b.bit (Fin.cast hsum3 i)⟩ with hb'
  -- The three segConv segments of `b'`.
  set c₁ : BinVec K₁ := ⟨fun i => b'.bit (Fin.castAdd K₃ (Fin.castAdd (n / 2) i))⟩ with hc₁
  set c₂ : BinVec (n / 2) := ⟨fun i => b'.bit (Fin.castAdd K₃ (Fin.natAdd K₁ i))⟩ with hc₂
  set c₃ : BinVec K₃ := ⟨fun i => b'.bit (Fin.natAdd (K₁ + n / 2) i)⟩ with hc₃
  -- RHS chain: whole-string sum (b) = whole-string sum (b') = segConv(b') = segConv-trace.
  have hRHS :
      (∑ m : Fin n → Bool,
          (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
            ∏ i : Fin n, RestrictSegmentFactorization.wfac δ.val (m i))
        = ∑' s : Trace n × Trace n × Trace (n / 2),
            segSum δ.val c₁ (fun t => if t = s.1.bits then 1 else 0)
              * (segSum δ.val c₂ (fun t => if t = s.2.2.bits then 1 else 0)
                * (segSum δ.val c₃ (fun t => if t = s.2.1.bits then 1 else 0)
                  * (if s.1.bits ++ s.2.2.bits ++ s.2.1.bits = τ.bits then (1 : ENNReal) else 0))) := by
    rw [← wholeStringSum_cast hsum3 b δ.val τ.bits]
    rw [PartialDominatesCutIndependence.whole_string_eq_segConv δ.val b' τ.bits]
    rw [segConv_list_eq_trace δ.val c₁ c₂ c₃ τ.bits (by omega) (le_refl _) (by omega)]
  -- The pinned middle window.
  set Mid : BinVec (n / 2) := midWindow b r hr0 hr2 with hMid
  -- LHS chain.
  rw [hRHS]
  -- Step A: reindex the product sample sum, pulling out the middle `M`.
  rw [ENNReal.tsum_prod']
  -- Step B: collapse the middle sum to `M = Mid` via the point middle indicator.
  rw [tsum_eq_single Mid ?_]
  · -- The `M = Mid` term: middleIndicator = 1; rewrite the three weights to segSums.
    have hK₁Z : (K₁ : ℤ) = ((n / 4 : ℕ) : ℤ) + r := Int.toNat_of_nonneg hpre0
    have hK₃Z : ((((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat : ℤ) = ((n / 4 + n / 2 : ℕ) : ℤ) + r :=
      Int.toNat_of_nonneg hsuf0
    -- Segment-equality bridges for prefix / suffix / middle.
    have hpreSeg : ∀ t₁ : Trace n, prefixWeight n b δ r t₁
        = segSum δ.val c₁ (fun t => if t = t₁.bits then 1 else 0) := by
      intro t₁
      rw [prefixWeight_eq_segSum b δ r t₁ hpre0 hpren]
      apply segSum_congr_bit
      intro i
      simp only [hc₁, hb']
      congr 1
    have hsufSeg : ∀ t₂ : Trace n, suffixWeight n b δ r t₂
        = segSum δ.val c₃ (fun t => if t = t₂.bits then 1 else 0) := by
      intro t₂
      rw [suffixWeight_eq_segSum b δ r t₂ hsuf0 hsufn]
      apply segSum_congr_bit
      intro i
      simp only [hc₃, hb']
      congr 1; apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    have hmidSeg : ∀ mid : Trace (n / 2),
        (traceDelete δ.val δ.pos.le δ.lt_one.le (fullTrace Mid) : Trace (n / 2) → ENNReal) mid
          = segSum δ.val c₂ (fun t => if t = mid.bits then 1 else 0) := by
      intro mid
      rw [PartialDominatesCutIndependence.traceDelete_fullTrace_eq_segSum Mid δ mid]
      apply segSum_congr_bit
      intro i
      simp only [hMid, hc₂, hb', midWindow]
      congr 1
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
      omega
    -- Per-(t₁,t₂) rewrite of the LHS summand into the convolution form, then
    -- reindex `∑'(t₁,t₂) ∑'mid → ∑'(t₁,t₂,mid)` and match termwise.
    have hperLHS : ∀ s : Trace n × Trace n,
        prefixWeight n b δ r (Mid, s).2.1 *
            (suffixWeight n b δ r (Mid, s).2.2 * middleIndicator n b (Mid, s).1 r) *
          ∑' mid : Trace (n / 2),
            (traceDelete δ.val δ.pos.le δ.lt_one.le (fullTrace (Mid, s).1) : Trace (n / 2) → ENNReal) mid
              * (if concatTrace (Mid, s).2.1.bits mid.bits (Mid, s).2.2.bits = τ then (1 : ENNReal) else 0)
        = ∑' mid : Trace (n / 2),
            segSum δ.val c₁ (fun t => if t = s.1.bits then 1 else 0)
              * (segSum δ.val c₃ (fun t => if t = s.2.bits then 1 else 0)
                * (segSum δ.val c₂ (fun t => if t = mid.bits then 1 else 0)
                  * (if s.1.bits ++ mid.bits ++ s.2.bits = τ.bits then (1 : ENNReal) else 0))) := by
      rintro ⟨t₁, t₂⟩
      simp only
      rw [middleIndicator_eq_point b Mid r hr0 hr2, hMid, if_pos rfl, mul_one]
      rw [hpreSeg t₁, hsufSeg t₂, ← ENNReal.tsum_mul_left]
      apply tsum_congr; intro mid
      rw [hmidSeg mid]
      -- Per-mid: case on whether the prefix / suffix segment sums vanish.
      by_cases hz1 : segSum δ.val c₁ (fun t => if t = t₁.bits then (1:ENNReal) else 0) = 0
      · rw [hz1]; ring
      by_cases hz3 : segSum δ.val c₃ (fun t => if t = t₂.bits then (1:ENNReal) else 0) = 0
      · rw [hz3]; ring
      -- Both nonzero ⟹ lengths bounded ⟹ concat fits, indicators agree.
      have hl1 : t₁.bits.length ≤ K₁ := segSum_point_ne_zero_length δ.val c₁ t₁.bits hz1
      have hl3 : t₂.bits.length ≤ K₃ := segSum_point_ne_zero_length δ.val c₃ t₂.bits hz3
      have hmidlen : mid.bits.length ≤ n / 2 := mid.length_le
      have hfit : (t₁.bits ++ mid.bits ++ t₂.bits).length ≤ n := by
        rw [List.length_append, List.length_append]; omega
      have hind : (if concatTrace t₁.bits mid.bits t₂.bits = τ then (1:ENNReal) else 0)
          = (if t₁.bits ++ mid.bits ++ t₂.bits = τ.bits then (1:ENNReal) else 0) := by
        by_cases hb : t₁.bits ++ mid.bits ++ t₂.bits = τ.bits
        · rw [if_pos hb, if_pos ((concatTrace_eq_target_iff _ _ _ _ hfit).mpr hb)]
        · rw [if_neg hb, if_neg (fun hc => hb ((concatTrace_eq_target_iff _ _ _ _ hfit).mp hc))]
      rw [hind]; ring
    -- Reindex ∑'(t₁,t₂) ∑'mid and the RHS Trace³ sum to the same iterated form.
    rw [tsum_congr hperLHS]
    -- Convert the RHS Trace³ sum to the iterated `∑'(p:Trace n×Trace n) ∑'mid` form.
    have hRHS2 :
        (∑' s : Trace n × Trace n × Trace (n / 2),
            (segSum δ.val c₁ fun t => if t = s.1.bits then (1:ENNReal) else 0) *
              ((segSum δ.val c₂ fun t => if t = s.2.2.bits then 1 else 0) *
                ((segSum δ.val c₃ fun t => if t = s.2.1.bits then 1 else 0) *
                  (if s.1.bits ++ s.2.2.bits ++ s.2.1.bits = τ.bits then 1 else 0))))
          = ∑' (p : Trace n × Trace n) (mid : Trace (n / 2)),
              (segSum δ.val c₁ fun t => if t = p.1.bits then (1:ENNReal) else 0) *
                ((segSum δ.val c₃ fun t => if t = p.2.bits then 1 else 0) *
                  ((segSum δ.val c₂ fun t => if t = mid.bits then 1 else 0) *
                    (if p.1.bits ++ mid.bits ++ p.2.bits = τ.bits then 1 else 0))) := by
      rw [← (Equiv.prodAssoc (Trace n) (Trace n) (Trace (n / 2))).tsum_eq]
      rw [ENNReal.tsum_prod']
      apply tsum_congr; rintro ⟨t₁, t₂⟩
      apply tsum_congr; intro mid
      simp only [Equiv.prodAssoc_apply]
      ring
    rw [hRHS2]
  · -- Off-diagonal `M ≠ Mid`: middleIndicator = 0 kills every summand.
    intro M hM
    apply ENNReal.tsum_eq_zero.mpr
    rintro ⟨t₁, t₂⟩
    rw [middleIndicator_eq_point b M r hr0 hr2, if_neg hM]
    simp

/-! ### `hcore` (the per-`b` core identity), via offset marginalization -/

/-- **`hcore`** — the remaining hypothesis of
`PartialDominatesBindForm.bind_identity_of_per_b`, proved under the arithmetic
gate `2 * (n / 4) = n / 2`.  Pulling the offset sum `∑' r` outermost and factoring
`offsetWeight n r` out, the per-`r` term equals the (r-independent) whole-string
keep-set sum on the offset support (`per_r_identity`) and `offsetWeight = 0`
elsewhere; the offset then marginalizes via `offsetWeight_tsum_eq_one`. -/
theorem hcore_proof {n : ℕ} (b : BinVec n) (δ : DelProb) (τ : Trace n) :
    (∑' (s : BinVec (n / 2) × Trace n × Trace n) (r : ℤ),
        (offsetWeight n r *
          (prefixWeight n b δ r s.2.1 *
            (suffixWeight n b δ r s.2.2 *
              middleIndicator n b s.1 r)))
        * (∑' mid : Trace (n / 2),
            (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1)
                : Trace (n / 2) → ENNReal) mid
              * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)))
      = ∑ m : Fin n → Bool,
          (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
            ∏ i : Fin n, RestrictSegmentFactorization.wfac δ.val (m i) := by
  -- Abbreviate the inner sample factor (independent of the offset weight).
  set G : (BinVec (n / 2) × Trace n × Trace n) → ℤ → ENNReal :=
    fun s r =>
      (prefixWeight n b δ r s.2.1 *
        (suffixWeight n b δ r s.2.2 * middleIndicator n b s.1 r))
      * (∑' mid : Trace (n / 2),
          (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1)
              : Trace (n / 2) → ENNReal) mid
            * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0))
    with hG
  -- Step 1: rewrite each summand as `offsetWeight r * G s r`.
  have hsummand : (∑' (s : BinVec (n / 2) × Trace n × Trace n) (r : ℤ),
        (offsetWeight n r *
          (prefixWeight n b δ r s.2.1 *
            (suffixWeight n b δ r s.2.2 * middleIndicator n b s.1 r)))
        * (∑' mid : Trace (n / 2),
            (traceDelete δ.val δ.pos.le δ.lt_one.le (PartialDominatesAssembly.fullTrace s.1)
                : Trace (n / 2) → ENNReal) mid
              * (if concatTrace s.2.1.bits mid.bits s.2.2.bits = τ then (1 : ENNReal) else 0)))
      = ∑' (s : BinVec (n / 2) × Trace n × Trace n) (r : ℤ), offsetWeight n r * G s r := by
    apply tsum_congr; intro s
    apply tsum_congr; intro r
    rw [hG]; ring
  rw [hsummand]
  -- Step 2: swap ∑'s and ∑'r.
  rw [ENNReal.tsum_comm]
  -- Step 3: factor offsetWeight out of the s-sum, then marginalize.
  have hmarg : (∑' (r : ℤ) (s : BinVec (n / 2) × Trace n × Trace n), offsetWeight n r * G s r)
      = ∑' r : ℤ, offsetWeight n r *
          (∑ m : Fin n → Bool,
            (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
              ∏ i : Fin n, RestrictSegmentFactorization.wfac δ.val (m i)) := by
    apply tsum_congr; intro r
    rw [ENNReal.tsum_mul_left]
    -- Per r: either r is in the offset support (use per_r_identity) or offsetWeight = 0.
    by_cases hsupp : 0 ≤ r + (n / 4 : ℕ) ∧ r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)
    · congr 1
      rw [← per_r_identity b δ τ r hsupp.1 hsupp.2]
    · rw [offsetWeight_eq_zero_of_not_mem hsupp]
      simp
  rw [hmarg]
  -- Step 4: ∑'r offsetWeight r * C = (∑'r offsetWeight r) * C = 1 * C = C.
  rw [ENNReal.tsum_mul_right, offsetWeight_tsum_eq_one, one_mul]

/-! ### The bind identity and the de-axiomatization of `partial_dominates_traceDist` -/

/-- **Bind identity.**  Under the gate `2 * (n / 4) = n / 2`, the partial-deletion
process pushed through the reconstruction kernel recovers the trace distribution.
This is `bind_identity_of_per_b` with `hcore` discharged by `hcore_proof`. -/
theorem bind_identity {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (td : TraceDist n S δ) (part : PartialDeletionProcess n S δ) (cfd : CoinFlipDist n S) :
    part.toPMF.bind (reconstructKernel δ) = td.toPMF := by
  apply PartialDominatesBindForm.bind_identity_of_per_b td part cfd
  intro b τ
  rw [← hcore_proof b δ τ]
  apply tsum_congr; intro s
  apply tsum_congr; intro r
  congr 1
  apply tsum_congr; intro mid
  congr 1
  congr 1

/-- **De-axiomatization of `partial_dominates_traceDist`** (under the gate
`2 * (n / 4) = n / 2`, which holds whenever `n % 4 ∈ {0, 1}`, in particular under
the paper's `n % 8 = 1`).  Combines `bind_identity` with the data-processing
inequality `Workspace.PriorWork.DataProcessingTV`. -/
theorem partial_dominates_traceDist_of_gate {n : ℕ} {S S' : ProbVec n} {δ : DelProb}
    (td : TraceDist n S δ) (td' : TraceDist n S' δ)
    (part : PartialDeletionProcess n S δ) (part' : PartialDeletionProcess n S' δ)
    (cfd : CoinFlipDist n S) (cfd' : CoinFlipDist n S')
    (_hgate : 2 * (n / 4) = n / 2) :
    Workspace.Types.TVDistance.TVDistance td.toPMF td'.toPMF ≤
      (1 / 2 : ℝ) *
        ∑' s : (BinVec (n / 2) × Trace n × Trace n),
          |((part.toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal) s).toReal
            - ((part'.toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal) s).toReal| := by
  have hbind := bind_identity td part cfd
  have hbind' := bind_identity td' part' cfd'
  have hdpi := DataProcessingTV (reconstructKernel δ) part.toPMF part'.toPMF
  -- Rewrite the bound PMFs to the trace distributions.
  rw [hbind, hbind'] at hdpi
  -- The DPI LHS is exactly `TVDistance td.toPMF td'.toPMF`.
  unfold Workspace.Types.TVDistance.TVDistance
  exact hdpi

/-- **De-axiomatization of `partial_dominates_traceDist` for odd `n`.**  The
gate-free `bind_identity` (the faithful disjoint tiling at suffix boundary
`n/4 + r + n/2`) makes the structural identity hold for all valid offsets and all
`n`; here it is exposed under the paper's odd-`n` hypothesis, so callers (e.g.
`SublemmaLemma6`) can discharge it with `(by omega : n % 2 = 1)`. -/
theorem partial_dominates_traceDist_of_odd {n : ℕ} {S S' : ProbVec n} {δ : DelProb}
    (td : TraceDist n S δ) (td' : TraceDist n S' δ)
    (part : PartialDeletionProcess n S δ) (part' : PartialDeletionProcess n S' δ)
    (cfd : CoinFlipDist n S) (cfd' : CoinFlipDist n S')
    (_hmod : n % 2 = 1) :
    Workspace.Types.TVDistance.TVDistance td.toPMF td'.toPMF ≤
      (1 / 2 : ℝ) *
        ∑' s : (BinVec (n / 2) × Trace n × Trace n),
          |((part.toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal) s).toReal
            - ((part'.toPMF : (BinVec (n / 2) × Trace n × Trace n) → ENNReal) s).toReal| := by
  have hbind := bind_identity td part cfd
  have hbind' := bind_identity td' part' cfd'
  have hdpi := DataProcessingTV (reconstructKernel δ) part.toPMF part'.toPMF
  rw [hbind, hbind'] at hdpi
  unfold Workspace.Types.TVDistance.TVDistance
  exact hdpi

end PartialDominatesHCore
