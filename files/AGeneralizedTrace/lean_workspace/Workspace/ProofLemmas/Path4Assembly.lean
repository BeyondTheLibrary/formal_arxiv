import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.DelProb
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.SignedInnerDefs
import Workspace.ProofLemmas.Path4WindowQ
import Workspace.ProofLemmas.Path4FullQ
import Workspace.ProofLemmas.Path4SuffixRecurrence
import Workspace.ProofLemmas.Path4Envelope
import Workspace.ProofLemmas.Path4MaskProd
import Workspace.ProofLemmas.EllShiftReindex
import Workspace.ProofLemmas.PrefixSuffixZSupport
import Workspace.ProofLemmas.QFactorBounds
import Workspace.ProofLemmas.WitnessOffsetTail
import Workspace.ProofLemmas.WitnessOffsetTailFull
import Workspace.ProofLemmas.LengthWeightBinPMFIdentity
import Workspace.ProofLemmas.LengthsOnlyExists

/-!
# Path4Assembly — the per-mask signed-inner bridge (`signed_inner_bridge`)

This file assembles the four discrepancies of paper Lemma 6 into the per-mask
bridge `signed_inner_bridge`, the crux integration step that de-axiomatised
`paper_lemma_6_algebraic_identity` (the now-removed axiom).

The bridge bounds the per-mask signed inner sum by `4 ·` the matching `altRSum`
aggregate plus an honest, *mask-dependent* perturbation envelope `perMaskPert`
(the (I) perturbation tail), NOT the old uniform `perMaskTail`.

## Structure of the proof (the (I)–(IV) bridge)

* `(I)` — split `Q_sel(r) = fullQ + (Q_sel(r) − fullQ)`; `signedInner = MATCHED + PERT`.
  Triangle: `|signedInner| ≤ |MATCHED| + |PERT|`.  Summed over `p` and after
  collapsing the `z`-sums, `∑_p |PERT| ≤ perMaskPert`.
* `(II)` — `fullQ ∈ (0,1]`, so `|MATCHED| ≤ |∑_r W(r)·(-1)^{p(r)}·∏_mask ellFactor|`.
* `(III)` — suffix off-by-one, handled by the Bernoulli recurrence
  `Path4SuffixRecurrence.matched_suffix_shift_abs_sum_le`.
* `(IV)` — ellFactor reindex + sign + offset/prefix argument shift.

## The `(IV)` offset-argument off-by-one — now resolved

The `(IV)` **offset-argument off-by-one** was once thought to be a structural
wall against a clean `≤ 4∑|altRSum|` bound, but with the `Bin(n/2)` `Fterm`
correction the mask reindex `j' = j+1` aligns MATCHED's ellFactor product with
`altRSum`'s, so no `r`-shift or offset off-by-one survives.  The bound is
proved in `matched_le_altRSum_aggregate` and consumed by `signed_inner_bridge`.
-/

set_option maxHeartbeats 4000000

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

namespace Workspace.ProofLemmas.Path4Assembly

/-- The witness scaling constant `α = (1/(4·e²·√(2π)))·√n`. -/
noncomputable def αcst (n : ℕ) : ℝ :=
  (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n

/-- The fixed-range residual product (`fullQeven = fullQodd` for odd `n`). -/
noncomputable def fullQ (n : ℕ) : ℝ :=
  Workspace.ProofLemmas.Path4FullQ.fullQeven n (αcst n)

/-- The per-offset window product selected by the mask parity: `Q_e(r)` if the
window-parity of the minimal `true`-bit is even, else `Q_o(r)`.  For the empty
mask we keep `Q_e(r) - Q_o(r)`. -/
noncomputable def windowQsel (n : ℕ) (r : ℤ) (b : ℕ) : ℝ :=
  if b = 0 then Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r
  else Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r

/-- The per-`r` residual envelope factor: on the typical window `|r| ≤ n/8` the
window-vs-full gap `|Q_sel(r) − fullQ|` (and the empty gap `|Q_e − Q_o|`) is
`≤ 2√n·exp(-n/128)`; outside it we only have the trivial `≤ 2` (each `Q ∈ [0,1]`),
but there the offset weight is in the exponentially-small binomial tail. -/
noncomputable def pertWindowBound (n : ℕ) (r : ℤ) : ℝ :=
  if (-((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8) then
    2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128)
  else 2

lemma pertWindowBound_nonneg (n : ℕ) (r : ℤ) : 0 ≤ pertWindowBound n r := by
  unfold pertWindowBound; split_ifs <;> positivity

/-- **The honest per-mask perturbation envelope** (the (I) tail, with the `1/2`
folded in).  Per `r`:
`(1/2)·offsetWeight(r)·(∏_{j∈mask} ellFactor(r,j))·pertWindowBound(r)`,
where `pertWindowBound(r)` dominates `|Q_sel(r) − fullQ|` (nonempty) and
`|Q_e(r) − Q_o(r)|` (empty) on the typical window and is the trivial `2` on the
exponentially-light offset tail `|r| > n/8`. -/
noncomputable def perMaskPert (n : ℕ) (m : Workspace.Types.BinVec.BinVec (n / 2)) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
      (offsetWeight n r).toReal *
        (∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)),
          ellFactor n (αcst n) r (j : ℕ)) *
        pertWindowBound n r

lemma perMaskPert_nonneg (n : ℕ) (hn1 : 1 ≤ n)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) : 0 ≤ perMaskPert n m := by
  unfold perMaskPert
  apply mul_nonneg (by norm_num)
  refine Finset.sum_nonneg (fun r _ => ?_)
  apply mul_nonneg
  apply mul_nonneg ENNReal.toReal_nonneg
  · apply Finset.prod_nonneg
    intro j _
    exact (Workspace.ProofLemmas.Path4Envelope.ellFactor_le_one n hn1 r (j : ℕ)).1
  · exact pertWindowBound_nonneg n r

/-! ## (0) No offset rescale: `offsetWeight n r = binPMFInt (n/2) (1/2) (r + n/4)`.

In the CURRENT `AlternatingSumExpression.Fterm`, the first factor is
`binPMFInt (n/2) (1/2) (r + n/4)` (the `Bin(n/2)` correction of commit dd23f38),
which is *byte-for-byte the offset sampling weight* `offsetWeight n r`.  Hence
there is NO offset rescale discrepancy in this formalization — discrepancy (1)
of the old `signed_inner_bounded_by_altRSum` doc is vacuous.  (The files
`OffsetWeightFterm` / `OffsetWeightUniformRatio` relate `offsetWeight` to the OLD
`Bin(n)` convention `binPMFInt n (1/2) (r+n/2)` and no longer apply.) -/
lemma offsetWeight_eq_binPMFInt (n : ℕ) (r : ℤ) :
    (offsetWeight n r).toReal
      = binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) := by
  have hn4 : ((n : ℤ) / 4) = ((n / 4 : ℕ) : ℤ) := by
    exact_mod_cast (Int.natCast_ediv n 4).symm
  have hn2 : ((n : ℤ) / 2) = ((n / 2 : ℕ) : ℤ) := by
    exact_mod_cast (Int.natCast_ediv n 2).symm
  unfold offsetWeight binPMFInt
  simp only
  by_cases h : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)
  · rw [dif_pos h]
    have hcond : 0 ≤ r + (n / 4 : ℤ) ∧ r + (n / 4 : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
      rw [hn4]; exact h
    rw [if_pos hcond]
    unfold binPMF
    have htoNat : (r + (n / 4 : ℤ)).toNat = (r + ((n / 4 : ℕ) : ℤ)).toNat := by rw [hn4]
    rw [htoNat]
    set k : ℕ := (r + ((n / 4 : ℕ) : ℤ)).toNat with hk
    have hkle : k ≤ n / 2 := by
      have := h.2
      rw [hk]
      exact Int.toNat_le.mpr this
    rw [if_pos hkle]
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 / 2)]
    -- C(n/2,k)·(1/2)^(n/2) = C(n/2,k)·(1/2)^k·(1-1/2)^(n/2-k)
    have hpow : ((1 : ℝ) / 2) ^ k * (1 - 1 / 2) ^ (n / 2 - k) = (1 / 2 : ℝ) ^ (n / 2) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, ← pow_add, Nat.add_sub_of_le hkle]
    rw [show (Nat.choose (n / 2) k : ℝ) * (1 / 2) ^ k * (1 - 1 / 2) ^ (n / 2 - k)
          = (Nat.choose (n / 2) k : ℝ) * (((1:ℝ) / 2) ^ k * (1 - 1 / 2) ^ (n / 2 - k)) from by ring,
        hpow]
  · rw [dif_neg h]
    have hcond : ¬ (0 ≤ r + (n / 4 : ℤ) ∧ r + (n / 4 : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) := by
      rw [hn4]; exact h
    rw [if_neg hcond]
    simp

/-! ## (II) `fullQ ∈ [0,1]` -/

lemma fullQ_mem (n : ℕ) (hn1 : 1 ≤ n) : 0 ≤ fullQ n ∧ fullQ n ≤ 1 := by
  unfold fullQ
  exact Workspace.ProofLemmas.Path4FullQ.full_Q_le_one_even n hn1 (αcst n) rfl

/-! ## Q-perturbation bound on the window, both parities + the empty-mask case.

`windowQe`/`windowQo` differ from `fullQ` by at most `√n·exp(-n/128)` (Path4WindowQ),
and for odd `n` `fullQeven = fullQodd`, so the empty-mask gap `|Q_e − Q_o|` is at
most `2√n·exp(-n/128)`. -/

lemma windowQsel_sub_fullQ_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (r : ℤ) (hr : -((n : ℤ) / 8) ≤ r) (hr' : r ≤ (n : ℤ) / 8) (b : ℕ) :
    |windowQsel n r b - fullQ n| ≤ Real.sqrt n * Real.exp (-(n : ℝ) / 128) := by
  have hodd : n % 2 = 1 := by omega
  unfold windowQsel fullQ
  by_cases hb : b = 0
  · subst hb
    simp only []
    have := Workspace.ProofLemmas.Path4WindowQ.windowQe_sub_fullQeven_le n hn hmod r hr hr'
    simpa [αcst] using this
  · simp only [if_neg hb]
    -- |windowQo − fullQeven| = |windowQo − fullQodd| since fullQeven = fullQodd (odd n)
    rw [Workspace.ProofLemmas.Path4FullQ.full_Q_even_eq_odd n hodd (αcst n)]
    have := Workspace.ProofLemmas.Path4WindowQ.windowQo_sub_fullQodd_le n hn hmod r hr hr'
    simpa [αcst] using this

/-- The empty-mask gap `|Q_e(r) − Q_o(r)| ≤ 2√n·exp(-n/128)`. -/
lemma windowQe_sub_windowQo_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (r : ℤ) (hr : -((n : ℤ) / 8) ≤ r) (hr' : r ≤ (n : ℤ) / 8) :
    |Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r -
        Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r|
      ≤ 2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) := by
  have hodd : n % 2 = 1 := by omega
  have he := Workspace.ProofLemmas.Path4WindowQ.windowQe_sub_fullQeven_le n hn hmod r hr hr'
  have ho := Workspace.ProofLemmas.Path4WindowQ.windowQo_sub_fullQodd_le n hn hmod r hr hr'
  simp only [αcst] at he ho ⊢
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
  rw [Workspace.ProofLemmas.Path4FullQ.full_Q_even_eq_odd n hodd α] at he
  -- |We - Wo| ≤ |We - fullQodd| + |fullQodd - Wo| ≤ √n e + √n e
  have htri : |Workspace.ProofLemmas.Path4WindowQ.windowQe n α r -
        Workspace.ProofLemmas.Path4WindowQ.windowQo n α r|
      ≤ |Workspace.ProofLemmas.Path4WindowQ.windowQe n α r -
            Workspace.ProofLemmas.Path4FullQ.fullQodd n α|
        + |Workspace.ProofLemmas.Path4FullQ.fullQodd n α -
            Workspace.ProofLemmas.Path4WindowQ.windowQo n α r| := by
    have := abs_sub_le (Workspace.ProofLemmas.Path4WindowQ.windowQe n α r)
      (Workspace.ProofLemmas.Path4FullQ.fullQodd n α)
      (Workspace.ProofLemmas.Path4WindowQ.windowQo n α r)
    exact this
  have ho' : |Workspace.ProofLemmas.Path4FullQ.fullQodd n α -
        Workspace.ProofLemmas.Path4WindowQ.windowQo n α r|
      ≤ Real.sqrt n * Real.exp (-(n : ℝ) / 128) := by
    rw [abs_sub_comm]; exact ho
  have hsum : |Workspace.ProofLemmas.Path4WindowQ.windowQe n α r -
            Workspace.ProofLemmas.Path4FullQ.fullQodd n α|
        + |Workspace.ProofLemmas.Path4FullQ.fullQodd n α -
            Workspace.ProofLemmas.Path4WindowQ.windowQo n α r|
      ≤ Real.sqrt n * Real.exp (-(n : ℝ) / 128) +
          Real.sqrt n * Real.exp (-(n : ℝ) / 128) := add_le_add he ho'
  calc |Workspace.ProofLemmas.Path4WindowQ.windowQe n α r -
        Workspace.ProofLemmas.Path4WindowQ.windowQo n α r|
      ≤ _ := htri
    _ ≤ _ := hsum
    _ = 2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) := by ring

/-! ## Aggregate of the perturbation envelope over masks: `perMaskPert_sum_le`. -/

/-- `∑_{r ∈ Icc(-(n/4))(n/4)} (offsetWeight n r).toReal ≤ 1` (public re-derivation
of the private `Path4Envelope.offsetWeight_finsum_toReal_le_one`). -/
lemma offsetWeight_finsum_le_one (n : ℕ) :
    ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)), (offsetWeight n r).toReal ≤ 1 := by
  have hne_top : ∀ r : ℤ, offsetWeight n r ≠ ⊤ := by
    intro r
    unfold offsetWeight
    simp only
    split_ifs
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    · exact ENNReal.zero_ne_top
  have hsum_toReal : ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)), (offsetWeight n r).toReal
      = (∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)), offsetWeight n r).toReal := by
    rw [ENNReal.toReal_sum]
    intro r _; exact hne_top r
  rw [hsum_toReal]
  have hle : (∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)), offsetWeight n r)
      ≤ ∑' r : ℤ, offsetWeight n r := ENNReal.sum_le_tsum _
  rw [OffsetWeightSumOne.offsetWeight_tsum_eq_one n] at hle
  have hmono : (∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)), offsetWeight n r).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
  simpa using hmono

/-- `2 * αcst n ≤ 2 * √n` (the witness constant `1/(4 e² √(2π)) ≤ 1`). -/
lemma two_alpha_le (n : ℕ) : 2 * αcst n ≤ 2 * Real.sqrt n := by
  have hαle : αcst n ≤ Real.sqrt n := by
    unfold αcst
    have hc : (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have he : (1 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
      have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        apply Real.sqrt_le_sqrt; nlinarith [Real.pi_gt_d2]
      nlinarith [he, hs, Real.exp_pos 2, Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2 * Real.pi)]
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith [hc, hsqrt_nn]
  linarith

lemma sqrt_n_lb (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) : (10 ^ 6 : ℝ) ≤ Real.sqrt n := by
  have h12 : Real.sqrt ((10 ^ 12 : ℝ)) = (10 ^ 6 : ℝ) := by
    rw [show (10 ^ 12 : ℝ) = (10 ^ 6 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [← h12]
  apply Real.sqrt_le_sqrt; exact_mod_cast hn

/-- The analytic exponent bound for the aggregate, with the two-piece envelope:
`(1/2) · exp(2α) · (2√n·exp(-n/128) + 4·exp(-n/256)) ≤ exp(-n/512)` for `n ≥ 10^12`. -/
lemma aggregate_exp_bound (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (1 / 2 : ℝ) * Real.exp (2 * αcst n) *
        (2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) + 4 * Real.exp (-(n : ℝ) / 256))
      ≤ Real.exp (-(n : ℝ) / 512) := by
  have hnpos : (0 : ℝ) < n := by
    have : (0:ℕ) < 10^12 := by norm_num
    exact_mod_cast (by omega : 0 < n)
  have h2α : 2 * αcst n ≤ 2 * Real.sqrt n := two_alpha_le n
  have hsqrt_lb : (10 ^ 6 : ℝ) ≤ Real.sqrt n := sqrt_n_lb n hn
  set s : ℝ := Real.sqrt n with hs
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hns : (n : ℝ) = s ^ 2 := by rw [hs]; rw [Real.sq_sqrt (le_of_lt hnpos)]
  -- 2s ≤ exp s
  have h2s_exp : 2 * s ≤ Real.exp s := by
    have hquad : 1 + s + s ^ 2 / 2 ≤ Real.exp s := Real.quadratic_le_exp_of_nonneg hs_nn
    nlinarith [hsqrt_lb, hquad, sq_nonneg (s - 2)]
  -- exp(2α) ≤ exp(2s)
  have hexp2α : Real.exp (2 * αcst n) ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr (by rw [hs] at h2α ⊢; exact h2α)
  have hexp2α_nn : 0 ≤ Real.exp (2 * αcst n) := le_of_lt (Real.exp_pos _)
  -- Each summand bound:
  -- (1/2)·exp(2α)·2√n·exp(-n/128) = s·exp(2α)·exp(-n/128) ≤ s·exp(2s−s²/128)
  -- (1/2)·exp(2α)·4·exp(-n/256) = 2·exp(2α)·exp(-n/256) ≤ 2·exp(2s−s²/256)
  -- Sum ≤ exp(-s²/512) by absorbing the polynomial via exp s.
  have hP1 : (1 / 2 : ℝ) * Real.exp (2 * αcst n) * (2 * s * Real.exp (-(n : ℝ) / 128))
      ≤ Real.exp (3 * s - s ^ 2 / 128) := by
    have hstep : Real.exp (2 * αcst n) * Real.exp (-(n : ℝ) / 128) ≤ Real.exp (2 * s - s ^ 2 / 128) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [hns]; rw [hs] at h2α; linarith
    calc (1 / 2 : ℝ) * Real.exp (2 * αcst n) * (2 * s * Real.exp (-(n : ℝ) / 128))
        = s * (Real.exp (2 * αcst n) * Real.exp (-(n : ℝ) / 128)) := by ring
      _ ≤ s * Real.exp (2 * s - s ^ 2 / 128) := mul_le_mul_of_nonneg_left hstep hs_nn
      _ ≤ Real.exp s * Real.exp (2 * s - s ^ 2 / 128) := by
          have : s ≤ Real.exp s := by nlinarith [Real.add_one_le_exp s]
          exact mul_le_mul_of_nonneg_right this (le_of_lt (Real.exp_pos _))
      _ = Real.exp (s + (2 * s - s ^ 2 / 128)) := by rw [← Real.exp_add]
      _ = Real.exp (3 * s - s ^ 2 / 128) := by ring_nf
  have hP2 : (1 / 2 : ℝ) * Real.exp (2 * αcst n) * (4 * Real.exp (-(n : ℝ) / 256))
      ≤ Real.exp (3 * s - s ^ 2 / 256) := by
    have hstep : Real.exp (2 * αcst n) * Real.exp (-(n : ℝ) / 256) ≤ Real.exp (2 * s - s ^ 2 / 256) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [hns]; rw [hs] at h2α; linarith
    calc (1 / 2 : ℝ) * Real.exp (2 * αcst n) * (4 * Real.exp (-(n : ℝ) / 256))
        = 2 * (Real.exp (2 * αcst n) * Real.exp (-(n : ℝ) / 256)) := by ring
      _ ≤ 2 * Real.exp (2 * s - s ^ 2 / 256) := mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ ≤ Real.exp s * Real.exp (2 * s - s ^ 2 / 256) := by
          have : (2 : ℝ) ≤ Real.exp s := by nlinarith [Real.add_one_le_exp s, hsqrt_lb]
          exact mul_le_mul_of_nonneg_right this (le_of_lt (Real.exp_pos _))
      _ = Real.exp (s + (2 * s - s ^ 2 / 256)) := by rw [← Real.exp_add]
      _ = Real.exp (3 * s - s ^ 2 / 256) := by ring_nf
  -- exp(3s − s²/128) + exp(3s − s²/256) ≤ exp(-s²/512)
  have hgoal_eq : Real.exp (-(n : ℝ) / 512) = Real.exp (-(s ^ 2) / 512) := by rw [hns]
  rw [hgoal_eq]
  have hsum_split : (1 / 2 : ℝ) * Real.exp (2 * αcst n) *
        (2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) + 4 * Real.exp (-(n : ℝ) / 256))
      = (1 / 2 : ℝ) * Real.exp (2 * αcst n) * (2 * s * Real.exp (-(n : ℝ) / 128))
        + (1 / 2 : ℝ) * Real.exp (2 * αcst n) * (4 * Real.exp (-(n : ℝ) / 256)) := by
    rw [hs]; ring
  rw [hsum_split]
  refine (add_le_add hP1 hP2).trans ?_
  -- both ≤ exp(-s²/512)/2.  exp x · 2 ≤ exp y  ⟺  x + log 2 ≤ y; we use log 2 ≤ 1.
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hb1 : Real.exp (3 * s - s ^ 2 / 128) ≤ Real.exp (-(s ^ 2) / 512) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    rw [show (2:ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hsqrt_lb, hlog2, sq_nonneg s]
  have hb2 : Real.exp (3 * s - s ^ 2 / 256) ≤ Real.exp (-(s ^ 2) / 512) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    rw [show (2:ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hsqrt_lb, hlog2, sq_nonneg s]
  have := add_le_add hb1 hb2
  linarith [this]

/-- **Offset tail sum.**  The offset mass over `r ∈ Icc(-(n/4))(n/4)` with `|r| > n/8`
is `≤ 2·exp(-n/256)`. -/
lemma offset_tail_sum_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1) :
    ∑ r ∈ (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))).filter
        (fun r => ¬ (-((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8)), (offsetWeight n r).toReal
      ≤ 2 * Real.exp (-(n : ℝ) / 256) := by
  classical
  have hn1 : 1 ≤ n := by omega
  -- Rewrite each offset to the binomial pmf, reindexed by k = (r + n/4).toNat.
  -- The map  r ↦ (r + (n/4:ℤ)).toNat  is injective on the Icc and sends the
  -- tail filter into  range(n/8) ∪ Ico(n/2 - n/8 + 1, n/2 + 1).
  set Sset : Finset ℤ := (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))).filter
      (fun r => ¬ (-((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8)) with hSset
  set g : ℤ → ℕ := fun r => (r + ((n / 4 : ℕ) : ℤ)).toNat with hg
  -- offsetWeight toReal = binPMF (n/2) (1/2) (g r), for r in the Icc.
  have hterm : ∀ r ∈ Sset, (offsetWeight n r).toReal = binPMF (n / 2) (1 / 2 : ℝ) (g r) := by
    intro r hr
    rw [hSset, Finset.mem_filter, Finset.mem_Icc] at hr
    rw [WitnessOffsetTail.offsetWeight_toReal_eq_binPMFInt n r]
    unfold binPMFInt
    have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
    have hlow : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := by rw [hc4]; have := hr.1.1; omega
    have hhigh : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
      have hc2 : ((n / 2 : ℕ) : ℤ) = (n / 2 : ℤ) := Int.natCast_div n 2
      rw [hc4, hc2]; have := hr.1.2; omega
    rw [if_pos ⟨hlow, hhigh⟩]
  rw [Finset.sum_congr rfl hterm]
  -- g is injective on Sset
  have hginj : ∀ a ∈ Sset, ∀ b ∈ Sset, g a = g b → a = b := by
    intro a ha b hb hab
    rw [hSset, Finset.mem_filter, Finset.mem_Icc] at ha hb
    rw [hg] at hab
    simp only at hab
    have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
    have hca : 0 ≤ a + ((n / 4 : ℕ) : ℤ) := by rw [hc4]; have := ha.1.1; omega
    have hcb : 0 ≤ b + ((n / 4 : ℕ) : ℤ) := by rw [hc4]; have := hb.1.1; omega
    have heqz : a + ((n / 4 : ℕ) : ℤ) = b + ((n / 4 : ℕ) : ℤ) := by
      rw [← Int.toNat_of_nonneg hca, ← Int.toNat_of_nonneg hcb, hab]
    omega
  -- image of Sset under g, with the sum reindexed
  rw [← Finset.sum_image (g := g) (s := Sset)
        (f := fun k => binPMF (n / 2) (1 / 2 : ℝ) k) hginj]
  -- the image is a subset of  range(n/8) ∪ Ico(n/2-n/8+1, n/2+1)
  set T : Finset ℕ := Finset.range (n / 8) ∪ Finset.Ico (n / 2 - n / 8 + 1) (n / 2 + 1) with hT
  have hsubset : Sset.image g ⊆ T := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hrS, hrk⟩ := hk
    rw [hSset, Finset.mem_filter, Finset.mem_Icc] at hrS
    rw [hT, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
    have hca : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := by rw [hc4]; have := hrS.1.1; omega
    have hkeq : (k : ℤ) = r + ((n / 4 : ℕ) : ℤ) := by
      rw [← hrk, hg]; simp only; rw [Int.toNat_of_nonneg hca]
    rw [hc4] at hkeq
    -- the tail condition: r < -n/8 or r > n/8
    have htail := hrS.2
    push_neg at htail
    -- n%8=1 arithmetic
    by_cases hrlt : r < -((n : ℤ) / 8)
    · left; omega
    · right
      have hrgt : (n : ℤ) / 8 < r := htail (not_lt.mp hrlt)
      have hkint : (n / 2 - n / 8 + 1 : ℤ) ≤ (k : ℤ) ∧ (k : ℤ) < (n / 2 + 1 : ℤ) := by
        constructor
        · have h1 : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := Int.natCast_div n 2
          have h2 : ((n / 8 : ℕ) : ℤ) = (n : ℤ) / 8 := Int.natCast_div n 8
          rw [hkeq]; omega
        · have h1 : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := Int.natCast_div n 2
          rw [hkeq]; have := hrS.1.2; omega
      constructor
      · have : ((n / 2 - n / 8 + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by
          have he : ((n / 2 - n / 8 + 1 : ℕ) : ℤ) = (n / 2 - n / 8 + 1 : ℤ) := by
            have : n / 8 ≤ n / 2 := by omega
            push_cast [Nat.sub_add_cancel]; omega
          rw [he]; exact hkint.1
        exact_mod_cast this
      · have : (k : ℤ) < ((n / 2 + 1 : ℕ) : ℤ) := by push_cast; exact hkint.2
        exact_mod_cast this
  -- bound by the sum over T, which splits into the two binomial tails
  have hnn : ∀ k ∈ T, (0:ℝ) ≤ binPMF (n / 2) (1 / 2 : ℝ) k := by
    intro k _
    unfold binPMF; split_ifs
    · positivity
    · exact le_refl 0
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k hk _ => hnn k hk)).trans ?_
  -- ∑_T binPMF ≤ ∑_range(n/8) + ∑_Ico(...)
  have hdisj : Disjoint (Finset.range (n / 8)) (Finset.Ico (n / 2 - n / 8 + 1) (n / 2 + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico] at hk'
    omega
  rw [hT, Finset.sum_union hdisj]
  have hlow := WitnessOffsetTail.offset_lower_tail n hn
  have hupp := WitnessOffsetTailFull.offset_upper_tail n hn
  calc (∑ k ∈ Finset.range (n / 8), binPMF (n / 2) (1 / 2 : ℝ) k)
        + ∑ k ∈ Finset.Ico (n / 2 - n / 8 + 1) (n / 2 + 1), binPMF (n / 2) (1 / 2 : ℝ) k
      ≤ Real.exp (-((n : ℝ) / 256)) + Real.exp (-((n : ℝ) / 256)) := add_le_add hlow hupp
    _ = 2 * Real.exp (-(n : ℝ) / 256) := by rw [neg_div]; ring

/-- **The perturbation envelope aggregates to `exp(-n/512)`.** -/
theorem perMaskPert_sum_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (hδ_lb : (320 : ℝ) / Real.sqrt n ≤ δ.val) (hδ_ub : δ.val ≤ 1 / 2) :
    ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
        (if (∀ j₁ j₂ : Fin (n / 2),
                m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
         then perMaskPert n m else 0)
      ≤ Real.exp (-(n : ℝ) / 512) := by
  classical
  have hn1 : 1 ≤ n := by omega
  -- bound each guarded term by perMaskPert (nonneg), drop the guard
  have hdrop : ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
        (if (∀ j₁ j₂ : Fin (n / 2),
                m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
         then perMaskPert n m else 0)
      ≤ ∑ m : Workspace.Types.BinVec.BinVec (n / 2), perMaskPert n m := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    by_cases h : (∀ j₁ j₂ : Fin (n / 2),
        m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
    · rw [if_pos h]
    · rw [if_neg h]; exact perMaskPert_nonneg n hn1 m
  refine hdrop.trans ?_
  -- ∑_m perMaskPert = (1/2)·∑_r offset(r)·pertWindowBound(r)·(∑_m ∏ell)
  have hswap : ∑ m : Workspace.Types.BinVec.BinVec (n / 2), perMaskPert n m
      = (1 / 2 : ℝ) * ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          (offsetWeight n r).toReal * pertWindowBound n r *
            (∑ m : Workspace.Types.BinVec.BinVec (n / 2),
              ∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)),
                ellFactor n (αcst n) r (j : ℕ)) := by
    unfold perMaskPert
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hswap]
  -- bound the m-sum of products by exp(2α)
  have hmaskbound : ∀ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
      (offsetWeight n r).toReal * pertWindowBound n r *
        (∑ m : Workspace.Types.BinVec.BinVec (n / 2),
          ∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)),
            ellFactor n (αcst n) r (j : ℕ))
      ≤ Real.exp (2 * αcst n) * ((offsetWeight n r).toReal * pertWindowBound n r) := by
    intro r _
    have hmp : (∑ m : Workspace.Types.BinVec.BinVec (n / 2),
          ∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)),
            ellFactor n (αcst n) r (j : ℕ))
        ≤ Real.exp (2 * αcst n) := by
      have h := Workspace.ProofLemmas.Path4MaskProd.mask_ellfactor_product_sum n hn1 r
      simpa [αcst] using h
    have hfac_nn : (0 : ℝ) ≤ (offsetWeight n r).toReal * pertWindowBound n r :=
      mul_nonneg ENNReal.toReal_nonneg (pertWindowBound_nonneg n r)
    have := mul_le_mul_of_nonneg_left hmp hfac_nn
    nlinarith [this, hfac_nn, le_of_lt (Real.exp_pos (2 * αcst n))]
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmaskbound) (by norm_num : (0:ℝ) ≤ 1/2)).trans ?_
  -- ∑_r exp(2α)·(offset·pertWindowBound) = exp(2α)·∑_r offset·pertWindowBound
  rw [← Finset.mul_sum]
  -- split ∑_r offset·pertWindowBound = typical + tail
  set E : ℝ := ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
      (offsetWeight n r).toReal * pertWindowBound n r with hE
  have hE_le : E ≤ 2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) + 4 * Real.exp (-(n : ℝ) / 256) := by
    rw [hE]
    -- split the Icc into the typical part (|r|≤n/8) and the tail
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
          (fun r => -((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8)]
    apply add_le_add
    · -- typical: pertWindowBound = 2√n·exp(-n/128), bounded by 2√n·exp · ∑offset ≤ 2√n·exp
      have htyp : ∀ r ∈ (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))).filter
            (fun r => -((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8),
          (offsetWeight n r).toReal * pertWindowBound n r
            ≤ (offsetWeight n r).toReal * (2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128)) := by
        intro r hr
        rw [Finset.mem_filter] at hr
        unfold pertWindowBound
        rw [if_pos hr.2]
      refine (Finset.sum_le_sum htyp).trans ?_
      rw [← Finset.sum_mul]
      have hsub : ∑ r ∈ (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))).filter
            (fun r => -((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8), (offsetWeight n r).toReal
          ≤ ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)), (offsetWeight n r).toReal :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun r _ _ => ENNReal.toReal_nonneg)
      have hone := offsetWeight_finsum_le_one n
      have hbnn : (0:ℝ) ≤ 2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) := by positivity
      calc (∑ r ∈ _, (offsetWeight n r).toReal) * (2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128))
          ≤ 1 * (2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128)) :=
            mul_le_mul_of_nonneg_right (le_trans hsub hone) hbnn
        _ ≤ 2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) := by linarith
    · -- tail: pertWindowBound = 2, so ∑ = 2·(tail offset mass) ≤ 2·2exp(-n/256) = 4exp(-n/256)
      have htail : ∀ r ∈ (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))).filter
            (fun r => ¬ (-((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8)),
          (offsetWeight n r).toReal * pertWindowBound n r
            = (offsetWeight n r).toReal * 2 := by
        intro r hr
        rw [Finset.mem_filter] at hr
        unfold pertWindowBound
        rw [if_neg hr.2]
      rw [Finset.sum_congr rfl htail, ← Finset.sum_mul]
      have htailsum := offset_tail_sum_le n hn hmod
      calc (∑ r ∈ _, (offsetWeight n r).toReal) * 2
          ≤ (2 * Real.exp (-(n : ℝ) / 256)) * 2 :=
            mul_le_mul_of_nonneg_right htailsum (by norm_num)
        _ = 4 * Real.exp (-(n : ℝ) / 256) := by ring
  have hexp_nn : 0 ≤ Real.exp (2 * αcst n) := le_of_lt (Real.exp_pos _)
  calc (1 / 2 : ℝ) * (Real.exp (2 * αcst n) * E)
      = (1 / 2 : ℝ) * Real.exp (2 * αcst n) * E := by ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (2 * αcst n) *
          (2 * Real.sqrt n * Real.exp (-(n : ℝ) / 128) + 4 * Real.exp (-(n : ℝ) / 256)) := by
        apply mul_le_mul_of_nonneg_left hE_le
        positivity
    _ ≤ Real.exp (-(n : ℝ) / 512) := aggregate_exp_bound n hn

/-! ## Window-range fact: `Icc(-(n/4))(n/4)` is NOT contained in `|r| ≤ n/8`.

The `signedInner`/`altRSum` sums run over `r ∈ Icc(-(n/4))(n/4)`, but the window
`Q`-perturbation bounds (Path4WindowQ) require `|r| ≤ n/8`.  For `|r| > n/8` we use
the trivial bound `|Q_sel(r) − fullQ| ≤ 1` (both factors in `[0,1]`) PLUS the
fact that the offset weight tail there is exponentially small.  This range
split is handled inside `perMaskPert`'s honest envelope by
using the `2√n·exp(-n/128)` bound only where it holds, but the offset weight
already decays past `n/8`.  We isolate the analytic obligations below. -/

/-- The **matched integrand**: `signedInner` with the window product `Q_sel(r)`
replaced by the fixed-range `fullQ n` (and the empty-mask case set to `0`, since
`fullQ` is parity-independent so `fullQ - fullQ = 0`).  After pulling the
window-parity sign `(-1)^{((n/4)+r+min')%2}` out of the parity `if`-selector. -/
noncomputable def matchedInner (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (p : ℕ × ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
    (offsetWeight n r).toReal *
      (prefixLengthWeight n δ r p.1).toReal *
      (suffixLengthWeight n δ r p.2).toReal *
      (if h : ((Finset.univ : Finset (Fin (n / 2))).filter
                  (fun j => m.bit j = true)).Nonempty then
          (-1 : ℝ) ^ (((n / 4 : ℤ) + r +
              ((((Finset.univ : Finset (Fin (n / 2))).filter
                  (fun j => m.bit j = true)).min' h : Fin (n / 2)) : ℕ)) % 2).toNat *
            fullQ n *
            (∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter
                (fun j => m.bit j = true)),
              ellFactor n (αcst n) r (j : ℕ))
        else (0 : ℝ))

/-- The **perturbation integrand**: `signedInner − matchedInner`.  For a nonempty
mask it is `∑_r W(r)·(-1)^{…}·(Q_sel(r) − fullQ)·∏ ellFactor`; for the empty mask
it is `∑_r W(r)·(Q_e(r) − Q_o(r))`. -/
noncomputable def pertInner (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (p : ℕ × ℕ) : ℝ :=
  Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p
    - matchedInner n δ m p

/-- Trivial split identity. -/
lemma signedInner_split (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (p : ℕ × ℕ) :
    Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p
      = matchedInner n δ m p + pertInner n δ m p := by
  unfold pertInner; ring

/-! ### The window-product selector identity.

`signedInner`'s nonempty branch uses `(-1)^{x%2} · (if x%2=0 then Q_e else Q_o)`,
where `Q_e = windowQe n (αcst n) r`, `Q_o = windowQo n (αcst n) r` and
`x = (n/4)+r+min'`.  We record that this equals the `windowQsel`-based form so the
perturbation factor `Q_sel − fullQ` can be bounded by `windowQsel_sub_fullQ_le`. -/

/-- **The MATCHED bound — now UNBLOCKED** (the `Fterm` ellFactor index is `j'-1`,
so the mask reindex `j' = j+1` makes MATCHED's ellFactor product at offset `r`
equal `altRSum`'s ellFactor product at offset `r`; no `r`-shift, no offset
off-by-one).  See the proof for the (I)–(IV) chain. -/

private noncomputable def mlaMaskEll (n : ℕ) (r : ℤ)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) : ℝ :=
  ∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)),
    ellFactor n (αcst n) r (j : ℕ)

private noncomputable def signOf (k : ℤ) : ℝ := (-1 : ℝ) ^ (k % 2).toNat

private lemma signOf_mul_add (a b : ℤ) : signOf (a + b) = signOf a * signOf b := by
  unfold signOf
  have ha := Int.emod_two_eq_zero_or_one a
  have hb := Int.emod_two_eq_zero_or_one b
  have hab : (a + b) % 2 = (a % 2 + b % 2) % 2 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [hab, ha, hb] <;> norm_num

private lemma signOf_natAbs (r : ℤ) : signOf r = (-1 : ℝ) ^ r.natAbs := by
  unfold signOf
  have hpar : (r % 2).toNat = r.natAbs % 2 := by omega
  rw [hpar]
  rcases Nat.even_or_odd r.natAbs with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show (k+k) % 2 = 0 from by omega, show k + k = 2*k from by ring]; simp [pow_mul]
  · rw [hk, show (2*k+1) % 2 = 1 from by omega]; simp [pow_add, pow_mul]

private lemma signOf_abs (k : ℤ) : |signOf k| = 1 := by
  unfold signOf; rw [abs_pow]; simp [abs_neg, abs_one]

private lemma matchedInner_nonempty_form (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm zp : ℕ)
    (hne : ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).Nonempty) :
    matchedInner n δ m (zm, zp)
      = signOf ((n / 4 : ℤ) +
          ((((Finset.univ : Finset (Fin (n / 2))).filter
              (fun j => m.bit j = true)).min' hne : Fin (n / 2)) : ℕ)) * fullQ n *
        ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          signOf r * (offsetWeight n r).toReal *
            (prefixLengthWeight n δ r zm).toReal *
            (suffixLengthWeight n δ r zp).toReal * mlaMaskEll n r m := by
  unfold matchedInner mlaMaskEll
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [dif_pos hne]
  set mn : ℕ := ((((Finset.univ : Finset (Fin (n / 2))).filter
      (fun j => m.bit j = true)).min' hne : Fin (n / 2)) : ℕ) with hmn
  have hsign : (-1 : ℝ) ^ (((n / 4 : ℤ) + r + (mn : ℤ)) % 2).toNat
      = signOf ((n / 4 : ℤ) + (mn : ℤ)) * signOf r := by
    have : ((n / 4 : ℤ) + r + (mn : ℤ)) = ((n / 4 : ℤ) + (mn : ℤ)) + r := by ring
    rw [show (-1 : ℝ) ^ (((n / 4 : ℤ) + r + (mn : ℤ)) % 2).toNat
          = signOf ((n / 4 : ℤ) + r + (mn : ℤ)) from rfl, this, signOf_mul_add]
  rw [hsign]
  ring

private lemma mlaMaskEll_eq_sigma (n : ℕ) (r : ℤ) (m : Workspace.Types.BinVec.BinVec (n / 2)) :
    mlaMaskEll n r m
      = ∏ j' ∈ Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m,
          ellFactor n (αcst n) r (j' - 1) := by
  unfold mlaMaskEll Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet
  rw [Finset.prod_image]
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    have : (j.val + 1 - 1 : ℕ) = (j : ℕ) := by omega
    rw [this]
  · intro a _ b _ hab
    simp only at hab
    have : a.val = b.val := by omega
    exact Fin.ext this

private noncomputable def mlaC (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm : ℕ) (r : ℤ) : ℝ :=
  signOf r * (offsetWeight n r).toReal * (prefixLengthWeight n δ r zm).toReal *
    mlaMaskEll n r m

private noncomputable def mlaMof (n : ℕ) (r : ℤ) : ℕ := ((n / 4 : ℤ) - r).toNat

private lemma mlaCore_eq_altRSum (n : ℕ) (hmod : n % 8 = 1) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm w : ℕ) :
    (∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        mlaC n δ m zm r * binPMF (mlaMof n r) (1 - δ.val) w)
      = altRSum n δ.val (αcst n) zm w
          (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m) := by
  unfold altRSum
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_Icc] at hr
  have hsupp : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
    have hc2 : ((n / 2 : ℕ) : ℤ) = (n / 2 : ℤ) := Int.natCast_div n 2
    rw [hc4, hc2]; omega
  unfold mlaC mlaMof Fterm
  rw [mlaMaskEll_eq_sigma]
  rw [signOf_natAbs]
  rw [Workspace.ProofLemmas.Path4Assembly.offsetWeight_eq_binPMFInt]
  rw [Workspace.ProofLemmas.LengthWeightBinPMFIdentity.prefixLengthWeight_toReal_eq n δ r zm hsupp]
  rw [← Workspace.ProofLemmas.LengthWeightBinPMFIdentity.binPMFInt_natCast
        (((n / 4 : ℤ) - r).toNat) (1 - δ.val) w]
  ring

private lemma mlaMatched_eq_cBinPMF (n : ℕ) (hmod : n % 8 = 1) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm zp : ℕ) :
    (∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        signOf r * (offsetWeight n r).toReal *
          (prefixLengthWeight n δ r zm).toReal *
          (suffixLengthWeight n δ r zp).toReal * mlaMaskEll n r m)
      = ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          mlaC n δ m zm r * binPMF ((mlaMof n r) + 1) (1 - δ.val) zp := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_Icc] at hr
  have hsupp : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
    have hc2 : ((n / 2 : ℕ) : ℤ) = (n / 2 : ℤ) := Int.natCast_div n 2
    rw [hc4, hc2]; omega
  unfold mlaC mlaMof
  rw [Workspace.ProofLemmas.LengthWeightBinPMFIdentity.suffixLengthWeight_toReal_eq n hmod δ r zp hsupp]
  ring

private lemma mlaMof_le (n : ℕ) (hmod : n % 8 = 1) (r : ℤ) (hr : -(n / 4 : ℤ) ≤ r) :
    mlaMof n r ≤ n / 2 := by
  unfold mlaMof
  have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
  have hub : ((n / 4 : ℤ) - r) ≤ ((2 * (n / 4) : ℕ) : ℤ) := by
    push_cast; rw [← hc4]; omega
  have htn : ((n / 4 : ℤ) - r).toNat ≤ 2 * (n / 4) := by
    have := Int.toNat_le.mpr hub
    simpa using this
  omega

private lemma mlaCore_high_w_zero (n : ℕ) (hmod : n % 8 = 1) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm w : ℕ) (hw : n / 2 + 1 ≤ w) :
    (∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        mlaC n δ m zm r * binPMF (mlaMof n r) (1 - δ.val) w) = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_Icc] at hr
  have hMof : mlaMof n r ≤ n / 2 := mlaMof_le n hmod r hr.1
  have : binPMF (mlaMof n r) (1 - δ.val) w = 0 := by
    unfold binPMF; rw [if_neg (by omega)]
  rw [this, mul_zero]

private lemma mlaMatchedInner_abs (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm zp : ℕ)
    (hne : ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).Nonempty) :
    |matchedInner n δ m (zm, zp)|
      = fullQ n *
        |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
            mlaC n δ m zm r * binPMF ((mlaMof n r) + 1) (1 - δ.val) zp| := by
  have hn1 : 1 ≤ n := by omega
  rw [matchedInner_nonempty_form n δ m zm zp hne]
  rw [mlaMatched_eq_cBinPMF n hmod δ m zm zp]
  rw [abs_mul, abs_mul]
  have hs : |signOf ((n / 4 : ℤ) +
      ((((Finset.univ : Finset (Fin (n / 2))).filter
          (fun j => m.bit j = true)).min' hne : Fin (n / 2)) : ℕ))| = 1 := signOf_abs _
  rw [hs, one_mul]
  rw [abs_of_nonneg (fullQ_mem n hn1).1]

private lemma mlaPerZm_bound (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb) (hδ_ub : δ.val ≤ 1 / 2)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (zm : ℕ) :
    (∑ zp ∈ Finset.range (n / 2 + 2),
        |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
            mlaC n δ m zm r * binPMF ((mlaMof n r) + 1) (1 - δ.val) zp|)
      ≤ ∑ w ∈ Finset.range (n / 2 + 1),
          |altRSum n δ.val (αcst n) zm w
            (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)| := by
  have hδ0 : (0 : ℝ) ≤ δ.val := δ.pos.le
  have hδ1 : δ.val ≤ 1 := δ.lt_one.le
  have hshift := Workspace.ProofLemmas.Path4SuffixRecurrence.matched_suffix_shift_abs_sum_le
    (n / 4) δ.val hδ0 hδ1 (mlaC n δ m zm) (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
    (mlaMof n) (n / 2 + 1)
  refine hshift.trans ?_
  have hdrop : ∑ w ∈ Finset.range (n / 2 + 3),
        |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
            mlaC n δ m zm r * binPMF (mlaMof n r) (1 - δ.val) w|
      = ∑ w ∈ Finset.range (n / 2 + 1),
          |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
              mlaC n δ m zm r * binPMF (mlaMof n r) (1 - δ.val) w| := by
    have hsub : Finset.range (n / 2 + 1) ⊆ Finset.range (n / 2 + 3) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub]
    intro w _ hw
    rw [Finset.mem_range, not_lt] at hw
    rw [mlaCore_high_w_zero n hmod δ m zm w hw, abs_zero]
  rw [hdrop]
  apply Finset.sum_le_sum
  intro w _
  rw [mlaCore_eq_altRSum n hmod δ m zm w]

private lemma mlaMatched_supp (n : ℕ) (hmod : n % 8 = 1) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (p : ℕ × ℕ)
    (hp : n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2) : matchedInner n δ m p = 0 := by
  unfold matchedInner
  refine Finset.sum_eq_zero (fun r _ => ?_)
  rcases hp with hp | hp
  · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.prefixLengthWeight_eq_zero_of_ge n δ r p.1 hp]
    simp
  · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.suffixLengthWeight_eq_zero_of_ge n hmod δ r p.2 hp]
    simp

private lemma mlaTsum_collapse (n : ℕ) (hmod : n % 8 = 1) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) :
    (∑' p : ℕ × ℕ, |matchedInner n δ m p|)
      = ∑ zm ∈ Finset.range (n / 2 + 1),
          ∑ zp ∈ Finset.range (n / 2 + 2), |matchedInner n δ m (zm, zp)| := by
  classical
  set box : Finset (ℕ × ℕ) := Finset.range (n / 2 + 1) ×ˢ Finset.range (n / 2 + 2) with hbox
  have hmem_box : ∀ p : ℕ × ℕ, p ∉ box → (n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2) := by
    intro p hp
    rw [hbox, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    push_neg at hp
    by_cases h1 : p.1 < n / 2 + 1
    · right; exact hp h1
    · left; omega
  have hsupp : ∀ p : ℕ × ℕ, p ∉ box → |matchedInner n δ m p| = 0 := by
    intro p hp; rw [mlaMatched_supp n hmod δ m p (hmem_box p hp)]; simp
  rw [tsum_eq_sum (s := box) (fun p hp => hsupp p hp)]
  rw [hbox, Finset.sum_product]

private lemma mlaRHS_nonneg (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) :
    0 ≤ (4 : ℝ) *
        (∑ zMinus ∈ Finset.range (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |altRSum n δ.val (αcst n) zMinus zPlus
              (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)|) := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro _ _
  apply Finset.sum_nonneg; intro _ _
  exact abs_nonneg _

theorem matched_le_altRSum_aggregate
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (hδ_lb : (320 : ℝ) / Real.sqrt n ≤ δ.val) (hδ_ub : δ.val ≤ 1 / 2)
    (m : Workspace.Types.BinVec.BinVec (n / 2))
    (hpar : ∀ j₁ j₂ : Fin (n / 2), m.bit j₁ = true → m.bit j₂ = true →
        (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2) :
    ((1 / 2) : ℝ) *
        (∑' p : ℕ × ℕ, |matchedInner n δ m p|)
      ≤ (4 : ℝ) *
          (∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val (αcst n) zMinus zPlus
                (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)|) := by
  classical
  have hn1 : 1 ≤ n := by omega
  by_cases hne : ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).Nonempty
  · -- nonempty case
    set RHSsum : ℝ := ∑ zMinus ∈ Finset.range (n / 2 + 1),
        ∑ zPlus ∈ Finset.range (n / 2 + 1),
          |altRSum n δ.val (αcst n) zMinus zPlus
            (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)| with hRHSsum
    have hRHSsum_nn : 0 ≤ RHSsum := by
      rw [hRHSsum]
      apply Finset.sum_nonneg; intro _ _
      apply Finset.sum_nonneg; intro _ _; exact abs_nonneg _
    rw [mlaTsum_collapse n hmod δ m]
    have hkey : ∑ zm ∈ Finset.range (n / 2 + 1),
          ∑ zp ∈ Finset.range (n / 2 + 2), |matchedInner n δ m (zm, zp)|
        ≤ RHSsum := by
      rw [hRHSsum]
      apply Finset.sum_le_sum
      intro zm _
      have hrw : ∑ zp ∈ Finset.range (n / 2 + 2), |matchedInner n δ m (zm, zp)|
          = fullQ n * ∑ zp ∈ Finset.range (n / 2 + 2),
              |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
                  mlaC n δ m zm r * binPMF ((mlaMof n r) + 1) (1 - δ.val) zp| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro zp _
        exact mlaMatchedInner_abs n hn hmod δ m zm zp hne
      rw [hrw]
      have hfullQ := fullQ_mem n hn1
      have hzm := mlaPerZm_bound n hn hmod δ hδ_ub m zm
      calc fullQ n * ∑ zp ∈ Finset.range (n / 2 + 2),
              |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
                  mlaC n δ m zm r * binPMF ((mlaMof n r) + 1) (1 - δ.val) zp|
          ≤ fullQ n * ∑ w ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val (αcst n) zm w
                (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)| :=
            mul_le_mul_of_nonneg_left hzm hfullQ.1
        _ ≤ 1 * ∑ w ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val (αcst n) zm w
                (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)| := by
            apply mul_le_mul_of_nonneg_right hfullQ.2
            apply Finset.sum_nonneg; intro _ _; exact abs_nonneg _
        _ = ∑ w ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val (αcst n) zm w
                (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)| := by rw [one_mul]
    calc ((1 / 2) : ℝ) * ∑ zm ∈ Finset.range (n / 2 + 1),
            ∑ zp ∈ Finset.range (n / 2 + 2), |matchedInner n δ m (zm, zp)|
        ≤ ((1 / 2) : ℝ) * RHSsum :=
          mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ ≤ (4 : ℝ) * RHSsum := by
          apply mul_le_mul_of_nonneg_right (by norm_num) hRHSsum_nn
  · -- empty case: matchedInner = 0
    have hzero : ∀ p : ℕ × ℕ, matchedInner n δ m p = 0 := by
      intro p
      unfold matchedInner
      refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [dif_neg hne, mul_zero]
    have hz : (∑' p : ℕ × ℕ, |matchedInner n δ m p|) = 0 := by
      simp only [hzero, abs_zero, tsum_zero]
    rw [hz, mul_zero]
    exact mlaRHS_nonneg n δ m

/-- The mask product `∏_{j∈mask} ellFactor n (αcst n) r j` (nonneg, ≤ 1 helper bundle). -/
private noncomputable def maskEll (n : ℕ) (r : ℤ)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) : ℝ :=
  ∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)),
    ellFactor n (αcst n) r (j : ℕ)

private lemma maskEll_nonneg (n : ℕ) (hn1 : 1 ≤ n) (r : ℤ)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) : 0 ≤ maskEll n r m := by
  unfold maskEll
  apply Finset.prod_nonneg
  intro j _
  exact (Workspace.ProofLemmas.Path4Envelope.ellFactor_le_one n hn1 r (j : ℕ)).1

/-- `windowQe`/`windowQo` lie in `[0,1]`. -/
private lemma windowQe_mem (n : ℕ) (hn1 : 1 ≤ n) (r : ℤ) :
    0 ≤ Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r ∧
      Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r ≤ 1 := by
  unfold Workspace.ProofLemmas.Path4WindowQ.windowQe αcst
  exact Workspace.ProofLemmas.QFactorBounds.Q_mem_unitInterval hn1 _ rfl
    (Finset.univ.filter (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0))
    (fun j => ((n / 4 : ℤ) + r + (j : ℕ)).toNat)

private lemma windowQo_mem (n : ℕ) (hn1 : 1 ≤ n) (r : ℤ) :
    0 ≤ Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r ∧
      Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r ≤ 1 := by
  unfold Workspace.ProofLemmas.Path4WindowQ.windowQo αcst
  exact Workspace.ProofLemmas.QFactorBounds.Q_mem_unitInterval hn1 _ rfl
    (Finset.univ.filter (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1))
    (fun j => ((n / 4 : ℤ) + r + (j : ℕ)).toNat)

private lemma windowQsel_mem (n : ℕ) (hn1 : 1 ≤ n) (r : ℤ) (b : ℕ) :
    0 ≤ windowQsel n r b ∧ windowQsel n r b ≤ 1 := by
  unfold windowQsel
  split_ifs
  · exact windowQe_mem n hn1 r
  · exact windowQo_mem n hn1 r

/-- The core gap bound: `|windowQsel n r b - fullQ n| ≤ pertWindowBound n r`. -/
private lemma windowQsel_sub_fullQ_le_bound (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (hmod : n % 8 = 1) (r : ℤ) (hr : -(n / 4 : ℤ) ≤ r) (hr' : r ≤ (n / 4 : ℤ)) (b : ℕ) :
    |windowQsel n r b - fullQ n| ≤ pertWindowBound n r := by
  have hn1 : 1 ≤ n := by omega
  unfold pertWindowBound
  by_cases hw : (-((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8)
  · rw [if_pos hw]
    have hbase := windowQsel_sub_fullQ_le n hn hmod r hw.1 hw.2 b
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hexp_nn : (0 : ℝ) ≤ Real.exp (-(n : ℝ) / 128) := le_of_lt (Real.exp_pos _)
    nlinarith [hbase, hsqrt_nn, hexp_nn]
  · rw [if_neg hw]
    have hQ := windowQsel_mem n hn1 r b
    have hF := fullQ_mem n hn1
    rw [abs_le]
    constructor <;> [skip; skip] <;> nlinarith [hQ.1, hQ.2, hF.1, hF.2]

/-- The empty-mask gap bound: `|windowQe - windowQo| ≤ pertWindowBound n r`. -/
private lemma windowQe_sub_windowQo_le_bound (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (hmod : n % 8 = 1) (r : ℤ) (hr : -(n / 4 : ℤ) ≤ r) (hr' : r ≤ (n / 4 : ℤ)) :
    |Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r -
        Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r|
      ≤ pertWindowBound n r := by
  have hn1 : 1 ≤ n := by omega
  unfold pertWindowBound
  by_cases hw : (-((n : ℤ) / 8) ≤ r ∧ r ≤ (n : ℤ) / 8)
  · rw [if_pos hw]
    exact windowQe_sub_windowQo_le n hn hmod r hw.1 hw.2
  · rw [if_neg hw]
    have hQe := windowQe_mem n hn1 r
    have hQo := windowQo_mem n hn1 r
    rw [abs_le]
    constructor <;> nlinarith [hQe.1, hQe.2, hQo.1, hQo.2]

/-- The weight prefactor `W(r,p) = offset(r)·prefix(r,p.1)·suffix(r,p.2)` (all `.toReal`). -/
private noncomputable def Wpfx (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) (p : ℕ × ℕ) : ℝ :=
  (offsetWeight n r).toReal * (prefixLengthWeight n δ r p.1).toReal *
    (suffixLengthWeight n δ r p.2).toReal

private lemma Wpfx_nonneg (n : ℕ) (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) (p : ℕ × ℕ) :
    0 ≤ Wpfx n δ r p := by
  unfold Wpfx
  apply mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

/-- **Per-`p` triangle bound.**  `|pertInner p| ≤ ∑_r W(r,p)·maskEll·pertWindowBound`. -/
private lemma pertInner_abs_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (p : ℕ × ℕ) :
    |pertInner n δ m p|
      ≤ ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          Wpfx n δ r p * maskEll n r m * pertWindowBound n r := by
  have hn1 : 1 ≤ n := by omega
  -- pertInner = signedInner - matchedInner; combine the two r-sums into one.
  unfold pertInner Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner matchedInner
  rw [← Finset.sum_sub_distrib]
  -- triangle inequality over the finite sum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun r hrmem => ?_)
  have hr_lb : -(n / 4 : ℤ) ≤ r := (Finset.mem_Icc.mp hrmem).1
  have hr_ub : r ≤ (n / 4 : ℤ) := (Finset.mem_Icc.mp hrmem).2
  -- abbreviations for the shared prefactor W and the mask product P
  set W : ℝ := (offsetWeight n r).toReal * (prefixLengthWeight n δ r p.1).toReal *
    (suffixLengthWeight n δ r p.2).toReal with hW
  have hW_eq : W = Wpfx n δ r p := by rw [hW, Wpfx]
  have hWnn : 0 ≤ W := by
    rw [hW]; apply mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  -- target RHS
  have hPnn : 0 ≤ maskEll n r m := maskEll_nonneg n hn1 r m
  by_cases hne : ((Finset.univ : Finset (Fin (n / 2))).filter
      (fun j => m.bit j = true)).Nonempty
  · -- nonempty branch
    rw [dif_pos hne, dif_pos hne]
    set x : ℤ := ((n / 4 : ℤ) + r +
      ((((Finset.univ : Finset (Fin (n / 2))).filter
          (fun j => m.bit j = true)).min' hne : Fin (n / 2)) : ℕ)) with hx
    set s : ℝ := (-1 : ℝ) ^ (x % 2).toNat with hs
    -- the literal window products in signedInner are `windowQe`/`windowQo` defeq;
    -- the literal mask product is `maskEll`.
    show |W * (s * (if x % 2 = 0
        then Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r
        else Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r) * maskEll n r m)
        - W * (s * fullQ n * maskEll n r m)|
      ≤ W * maskEll n r m * pertWindowBound n r
    set Qsel : ℝ := (if x % 2 = 0
        then Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r
        else Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r) with hQsel
    have heq : W * (s * Qsel * maskEll n r m) - W * (s * fullQ n * maskEll n r m)
        = (s * W * maskEll n r m) * (Qsel - fullQ n) := by ring
    rw [heq, abs_mul]
    have hsabs : |s * W * maskEll n r m| = W * maskEll n r m := by
      rw [abs_mul, abs_mul]
      have hsabs1 : |s| = 1 := by rw [hs, abs_pow]; simp [abs_neg, abs_one]
      rw [hsabs1, one_mul, abs_of_nonneg hWnn, abs_of_nonneg hPnn]
    rw [hsabs]
    have hgap : |Qsel - fullQ n| ≤ pertWindowBound n r := by
      rw [hQsel]
      by_cases hpar0 : x % 2 = 0
      · rw [if_pos hpar0]
        have := windowQsel_sub_fullQ_le_bound n hn hmod r hr_lb hr_ub 0
        simpa [windowQsel, αcst] using this
      · rw [if_neg hpar0]
        have := windowQsel_sub_fullQ_le_bound n hn hmod r hr_lb hr_ub 1
        simpa [windowQsel, αcst] using this
    nlinarith [hgap, hWnn, hPnn, mul_nonneg hWnn hPnn, abs_nonneg (Qsel - fullQ n)]
  · -- empty branch
    rw [dif_neg hne, dif_neg hne]
    show |W * (Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r -
          Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r) - W * 0|
      ≤ W * maskEll n r m * pertWindowBound n r
    have hmaskEll1 : maskEll n r m = 1 := by
      unfold maskEll
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.prod_empty]
    rw [hmaskEll1, mul_one, mul_zero, sub_zero, abs_mul, abs_of_nonneg hWnn]
    have hgap := windowQe_sub_windowQo_le_bound n hn hmod r hr_lb hr_ub
    nlinarith [hgap, hWnn,
      abs_nonneg (Workspace.ProofLemmas.Path4WindowQ.windowQe n (αcst n) r -
        Workspace.ProofLemmas.Path4WindowQ.windowQo n (αcst n) r)]

/-- `binomialPMF` is never `⊤`. -/
private lemma binomialPMF_ne_top (len : ℕ) (δ : Workspace.Types.DelProb.DelProb) (z : ℕ) :
    Workspace.Types.LengthsOnlyProcess.binomialPMF len δ z ≠ ⊤ := by
  unfold Workspace.Types.LengthsOnlyProcess.binomialPMF
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

private lemma prefixLengthWeight_ne_top (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) (z : ℕ) : prefixLengthWeight n δ r z ≠ ⊤ := by
  unfold prefixLengthWeight
  simp only
  split_ifs
  · exact binomialPMF_ne_top _ δ _
  · exact ENNReal.zero_ne_top

private lemma suffixLengthWeight_ne_top (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) (z : ℕ) : suffixLengthWeight n δ r z ≠ ⊤ := by
  unfold suffixLengthWeight
  simp only
  split_ifs
  · exact binomialPMF_ne_top _ δ _
  · exact ENNReal.zero_ne_top

/-- `∑'_a (prefixLengthWeight n δ r a).toReal ≤ 1`. -/
private lemma prefix_toReal_tsum_le_one (n : ℕ) (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) :
    ∑' a : ℕ, (prefixLengthWeight n δ r a).toReal ≤ 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => prefixLengthWeight_ne_top n δ r a)]
  have hle : (∑' a : ℕ, prefixLengthWeight n δ r a) ≤ 1 := by
    by_cases hrange : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)
    · rw [LengthsOnlyExistsScratch.prefixLengthWeight_tsum n δ r hrange]
    · have hz : ∀ a : ℕ, prefixLengthWeight n δ r a = 0 := by
        intro a; unfold prefixLengthWeight; simp only; rw [dif_neg hrange]
      simp only [hz, tsum_zero]; exact zero_le_one
  calc (∑' a : ℕ, prefixLengthWeight n δ r a).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
    _ = 1 := by simp

/-- `∑'_a (suffixLengthWeight n δ r a).toReal ≤ 1` (needs `n % 8 = 1` only via the
in-range tsum lemma's hypotheses, but the bound holds unconditionally). -/
private lemma suffix_toReal_tsum_le_one (n : ℕ) (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) :
    ∑' a : ℕ, (suffixLengthWeight n δ r a).toReal ≤ 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => suffixLengthWeight_ne_top n δ r a)]
  have hle : (∑' a : ℕ, suffixLengthWeight n δ r a) ≤ 1 := by
    by_cases hrange : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)
    · rw [LengthsOnlyExistsScratch.suffixLengthWeight_tsum n δ r hrange]
    · have hz : ∀ a : ℕ, suffixLengthWeight n δ r a = 0 := by
        intro a; unfold suffixLengthWeight; simp only; rw [dif_neg hrange]
      simp only [hz, tsum_zero]; exact zero_le_one
  calc (∑' a : ℕ, suffixLengthWeight n δ r a).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
    _ = 1 := by simp

private lemma prefix_toReal_summable (n : ℕ) (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) :
    Summable (fun a : ℕ => (prefixLengthWeight n δ r a).toReal) := by
  apply summable_of_ne_finset_zero (s := Finset.range (n / 2 + 1))
  intro a ha
  rw [Finset.mem_range, not_lt] at ha
  rw [Workspace.ProofLemmas.PrefixSuffixZSupport.prefixLengthWeight_eq_zero_of_ge n δ r a ha]
  simp

private lemma suffix_toReal_summable (n : ℕ) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) :
    Summable (fun a : ℕ => (suffixLengthWeight n δ r a).toReal) := by
  apply summable_of_ne_finset_zero (s := Finset.range (n / 2 + 2))
  intro a ha
  rw [Finset.mem_range, not_lt] at ha
  rw [Workspace.ProofLemmas.PrefixSuffixZSupport.suffixLengthWeight_eq_zero_of_ge n hmod δ r a ha]
  simp

/-- `∑'_p (prefix(p.1)·suffix(p.2)).toReal ≤ 1` over `p : ℕ × ℕ`. -/
private lemma prefix_suffix_tsum_le_one (n : ℕ) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) :
    ∑' p : ℕ × ℕ, (prefixLengthWeight n δ r p.1).toReal *
        (suffixLengthWeight n δ r p.2).toReal ≤ 1 := by
  have hpre := prefix_toReal_summable n δ r
  have hsuf := suffix_toReal_summable n hmod δ r
  have hsummable_prod : Summable (fun x : ℕ × ℕ =>
      (prefixLengthWeight n δ r x.1).toReal * (suffixLengthWeight n δ r x.2).toReal) :=
    hpre.mul_of_nonneg hsuf (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
  rw [← Summable.tsum_mul_tsum hpre hsuf hsummable_prod]
  have h1 := prefix_toReal_tsum_le_one n δ r
  have h2 := suffix_toReal_tsum_le_one n δ r
  have hp_nn : 0 ≤ ∑' a : ℕ, (prefixLengthWeight n δ r a).toReal :=
    tsum_nonneg (fun _ => ENNReal.toReal_nonneg)
  have hs_nn : 0 ≤ ∑' a : ℕ, (suffixLengthWeight n δ r a).toReal :=
    tsum_nonneg (fun _ => ENNReal.toReal_nonneg)
  nlinarith [h1, h2, hp_nn, hs_nn]

/-- **The PERT bound.**  `(1/2)·∑'_p |pertInner p| ≤ perMaskPert n m`. -/
theorem pert_le_perMaskPert
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (hδ_lb : (320 : ℝ) / Real.sqrt n ≤ δ.val) (hδ_ub : δ.val ≤ 1 / 2)
    (m : Workspace.Types.BinVec.BinVec (n / 2))
    (hpar : ∀ j₁ j₂ : Fin (n / 2), m.bit j₁ = true → m.bit j₂ = true →
        (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2) :
    ((1 / 2) : ℝ) * (∑' p : ℕ × ℕ, |pertInner n δ m p|)
      ≤ perMaskPert n m := by
  classical
  have hn1 : 1 ≤ n := by omega
  set Icc : Finset ℤ := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) with hIcc
  -- per-r summand function
  set g : ℤ → ℕ × ℕ → ℝ := fun r p => Wpfx n δ r p * maskEll n r m * pertWindowBound n r with hg
  -- support box for |pertInner| and the RHS bound
  set box : Finset (ℕ × ℕ) := Finset.range (n / 2 + 1) ×ˢ Finset.range (n / 2 + 2) with hbox
  have hmem_box : ∀ p : ℕ × ℕ, p ∉ box → (n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2) := by
    intro p hp
    rw [hbox, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    push_neg at hp
    by_cases h1 : p.1 < n / 2 + 1
    · right; exact hp h1
    · left; omega
  -- pertInner vanishes off box
  have hsupp_pert : ∀ p : ℕ × ℕ, n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2 →
      pertInner n δ m p = 0 := by
    intro p hp
    unfold pertInner Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner matchedInner
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rcases hp with hp | hp
    · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.prefixLengthWeight_eq_zero_of_ge n δ r p.1 hp]
      simp
    · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.suffixLengthWeight_eq_zero_of_ge n hmod δ r p.2 hp]
      simp
  have hsummable_pert : Summable (fun p : ℕ × ℕ => |pertInner n δ m p|) := by
    apply summable_of_ne_finset_zero (s := box)
    intro p hp; rw [hsupp_pert p (hmem_box p hp)]; simp
  -- summability of the per-r summand (for fixed r): finitely supported on box
  have hsupp_g : ∀ (r : ℤ) (p : ℕ × ℕ), n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2 → g r p = 0 := by
    intro r p hp
    rw [hg]; simp only
    have hWzero : Wpfx n δ r p = 0 := by
      unfold Wpfx
      rcases hp with hp | hp
      · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.prefixLengthWeight_eq_zero_of_ge n δ r p.1 hp]
        simp
      · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.suffixLengthWeight_eq_zero_of_ge n hmod δ r p.2 hp]
        simp
    rw [hWzero]; ring
  have hsummable_g : ∀ r ∈ Icc, Summable (fun p : ℕ × ℕ => g r p) := by
    intro r _
    apply summable_of_ne_finset_zero (s := box)
    intro p hp; exact hsupp_g r p (hmem_box p hp)
  -- summability of the finite sum ∑_r g r p
  have hsummable_sum : Summable (fun p : ℕ × ℕ => ∑ r ∈ Icc, g r p) :=
    summable_sum hsummable_g
  -- Step A: ∑'_p |pertInner| ≤ ∑'_p (∑_r g r p)
  have hstepA : (∑' p : ℕ × ℕ, |pertInner n δ m p|)
      ≤ ∑' p : ℕ × ℕ, ∑ r ∈ Icc, g r p := by
    refine Summable.tsum_le_tsum (fun p => ?_) hsummable_pert hsummable_sum
    have := pertInner_abs_le n hn hmod δ m p
    rw [hg, hIcc]; exact this
  -- Step B: swap tsum and the finite r-sum
  have hstepB : (∑' p : ℕ × ℕ, ∑ r ∈ Icc, g r p)
      = ∑ r ∈ Icc, ∑' p : ℕ × ℕ, g r p :=
    Summable.tsum_finsetSum hsummable_g
  -- Step C: for each r, ∑'_p g r p ≤ offset.toReal * maskEll * pertWindowBound
  have hstepC : ∀ r ∈ Icc, (∑' p : ℕ × ℕ, g r p)
      ≤ (offsetWeight n r).toReal * maskEll n r m * pertWindowBound n r := by
    intro r _
    -- g r p = (maskEll * pertWindowBound * offset) * (prefix(p.1)*suffix(p.2))
    have hfac : ∀ p : ℕ × ℕ, g r p
        = (maskEll n r m * pertWindowBound n r * (offsetWeight n r).toReal) *
          ((prefixLengthWeight n δ r p.1).toReal * (suffixLengthWeight n δ r p.2).toReal) := by
      intro p; rw [hg]; simp only [Wpfx]; ring
    simp only [hfac]
    rw [tsum_mul_left]
    have hcnn : 0 ≤ maskEll n r m * pertWindowBound n r * (offsetWeight n r).toReal :=
      mul_nonneg (mul_nonneg (maskEll_nonneg n hn1 r m) (pertWindowBound_nonneg n r))
        ENNReal.toReal_nonneg
    have hps := prefix_suffix_tsum_le_one n hmod δ r
    calc (maskEll n r m * pertWindowBound n r * (offsetWeight n r).toReal) *
            (∑' p : ℕ × ℕ, (prefixLengthWeight n δ r p.1).toReal *
              (suffixLengthWeight n δ r p.2).toReal)
        ≤ (maskEll n r m * pertWindowBound n r * (offsetWeight n r).toReal) * 1 :=
          mul_le_mul_of_nonneg_left hps hcnn
      _ = (offsetWeight n r).toReal * maskEll n r m * pertWindowBound n r := by ring
  -- assemble: ∑'_p |pertInner| ≤ ∑_r offset*maskEll*pertWindowBound = 2*perMaskPert
  have hRHS_eq : ∑ r ∈ Icc, (offsetWeight n r).toReal * maskEll n r m * pertWindowBound n r
      = 2 * perMaskPert n m := by
    unfold perMaskPert maskEll
    rw [hIcc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  have hfinal : (∑' p : ℕ × ℕ, |pertInner n δ m p|) ≤ 2 * perMaskPert n m := by
    refine hstepA.trans ?_
    rw [hstepB, ← hRHS_eq]
    exact Finset.sum_le_sum hstepC
  linarith [hfinal]

/-! ## The (I) split + PERT collapse, then assembly into `signed_inner_bridge`. -/

/-- **The per-mask signed-inner bridge.** -/
theorem signed_inner_bridge (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (hδ_lb : (320 : ℝ) / Real.sqrt n ≤ δ.val) (hδ_ub : δ.val ≤ 1 / 2)
    (m : Workspace.Types.BinVec.BinVec (n / 2))
    (hpar : ∀ j₁ j₂ : Fin (n / 2), m.bit j₁ = true → m.bit j₂ = true →
        (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2) :
    ((1 / 2) : ℝ) *
        (∑' p : ℕ × ℕ,
          |Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p|)
      ≤ (4 : ℝ) *
          (∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val (αcst n) zMinus zPlus
                (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)|)
        + perMaskPert n m := by
  classical
  -- (1) The `signedInner` tsum collapses to a FINITE double sum (prefix/suffix
  -- weights vanish off `range(n/2+1) × range(n/2+2)`), hence everything is summable.
  -- We bound via the triangle split `signedInner = matchedInner + pertInner`.
  -- Summability of |matchedInner|, |pertInner|: both have the same finite support.
  have hsplit : ∀ p : ℕ × ℕ,
      |Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p|
        ≤ |matchedInner n δ m p| + |pertInner n δ m p| := by
    intro p
    rw [signedInner_split n δ m p]
    exact abs_add_le _ _
  -- support facts: signedInner, matchedInner, pertInner all vanish off the finite box
  have hsupp_match : ∀ p : ℕ × ℕ, n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2 →
      matchedInner n δ m p = 0 := by
    intro p hp
    unfold matchedInner
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rcases hp with hp | hp
    · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.prefixLengthWeight_eq_zero_of_ge n δ r p.1 hp]
      simp
    · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.suffixLengthWeight_eq_zero_of_ge n hmod δ r p.2 hp]
      simp
  have hsupp_signed : ∀ p : ℕ × ℕ, n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2 →
      Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p = 0 := by
    intro p hp
    unfold Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rcases hp with hp | hp
    · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.prefixLengthWeight_eq_zero_of_ge n δ r p.1 hp]
      simp
    · rw [Workspace.ProofLemmas.PrefixSuffixZSupport.suffixLengthWeight_eq_zero_of_ge n hmod δ r p.2 hp]
      simp
  have hsupp_pert : ∀ p : ℕ × ℕ, n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2 →
      pertInner n δ m p = 0 := by
    intro p hp
    unfold pertInner
    rw [hsupp_signed p hp, hsupp_match p hp]; ring
  -- finite support set
  set box : Finset (ℕ × ℕ) := Finset.range (n / 2 + 1) ×ˢ Finset.range (n / 2 + 2) with hbox
  have hmem_box : ∀ p : ℕ × ℕ, p ∉ box → (n / 2 + 1 ≤ p.1 ∨ n / 2 + 2 ≤ p.2) := by
    intro p hp
    rw [hbox, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    push_neg at hp
    by_cases h1 : p.1 < n / 2 + 1
    · right; exact hp h1
    · left; omega
  -- tsum |signedInner| = finite sum over box
  have hsummable_signed : Summable (fun p : ℕ × ℕ =>
      |Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p|) := by
    apply summable_of_ne_finset_zero (s := box)
    intro p hp; rw [hsupp_signed p (hmem_box p hp)]; simp
  have hsummable_match : Summable (fun p : ℕ × ℕ => |matchedInner n δ m p|) := by
    apply summable_of_ne_finset_zero (s := box)
    intro p hp; rw [hsupp_match p (hmem_box p hp)]; simp
  have hsummable_pert : Summable (fun p : ℕ × ℕ => |pertInner n δ m p|) := by
    apply summable_of_ne_finset_zero (s := box)
    intro p hp; rw [hsupp_pert p (hmem_box p hp)]; simp
  -- ∑'|signedInner| ≤ ∑'|matchedInner| + ∑'|pertInner|
  have htsum_le : (∑' p : ℕ × ℕ,
        |Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p|)
      ≤ (∑' p : ℕ × ℕ, |matchedInner n δ m p|)
        + (∑' p : ℕ × ℕ, |pertInner n δ m p|) := by
    rw [← Summable.tsum_add hsummable_match hsummable_pert]
    exact Summable.tsum_le_tsum hsplit hsummable_signed (hsummable_match.add hsummable_pert)
  -- assemble: (1/2)∑'|signed| ≤ (1/2)∑'|matched| + (1/2)∑'|pert| ≤ 4∑|altRSum| + perMaskPert
  have hmatch := matched_le_altRSum_aggregate n hn hmod δ hδ_lb hδ_ub m hpar
  have hpert := pert_le_perMaskPert n hn hmod δ hδ_lb hδ_ub m hpar
  have hhalf_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc ((1 / 2) : ℝ) *
          (∑' p : ℕ × ℕ,
            |Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.signedInner n δ m p|)
      ≤ ((1 / 2) : ℝ) *
          ((∑' p : ℕ × ℕ, |matchedInner n δ m p|)
            + (∑' p : ℕ × ℕ, |pertInner n δ m p|)) :=
        mul_le_mul_of_nonneg_left htsum_le hhalf_nn
    _ = ((1 / 2) : ℝ) * (∑' p : ℕ × ℕ, |matchedInner n δ m p|)
          + ((1 / 2) : ℝ) * (∑' p : ℕ × ℕ, |pertInner n δ m p|) := by ring
    _ ≤ (4 : ℝ) *
          (∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val (αcst n) zMinus zPlus
                (Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.sigmaSet n m)|)
          + perMaskPert n m := add_le_add hmatch hpert

end Workspace.ProofLemmas.Path4Assembly
