import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CoinFlipBitMarginal
import Workspace.ProofLemmas.WitnessBitMass
import Workspace.ProofLemmas.WitnessSuffixMass
import Workspace.ProofLemmas.WitnessPrefixSuffixTailTonelli

/-!
# WitnessBitProb — bounding the prefix/suffix-bit probability for `|r| ≤ n/8`

For a fixed offset `r` with `|r| ≤ n/8`, the prefix/suffix-bit event
`bitPred b r` is the union, over a concrete finite set `T_r ⊆ Fin n` of
coordinates lying in the prefix `< 3n/8` or suffix `≥ 5n/8`, of `b.bit i = true`.
By `CoinFlipBitMarginal.bit_union_bound` the witness probability of this event is
`≤ ∑_{i ∈ T_r} S.p i ≤ 2·√n·exp(-n/256)`.

All lemmas sorry-free.
-/

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist
open Workspace.Types.AlternatingSumExpression
open scoped Classical

namespace WitnessBitProb

variable {n : ℕ}

/-- Mass of any coordinate set living inside the prefix `< 3n/8` / suffix `≥ 5n/8`
is `≤ 2·√n·exp(-n/256)`, given the per-coordinate witness bound
`S.p i ≤ √n · binPMF n (1/2) i`. -/
theorem witness_set_mass_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (S : ProbVec n)
    (hSval : ∀ i : Fin n, S.p i ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val)
    (T : Finset (Fin n))
    (hT : ∀ i ∈ T, (i.val < 3 * n / 8) ∨ (5 * n / 8 ≤ i.val)) :
    (∑ i ∈ T, S.p i) ≤ 2 * (Real.sqrt n * Real.exp (-((n : ℝ) / 256))) := by
  -- Split T into prefix and suffix parts.
  classical
  set Tp : Finset (Fin n) := T.filter (fun i => i.val < 3 * n / 8) with hTp
  set Ts : Finset (Fin n) := T.filter (fun i => ¬ (i.val < 3 * n / 8)) with hTs
  have hsplit : (∑ i ∈ T, S.p i) = (∑ i ∈ Tp, S.p i) + (∑ i ∈ Ts, S.p i) := by
    rw [hTp, hTs]
    exact (Finset.sum_filter_add_sum_filter_not T (fun i => i.val < 3 * n / 8) S.p).symm
  rw [hsplit]
  have hSnn : ∀ i : Fin n, 0 ≤ S.p i := S.nonneg
  -- Membership facts.
  have hTp_mem : ∀ i ∈ Tp, i.val < 3 * n / 8 := by
    intro i hi; rw [hTp, Finset.mem_filter] at hi; exact hi.2
  have hTs_mem : ∀ i ∈ Ts, 5 * n / 8 ≤ i.val := by
    intro i hi
    rw [hTs, Finset.mem_filter] at hi
    rcases hT i hi.1 with h | h
    · exact absurd h hi.2
    · exact h
  have hbinnn : ∀ k : ℕ, (0 : ℝ) ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) k := by
    intro k
    have : (0 : ℝ) ≤ binPMF n (1 / 2 : ℝ) k := by
      unfold binPMF; by_cases h : k ≤ n
      · rw [if_pos h]; positivity
      · rw [if_neg h]
    positivity
  -- PREFIX part.
  have hpre : (∑ i ∈ Tp, S.p i)
      ≤ Real.sqrt n * Real.exp (-((n : ℝ) / 256)) := by
    have h1 : (∑ i ∈ Tp, S.p i)
        ≤ ∑ i ∈ Tp, Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val :=
      Finset.sum_le_sum (fun i _ => hSval i)
    refine le_trans h1 ?_
    -- reindex Tp by i ↦ i.val (injective) into its image, then ⊆ range (3n/8)
    have himg : (∑ i ∈ Tp, Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val)
        = ∑ k ∈ Finset.image Fin.val Tp, Real.sqrt n * binPMF n (1 / 2 : ℝ) k :=
      (Finset.sum_image (g := Fin.val) (s := Tp)
        (f := fun k => Real.sqrt n * binPMF n (1 / 2 : ℝ) k)
        (fun a _ b _ h => Fin.ext h)).symm
    rw [himg]
    have hsub : Finset.image Fin.val Tp ⊆ Finset.range (3 * n / 8) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨i, hiTp, rfl⟩ := hk
      rw [Finset.mem_range]; exact hTp_mem i hiTp
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => hbinnn k)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (WitnessBitTail.binPMF_prefix_tail n hn)
      (Real.sqrt_nonneg _)
  -- SUFFIX part.
  have hsuf : (∑ i ∈ Ts, S.p i)
      ≤ Real.sqrt n * Real.exp (-((n : ℝ) / 256)) := by
    have h1 : (∑ i ∈ Ts, S.p i)
        ≤ ∑ i ∈ Ts, Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val :=
      Finset.sum_le_sum (fun i _ => hSval i)
    refine le_trans h1 ?_
    have himg : (∑ i ∈ Ts, Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val)
        = ∑ k ∈ Finset.image Fin.val Ts, Real.sqrt n * binPMF n (1 / 2 : ℝ) k :=
      (Finset.sum_image (g := Fin.val) (s := Ts)
        (f := fun k => Real.sqrt n * binPMF n (1 / 2 : ℝ) k)
        (fun a _ b _ h => Fin.ext h)).symm
    rw [himg]
    have hsub : Finset.image Fin.val Ts ⊆ Finset.Ico (5 * n / 8) n := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨i, hiTs, rfl⟩ := hk
      rw [Finset.mem_Ico]
      exact ⟨hTs_mem i hiTs, i.isLt⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => hbinnn k)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (WitnessSuffixMass.binPMF_suffix_tail n hn)
      (Real.sqrt_nonneg _)
  linarith

/-- **Real-valued union bound.**  The real-valued mass of the event "some
coordinate in `T` is `true`" is `≤ ∑_{i ∈ T} S.p i`. -/
theorem bit_union_bound_real (S : ProbVec n) (cfd : CoinFlipDist n S)
    (T : Finset (Fin n)) :
    (∑ b : BinVec n,
        (if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b).toReal else 0))
      ≤ ∑ i ∈ T, S.p i := by
  classical
  -- ENNReal union bound from CoinFlipBitMarginal
  have hen := CoinFlipBitMarginal.bit_union_bound S cfd S.nonneg S.le_one T
  -- each LHS summand is finite
  have hfin : ∀ b : BinVec n, b ∈ (Finset.univ : Finset (BinVec n)) →
      (if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b) else 0) ≠ ⊤ := by
    intro b _
    by_cases h : ∃ i ∈ T, b.bit i = true
    · rw [if_pos h]; exact PMF.apply_ne_top _ _
    · rw [if_neg h]; exact ENNReal.zero_ne_top
  have hfinR : ∀ i ∈ T, ENNReal.ofReal (S.p i) ≠ ⊤ := fun i _ => ENNReal.ofReal_ne_top
  -- toReal the RHS: ∑ ofReal(S.p i) → ∑ S.p i
  have hRHS : (∑ i ∈ T, ENNReal.ofReal (S.p i)).toReal = ∑ i ∈ T, S.p i := by
    rw [ENNReal.toReal_sum hfinR]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_ofReal (S.nonneg i)]
  -- toReal the LHS summand-wise
  have hLHS : (∑ b : BinVec n,
        (if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b) else 0)).toReal
      = ∑ b : BinVec n,
          (if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b).toReal else 0) := by
    rw [ENNReal.toReal_sum hfin]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : ∃ i ∈ T, b.bit i = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, ENNReal.toReal_zero]
  -- now transfer the ENNReal inequality to reals
  have hRHS_fin : (∑ i ∈ T, ENNReal.ofReal (S.p i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hfinR
  have hmono := ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top hRHS_fin hen) hRHS_fin
  rw [hLHS, hRHS] at hmono
  exact hmono.mpr hen

open WitnessPrefixSuffixTailTonelli in
/-- **Per-offset bit-probability bound** (for `|r| ≤ n/8`).  For the witness `S`
satisfying `S.p i ≤ √n·binPMF n (1/2) i`, the witness probability of the
prefix/suffix-bit event `bitPred b r` is `≤ 2·√n·exp(-n/256)`. -/
theorem bitPred_prob_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (S : ProbVec n) (cfd : CoinFlipDist n S)
    (hSval : ∀ i : Fin n, S.p i ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val)
    (r : ℤ) (hr : -((n / 8 : ℕ) : ℤ) ≤ r ∧ r ≤ ((n / 8 : ℕ) : ℤ)) :
    (∑ b : BinVec n,
        (if bitPred b r then (cfd.toPMF b).toReal else 0))
      ≤ 2 * (Real.sqrt n * Real.exp (-((n : ℝ) / 256))) := by
  classical
  -- the concrete coordinate set realising the predicate
  set T : Finset (Fin n) := Finset.univ.filter
    (fun i : Fin n => (i.val : ℤ) < (n / 4 : ℕ) + r ∨
        (3 * (n / 4 : ℕ) : ℤ) + r ≤ i.val) with hTdef
  -- bitPred b r ↔ ∃ i ∈ T, b.bit i = true
  have hiff : ∀ b : BinVec n,
      bitPred b r ↔ (∃ i ∈ T, b.bit i = true) := by
    intro b
    constructor
    · rintro ⟨i, hcond, hbit⟩
      exact ⟨i, by rw [hTdef, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hcond⟩, hbit⟩
    · rintro ⟨i, hiT, hbit⟩
      rw [hTdef, Finset.mem_filter] at hiT
      exact ⟨i, hiT.2, hbit⟩
  -- rewrite the LHS via the iff
  have hrw : (∑ b : BinVec n, (if bitPred b r then (cfd.toPMF b).toReal else 0))
      = ∑ b : BinVec n, (if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b).toReal else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : bitPred b r
    · rw [if_pos h, if_pos ((hiff b).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hiff b).mpr hh))]
  rw [hrw]
  refine le_trans (bit_union_bound_real S cfd T) ?_
  -- T positions sit in prefix/suffix; apply witness_set_mass_le
  apply witness_set_mass_le n hn S hSval T
  intro i hiT
  rw [hTdef, Finset.mem_filter] at hiT
  -- from |r| ≤ n/8 and n % 8 = 1, derive i.val < 3n/8 ∨ 5n/8 ≤ i.val
  have hquarter : (n / 4 : ℕ) + (n / 8 : ℕ) = 3 * n / 8 := by omega
  have h34 : 3 * (n / 4 : ℕ) - (n / 8 : ℕ) = 5 * n / 8 := by omega
  rcases hiT.2 with hlo | hhi
  · -- i.val < n/4 + r ≤ n/4 + n/8 = 3n/8
    left
    have : (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + ((n / 8 : ℕ) : ℤ) := by
      calc (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r := hlo
        _ ≤ ((n / 4 : ℕ) : ℤ) + ((n / 8 : ℕ) : ℤ) := by linarith [hr.2]
    have hcast : ((n / 4 : ℕ) : ℤ) + ((n / 8 : ℕ) : ℤ) = ((3 * n / 8 : ℕ) : ℤ) := by
      rw [← hquarter]; push_cast; ring
    rw [hcast] at this
    exact_mod_cast this
  · -- 3·(n/4) + r ≤ i.val ; r ≥ -n/8 ⇒ 5n/8 ≤ i.val
    right
    have : ((3 * (n / 4 : ℕ) : ℤ)) - ((n / 8 : ℕ) : ℤ) ≤ (i.val : ℤ) := by
      have h1 : ((3 * (n / 4 : ℕ) : ℤ)) + r ≤ (i.val : ℤ) := hhi
      linarith [hr.1]
    have hcast : ((3 * (n / 4 : ℕ) : ℤ)) - ((n / 8 : ℕ) : ℤ) = ((5 * n / 8 : ℕ) : ℤ) := by
      have : (3 * (n / 4 : ℕ) : ℕ) - (n / 8 : ℕ) = 5 * n / 8 := h34
      omega
    rw [hcast] at this
    exact_mod_cast this

end WitnessBitProb
