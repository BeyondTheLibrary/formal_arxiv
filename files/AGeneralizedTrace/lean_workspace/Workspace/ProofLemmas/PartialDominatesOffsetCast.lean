import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.PartialDeletionProcess
import Workspace.ProofLemmas.RestrictSegmentFactorization
import Workspace.ProofLemmas.PartialDominatesAssembly
import Workspace.ProofLemmas.PartialDominatesSegmentAlign
import Workspace.ProofLemmas.PartialDominatesSegmentCast

/-!
# ℤ → ℕ offset window casts for the `hcore` step

This file bridges the integer-gated `prefixWeight` / `suffixWeight`
(`PartialDeletionProcess`, sums over `Fin n → Bool` with `ℤ`-comparisons) to the
cast-free fixed-width segment sums `PartialDominatesSegmentAlign.{prefixWindow_eq_segSum,
suffixWindow_eq_segSum}` (sums over `Fin (k+m) → Bool` with `ℕ`-comparisons), for
offsets `r` in the `offsetWeight`-support range.
-/

namespace PartialDominatesOffsetCast

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.DeletionChannel
open RestrictSegmentFactorization
open PartialDominatesAssembly
open PartialDominatesSegmentAlign

open scoped Classical

/-- `restrict` is invariant under a length-`cast` reindex of both the vector and
the mask: for `h : k = n`, restricting `b : BinVec n` by `μ` equals restricting
the `cast`-pulled-back `BinVec k` by the `cast`-pulled-back mask. -/
lemma restrict_cast {k n : ℕ} (h : k = n) (b : BinVec n) (μ : Fin n → Bool) :
    restrict (⟨fun j => b.bit (Fin.cast h j)⟩ : BinVec k) (fun j => μ (Fin.cast h j))
      = restrict b μ := by
  rw [restrict_eq_keepWith, restrict_eq_keepWith]
  rw [List.ofFn_congr h.symm b.bit, List.ofFn_congr h.symm μ]

/-! ### Prefix offset cast (piece 1a)

`prefixWeight n b δ r t₁` sums over `μ : Fin n → Bool` gated by `isPrefixMask`
(false for `(i:ℤ) ≥ n/4+r`) with the per-index weight product gated
`if (i:ℤ) < n/4+r`.  We reindex the mask domain `Fin n ≃ Fin (k+m)` with
`k = (n/4+r).toNat`, `m = n-k`, turning the `ℤ`-gate into the `ℕ`-gate of
`prefixWindow_eq_segSum`. -/

/-- The integer gate `(i:ℤ) < n/4 + r` matches the natural gate `(j:ℕ) < k`
under the cast `i = Fin.cast h.symm j`, where `k = (n/4+r).toNat` and
`(k:ℤ) = n/4 + r` (valid since `0 ≤ n/4 + r`). -/
lemma prefixWeight_eq_segSum {n : ℕ} (b : BinVec n) (δ : DelProb) (r : ℤ)
    (t₁ : Trace n)
    (hk0 : 0 ≤ ((n / 4 : ℕ) : ℤ) + r)
    (hkn : ((n / 4 : ℕ) : ℤ) + r ≤ (n : ℤ)) :
    prefixWeight n b δ r t₁
      = segSum δ.val
          (⟨fun i => b.bit (Fin.cast (by
              have hkn' : (((n / 4 : ℕ) : ℤ) + r).toNat ≤ n := by
                have h := Int.toNat_le.mpr hkn; simpa using h
              omega)
            (Fin.castAdd (n - (((n / 4 : ℕ) : ℤ) + r).toNat) i))⟩ : BinVec (((n / 4 : ℕ) : ℤ) + r).toNat)
          (fun s => if s = t₁.bits then 1 else 0) := by
  -- Notation.
  set K : ℕ := (((n / 4 : ℕ) : ℤ) + r).toNat with hK
  have hKZ : (K : ℤ) = ((n / 4 : ℕ) : ℤ) + r := Int.toNat_of_nonneg hk0
  have hKn : K ≤ n := by
    have := Int.toNat_le.mpr hkn; simpa [hK] using this
  set m : ℕ := n - K with hm
  have hsum : K + m = n := by omega
  -- The cast of `b` into `BinVec (K + m)`.
  set b' : BinVec (K + m) := ⟨fun i => b.bit (Fin.cast hsum i)⟩ with hb'
  -- Forward direction of prefixWindow_eq_segSum.
  have hwin := PartialDominatesSegmentAlign.prefixWindow_eq_segSum (k := K) (m := m) δ.val b'
        (fun s => if s = t₁.bits then 1 else 0)
  -- The segment of `b'` matches the goal's segment (defeq up to the cast arg).
  rw [show (segSum δ.val
          (⟨fun i => b.bit (Fin.cast hsum (Fin.castAdd (n - K) i))⟩ : BinVec K)
          (fun s => if s = t₁.bits then 1 else 0))
        = segSum δ.val (⟨fun i => b'.bit (Fin.castAdd m i)⟩ : BinVec K)
            (fun s => if s = t₁.bits then 1 else 0) from by
      congr 1]
  rw [← hwin]
  -- Now match the integer-gated `prefixWeight` to the `Fin (K+m)` masked sum.
  unfold prefixWeight
  -- Reindex the RHS `Fin (K+m) → Bool` sum to a `Fin n → Bool` sum.
  set E : (Fin (K + m) → Bool) ≃ (Fin n → Bool) :=
    (finCongr hsum).arrowCongr (Equiv.refl Bool) with hE
  rw [← Equiv.sum_comp E.symm
        (fun ν : Fin (K + m) → Bool =>
          if (∀ i : Fin m, ν (Fin.natAdd K i) = false) then
            ((fun s => if s = t₁.bits then (1 : ENNReal) else 0) (restrict b' ν)) *
              ∏ i : Fin (K + m), (if (i : ℕ) < K then wfac δ.val (ν i) else 1)
          else 0)]
  apply Finset.sum_congr rfl
  intro μ _
  -- `ν j := μ (Fin.cast hsum j)`.
  have hEsymm : (E.symm μ) = (fun j : Fin (K + m) => μ (Fin.cast hsum j)) := by
    funext j
    simp [hE, Equiv.arrowCongr, finCongr]
  rw [hEsymm]
  -- The index `Fin.cast hsum (Fin.natAdd K i)` for `i : Fin m` ranges over `{j : j ≥ K}`.
  -- (1) prefix-mask ⟺ false-tail.
  have hmask : isPrefixMask n r μ ↔ (∀ i : Fin m, μ (Fin.cast hsum (Fin.natAdd K i)) = false) := by
    constructor
    · intro hpm i
      apply hpm
      have hval : ((Fin.cast hsum (Fin.natAdd K i) : Fin n) : ℕ) = K + (i : ℕ) := by
        rw [Fin.val_cast]; simp [Fin.natAdd]
      rw [hKZ.symm]
      have : (K : ℤ) ≤ (((Fin.cast hsum (Fin.natAdd K i) : Fin n) : ℕ) : ℤ) := by
        rw [hval]; push_cast; omega
      exact_mod_cast this
    · intro htail i hi
      -- `i ≥ K` (in ℕ), so `i` is in the tail block: `i = Fin.cast hsum (Fin.natAdd K (i - K))`.
      have hiK : K ≤ (i : ℕ) := by
        have : (K : ℤ) ≤ (i : ℤ) := by rw [hKZ]; exact hi
        exact_mod_cast this
      have hidx : (i : ℕ) - K < m := by omega
      have := htail ⟨(i : ℕ) - K, hidx⟩
      have hcast : (Fin.cast hsum (Fin.natAdd K ⟨(i : ℕ) - K, hidx⟩) : Fin n) = i := by
        apply Fin.ext
        simp [Fin.natAdd]
        omega
      rwa [hcast] at this
  -- (2) restrict matches.
  have hrestrict : restrict b' (fun j : Fin (K + m) => μ (Fin.cast hsum j)) = restrict b μ := by
    rw [hb']
    rw [show (⟨fun i => b.bit (Fin.cast hsum i)⟩ : BinVec (K + m))
          = (⟨fun j => b.bit (Fin.cast hsum j)⟩ : BinVec (K + m)) from rfl]
    exact restrict_cast hsum b μ
  -- (3) gate product matches.
  have hgate : (∏ i : Fin n, (if ((i : ℤ) < ((n / 4 : ℕ) : ℤ) + r) then
          (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) else 1))
      = ∏ j : Fin (K + m), (if (j : ℕ) < K then wfac δ.val (μ (Fin.cast hsum j)) else 1) := by
    rw [← Equiv.prod_comp (finCongr hsum)
          (fun i : Fin n => (if ((i : ℤ) < ((n / 4 : ℕ) : ℤ) + r) then
            (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) else 1))]
    apply Finset.prod_congr rfl
    intro j _
    have hjcast : ((finCongr hsum j : Fin n) : ℕ) = (j : ℕ) := by simp [finCongr]
    have hgateZ : (((finCongr hsum j : Fin n) : ℤ) < ((n / 4 : ℕ) : ℤ) + r) ↔ (j : ℕ) < K := by
      rw [← hKZ]
      have hjZ : ((finCongr hsum j : Fin n) : ℤ) = (j : ℕ) := by exact_mod_cast hjcast
      rw [hjZ]
      constructor
      · intro hlt; exact_mod_cast hlt
      · intro hlt; exact_mod_cast hlt
    by_cases hc : (j : ℕ) < K
    · rw [if_pos (hgateZ.mpr hc), if_pos hc]
      unfold wfac
      have : (finCongr hsum j : Fin n) = Fin.cast hsum j := by simp [finCongr]
      rw [this]
    · rw [if_neg (fun h => hc (hgateZ.mp h)), if_neg hc]
  -- Assemble: rewrite the gate product, then match the two `if`s.
  rw [hgate]
  simp only []
  rw [hrestrict]
  by_cases hpm : isPrefixMask n r μ
  · rw [if_pos (hmask.mp hpm)]
    by_cases hr : restrict b μ = t₁.bits
    · rw [if_pos ⟨hpm, hr⟩, if_pos hr]
    · rw [if_neg (fun h => hr h.2), if_neg hr, zero_mul]
  · rw [if_neg (fun h => hpm (hmask.mpr h))]
    rw [if_neg (fun h => hpm h.1), zero_mul]

/-! ### Suffix offset cast (piece 1b)

Mirror of `prefixWeight_eq_segSum`.  `suffixWeight n b δ r t₂` sums over
`μ : Fin n → Bool` gated by `isSuffixMask` (false for `(i:ℤ) < 3n/4+r`) with the
per-index weight product gated `if (i:ℤ) ≥ 3n/4+r`.  We reindex
`Fin n ≃ Fin (k+m)` with `k = (3n/4+r).toNat` (the false-prefix block) and
`m = n-k` (the suffix segment), turning the `ℤ`-gate into the `ℕ`-gate of
`suffixWindow_eq_segSum`. -/
lemma suffixWeight_eq_segSum {n : ℕ} (b : BinVec n) (δ : DelProb) (r : ℤ)
    (t₂ : Trace n)
    (hk0 : 0 ≤ ((n / 4 + n / 2 : ℕ) : ℤ) + r)
    (hkn : ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (n : ℤ)) :
    suffixWeight n b δ r t₂
      = segSum δ.val
          (⟨fun i => b.bit (Fin.cast (by
              have hkn' : (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat ≤ n := by
                have h := Int.toNat_le.mpr hkn; simpa using h
              omega)
            (Fin.natAdd (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat i))⟩
              : BinVec (n - (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat))
          (fun s => if s = t₂.bits then 1 else 0) := by
  set K : ℕ := (((n / 4 + n / 2 : ℕ) : ℤ) + r).toNat with hK
  have hKZ : (K : ℤ) = ((n / 4 + n / 2 : ℕ) : ℤ) + r := Int.toNat_of_nonneg hk0
  have hKn : K ≤ n := by
    have := Int.toNat_le.mpr hkn; simpa [hK] using this
  set m : ℕ := n - K with hm
  have hsum : K + m = n := by omega
  set b' : BinVec (K + m) := ⟨fun i => b.bit (Fin.cast hsum i)⟩ with hb'
  have hwin := PartialDominatesSegmentAlign.suffixWindow_eq_segSum (k := K) (m := m) δ.val b'
        (fun s => if s = t₂.bits then 1 else 0)
  rw [show (segSum δ.val
          (⟨fun i => b.bit (Fin.cast hsum (Fin.natAdd K i))⟩ : BinVec m)
          (fun s => if s = t₂.bits then 1 else 0))
        = segSum δ.val (⟨fun i => b'.bit (Fin.natAdd K i)⟩ : BinVec m)
            (fun s => if s = t₂.bits then 1 else 0) from by
      congr 1]
  rw [← hwin]
  unfold suffixWeight
  set E : (Fin (K + m) → Bool) ≃ (Fin n → Bool) :=
    (finCongr hsum).arrowCongr (Equiv.refl Bool) with hE
  rw [← Equiv.sum_comp E.symm
        (fun ν : Fin (K + m) → Bool =>
          if (∀ i : Fin K, ν (Fin.castAdd m i) = false) then
            ((fun s => if s = t₂.bits then (1 : ENNReal) else 0) (restrict b' ν)) *
              ∏ i : Fin (K + m), (if (i : ℕ) ≥ K then wfac δ.val (ν i) else 1)
          else 0)]
  apply Finset.sum_congr rfl
  intro μ _
  have hEsymm : (E.symm μ) = (fun j : Fin (K + m) => μ (Fin.cast hsum j)) := by
    funext j
    simp [hE, Equiv.arrowCongr, finCongr]
  rw [hEsymm]
  -- (1) suffix-mask ⟺ false-prefix.
  have hmask : isSuffixMask n r μ ↔ (∀ i : Fin K, μ (Fin.cast hsum (Fin.castAdd m i)) = false) := by
    constructor
    · intro hsm i
      apply hsm
      have hval : ((Fin.cast hsum (Fin.castAdd m i) : Fin n) : ℕ) = (i : ℕ) := by
        rw [Fin.val_cast]; simp [Fin.castAdd, Fin.castLE]
      rw [hKZ.symm]
      have hlt : (((Fin.cast hsum (Fin.castAdd m i) : Fin n) : ℕ) : ℤ) < (K : ℤ) := by
        rw [hval]; exact_mod_cast i.isLt
      exact_mod_cast hlt
    · intro hpre i hi
      have hiK : (i : ℕ) < K := by
        have : (i : ℤ) < (K : ℤ) := by rw [hKZ]; exact hi
        exact_mod_cast this
      have := hpre ⟨(i : ℕ), hiK⟩
      have hcast : (Fin.cast hsum (Fin.castAdd m ⟨(i : ℕ), hiK⟩) : Fin n) = i := by
        apply Fin.ext
        rw [Fin.val_cast]; simp [Fin.castAdd, Fin.castLE]
      rwa [hcast] at this
  -- (2) restrict matches.
  have hrestrict : restrict b' (fun j : Fin (K + m) => μ (Fin.cast hsum j)) = restrict b μ := by
    rw [hb']
    exact restrict_cast hsum b μ
  -- (3) gate product matches.
  have hgate : (∏ i : Fin n, (if ((i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r) then
          (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) else 1))
      = ∏ j : Fin (K + m), (if (j : ℕ) ≥ K then wfac δ.val (μ (Fin.cast hsum j)) else 1) := by
    rw [← Equiv.prod_comp (finCongr hsum)
          (fun i : Fin n => (if ((i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r) then
            (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) else 1))]
    apply Finset.prod_congr rfl
    intro j _
    have hjcast : ((finCongr hsum j : Fin n) : ℕ) = (j : ℕ) := by simp [finCongr]
    have hjZ : ((finCongr hsum j : Fin n) : ℤ) = (j : ℕ) := by exact_mod_cast hjcast
    have hgateZ : (((finCongr hsum j : Fin n) : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r) ↔ (j : ℕ) ≥ K := by
      rw [← hKZ, hjZ]
      constructor
      · intro hge; exact_mod_cast hge
      · intro hge; exact_mod_cast hge
    by_cases hc : (j : ℕ) ≥ K
    · rw [if_pos (hgateZ.mpr hc), if_pos hc]
      unfold wfac
      have : (finCongr hsum j : Fin n) = Fin.cast hsum j := by simp [finCongr]
      rw [this]
    · rw [if_neg (fun h => hc (hgateZ.mp h)), if_neg hc]
  rw [hgate]
  simp only []
  rw [hrestrict]
  by_cases hsm : isSuffixMask n r μ
  · rw [if_pos (hmask.mp hsm)]
    by_cases hr : restrict b μ = t₂.bits
    · rw [if_pos ⟨hsm, hr⟩, if_pos hr]
    · rw [if_neg (fun h => hr h.2), if_neg hr, zero_mul]
  · rw [if_neg (fun h => hsm (hmask.mpr h))]
    rw [if_neg (fun h => hsm h.1), zero_mul]

end PartialDominatesOffsetCast
