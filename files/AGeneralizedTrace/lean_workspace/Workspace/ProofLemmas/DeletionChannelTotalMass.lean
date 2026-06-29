import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.DeletionLengthMarginal

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

namespace DeletionChannelTotalMassProof

/-- Decompose a single value via length-indicator: if `f t = w`, then
`w = ∑_z [|t|=z] * w` over a finite range that contains `|t|`. -/
lemma decompose_by_length {n : ℕ} (t : Workspace.Types.Trace.Trace n)
    (w : ENNReal) :
    w = ∑ z ∈ Finset.range (n + 1),
        (if t.bits.length = z then w else 0) := by
  rw [Finset.sum_eq_single t.bits.length]
  · simp
  · intro z _ hz
    rw [if_neg (Ne.symm hz)]
  · intro h
    exfalso
    apply h
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le t.length_le)

/-- Binomial total mass: ∑_{z=0}^{N} C(N,z) (1-δ)^z δ^(N-z) = 1.
Uses `add_pow` for `(1-δ + δ)^N`. -/
lemma binomialPMF_sum_eq_one (N : ℕ) (δ : Workspace.Types.DelProb.DelProb) :
    ∑ z ∈ Finset.range (N + 1), binomialPMF N δ z = 1 := by
  have h1 : (0 : ℝ) ≤ 1 - δ.val := by linarith [δ.lt_one]
  have h2 : (0 : ℝ) ≤ δ.val := le_of_lt δ.pos
  -- The real-valued binomial identity
  have hsum_real : ∑ z ∈ Finset.range (N + 1),
      (1 - δ.val) ^ z * δ.val ^ (N - z) * (N.choose z : ℝ) = 1 := by
    have hadd := add_pow (1 - δ.val) δ.val N
    have hone : (1 - δ.val) + δ.val = 1 := by ring
    rw [hone] at hadd
    -- hadd : 1 ^ N = ∑ k ∈ Finset.range (N + 1), (1-δ)^k * δ^(N-k) * N.choose k
    rw [one_pow] at hadd
    exact hadd.symm
  -- Now convert to ENNReal sum
  unfold binomialPMF
  -- Goal: ∑ z, (N.choose z : ENNReal) * ofReal((1-δ.val)^z) * ofReal(δ.val^(N-z)) = 1
  have hkey : ∀ z ∈ Finset.range (N + 1),
      (N.choose z : ENNReal) * ENNReal.ofReal ((1 - δ.val) ^ z) *
        ENNReal.ofReal (δ.val ^ (N - z)) =
      ENNReal.ofReal ((1 - δ.val) ^ z * δ.val ^ (N - z) * (N.choose z : ℝ)) := by
    intro z _
    have hp1 : (0 : ℝ) ≤ (1 - δ.val) ^ z := pow_nonneg h1 z
    have hp2 : (0 : ℝ) ≤ δ.val ^ (N - z) := pow_nonneg h2 (N - z)
    rw [show ((1 - δ.val) ^ z * δ.val ^ (N - z) * (N.choose z : ℝ)) =
            ((N.choose z : ℝ) * ((1 - δ.val) ^ z * δ.val ^ (N - z))) from by ring]
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_mul hp1]
    rw [ENNReal.ofReal_natCast]
    ring
  rw [Finset.sum_congr rfl hkey]
  -- Now goal: ∑ z, ofReal(...) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [hsum_real, ENNReal.ofReal_one]
  · intro z _
    have hp1 : (0 : ℝ) ≤ (1 - δ.val) ^ z := pow_nonneg h1 z
    have hp2 : (0 : ℝ) ≤ δ.val ^ (N - z) := pow_nonneg h2 (N - z)
    have hp3 : (0 : ℝ) ≤ (N.choose z : ℝ) := Nat.cast_nonneg _
    positivity

/-- For terms outside the binomial range, binomialPMF vanishes. -/
lemma binomialPMF_eq_zero_of_gt {N : ℕ} (δ : Workspace.Types.DelProb.DelProb)
    {z : ℕ} (h : N < z) : binomialPMF N δ z = 0 := by
  unfold binomialPMF
  have : N.choose z = 0 := Nat.choose_eq_zero_of_lt h
  simp [this]

/-- Extend the binomialPMF sum to a larger range. -/
lemma binomialPMF_sum_extend (N M : ℕ) (h : N ≤ M)
    (δ : Workspace.Types.DelProb.DelProb) :
    ∑ z ∈ Finset.range (M + 1), binomialPMF N δ z = 1 := by
  rw [← binomialPMF_sum_eq_one N δ]
  -- Goal: ∑ z ∈ range(M+1), bin N δ z = ∑ z ∈ range(N+1), bin N δ z
  -- Use symm to flip and apply sum_subset_zero_on_sdiff with s₁ = range(N+1) ⊆ s₂ = range(M+1)
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · -- range(N+1) ⊆ range(M+1)
    intro z hz
    rw [Finset.mem_range] at hz ⊢
    omega
  · -- For z ∈ range(M+1) \ range(N+1), bin N δ z = 0
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hz
    apply binomialPMF_eq_zero_of_gt δ
    omega
  · intros; rfl

/-- Cast bridge: `((n / 4 : ℕ) : ℤ) = (n : ℤ) / 4`. -/
lemma nat_div_four_cast (n : ℕ) : ((n / 4 : ℕ) : ℤ) = (n : ℤ) / 4 := by
  push_cast
  omega

/-- Cast bridge: `((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2`. -/
lemma nat_div_two_cast (n : ℕ) : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by
  push_cast
  omega

/-- The total prefix mass formula. -/
lemma sum_prefixWeight_eq_one {n : ℕ} (b : Workspace.Types.BinVec.BinVec n)
    (δ : Workspace.Types.DelProb.DelProb) (r : ℤ)
    (h_lo : 0 ≤ r + (n / 4 : ℤ))
    (h_hi : r + (n / 4 : ℤ) ≤ (n / 2 : ℤ)) :
    (∑' t : Workspace.Types.Trace.Trace n, prefixWeight n b δ r t) = 1 := by
  -- Step 1: Decompose each summand by length
  have step1 :
      (∑' t : Workspace.Types.Trace.Trace n, prefixWeight n b δ r t) =
      ∑' t : Workspace.Types.Trace.Trace n,
        ∑ z ∈ Finset.range (n + 1),
          (if t.bits.length = z then prefixWeight n b δ r t else 0) := by
    apply tsum_congr
    intro t
    exact decompose_by_length t (prefixWeight n b δ r t)
  rw [step1]
  -- Step 2: Swap tsum and Finset.sum
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  -- Step 3: Apply DeletionLengthMarginal at each z
  have step3 : ∀ z ∈ Finset.range (n + 1),
      (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then prefixWeight n b δ r t else 0)) =
      prefixLengthWeight n δ r z := by
    intro z _
    exact (DeletionLengthMarginal b δ r h_lo h_hi z).1
  rw [Finset.sum_congr rfl step3]
  -- Step 4: Rewrite prefixLengthWeight using in-range hypothesis (it's the if-positive branch)
  have h_lo' : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := by
    rw [nat_div_four_cast]; exact h_lo
  have h_hi' : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    rw [nat_div_four_cast, nat_div_two_cast]; exact h_hi
  have h_inrange : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧
      r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := ⟨h_lo', h_hi'⟩
  have h_unfold : ∀ z, prefixLengthWeight n δ r z =
      binomialPMF (r + ((n / 4 : ℕ) : ℤ)).toNat δ z := by
    intro z
    unfold prefixLengthWeight
    -- The let binding evaluates k := r + (n/4 : ℕ); the if-condition matches h_inrange.
    rw [dif_pos h_inrange]
  simp only [h_unfold]
  -- Step 5: Sum is 1 by the binomial identity (with len ≤ n)
  apply binomialPMF_sum_extend
  -- Need: (r + n/4).toNat ≤ n
  have h_nonneg : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := h_lo'
  have h_toNat_eq : ((r + ((n / 4 : ℕ) : ℤ)).toNat : ℤ) = r + ((n / 4 : ℕ) : ℤ) :=
    Int.toNat_of_nonneg h_nonneg
  -- We have h_hi' : r + (n/4 : ℕ) ≤ (n/2 : ℕ), and (n/2 : ℕ) ≤ n
  have h_div_le : (n / 2 : ℕ) ≤ n := Nat.div_le_self n 2
  -- Combine: (r+n/4).toNat ≤ (n/2 : ℕ) ≤ n
  have h_toNat_le_div : (r + ((n / 4 : ℕ) : ℤ)).toNat ≤ n / 2 := by
    have h2 : (((r + ((n / 4 : ℕ) : ℤ)).toNat : ℤ)) ≤ ((n / 2 : ℕ) : ℤ) := by
      rw [h_toNat_eq]; exact h_hi'
    exact_mod_cast h2
  exact h_toNat_le_div.trans h_div_le

/-- The total suffix mass formula. -/
lemma sum_suffixWeight_eq_one {n : ℕ} (b : Workspace.Types.BinVec.BinVec n)
    (δ : Workspace.Types.DelProb.DelProb) (r : ℤ)
    (h_lo : 0 ≤ r + (n / 4 : ℤ))
    (h_hi : r + (n / 4 : ℤ) ≤ (n / 2 : ℤ)) :
    (∑' t : Workspace.Types.Trace.Trace n, suffixWeight n b δ r t) = 1 := by
  have step1 :
      (∑' t : Workspace.Types.Trace.Trace n, suffixWeight n b δ r t) =
      ∑' t : Workspace.Types.Trace.Trace n,
        ∑ z ∈ Finset.range (n + 1),
          (if t.bits.length = z then suffixWeight n b δ r t else 0) := by
    apply tsum_congr
    intro t
    exact decompose_by_length t (suffixWeight n b δ r t)
  rw [step1]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have step3 : ∀ z ∈ Finset.range (n + 1),
      (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then suffixWeight n b δ r t else 0)) =
      suffixLengthWeight n δ r z := by
    intro z _
    exact (DeletionLengthMarginal b δ r h_lo h_hi z).2
  rw [Finset.sum_congr rfl step3]
  have h_lo' : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := by
    rw [nat_div_four_cast]; exact h_lo
  have h_hi' : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    rw [nat_div_four_cast, nat_div_two_cast]; exact h_hi
  have h_inrange : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧
      r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := ⟨h_lo', h_hi'⟩
  have h_unfold : ∀ z, suffixLengthWeight n δ r z =
      binomialPMF (n - n / 2 - (r + ((n / 4 : ℕ) : ℤ)).toNat) δ z := by
    intro z
    unfold suffixLengthWeight
    rw [dif_pos h_inrange]
  simp only [h_unfold]
  apply binomialPMF_sum_extend
  exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

end DeletionChannelTotalMassProof

theorem DeletionChannelTotalMass :
    ∀ {n : ℕ} (b : Workspace.Types.BinVec.BinVec n)
      (δ : Workspace.Types.DelProb.DelProb)
      (r : ℤ),
      0 ≤ r + (n / 4 : ℤ) → r + (n / 4 : ℤ) ≤ (n / 2 : ℤ) →
      (∑' t : Workspace.Types.Trace.Trace n,
          Workspace.Types.PartialDeletionProcess.prefixWeight n b δ r t) = 1
      ∧
      (∑' t : Workspace.Types.Trace.Trace n,
          Workspace.Types.PartialDeletionProcess.suffixWeight n b δ r t) = 1 := by
  intro n b δ r h_lo h_hi
  exact ⟨DeletionChannelTotalMassProof.sum_prefixWeight_eq_one b δ r h_lo h_hi,
         DeletionChannelTotalMassProof.sum_suffixWeight_eq_one b δ r h_lo h_hi⟩
