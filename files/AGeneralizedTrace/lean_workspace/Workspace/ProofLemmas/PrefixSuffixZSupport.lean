import Mathlib
import Workspace.Types.DelProb
import Workspace.Types.LengthsOnlyProcess

open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.DelProb

namespace Workspace.ProofLemmas.PrefixSuffixZSupport

/-- Lemma 1: binomialPMF is 0 when z > len, because Nat.choose len z = 0. -/
theorem binomialPMF_eq_zero_of_lt (len z : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (h : len < z) : Workspace.Types.LengthsOnlyProcess.binomialPMF len δ z = 0 := by
  unfold binomialPMF
  have hc : Nat.choose len z = 0 := Nat.choose_eq_zero_of_lt h
  simp [hc]

/-- Lemma 2: prefixLengthWeight is 0 for z ≥ n/2 + 1. -/
theorem prefixLengthWeight_eq_zero_of_ge (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) (z : ℕ) (hz : n / 2 + 1 ≤ z) :
    Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r z = 0 := by
  unfold prefixLengthWeight
  simp only
  split_ifs with hk
  · -- hk : 0 ≤ k ∧ k ≤ (n / 2 : ℕ)  where k = r + (n / 4 : ℕ)
    apply binomialPMF_eq_zero_of_lt
    -- k.toNat ≤ n / 2, and z ≥ n / 2 + 1, so k.toNat < z
    have hk2 : (r + (n / 4 : ℕ)).toNat ≤ n / 2 := by
      have := hk.2
      exact Int.toNat_le.mpr this
    omega
  · rfl

/-- Lemma 3: suffixLengthWeight is 0 for z ≥ n/2 + 2 (under n % 8 = 1). -/
theorem suffixLengthWeight_eq_zero_of_ge (n : ℕ) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) (z : ℕ) (hz : n / 2 + 2 ≤ z) :
    Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r z = 0 := by
  unfold suffixLengthWeight
  simp only
  split_ifs with hk
  · apply binomialPMF_eq_zero_of_lt
    -- suffix length = n - 2*(n/4) - k.toNat
    -- Under n % 8 = 1: n - 2*(n/4) ≤ n/2 + 1 (by omega from n%8=1)
    -- k.toNat ≥ 0, so suffix length ≤ n/2 + 1 < z
    have hk2 : (r + (n / 4 : ℕ)).toNat ≤ n / 2 := by
      have := hk.2
      exact Int.toNat_le.mpr this
    -- n - 2 * (n / 4) ≤ n / 2 + 1 when n % 8 = 1
    have hbound : n - 2 * (n / 4) ≤ n / 2 + 1 := by omega
    omega
  · rfl

/-- Lemma 4: tsum over ℕ of prefixLengthWeight equals finite sum over range(n/2+1). -/
theorem tsum_prefixLengthWeight_eq_finite (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) :
    (∑' z : ℕ, Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r z) =
    ∑ z ∈ Finset.range (n / 2 + 1),
      Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r z := by
  apply tsum_eq_sum
  intro z hz
  apply prefixLengthWeight_eq_zero_of_ge
  simp only [Finset.mem_range, not_lt] at hz
  exact hz

/-- Lemma 5: tsum over ℕ of suffixLengthWeight equals finite sum over range(n/2+2). -/
theorem tsum_suffixLengthWeight_eq_finite (n : ℕ) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb) (r : ℤ) :
    (∑' z : ℕ, Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r z) =
    ∑ z ∈ Finset.range (n / 2 + 2),
      Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r z := by
  apply tsum_eq_sum
  intro z hz
  apply suffixLengthWeight_eq_zero_of_ge n hmod
  simp only [Finset.mem_range, not_lt] at hz
  exact hz

end Workspace.ProofLemmas.PrefixSuffixZSupport
