import Mathlib
import Workspace.Types.DelProb
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-!
# LengthWeightBinPMFIdentity

Identities relating the lengths-only process's prefix/suffix length weights to the
binomial-PMF factors of `Fterm`.

* `binomialPMF_toReal_eq_binPMF` : the ENNReal `binomialPMF len δ z` cast to ℝ equals
  the real binomial PMF `binPMF len (1 - δ) z`.  (`binomialPMF` uses success
  probability `1 - δ`; `binPMF p` uses success probability `p`; the two agree with
  `p = 1 - δ` since `δ^(len-z) = (1 - (1-δ))^(len-z)`.)

* `prefixLengthWeight_toReal_eq` : prefix length weight cast to ℝ equals the SECOND
  factor of `Fterm`, i.e. `binPMFInt ((n/4)+r).toNat (1-δ) z` (discrepancy ZERO).

* `suffixLengthWeight_toReal_eq` : suffix length weight cast to ℝ equals
  `binPMFInt (((n/4)-r).toNat + 1) (1-δ) z` — the suffix has length one MORE than
  the `Fterm` factor (the off-by-one of `SuffixOffByOneIntegrated`), for `n % 8 = 1`.
-/

namespace Workspace.ProofLemmas.LengthWeightBinPMFIdentity

open Workspace.Types.AlternatingSumExpression
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.DelProb

/-- `binomialPMF len δ z` (an ENNReal) cast to ℝ equals `binPMF len (1 - δ) z`. -/
lemma binomialPMF_toReal_eq_binPMF (len : ℕ) (δ : DelProb) (z : ℕ) :
    (binomialPMF len δ z).toReal = binPMF len (1 - δ.val) z := by
  unfold binomialPMF binPMF
  have hδ0 : (0 : ℝ) ≤ δ.val := δ.pos.le
  have hδ1 : δ.val ≤ 1 := δ.lt_one.le
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg (by linarith) z),
      ENNReal.toReal_ofReal (pow_nonneg hδ0 (len - z))]
  split_ifs with hz
  · -- z ≤ len: same product, with (1 - (1 - δ)) = δ
    have hsub : (1 : ℝ) - (1 - δ.val) = δ.val := by ring
    rw [hsub]
  · -- z > len: choose len z = 0, both sides 0
    have hch : (Nat.choose len z : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [hch]; ring

/-- `binPMFInt M p (z : ℕ)` for a natural index `z` equals `binPMF M p z` (the
nonnegative-index branch is always taken). -/
lemma binPMFInt_natCast (M : ℕ) (p : ℝ) (z : ℕ) :
    binPMFInt M p (z : ℤ) = binPMF M p z := by
  unfold binPMFInt
  by_cases hz : (z : ℤ) ≤ (M : ℤ)
  · rw [if_pos ⟨by positivity, hz⟩, Int.toNat_natCast]
  · rw [if_neg (by omega)]
    unfold binPMF
    rw [if_neg (by omega)]

/-- **Prefix length weight = Fterm's prefix binomial factor (discrepancy ZERO).**
On the offset support `0 ≤ r + n/4 ≤ n/2`, the prefix length weight cast to ℝ equals
`binPMFInt ((n/4 : ℤ) + r).toNat (1 - δ) z`, exactly the second factor of `Fterm`. -/
lemma prefixLengthWeight_toReal_eq (n : ℕ) (δ : DelProb) (r : ℤ) (z : ℕ)
    (hsupp : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (prefixLengthWeight n δ r z).toReal
      = binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ.val) (z : ℤ) := by
  unfold prefixLengthWeight
  rw [dif_pos hsupp]
  rw [binomialPMF_toReal_eq_binPMF, binPMFInt_natCast]
  congr 2
  -- (r + (n/4:ℕ)).toNat = ((n/4:ℤ) + r).toNat
  have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
  rw [hc4, add_comm]

/-- **Suffix length weight off-by-one identity.**
On the offset support, for `n % 8 = 1` the suffix length weight cast to ℝ equals
`binPMF (((n / 4 : ℤ) - r).toNat + 1) (1 - δ) z`.  The suffix has length one MORE than
`Fterm`'s third factor `binPMFInt ((n/4:ℤ) - r).toNat (1-δ) z` — this is the off-by-one
that `SuffixOffByOneIntegrated` absorbs. -/
lemma suffixLengthWeight_toReal_eq (n : ℕ) (hmod : n % 8 = 1) (δ : DelProb) (r : ℤ)
    (z : ℕ)
    (hsupp : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (suffixLengthWeight n δ r z).toReal
      = binPMF (((n / 4 : ℤ) - r).toNat + 1) (1 - δ.val) z := by
  unfold suffixLengthWeight
  rw [dif_pos hsupp, binomialPMF_toReal_eq_binPMF]
  congr 2
  -- length: n - 2*(n/4) - (r + n/4).toNat = (n/4 - r).toNat + 1   for n%8=1
  have hmod4 : n % 4 = 1 := by omega
  -- n/4 = q, n = 4q+1, n/2 = 2q
  have hk_nonneg : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := hsupp.1
  have hq2 : n - 2 * (n / 4) = 2 * (n / 4) + 1 := by omega
  -- (r + n/4).toNat as a Nat
  set k := (r + ((n / 4 : ℕ) : ℤ)).toNat with hkdef
  have hk_eq : (k : ℤ) = r + ((n / 4 : ℕ) : ℤ) := Int.toNat_of_nonneg hk_nonneg
  have hk_le : k ≤ 2 * (n / 4) := by
    have : (k : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by rw [hk_eq]; exact hsupp.2
    have h2 : (n / 2 : ℕ) = 2 * (n / 4) := by omega
    omega
  -- ((n/4:ℤ) - r).toNat
  have hr_le : r ≤ ((n / 4 : ℕ) : ℤ) := by
    have h2 : (n / 2 : ℕ) = 2 * (n / 4) := by omega
    have := hsupp.2
    omega
  have hdiff_nonneg : 0 ≤ ((n / 4 : ℤ) - r) := by
    have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
    rw [← hc4]; omega
  set t := ((n / 4 : ℤ) - r).toNat with htdef
  have ht_eq : (t : ℤ) = (n / 4 : ℤ) - r := Int.toNat_of_nonneg hdiff_nonneg
  have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
  -- k + t = 2*(n/4):  (r + n/4) + (n/4 - r) = 2*(n/4)
  have hkt : (k : ℤ) + (t : ℤ) = 2 * ((n / 4 : ℕ) : ℤ) := by
    rw [hk_eq, ht_eq, hc4]; ring
  have hkt_nat : k + t = 2 * (n / 4) := by omega
  -- goal length: n - 2*(n/4) - k = t + 1
  omega

end Workspace.ProofLemmas.LengthWeightBinPMFIdentity
