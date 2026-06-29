import Mathlib
import Workspace.ProofLemmas.GlinWeightedMGF
import Workspace.ProofLemmas.PeriodicBaseKfoldPeriodisation
import Workspace.ProofLemmas.PeriodicCircConvPeriodisation
import Workspace.ProofLemmas.GenvConvergence

open scoped Real
open MeasureTheory intervalIntegral

set_option maxHeartbeats 4000000

/-!
# Per-B periodisation: `circPowR (Bbase n) B ξ ≤ ∑'_s linPow (Bbase0 n) B (ξ+2πs)`

This discharges the six Tonelli/integrability hypotheses of
`PeriodicBaseKfoldPeriodisation.periodise_kfold` for the genuinely-`2π`-periodic
base `g := Bbase n` (`= ‖FT (pBinC n)‖`).  Its fundamental-domain restriction is
exactly `Bbase0 n` (`GlinWeightedMGF.Bbase0`), which is continuous with compact
support `[-π,π]` (`Bbase0_continuous`, `Bbase0_supp`).  Hence

  `circPowR (Bbase n) B ξ ≤ ∑'_s linPow (Bbase0 n) B (ξ+2πs)`   (B ≥ 1, |ξ| ≤ π).
-/

namespace PerBPeriodisation

open PeriodicBaseKfoldPeriodisation
open GlinWeightedMGF
open T4ToCircPowRPeriodic
open GenvConvergence
open PeriodicCircConvPeriodisation

/-- **General periodisation summability.**  If `f` vanishes off `[-R,R]` then the
shifted series `s ↦ f (x + 2πs)` is summable (only finitely many shifts hit the
compact support). -/
theorem periodised_summable_of_compact_support (f : ℝ → ℝ) (R : ℝ)
    (hsupp : ∀ y, |y| > R → f y = 0) (x : ℝ) :
    Summable (fun s : ℤ => f (x + 2 * Real.pi * (s : ℝ))) := by
  apply summable_of_finite_support
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  apply Set.Finite.subset (Set.finite_Icc
    (⌈(-R - x) / (2 * Real.pi)⌉) (⌊(R - x) / (2 * Real.pi)⌋))
  intro s hs
  simp only [Function.mem_support, ne_eq] at hs
  have hmem : |x + 2 * Real.pi * (s : ℝ)| ≤ R := by
    by_contra hc
    exact hs (hsupp _ (not_le.mp hc))
  rw [abs_le] at hmem
  rw [Set.mem_Icc]
  refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
  · rw [div_le_iff₀ h2π]; nlinarith [hmem.1]
  · rw [le_div_iff₀ h2π]; nlinarith [hmem.2]

/-- **General periodisation boundedness.**  If `f ≥ 0`, `f ≤ M`, and `f` vanishes off
`[-R,R]`, then the shifted series is uniformly bounded (independent of `x`) by
`M·(R/π + 2)`.  Only finitely many shifts hit the support, each contributing `≤ M`. -/
theorem periodised_bdd_of_compact_support (f : ℝ → ℝ) (R M : ℝ) (hR : 0 ≤ R)
    (hf_nn : ∀ y, 0 ≤ f y) (hf_le : ∀ y, f y ≤ M)
    (hsupp : ∀ y, |y| > R → f y = 0) (x : ℝ) :
    (∑' s : ℤ, f (x + 2 * Real.pi * (s : ℝ))) ≤ M * (R / Real.pi + 2) := by
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have hMnn : 0 ≤ M := le_trans (hf_nn x) (hf_le x)
  set lo : ℤ := ⌈(-R - x) / (2 * Real.pi)⌉ with hlo_def
  set hi : ℤ := ⌊(R - x) / (2 * Real.pi)⌋ with hhi_def
  have hsupp_sub :
      (Function.support (fun s : ℤ => f (x + 2 * Real.pi * (s : ℝ)))) ⊆ ↑(Finset.Icc lo hi) := by
    intro s hs
    simp only [Function.mem_support, ne_eq] at hs
    have hmem : |x + 2 * Real.pi * (s : ℝ)| ≤ R := by
      by_contra hc; exact hs (hsupp _ (not_le.mp hc))
    rw [abs_le] at hmem
    rw [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
    · rw [div_le_iff₀ h2π]; nlinarith [hmem.1]
    · rw [le_div_iff₀ h2π]; nlinarith [hmem.2]
  rw [tsum_eq_sum' hsupp_sub]
  -- bound the real cardinality (hi - lo + 1) ≤ R/π + 1
  have hcard_real : ((Finset.Icc lo hi).card : ℝ) ≤ R / Real.pi + 2 := by
    by_cases hempty : hi < lo
    · rw [Finset.Icc_eq_empty (by omega)]
      simp only [Finset.card_empty, Nat.cast_zero]
      have : 0 ≤ R / Real.pi := div_nonneg hR (le_of_lt Real.pi_pos)
      linarith
    · push_neg at hempty
      rw [Int.card_Icc]
      have htoNat : ((hi + 1 - lo).toNat : ℝ) = ((hi : ℝ) + 1 - (lo : ℝ)) := by
        have : ((hi + 1 - lo).toNat : ℤ) = hi + 1 - lo := Int.toNat_of_nonneg (by omega)
        have h2 : (((hi + 1 - lo).toNat : ℤ) : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by rw [this]
        rw [Int.cast_natCast] at h2
        rw [h2]; push_cast; ring
      rw [htoNat]
      -- (hi - lo + 1 : ℝ) ≤ R/π + 2
      have hhi_le : (hi : ℝ) ≤ (R - x) / (2 * Real.pi) := Int.floor_le _
      have hlo_ge : (-R - x) / (2 * Real.pi) ≤ (lo : ℝ) := Int.le_ceil _
      have hdiff : (hi : ℝ) - (lo : ℝ) ≤ R / Real.pi := by
        have hstep : (hi : ℝ) - (lo : ℝ)
            ≤ (R - x) / (2 * Real.pi) - (-R - x) / (2 * Real.pi) := by linarith
        have heq : (R - x) / (2 * Real.pi) - (-R - x) / (2 * Real.pi) = R / Real.pi := by
          field_simp; ring
        linarith [heq ▸ hstep]
      linarith
  calc (∑ s ∈ Finset.Icc lo hi, f (x + 2 * Real.pi * (s : ℝ)))
      ≤ ∑ _s ∈ Finset.Icc lo hi, M := Finset.sum_le_sum (fun s _ => hf_le _)
    _ = (Finset.Icc lo hi).card • M := by rw [Finset.sum_const]
    _ = ((Finset.Icc lo hi).card : ℝ) * M := by rw [nsmul_eq_mul]
    _ ≤ (R / Real.pi + 2) * M := mul_le_mul_of_nonneg_right hcard_real hMnn
    _ = M * (R / Real.pi + 2) := by ring

/-- `Bbase0 n` is exactly the fundamental-domain restriction `g0` that
`periodise_kfold` builds from `g := Bbase n`. -/
theorem Bbase0_eq_g0 (n : ℕ) :
    Bbase0 n = fun x => if |x| ≤ Real.pi then Bbase n x else 0 := rfl

/-- `Bbase0 n` has compact support contained in `[-π,π]`. -/
theorem Bbase0_hasCompactSupport (n : ℕ) (hn : 1 ≤ n) :
    HasCompactSupport (Bbase0 n) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -Real.pi) (b := Real.pi))
  intro x hx
  rw [Set.mem_Icc, not_and_or] at hx
  apply Bbase0_supp
  rw [gt_iff_lt, lt_abs]
  rcases hx with h | h
  · right; linarith [not_le.mp h]
  · left; linarith [not_le.mp h]

/-- Summability of the periodised `Bbase0`-series: only finitely many shifts land
in the compact support `[-π,π]`. -/
theorem Bbase0_periodised_summable (n : ℕ) (hn : 1 ≤ n) (w : ℝ) :
    Summable (fun s : ℤ =>
      (fun x => if |x| ≤ Real.pi then Bbase n x else 0) (w + 2 * Real.pi * (s : ℝ))) := by
  rw [← Bbase0_eq_g0 n]
  exact periodised_summable_of_compact_support (Bbase0 n) Real.pi (Bbase0_supp n) w

/-- `circPowR (Bbase n) m` is continuous for `m ≥ 1`. -/
theorem circPowR_Bbase_continuous (n : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    Continuous (fun ξ => circPowR (Bbase n) m ξ) :=
  circPowR_continuous (Bbase n) (Bbase_continuous n) m hm

/-- The circular-power convolution integrand (P-side) is interval-integrable on the
fundamental window: a product of two continuous functions. -/
theorem hcircint_Bbase (n : ℕ) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    IntervalIntegrable (fun η => circPowR (Bbase n) m η * Bbase n (ξ - η))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  apply Continuous.intervalIntegrable
  exact (circPowR_Bbase_continuous n m hm).mul
    ((Bbase_continuous n).comp (continuous_const.sub continuous_id))

/-- The linear-power convolution integrand (whole line) is integrable: `linPow Bbase0
m` is integrable (compact support) and `Bbase n (ξ-·)` is bounded by 1. -/
theorem hfoldint_Bbase (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    Integrable (fun η => linPow (Bbase0 n) m η * Bbase n (ξ - η)) := by
  apply MeasureTheory.Integrable.mul_bdd (c := 1)
  · exact linPow_Bbase0_int n hn m hm
  · exact ((Bbase_continuous n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Bbase_nonneg n _)]
    exact Bbase_le_one n _

/-- `Bbase0 n` is bounded by `1` everywhere. -/
theorem Bbase0_le_one' (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : Bbase0 n x ≤ 1 := by
  unfold Bbase0
  split_ifs with h
  · exact Bbase_le_one n x
  · norm_num

/-- **The periodised fundamental-domain base series is bounded by `2`.**  At most two
shifts land in the width-`2π` support `[-π,π]` (consecutive integers differ by `2π`),
and each contributes `≤ 1`. -/
theorem periodised_Bbase0_le_two (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (∑' s : ℤ, Bbase0 n (x + 2 * Real.pi * (s : ℝ))) ≤ 2 := by
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  -- The two-element finset capturing all possible nonzero shifts.
  set s0 : ℤ := ⌊(Real.pi - x) / (2 * Real.pi)⌋ with hs0
  set T : Finset ℤ := {s0 - 1, s0, s0 + 1} with hT
  have hsupp_sub : (Function.support (fun s : ℤ => Bbase0 n (x + 2 * Real.pi * (s : ℝ)))) ⊆ ↑T := by
    intro s hs
    simp only [Function.mem_support, ne_eq] at hs
    have hmem : |x + 2 * Real.pi * (s : ℝ)| ≤ Real.pi := by
      by_contra hc
      exact hs (Bbase0_supp n _ (not_le.mp hc))
    rw [abs_le] at hmem
    -- s ≤ (π-x)/(2π) and s ≥ (-π-x)/(2π); these floor/ceil into {s0-1,s0,s0+1}
    have hhi : (s : ℝ) ≤ (Real.pi - x) / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]; nlinarith [hmem.2]
    have hlo : (-Real.pi - x) / (2 * Real.pi) ≤ (s : ℝ) := by
      rw [div_le_iff₀ h2π]; nlinarith [hmem.1]
    have hsle : s ≤ s0 := Int.le_floor.mpr hhi
    have hsge : s0 - 1 ≤ s := by
      have : (-Real.pi - x) / (2 * Real.pi) = (Real.pi - x) / (2 * Real.pi) - 1 := by
        field_simp; ring
      rw [this] at hlo
      have hfloor : (s0 : ℝ) ≤ (Real.pi - x) / (2 * Real.pi) := Int.floor_le _
      -- s ≥ (π-x)/(2π) - 1 ≥ s0 - 1 (since s0 ≤ (π-x)/(2π))... but careful direction.
      -- We have s ≥ (π-x)/(2π) - 1 and s0 = ⌊(π-x)/(2π)⌋ so (π-x)/(2π) < s0 + 1.
      have hlt : (Real.pi - x) / (2 * Real.pi) < (s0 : ℝ) + 1 := Int.lt_floor_add_one _
      have : ((s0 : ℝ)) - 1 < (s : ℝ) + 1 := by linarith
      have hcast : (s0 : ℝ) - 1 < (s : ℝ) + 1 := this
      have : s0 - 1 < s + 1 := by exact_mod_cast hcast
      omega
    rw [hT, Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  -- tsum over support = finset sum over T (terms outside support are 0).
  rw [tsum_eq_sum' hsupp_sub]
  -- each term ≤ 1, card T ≤ 3 ... need ≤ 2.  Use: at most two of the three are nonzero.
  -- Bound: ∑ ≤ ∑ of (the at most 2 nonzero), but simpler: bound each by 1 and note s0-1 & s0+1 can't both be nonzero.
  -- Crude provable bound: the three-term sum, with the two extreme terms not both nonzero.
  have hb : ∀ s : ℤ, Bbase0 n (x + 2 * Real.pi * (s : ℝ)) ≤ 1 := fun s => Bbase0_le_one' n hn _
  have hnn : ∀ s : ℤ, 0 ≤ Bbase0 n (x + 2 * Real.pi * (s : ℝ)) := fun s => Bbase0_nonneg n _
  -- The two extreme shifts s0-1 and s0+1 cannot both be nonzero (they are 4π apart).
  have hextreme : Bbase0 n (x + 2 * Real.pi * ((s0 - 1 : ℤ) : ℝ)) = 0
      ∨ Bbase0 n (x + 2 * Real.pi * ((s0 + 1 : ℤ) : ℝ)) = 0 := by
    by_contra hc
    push_neg at hc
    have h1 : |x + 2 * Real.pi * ((s0 - 1 : ℤ) : ℝ)| ≤ Real.pi := by
      by_contra hcc; exact hc.1 (Bbase0_supp n _ (not_le.mp hcc))
    have h2 : |x + 2 * Real.pi * ((s0 + 1 : ℤ) : ℝ)| ≤ Real.pi := by
      by_contra hcc; exact hc.2 (Bbase0_supp n _ (not_le.mp hcc))
    rw [abs_le] at h1 h2
    push_cast at h1 h2
    have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  -- Now sum over {s0-1, s0, s0+1}: ≤ 2.
  have hne1 : s0 - 1 ≠ s0 := by omega
  have hne2 : s0 - 1 ≠ s0 + 1 := by omega
  have hne3 : s0 ≠ s0 + 1 := by omega
  rw [hT]
  rw [Finset.sum_insert (by simp [hne1, hne2]),
      Finset.sum_insert (by simp [hne3])]
  simp only [Finset.sum_singleton]
  rcases hextreme with he | he
  · rw [he]; nlinarith [hb s0, hb (s0+1), hnn s0, hnn (s0+1)]
  · rw [he]; nlinarith [hb (s0-1), hb s0, hnn (s0-1), hnn s0]

/-- For any constant shift `c`, `η ↦ linPow (Bbase0 n) m η * Bbase0 n (c - η)` is
integrable (compact-support integrable `linPow` times bounded `Bbase0`). -/
theorem linPow_Bbase0_mul_shift_int (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (c : ℝ) :
    Integrable (fun η => linPow (Bbase0 n) m η * Bbase0 n (c - η)) := by
  apply MeasureTheory.Integrable.mul_bdd (c := 1)
  · exact linPow_Bbase0_int n hn m hm
  · exact ((Bbase0_continuous n hn).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Bbase0_nonneg n _)]
    exact Bbase0_le_one' n hn _

/-- `∫ η, linPow (Bbase0 n) m η * Bbase0 n (c - η) = linPow (Bbase0 n) (m+1) c`
(recognise the convolution that produces the next linear power). -/
theorem linPow_Bbase0_mul_shift_integral (n : ℕ) (m : ℕ) (hm : 1 ≤ m) (c : ℝ) :
    (∫ η, linPow (Bbase0 n) m η * Bbase0 n (c - η)) = linPow (Bbase0 n) (m + 1) c := by
  rw [linPow_Bbase0_rec n m hm c]

/-- The series `s ↦ linPow (Bbase0 n) (m+1) (ξ + 2πs)` is summable: `linPow ... (m+1)`
has compact support `[-(m+1)π, (m+1)π]`. -/
theorem linPow_Bbase0_periodised_summable (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    Summable (fun s : ℤ => linPow (Bbase0 n) (m + 1) (ξ + 2 * Real.pi * (s : ℝ))) := by
  apply periodised_summable_of_compact_support (linPow (Bbase0 n) (m + 1))
    (((m : ℝ) + 1) * Real.pi)
  intro y hy
  apply linPow_Bbase0_supp n (m + 1) (Nat.succ_le_succ (Nat.zero_le _)) y
  push_cast at hy ⊢
  convert hy using 2

/-- Measurability of the periodised fundamental-domain base
`η ↦ ∑'_s Bbase0 n ((ξ-η)+2πs)` (via the NNReal tsum of measurable nonneg terms). -/
theorem periodised_Bbase0_aesm (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) :
    AEStronglyMeasurable
      (fun η => ∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))) volume := by
  -- Rewrite the real tsum as the coercion of an NNReal tsum (all terms nonneg).
  have hmeas : Measurable
      (fun η => ∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))) := by
    have hterm_meas : ∀ s : ℤ,
        Measurable (fun η => (Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))).toNNReal) := by
      intro s
      apply Measurable.real_toNNReal
      exact ((Bbase0_continuous n hn).comp
        ((continuous_const.sub continuous_id).add continuous_const)).measurable
    have hnn : Measurable
        (fun η => ∑' s:ℤ, (Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))).toNNReal) :=
      Measurable.nnreal_tsum hterm_meas
    -- the real tsum equals (NNReal tsum : ℝ) since terms are nonneg
    have heq : (fun η => ∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ)))
        = (fun η => ((∑' s:ℤ, (Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))).toNNReal : NNReal) : ℝ)) := by
      funext η
      rw [NNReal.coe_tsum]
      apply tsum_congr; intro s
      rw [Real.coe_toNNReal _ (Bbase0_nonneg n _)]
    rw [heq]
    exact NNReal.continuous_coe.measurable.comp hnn
  exact hmeas.aestronglyMeasurable

/-- **Whole-line integrability of `linPow Bbase0 m · periodised-Bbase0`** (the
`hPg0int` hypothesis of `periodise_kfold` for `g := Bbase n`). -/
theorem hPg0int_Bbase (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    Integrable (fun η => linPow (Bbase0 n) m η
      * (∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ)))) := by
  apply MeasureTheory.Integrable.mul_bdd (c := 2)
  · exact linPow_Bbase0_int n hn m hm
  · exact periodised_Bbase0_aesm n hn ξ
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_of_nonneg
      (tsum_nonneg (fun s => Bbase0_nonneg n _))]
    exact periodised_Bbase0_le_two n hn (ξ - η)

/-- `linPow (Bbase0 n) m` is continuous (iterated convolution of the continuous
compact-support base `Bbase0 n`). -/
theorem linPow_Bbase0_continuous (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    Continuous (linPow (Bbase0 n) m) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  clear hm
  induction m' with
  | zero =>
    show Continuous (linPow (Bbase0 n) 1)
    rw [linPow_one]; exact Bbase0_continuous n hn
  | succ k ih =>
    have heq : linPow (Bbase0 n) (k + 1 + 1) =
        MeasureTheory.convolution (linPow (Bbase0 n) (k + 1)) (Bbase0 n)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      funext ξ
      rw [show k + 1 + 1 = k + 2 from rfl, linPow_succ_succ]
      rw [MeasureTheory.convolution_lsmul]; simp [smul_eq_mul]
    rw [heq]
    have hcs : HasCompactSupport (linPow (Bbase0 n) (k + 1)) := by
      apply HasCompactSupport.intro (isCompact_Icc (a := -(((k:ℝ)+1) * Real.pi))
        (b := ((k:ℝ)+1) * Real.pi))
      intro x hx
      rw [Set.mem_Icc, not_and_or] at hx
      apply linPow_Bbase0_supp n (k + 1) (Nat.succ_le_succ (Nat.zero_le _)) x
      rw [gt_iff_lt, lt_abs]
      rcases hx with h | h
      · right; push_cast; linarith [not_le.mp h]
      · left; push_cast; linarith [not_le.mp h]
    exact HasCompactSupport.continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hcs ih (Bbase0_continuous n hn).locallyIntegrable

/-- Measurability of the periodised linear power `η ↦ ∑'_t linPow Bbase0 m (η+2πt)`. -/
theorem periodised_linPow_aesm (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    AEStronglyMeasurable
      (fun η => ∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) volume := by
  have hcont : Continuous (linPow (Bbase0 n) m) := linPow_Bbase0_continuous n hn m hm
  have hmeas : Measurable
      (fun η => ∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) := by
    have hterm_meas : ∀ t : ℤ,
        Measurable (fun η => (linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))).toNNReal) := by
      intro t
      exact (hcont.comp (continuous_id.add continuous_const)).measurable.real_toNNReal
    have hnn := Measurable.nnreal_tsum hterm_meas
    have heq : (fun η => ∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)))
        = (fun η => ((∑' t:ℤ, (linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))).toNNReal : NNReal) : ℝ)) := by
      funext η
      rw [NNReal.coe_tsum]
      apply tsum_congr; intro t
      rw [Real.coe_toNNReal _ (linPow_Bbase0_nn n m hm _)]
    rw [heq]
    exact NNReal.continuous_coe.measurable.comp hnn
  exact hmeas.aestronglyMeasurable

/-- `linPow (Bbase0 n) m` is uniformly bounded: it is continuous with compact support. -/
theorem linPow_Bbase0_bdd (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    ∃ M : ℝ, ∀ x, linPow (Bbase0 n) m x ≤ M := by
  have hcs : HasCompactSupport (linPow (Bbase0 n) m) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -((m:ℝ) * Real.pi))
      (b := (m:ℝ) * Real.pi))
    intro x hx
    rw [Set.mem_Icc, not_and_or] at hx
    apply linPow_Bbase0_supp n m hm x
    rw [gt_iff_lt, lt_abs]
    rcases hx with h | h
    · right; linarith [not_le.mp h]
    · left; linarith [not_le.mp h]
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous (linPow_Bbase0_continuous n hn m hm)
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rw [Real.norm_eq_abs] at this
  exact le_trans (le_abs_self _) this

/-- The periodised linear power `η ↦ ∑'_t linPow (Bbase0 n) m (η+2πt)` is uniformly
bounded by an `η`-independent constant. -/
theorem periodised_linPow_bdd (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ η, (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) ≤ C := by
  obtain ⟨M, hM⟩ := linPow_Bbase0_bdd n hn m hm
  refine ⟨max M 0 * ((m:ℝ) * Real.pi / Real.pi + 2), fun η => ?_⟩
  apply periodised_bdd_of_compact_support (linPow (Bbase0 n) m)
    ((m:ℝ) * Real.pi) (max M 0)
  · positivity
  · exact fun y => linPow_Bbase0_nn n m hm y
  · exact fun y => le_trans (hM y) (le_max_left _ _)
  · intro y hy
    apply linPow_Bbase0_supp n m hm y
    exact hy

/-- **Interval-integrability of the periodised linear-power convolution integrand**
(the `hQint` hypothesis of `periodise_kfold` for `g := Bbase n`).  The periodised
`linPow` is bounded and AE-measurable; `Bbase n (ξ-·)` is continuous and bounded by `1`;
their product is bounded and AE-measurable on the finite window `[-π,π]`. -/
theorem hQint_Bbase (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    IntervalIntegrable
      (fun η => (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)))
        * Bbase n (ξ - η)) MeasureTheory.volume (-Real.pi) Real.pi := by
  obtain ⟨C, hC⟩ := periodised_linPow_bdd n hn m hm
  have hCnn : 0 ≤ C := le_trans (tsum_nonneg (fun t => linPow_Bbase0_nn n m hm _)) (hC 0)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := C)
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · apply AEStronglyMeasurable.mul
    · exact periodised_linPow_aesm n hn m hm
    · exact ((Bbase_continuous n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))|
        = ∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) :=
      abs_of_nonneg (tsum_nonneg (fun t => linPow_Bbase0_nn n m hm _))
    have h2 : |Bbase n (ξ - η)| ≤ 1 := by
      rw [abs_of_nonneg (Bbase_nonneg n _)]; exact Bbase_le_one n _
    rw [h1]
    calc (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * |Bbase n (ξ - η)|
        ≤ C * |Bbase n (ξ - η)| :=
          mul_le_mul_of_nonneg_right (hC η) (abs_nonneg _)
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 hCnn
      _ = C := mul_one C

/-- **Tonelli interchange #2** for `g := Bbase n` (whole-line):
`∫ η, linPow Bbase0 m η · (∑'_s Bbase0 ((ξ-η)+2πs)) = ∑'_s ∫ η, linPow Bbase0 m η · Bbase0 ((ξ+2πs)-η)`.
The integrand is nonnegative; the per-`s` integral is `linPow Bbase0 (m+1) (ξ+2πs)`,
whose series is summable, so `integral_tsum_of_summable_integral_norm` applies. -/
theorem hswap2_Bbase (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    (∫ η, linPow (Bbase0 n) m η
        * (∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))))
      = ∑' s:ℤ, ∫ η, linPow (Bbase0 n) m η * Bbase0 n ((ξ + 2 * Real.pi * (s : ℝ)) - η) := by
  -- per-s integrand
  set F : ℤ → ℝ → ℝ :=
    fun s η => linPow (Bbase0 n) m η * Bbase0 n ((ξ + 2 * Real.pi * (s : ℝ)) - η) with hF
  -- Step 1: rewrite the LHS integrand as a tsum over s of F s η.
  have hpt : ∀ η, linPow (Bbase0 n) m η
        * (∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ)))
      = ∑' s:ℤ, F s η := by
    intro η
    rw [← tsum_mul_left]
    apply tsum_congr; intro s
    simp only [hF]
    congr 2
    ring
  -- Step 2: per-s integrability of F s.
  have hint : ∀ s, Integrable (F s) := by
    intro s
    simp only [hF]
    exact linPow_Bbase0_mul_shift_int n hn m hm (ξ + 2 * Real.pi * (s : ℝ))
  -- Step 3: summability of ∫ ‖F s‖.
  have hnormeq : ∀ s, (∫ η, ‖F s η‖) = linPow (Bbase0 n) (m + 1) (ξ + 2 * Real.pi * (s : ℝ)) := by
    intro s
    have : (∫ η, ‖F s η‖) = ∫ η, F s η := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro η
      simp only [hF]
      rw [Real.norm_of_nonneg]
      exact mul_nonneg (linPow_Bbase0_nn n m hm η) (Bbase0_nonneg n _)
    rw [this]
    simp only [hF]
    exact linPow_Bbase0_mul_shift_integral n m hm (ξ + 2 * Real.pi * (s : ℝ))
  have hsumm : Summable (fun s => ∫ η, ‖F s η‖) := by
    apply Summable.congr (linPow_Bbase0_periodised_summable n hn m hm ξ)
    intro s; rw [hnormeq s]
  -- Assemble.
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm
  calc (∫ η, linPow (Bbase0 n) m η
          * (∑' s:ℤ, Bbase0 n ((ξ - η) + 2 * Real.pi * (s : ℝ))))
      = ∫ η, ∑' s:ℤ, F s η := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hpt
    _ = ∑' s:ℤ, ∫ η, F s η := hswap.symm
    _ = ∑' s:ℤ, ∫ η, linPow (Bbase0 n) m η * Bbase0 n ((ξ + 2 * Real.pi * (s : ℝ)) - η) := by
        rfl

/-- Per-`t` integrability of the windowed integrand `η ↦ linPow (Bbase0 n) m (η+2πt) ·
Bbase n (ξ-η)` on the fundamental window `Ioc (-π) π`: a bounded AE-measurable function
on a finite-measure set. -/
theorem windowed_shift_integrableOn (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ)
    (t : ℤ) :
    MeasureTheory.IntegrableOn
      (fun η => linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) * Bbase n (ξ - η))
      (Set.Ioc (-Real.pi) Real.pi) MeasureTheory.volume := by
  obtain ⟨M, hM⟩ := linPow_Bbase0_bdd n hn m hm
  have hMnn : 0 ≤ M := le_trans (linPow_Bbase0_nn n m hm 0) (hM 0)
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := M)
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · apply AEStronglyMeasurable.mul
    · exact ((linPow_Bbase0_continuous n hn m hm).comp
        (continuous_id.add continuous_const)).aestronglyMeasurable
    · exact ((Bbase_continuous n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))|
        = linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) :=
      abs_of_nonneg (linPow_Bbase0_nn n m hm _)
    have h2 : |Bbase n (ξ - η)| ≤ 1 := by
      rw [abs_of_nonneg (Bbase_nonneg n _)]; exact Bbase_le_one n _
    rw [h1]
    calc linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) * |Bbase n (ξ - η)|
        ≤ M * |Bbase n (ξ - η)| :=
          mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hMnn
      _ = M := mul_one M

/-- **Tonelli interchange #1** for `g := Bbase n` (windowed, over `[-π,π]`):
`∫_{-π}^{π} (∑'_t linPow Bbase0 m (η+2πt)) · Bbase n (ξ-η) dη
   = ∑'_t ∫_{-π}^{π} linPow Bbase0 m (η+2πt) · Bbase n (ξ-η) dη`.
The integrand is nonnegative; summability of `∫_{Ioc} ‖·‖` follows from bounded
finset partial sums (`≤ C·(2π)` since the periodised `linPow` is bounded by `C`),
so `integral_tsum_of_summable_integral_norm` applies on `volume.restrict (Ioc -π π)`. -/
theorem hswap1_Bbase (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    (∫ η in (-Real.pi)..Real.pi,
        (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * Bbase n (ξ - η))
      = ∑' t:ℤ, ∫ η in (-Real.pi)..Real.pi,
          linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) * Bbase n (ξ - η) := by
  have hπ : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  -- per-t windowed integrand
  set G : ℤ → ℝ → ℝ :=
    fun t η => linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) * Bbase n (ξ - η) with hG
  -- bound the periodised linPow by a constant C
  obtain ⟨C, hC⟩ := periodised_linPow_bdd n hn m hm
  have hCnn : 0 ≤ C := le_trans (tsum_nonneg (fun t => linPow_Bbase0_nn n m hm _)) (hC 0)
  -- rewrite both sides as set integrals over Ioc (-π) π
  rw [intervalIntegral.integral_of_le hπ]
  -- per-t integrability on the restricted measure
  have hint : ∀ t, MeasureTheory.Integrable (G t)
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    intro t
    exact windowed_shift_integrableOn n hn m hm ξ t
  -- the LHS integrand is the tsum of the G t (pointwise), since linPow is summable
  have hsumt : ∀ η, Summable (fun t : ℤ => linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) := by
    intro η
    apply periodised_summable_of_compact_support (linPow (Bbase0 n) m) ((m:ℝ) * Real.pi)
    intro y hy; exact linPow_Bbase0_supp n m hm y hy
  have hpt : ∀ η,
      (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * Bbase n (ξ - η)
        = ∑' t:ℤ, G t η := by
    intro η
    rw [hG]
    rw [← tsum_mul_right]
  -- nonnegativity of each ‖G t η‖ = G t η
  have hnormeq : ∀ t,
      (∫ η in Set.Ioc (-Real.pi) Real.pi, ‖G t η‖)
        = ∫ η in Set.Ioc (-Real.pi) Real.pi, G t η := by
    intro t
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro η
    simp only [hG]
    rw [Real.norm_of_nonneg
      (mul_nonneg (linPow_Bbase0_nn n m hm _) (Bbase_nonneg n _))]
  -- summability of t ↦ ∫_Ioc ‖G t‖ via bounded finset partial sums
  have hsumm : Summable (fun t => ∫ η in Set.Ioc (-Real.pi) Real.pi, ‖G t η‖) := by
    apply summable_of_sum_le (c := C * (2 * Real.pi))
    · intro t
      simp only
      rw [hnormeq t]
      exact MeasureTheory.integral_nonneg
        (fun η => mul_nonneg (linPow_Bbase0_nn n m hm _) (Bbase_nonneg n _))
    · intro u
      -- ∑_{t∈u} ∫_Ioc G t = ∫_Ioc ∑_{t∈u} G t ≤ ∫_Ioc C = C·(2π)
      have hswapfin :
          (∑ t ∈ u, ∫ η in Set.Ioc (-Real.pi) Real.pi, ‖G t η‖)
            = ∫ η in Set.Ioc (-Real.pi) Real.pi, ∑ t ∈ u, ‖G t η‖ := by
        rw [MeasureTheory.integral_finset_sum]
        intro t _
        exact (hint t).norm
      rw [hswapfin]
      have hbound : ∀ η ∈ Set.Ioc (-Real.pi) Real.pi, (∑ t ∈ u, ‖G t η‖) ≤ C := by
        intro η _
        have hstep : (∑ t ∈ u, ‖G t η‖)
            = (∑ t ∈ u, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * Bbase n (ξ - η) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          simp only [hG]
          rw [Real.norm_of_nonneg
            (mul_nonneg (linPow_Bbase0_nn n m hm _) (Bbase_nonneg n _))]
        rw [hstep]
        have hpart : (∑ t ∈ u, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)))
            ≤ ∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) :=
          (hsumt η).sum_le_tsum u
            (fun t _ => linPow_Bbase0_nn n m hm _)
        calc (∑ t ∈ u, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * Bbase n (ξ - η)
            ≤ (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * Bbase n (ξ - η) :=
              mul_le_mul_of_nonneg_right hpart (Bbase_nonneg n _)
          _ ≤ C * 1 := by
              apply mul_le_mul (hC η) (Bbase_le_one n _) (Bbase_nonneg n _) hCnn
          _ = C := mul_one C
      calc (∫ η in Set.Ioc (-Real.pi) Real.pi, ∑ t ∈ u, ‖G t η‖)
          ≤ ∫ η in Set.Ioc (-Real.pi) Real.pi, C := by
            apply MeasureTheory.setIntegral_mono_on
            · apply MeasureTheory.integrable_finset_sum
              intro t _; exact (hint t).norm
            · exact MeasureTheory.integrableOn_const
                (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
            · exact measurableSet_Ioc
            · exact hbound
        _ = C * (2 * Real.pi) := by
            rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hπ]
            rw [smul_eq_mul]
            ring
  -- assemble via integral_tsum_of_summable_integral_norm on the restricted measure
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm
  calc (∫ η in Set.Ioc (-Real.pi) Real.pi,
          (∑' t:ℤ, linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ))) * Bbase n (ξ - η))
      = ∫ η in Set.Ioc (-Real.pi) Real.pi, ∑' t:ℤ, G t η := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hpt
    _ = ∑' t:ℤ, ∫ η in Set.Ioc (-Real.pi) Real.pi, G t η := hswap.symm
    _ = ∑' t:ℤ, ∫ η in (-Real.pi)..Real.pi, G t η := by
        apply tsum_congr; intro t
        rw [intervalIntegral.integral_of_le hπ]
    _ = ∑' t:ℤ, ∫ η in (-Real.pi)..Real.pi,
          linPow (Bbase0 n) m (η + 2 * Real.pi * (t : ℝ)) * Bbase n (ξ - η) := by rfl

/-- **Per-`B` periodisation reconciliation** (Lemma 7 piece for the genuine base
`g := Bbase n`).  Instantiating `periodise_kfold` with all six discharged
Tonelli/integrability hypotheses yields, for every `B ≥ 1` and `|ξ| ≤ π`,

  `circPowR (Bbase n) B ξ ≤ ∑'_s linPow (Bbase0 n) B (ξ + 2πs)`.

This is the per-`B` reconciliation that the multiplicity expansion will sum over `B`. -/
theorem circPowR_Bbase_le_periodised_linPow (n : ℕ) (hn : 1 ≤ n)
    (B : ℕ) (hB : 1 ≤ B) (ξ : ℝ) (hξ : |ξ| ≤ Real.pi) :
    circPowR (Bbase n) B ξ
      ≤ ∑' s:ℤ, linPow (Bbase0 n) B (ξ + 2 * Real.pi * (s : ℝ)) := by
  exact periodise_kfold (Bbase n)
    (Bbase_nonneg n)
    (fun x => Bbase_periodic n x)
    (fun w => Bbase0_periodised_summable n hn w)
    (fun m hm ξ => hcircint_Bbase n m hm ξ)
    (fun m hm ξ => hQint_Bbase n hn m hm ξ)
    (fun m hm ξ => hfoldint_Bbase n hn m hm ξ)
    (fun m hm ξ => hPg0int_Bbase n hn m hm ξ)
    (fun m hm ξ => hswap1_Bbase n hn m hm ξ)
    (fun m hm ξ => hswap2_Bbase n hn m hm ξ)
    B hB ξ hξ

end PerBPeriodisation
