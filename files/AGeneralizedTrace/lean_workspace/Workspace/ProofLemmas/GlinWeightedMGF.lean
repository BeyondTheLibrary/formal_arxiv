import Mathlib
import Workspace.ProofLemmas.GenvConvergence
import Workspace.ProofLemmas.PeriodicBaseKfoldPeriodisation
import Workspace.ProofLemmas.MGFOfIteratedConvolution

open scoped Real Complex
open MeasureTheory intervalIntegral

set_option maxHeartbeats 4000000

/-!
# The LINEAR single-factor envelope `Glin` and its weighted-MGF gate (Lemma 7)

This file implements the F49 fix for the `SublemmaFourierKway` k ≥ 1 bridge: instead
of restricting the *circular* series `Genv` to `[-π,π]` (whose weighted MGF does not
factor), we build the per-factor envelope on the **linear** convolution series.

* `Bbase0 n := Bbase n · 1_{[-π,π]}` — the single compact-support factor.  It is
  *continuous* with compact support (because `Bbase n (±π) = cos(±π/2)^n = 0`).
* `Glin n η := ∑'_b α^{b+1} · linPow (Bbase0 n) (b+1) η` — the linear single-factor
  envelope, where `linPow` is the iterated *linear* self-convolution on ℝ.

The key result `Glin_mgf_le_one` is the clean weighted-MGF gate that the circular
`Genv0` route could never reach:

    ∫_ℝ e^{√n ξ} · Glin n ξ ≤ 1.

Its proof factors cleanly:
  `∫ e^{√n} linPow(Bbase0)(b+1) = (∫ e^{√n} Bbase0)^{b+1} = g(√n)^{b+1}`
(`MGFOfIteratedConvolution`, `Bbase0` compact support), with `∫ e^{√n} Bbase0 =
Gweight n √n = g(√n)`.  Swapping `∫` and `∑'` (dominated by the convergent geometric
series `∑ (α g)^{b+1}`) gives

    ∫ e^{√n} Glin = ∑_{b≥0} (α · g(√n))^{b+1} = (α g)/(1 - α g) ≤ 1,

using `GenvConvergence.alphaGweight_le_half` (`α g(√n) ≤ 1/2`).
-/

namespace GlinWeightedMGF

open GenvConvergence
open T4ToCircPowRPeriodic
open PeriodicBaseKfoldPeriodisation
open PerFactorFourierModulus

/-! ## The compact-support base `Bbase0` and the linear envelope `Glin`. -/

/-- The single compact-support factor: `Bbase n` restricted to `[-π,π]`. -/
noncomputable def Bbase0 (n : ℕ) : ℝ → ℝ :=
  fun x => if |x| ≤ Real.pi then Bbase n x else 0

theorem Bbase0_nonneg (n : ℕ) (x : ℝ) : 0 ≤ Bbase0 n x := by
  unfold Bbase0; split_ifs; exacts [Bbase_nonneg n x, le_refl 0]

theorem Bbase0_supp (n : ℕ) : ∀ x, |x| > Real.pi → Bbase0 n x = 0 := by
  intro x hx; unfold Bbase0; rw [if_neg (not_le.mpr hx)]

/-- `Bbase0 n` is continuous: `Bbase n` glues to `0` across the boundary `|x| = π`
where `Bbase n (±π) = cos(±π/2)^n = 0`. -/
theorem Bbase0_continuous (n : ℕ) (hn : 1 ≤ n) : Continuous (Bbase0 n) := by
  unfold Bbase0
  apply continuous_if (p := fun x => |x| ≤ Real.pi)
  · intro a ha
    have hset : {x : ℝ | |x| ≤ Real.pi} = Set.Icc (-Real.pi) Real.pi := by
      ext x; simp [Set.mem_Icc, abs_le]
    have hbd : a = -Real.pi ∨ a = Real.pi := by
      have hmem : a ∈ frontier (Set.Icc (-Real.pi) Real.pi) := by rw [hset] at ha; exact ha
      rw [frontier_Icc (by linarith [Real.pi_pos])] at hmem
      rcases hmem with h | h
      · left; simpa using h
      · right; simpa using h
    have hle : |a| ≤ Real.pi := by
      rcases hbd with h | h
      · rw [h, abs_of_neg (by linarith [Real.pi_pos])]; linarith
      · rw [h, abs_of_pos Real.pi_pos]
    rw [Bbase_eq_cos_pow n hn a hle]
    have hcos : Real.cos (a / 2) = 0 := by
      rcases hbd with h | h
      · rw [h, show -Real.pi / 2 = -(Real.pi/2) by ring, Real.cos_neg, Real.cos_pi_div_two]
      · rw [h, Real.cos_pi_div_two]
    rw [hcos, zero_pow (by omega)]
  · exact (Bbase_continuous n).continuousOn
  · exact continuousOn_const

theorem Bbase0_integrable (n : ℕ) (hn : 1 ≤ n) :
    MeasureTheory.Integrable (Bbase0 n) := by
  apply (Bbase0_continuous n hn).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc (a := -Real.pi) (b := Real.pi))
  intro x hx
  rw [Set.mem_Icc, not_and_or] at hx
  apply Bbase0_supp
  rw [gt_iff_lt, lt_abs]
  rcases hx with h | h
  · right; linarith [not_le.mp h]
  · left; linarith [not_le.mp h]

/-- The weighted whole-line MGF of `Bbase0 n` equals the interval weighted MGF
`Gweight n t = ∫_{-π}^{π} e^{tη} Bbase n η`. -/
theorem Bbase0_weighted_integral (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (∫ ξ, Real.exp (t * ξ) * Bbase0 n ξ) = Gweight n t := by
  unfold Gweight Bbase0
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  funext ξ
  rw [Set.indicator_apply]
  by_cases h : ξ ∈ Set.Ioc (-Real.pi) Real.pi
  · rw [if_pos h, if_pos (by rw [Set.mem_Ioc] at h; rw [abs_le]; exact ⟨le_of_lt h.1, h.2⟩),
      mul_comm]
  · rw [if_neg h]
    by_cases h2 : |ξ| ≤ Real.pi
    · rw [if_pos h2]
      rw [Set.mem_Ioc, not_and_or] at h
      rw [abs_le] at h2
      have hxeq : ξ = -Real.pi := by
        rcases h with h | h
        · linarith [h2.1]
        · linarith [h2.2]
      rw [hxeq, Bbase_eq_cos_pow n hn (-Real.pi)
          (by rw [abs_le]; constructor <;> linarith [Real.pi_pos]),
        show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two,
        zero_pow (by omega : n ≠ 0), mul_zero]
    · rw [if_neg h2, mul_zero]

/-! ## Properties of the iterated linear self-convolution `linPow (Bbase0 n)`. -/

/-- The recurrence form for `b ≥ 1` matching `MGFOfIteratedConvolution`. -/
theorem linPow_Bbase0_rec (n : ℕ) : ∀ b : ℕ, 1 ≤ b → ∀ η : ℝ,
    linPow (Bbase0 n) (b + 1) η = ∫ y, linPow (Bbase0 n) b y * Bbase0 n (η - y) := by
  intro b hb η
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb)
  rw [show b' + 1 + 1 = b' + 2 from rfl, linPow_succ_succ]

theorem linPow_Bbase0_nn (n : ℕ) : ∀ b : ℕ, 1 ≤ b → ∀ η, 0 ≤ linPow (Bbase0 n) b η := by
  intro b _ η
  exact linPow_nn (Bbase0 n) (Bbase0_nonneg n) b η

/-- Each `linPow (Bbase0 n) b` is integrable: a `b`-fold convolution of an
integrable function. -/
theorem linPow_Bbase0_int (n : ℕ) (hn : 1 ≤ n) :
    ∀ b : ℕ, 1 ≤ b → MeasureTheory.Integrable (linPow (Bbase0 n) b) := by
  have hB0_int := Bbase0_integrable n hn
  intro b hb
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb)
  clear hb
  induction b' with
  | zero =>
    show MeasureTheory.Integrable (linPow (Bbase0 n) 1)
    rw [linPow_one]
    exact hB0_int
  | succ k ih =>
    have heq : linPow (Bbase0 n) (k + 1 + 1) =
        MeasureTheory.convolution (linPow (Bbase0 n) (k + 1)) (Bbase0 n)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      funext η
      rw [show k + 1 + 1 = k + 2 from rfl, linPow_succ_succ]
      rw [MeasureTheory.convolution_lsmul]
      simp [smul_eq_mul]
    rw [heq]
    exact MeasureTheory.Integrable.integrable_convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) ih hB0_int

/-- `linPow (Bbase0 n) b` vanishes outside `[-bπ, bπ]`. -/
theorem linPow_Bbase0_supp (n : ℕ) :
    ∀ b : ℕ, 1 ≤ b → ∀ x, |x| > (b : ℝ) * Real.pi → linPow (Bbase0 n) b x = 0 := by
  intro b hb
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb)
  clear hb
  induction b' with
  | zero =>
    intro x hx
    show linPow (Bbase0 n) 1 x = 0
    rw [linPow_one]
    apply Bbase0_supp
    have h_cast : ((Nat.succ 0 : ℕ) : ℝ) * Real.pi = Real.pi := by push_cast; ring
    rw [h_cast] at hx
    linarith
  | succ k ih =>
    intro x hx
    have hk1 : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [linPow_Bbase0_rec n (k + 1) hk1 x]
    have h_pointwise : ∀ y, linPow (Bbase0 n) (k + 1) y * Bbase0 n (x - y) = 0 := by
      intro y
      by_cases hy : |y| > ((k + 1 : ℕ) : ℝ) * Real.pi
      · rw [ih y hy, zero_mul]
      · rw [not_lt] at hy
        have h_xy : |x - y| > Real.pi := by
          have h_abs : |x| - |y| ≤ |x - y| := abs_sub_abs_le_abs_sub _ _
          have h_cast_succ : ((k + 1 + 1 : ℕ) : ℝ) * Real.pi
              = ((k + 1 : ℕ) : ℝ) * Real.pi + Real.pi := by push_cast; ring
          rw [h_cast_succ] at hx
          linarith
        rw [Bbase0_supp n (x - y) h_xy, mul_zero]
    rw [show (fun y => linPow (Bbase0 n) (k + 1) y * Bbase0 n (x - y)) = (fun _ => (0 : ℝ)) by
      funext y; exact h_pointwise y]
    simp

/-! ## MGF factorization of the iterated convolution `linPow (Bbase0 n)`. -/

/-- **Per-`b` MGF factorization.**  For every `t` and `b`,
`∫ e^{tη} linPow (Bbase0 n) (b+1) η = (∫ e^{tξ} Bbase0 n ξ)^{b+1} = (Gweight n t)^{b+1}`.
This is `MGFOfIteratedConvolution` specialised to the compactly-supported base
`Bbase0 n`, followed by `Bbase0_weighted_integral`. -/
theorem linPow_Bbase0_mgf (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : ∀ b : ℕ,
    (∫ η, Real.exp (t * η) * linPow (Bbase0 n) (b + 1) η)
      = (Gweight n t) ^ (b + 1) := by
  intro b
  rw [MGFOfIteratedConvolution (Bbase0 n) (Bbase0_nonneg n) (Bbase0_integrable n hn)
    Real.pi Real.pi_pos (Bbase0_supp n)
    (linPow (Bbase0 n)) (linPow_one (Bbase0 n)) (linPow_Bbase0_rec n)
    (linPow_Bbase0_nn n) (linPow_Bbase0_int n hn) (linPow_Bbase0_supp n) t b]
  rw [Bbase0_weighted_integral n hn t]

/-- The **linear single-factor envelope** `Glin n η := ∑'_b α^{b+1} linPow(Bbase0 n)(b+1) η`. -/
noncomputable def Glin (n : ℕ) (η : ℝ) : ℝ :=
  ∑' b : ℕ, alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) η

theorem Glin_nonneg (n : ℕ) (η : ℝ) : 0 ≤ Glin n η := by
  unfold Glin
  apply tsum_nonneg
  intro b
  exact mul_nonneg (pow_nonneg (alphaC_nonneg n) _) (linPow_Bbase0_nn n (b + 1) (Nat.succ_le_succ (Nat.zero_le _)) η)

/-! ## The weighted-MGF gate `∫ e^{√n ξ} Glin n ξ ≤ 1`. -/

/-- The per-`b` summand of `e^{√n ξ} · Glin n ξ`. -/
private noncomputable def Fterm (n : ℕ) (b : ℕ) : ℝ → ℝ :=
  fun ξ => alphaC n ^ (b + 1) * (Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Bbase0 n) (b + 1) ξ)

/-- The weighted iterated convolution `e^{√n ξ} · linPow(Bbase0 n)(b+1) ξ` is integrable:
`linPow` is integrable and supported in the compact `[-(b+1)π,(b+1)π]`, and `e^{√n·}` is
continuous, so the product is integrable. -/
theorem weighted_linPow_integrable (n : ℕ) (hn : 1 ≤ n) (b : ℕ) :
    MeasureTheory.Integrable
      (fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Bbase0 n) (b + 1) ξ) := by
  set R : ℝ := ((b : ℝ) + 1) * Real.pi with hR
  have hRpos : 0 < R := by
    rw [hR]; positivity
  have hsupp : ∀ x, |x| > R → linPow (Bbase0 n) (b + 1) x = 0 := by
    intro x hx
    apply linPow_Bbase0_supp n (b + 1) (Nat.succ_le_succ (Nat.zero_le _)) x
    rw [hR] at hx; push_cast at hx ⊢; convert hx using 2
  -- IntegrableOn linPow on the compact set Icc[-R,R].
  have hlin_int : MeasureTheory.Integrable (linPow (Bbase0 n) (b + 1)) :=
    linPow_Bbase0_int n hn (b + 1) (Nat.succ_le_succ (Nat.zero_le _))
  have hIO : MeasureTheory.IntegrableOn (linPow (Bbase0 n) (b + 1)) (Set.Icc (-R) R) :=
    hlin_int.integrableOn
  -- Multiply by the continuous weight on the compact Icc.
  have hmul : MeasureTheory.IntegrableOn
      (fun ξ => linPow (Bbase0 n) (b + 1) ξ * Real.exp (Real.sqrt (n : ℝ) * ξ))
      (Set.Icc (-R) R) :=
    hIO.mul_continuousOn
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      isCompact_Icc
  -- Outside the Icc the product vanishes, so it is integrable on the whole line.
  have hzero : ∀ x ∉ Set.Icc (-R) R,
      (fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Bbase0 n) (b + 1) ξ) x = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or] at hx
    have hax : |x| > R := by
      rw [gt_iff_lt, lt_abs]
      rcases hx with h | h
      · right; linarith [not_le.mp h]
      · left; linarith [not_le.mp h]
    simp only [hsupp x hax, mul_zero]
  rw [← MeasureTheory.integrableOn_univ]
  have hsplit : (Set.univ : Set ℝ) = Set.Icc (-R) R ∪ (Set.Icc (-R) R)ᶜ := by
    simp
  rw [hsplit]
  apply MeasureTheory.IntegrableOn.union
  · refine (hmul.congr_fun ?_ measurableSet_Icc)
    intro x _; simp only []; rw [mul_comm]
  · apply MeasureTheory.IntegrableOn.congr_fun (f := fun _ => (0 : ℝ))
    · exact MeasureTheory.integrableOn_zero
    · intro x hx; exact (hzero x hx).symm
    · exact measurableSet_Icc.compl

theorem Fterm_integrable (n : ℕ) (hn : 1 ≤ n) (b : ℕ) :
    MeasureTheory.Integrable (Fterm n b) := by
  unfold Fterm
  exact (weighted_linPow_integrable n hn b).const_mul _

/-- `∫ Fterm n b = (α · Gweight n √n)^{b+1}`. -/
theorem Fterm_integral (n : ℕ) (hn : 1 ≤ n) (b : ℕ) :
    (∫ ξ, Fterm n b ξ) = (alphaC n * Gweight n (Real.sqrt (n : ℝ))) ^ (b + 1) := by
  unfold Fterm
  rw [MeasureTheory.integral_const_mul]
  rw [linPow_Bbase0_mgf n hn (Real.sqrt (n : ℝ)) b]
  rw [mul_pow]

theorem Fterm_nonneg (n : ℕ) (b : ℕ) (ξ : ℝ) : 0 ≤ Fterm n b ξ := by
  unfold Fterm
  apply mul_nonneg (pow_nonneg (alphaC_nonneg n) _)
  exact mul_nonneg (Real.exp_pos _).le
    (linPow_Bbase0_nn n (b + 1) (Nat.succ_le_succ (Nat.zero_le _)) ξ)

/-- **The weighted-MGF gate** (F49 fix): `∫_ℝ e^{√n ξ} Glin n ξ ≤ 1`. -/
theorem Glin_mgf_le_one (n : ℕ) (hn : 1 ≤ n) :
    (∫ ξ, Real.exp (Real.sqrt (n : ℝ) * ξ) * Glin n ξ) ≤ 1 := by
  set q : ℝ := alphaC n * Gweight n (Real.sqrt (n : ℝ)) with hq
  have hq_nn : 0 ≤ q := mul_nonneg (alphaC_nonneg n) (Gweight_nonneg n _)
  have hq_half : q ≤ 1 / 2 := alphaGweight_le_half n hn
  have hq_lt : q < 1 := by linarith
  -- Each Fterm integrable; summability of ∫‖Fterm‖.
  have hint : ∀ b, MeasureTheory.Integrable (Fterm n b) := fun b => Fterm_integrable n hn b
  have hnorm_eq : ∀ b, (∫ ξ, ‖Fterm n b ξ‖) = q ^ (b + 1) := by
    intro b
    have : (∫ ξ, ‖Fterm n b ξ‖) = ∫ ξ, Fterm n b ξ := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ; simp only []; rw [Real.norm_of_nonneg (Fterm_nonneg n b ξ)]
    rw [this, Fterm_integral n hn b]
  have hsumm : Summable (fun b => ∫ ξ, ‖Fterm n b ξ‖) := by
    apply Summable.congr (f := fun b => q ^ (b + 1))
    · apply (summable_geometric_of_lt_one hq_nn hq_lt).comp_injective (Nat.succ_injective) |>.congr
      intro b; rfl
    · intro b; rw [hnorm_eq b]
  -- Swap ∫ and ∑'.
  have hswap : (∑' b, ∫ ξ, Fterm n b ξ) = ∫ ξ, ∑' b, Fterm n b ξ :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm
  -- The pointwise sum equals e^{√n ξ} · Glin n ξ.
  have hpt : ∀ ξ, (∑' b, Fterm n b ξ) = Real.exp (Real.sqrt (n : ℝ) * ξ) * Glin n ξ := by
    intro ξ
    unfold Fterm Glin
    rw [← tsum_mul_left]
    apply tsum_congr; intro b; ring
  -- Assemble.
  rw [show (fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) * Glin n ξ)
        = (fun ξ => ∑' b, Fterm n b ξ) from by funext ξ; rw [hpt ξ]]
  rw [← hswap]
  -- ∑'_b ∫ Fterm = ∑'_b q^{b+1} = q/(1-q) ≤ 1.
  have hval : (∑' b, ∫ ξ, Fterm n b ξ) = ∑' b : ℕ, q ^ (b + 1) := by
    apply tsum_congr; intro b; rw [Fterm_integral n hn b]
  rw [hval]
  -- ∑'_b q^{b+1} = q · ∑'_b q^b = q/(1-q).
  have hgeo : (∑' b : ℕ, q ^ (b + 1)) = q * (1 - q)⁻¹ := by
    rw [show (fun b : ℕ => q ^ (b + 1)) = (fun b : ℕ => q * q ^ b) from by funext b; rw [pow_succ]; ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq_nn hq_lt]
  rw [hgeo]
  -- q/(1-q) ≤ 1 ⟺ q ≤ 1-q ⟺ q ≤ 1/2.
  rw [mul_inv_le_iff₀ (by linarith)]
  linarith

end GlinWeightedMGF
