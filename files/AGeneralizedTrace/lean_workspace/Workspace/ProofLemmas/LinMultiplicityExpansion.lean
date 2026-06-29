import Mathlib
import Workspace.ProofLemmas.GenvConvergence
import Workspace.ProofLemmas.CircConvBilinear
import Workspace.ProofLemmas.CircPowMultiplicity
import Workspace.ProofLemmas.GlinWeightedMGF
import Workspace.ProofLemmas.PerBPeriodisation
import Workspace.ProofLemmas.CircMultiplicityExpansion

open scoped Real BigOperators
open MeasureTheory intervalIntegral
open CircConvInfra PeriodicBaseKfoldPeriodisation CircPowMultiplicity CircConvBilinear
open T4ToCircPowRPeriodic GenvConvergence PerFactorFourierModulus GlinWeightedMGF
open PerBPeriodisation CircMultiplicityExpansion

set_option maxHeartbeats 4000000

/-!
# Linear multiplicity expansion (Lemma 7, Step 1 — linear half)

`linPow (Glin n) k ξ = ∑'_m (multM k m) · αC^(k+m) · linPow (Bbase0 n) (k+m) ξ`
for `k ≥ 1`, where `Glin n = ∑'_b αC^(b+1) linPow (Bbase0 n) (b+1)`.

This is the LINEAR twin of `CircMultiplicityExpansion.circ_expansion`.  The
combinatorial coefficient `multM` and the scalar collapse `step_collapse` are
reused verbatim from `CircMultiplicityExpansion`.

Key difference from the circular case: `Glin n` is NOT compactly supported (it is
an infinite series of compact-support functions), so the `linConv_tsum_left`
side-conditions are discharged via `Glin` BOUNDEDNESS + continuity (established
below from a geometric domination), not from compact support.  The per-`B`
integrands `linPow (Bbase0 n)(k+B) η · Glin (ξ - η)` are still integrable because
the FIRST factor is compactly supported.
-/

namespace LinMultiplicityExpansion

/-! ## `Good` packaging of `Bbase0`. -/

theorem good_Bbase0 (n : ℕ) (hn : 1 ≤ n) : Good (Bbase0 n) :=
  ⟨Bbase0_continuous n hn, Bbase0_hasCompactSupport n hn⟩

/-! ## The linear geometric sup bound. -/

/-- The L¹ mass of `Bbase0 n` equals `Gint n`. -/
theorem Bbase0_integral_eq_Gint (n : ℕ) (hn : 1 ≤ n) :
    (∫ ξ, Bbase0 n ξ) = Gint n := by
  have h1 : (∫ ξ, Bbase0 n ξ) = Gweight n 0 := by
    have := Bbase0_weighted_integral n hn 0
    simpa using this
  have h2 : Gweight n 0 = Gint n := by
    unfold Gweight Gint
    apply intervalIntegral.integral_congr
    intro η _
    simp
  rw [h1, h2]

/-- The shifted L¹ mass `∫ Bbase0 n (ξ - η) dη = Gint n` (translation invariance). -/
theorem Bbase0_shift_integral_eq_Gint (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) :
    (∫ η, Bbase0 n (ξ - η)) = Gint n := by
  rw [MeasureTheory.integral_sub_left_eq_self (Bbase0 n) MeasureTheory.volume ξ]
  exact Bbase0_integral_eq_Gint n hn

/-- **Uniform geometric sup bound for the linear power.**
`linPow (Bbase0 n) m ξ ≤ (Gint n) ^ (m - 1)` for `m ≥ 1`. -/
theorem linPow_Bbase0_sup_bound (n : ℕ) (hn : 1 ≤ n) :
    ∀ m, 1 ≤ m → ∀ ξ, linPow (Bbase0 n) m ξ ≤ (Gint n) ^ (m - 1) := by
  have hGint_nn : 0 ≤ Gint n := Gint_nonneg n
  intro m hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  clear hm
  induction m' with
  | zero =>
    intro ξ
    show linPow (Bbase0 n) 1 ξ ≤ (Gint n) ^ (1 - 1)
    rw [linPow_one, pow_zero]
    exact Bbase0_le_one' n hn ξ
  | succ k ih =>
    intro ξ
    have hk1 : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [linPow_Bbase0_rec n (k + 1) hk1 ξ]
    -- ∫ linPow (k+1) η * Bbase0 (ξ-η) ≤ ∫ Gint^k * Bbase0 (ξ-η) = Gint^k * Gint = Gint^(k+1)
    have hMk : 0 ≤ (Gint n) ^ k := pow_nonneg hGint_nn k
    have hint_lhs : Integrable (fun η => linPow (Bbase0 n) (k + 1) η * Bbase0 n (ξ - η)) :=
      linPow_Bbase0_mul_shift_int n hn (k + 1) hk1 ξ
    have hint_rhs : Integrable (fun η => (Gint n) ^ k * Bbase0 n (ξ - η)) := by
      apply Integrable.const_mul
      exact (Bbase0_integrable n hn).comp_sub_left ξ
    have hbound : (∫ η, linPow (Bbase0 n) (k + 1) η * Bbase0 n (ξ - η))
        ≤ ∫ η, (Gint n) ^ k * Bbase0 n (ξ - η) := by
      apply MeasureTheory.integral_mono hint_lhs hint_rhs
      intro η
      apply mul_le_mul_of_nonneg_right (ih η) (Bbase0_nonneg n _)
    calc (∫ η, linPow (Bbase0 n) (k + 1) η * Bbase0 n (ξ - η))
        ≤ ∫ η, (Gint n) ^ k * Bbase0 n (ξ - η) := hbound
      _ = (Gint n) ^ k * ∫ η, Bbase0 n (ξ - η) := by rw [MeasureTheory.integral_const_mul]
      _ = (Gint n) ^ k * Gint n := by rw [Bbase0_shift_integral_eq_Gint n hn ξ]
      _ = (Gint n) ^ (k + 1 + 1 - 1) := by rw [show k + 1 + 1 - 1 = k + 1 by omega, pow_succ]

/-! ## Geometric facts for the linear ratio `q' = αC · Gint < 1`. -/

theorem alphaGint_nonneg (n : ℕ) : 0 ≤ alphaC n * Gint n :=
  mul_nonneg (alphaC_nonneg n) (Gint_nonneg n)

theorem alphaGint_lt_one (n : ℕ) (hn : 1 ≤ n) : alphaC n * Gint n < 1 := by
  have := alphaG_le_half n hn; linarith

/-! ## Continuity and boundedness of the (non-compact) linear envelope `Glin`. -/

/-- Per-term geometric majorant `b ↦ αC^(b+1) · Gint^b = αC · (αC·Gint)^b`, summable. -/
theorem Glin_majorant_summable (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun b : ℕ => alphaC n ^ (b + 1) * (Gint n) ^ b) := by
  have hq_nn : 0 ≤ alphaC n * Gint n := alphaGint_nonneg n
  have hq_lt : alphaC n * Gint n < 1 := alphaGint_lt_one n hn
  have hgeo : Summable (fun b : ℕ => alphaC n * (alphaC n * Gint n) ^ b) :=
    (summable_geometric_of_lt_one hq_nn hq_lt).mul_left _
  apply hgeo.congr
  intro b
  rw [mul_pow, pow_succ]
  ring

/-- Per-term pointwise bound: `αC^(b+1) · linPow (Bbase0 n) (b+1) x ≤ αC^(b+1) · Gint^b`. -/
theorem Glin_term_le (n : ℕ) (hn : 1 ≤ n) (b : ℕ) (x : ℝ) :
    alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) x ≤ alphaC n ^ (b + 1) * (Gint n) ^ b := by
  have hb1 : (1 : ℕ) ≤ b + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hsup := linPow_Bbase0_sup_bound n hn (b + 1) hb1 x
  rw [show b + 1 - 1 = b by omega] at hsup
  exact mul_le_mul_of_nonneg_left hsup (pow_nonneg (alphaC_nonneg n) _)

/-- `Glin n` is continuous: uniform-limit of continuous terms with geometric domination. -/
theorem Glin_continuous (n : ℕ) (hn : 1 ≤ n) : Continuous (Glin n) := by
  have heq : Glin n = fun x => ∑' b : ℕ, alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) x := by
    funext x; rfl
  rw [heq]
  apply continuous_tsum
    (f := fun b x => alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) x)
    (u := fun b => alphaC n ^ (b + 1) * (Gint n) ^ b)
  · intro b
    exact continuous_const.mul
      (linPow_Bbase0_continuous n hn (b + 1) (Nat.succ_le_succ (Nat.zero_le _)))
  · exact Glin_majorant_summable n hn
  · intro b x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (alphaC_nonneg n) _)
        (linPow_Bbase0_nn n (b + 1) (Nat.succ_le_succ (Nat.zero_le _)) x))]
    exact Glin_term_le n hn b x

/-- `Glin n` is uniformly bounded: `Glin n x ≤ ∑'_b αC^(b+1) Gint^b` for all `x`. -/
theorem Glin_bdd (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, Glin n x ≤ M := by
  have hGint_nn : 0 ≤ Gint n := Gint_nonneg n
  refine ⟨∑' b : ℕ, alphaC n ^ (b + 1) * (Gint n) ^ b, ?_, ?_⟩
  · apply tsum_nonneg
    intro b
    exact mul_nonneg (pow_nonneg (alphaC_nonneg n) _) (pow_nonneg hGint_nn _)
  · intro x
    show (∑' b : ℕ, alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) x)
      ≤ ∑' b : ℕ, alphaC n ^ (b + 1) * (Gint n) ^ b
    have hLsumm : Summable (fun b : ℕ => alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) x) :=
      Summable.of_nonneg_of_le
        (fun b => mul_nonneg (pow_nonneg (alphaC_nonneg n) _)
          (linPow_Bbase0_nn n (b + 1) (Nat.succ_le_succ (Nat.zero_le _)) x))
        (fun b => Glin_term_le n hn b x)
        (Glin_majorant_summable n hn)
    exact Summable.tsum_le_tsum (fun b => Glin_term_le n hn b x) hLsumm
      (Glin_majorant_summable n hn)

/-! ## Whole-line L¹ mass of the linear power. -/

/-- `∫ linPow (Bbase0 n) m = Gint n ^ m` for `m ≥ 1` (MGF factorization at `t = 0`). -/
theorem linPow_Bbase0_L1_eq (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    (∫ η, linPow (Bbase0 n) m η) = (Gint n) ^ m := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  have hmgf := linPow_Bbase0_mgf n hn 0 m'
  simp only [zero_mul, Real.exp_zero, one_mul] at hmgf
  rw [hmgf]
  congr 1
  -- Gweight n 0 = Gint n
  unfold Gweight Gint
  apply intervalIntegral.integral_congr
  intro η _; simp

/-- Each `linPow (Bbase0 n) m` is integrable (compact-support continuous). -/
theorem linPow_Bbase0_integrable' (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    Integrable (linPow (Bbase0 n) m) :=
  linPow_Bbase0_int n hn m hm

/-! ## `linConv` distributes a `tsum` in the RIGHT argument. -/

/-- `linConv f (∑'_a u_a) ξ = ∑'_a linConv f (u_a) ξ`, via the unconditional
commutativity `linConv_comm`, when the left-distribution side conditions hold
after the swap. -/
theorem linConv_tsum_right (f : ℝ → ℝ) (u : ℕ → ℝ → ℝ) (ξ : ℝ)
    (hint : ∀ a, MeasureTheory.Integrable (fun η => u a η * f (ξ - η)))
    (hsumm : Summable (fun a => ∫ η, ‖u a η * f (ξ - η)‖)) :
    linConv f (fun η => ∑' a, u a η) ξ = ∑' a, linConv f (u a) ξ := by
  rw [linConv_comm]
  rw [linConv_tsum_left u f ξ hint hsumm]
  apply tsum_congr
  intro a
  rw [linConv_comm]

/-! ## Base case `k = 1`. -/

theorem expansion_base_lin (n : ℕ) (ξ : ℝ) :
    linPow (Glin n) 1 ξ
      = ∑' m : ℕ, ((multM 1 m : ℝ) * alphaC n ^ (1 + m)) * linPow (Bbase0 n) (1 + m) ξ := by
  rw [linPow_one]
  show Glin n ξ = _
  unfold Glin
  apply tsum_congr
  intro m
  rw [multM_one m]
  push_cast
  rw [show (1 : ℝ) * alphaC n ^ (1 + m) = alphaC n ^ (m + 1) by rw [Nat.add_comm]; ring]
  rw [show 1 + m = m + 1 by omega]

/-! ## Inductive-step integrability side conditions. -/

/-- Per-`B` integrability of the LEFT-distribution integrand
`η ↦ (multM k B · αC^{k+B} · linPow (Bbase0 n)(k+B) η) · Glin n (ξ - η)` on ℝ. -/
theorem stepL_int_lin (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (B : ℕ) :
    MeasureTheory.Integrable
      (fun η => ((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η)
        * Glin n (ξ - η)) := by
  obtain ⟨M, hM0, hMle⟩ := Glin_bdd n hn
  -- compact-support integrable first factor × bounded measurable second factor
  apply MeasureTheory.Integrable.mul_bdd (c := M)
  · apply Integrable.const_mul
    exact linPow_Bbase0_int n hn (k + B) (by omega)
  · exact ((Glin_continuous n hn).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Glin_nonneg n _)]
    exact hMle _

/-- Per-`a` integrability of the RIGHT-distribution integrand
`η ↦ (αC^{a+1} · linPow (Bbase0 n)(a+1) η) · linPow (Bbase0 n)(k+B) (ξ - η)` on ℝ. -/
theorem stepR_int_lin (n : ℕ) (hn : 1 ≤ n) (k B : ℕ) (hkB : 1 ≤ k + B) (ξ : ℝ) (a : ℕ) :
    MeasureTheory.Integrable
      (fun η => ((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η))
        * linPow (Bbase0 n) (k + B) (ξ - η)) := by
  -- both factors compact-support; first integrable, second bounded
  obtain ⟨M, hM⟩ := linPow_Bbase0_bdd n hn (k + B) hkB
  apply MeasureTheory.Integrable.mul_bdd (c := max M 0)
  · apply Integrable.const_mul
    exact linPow_Bbase0_int n hn (a + 1) (by omega)
  · exact ((linPow_Bbase0_continuous n hn (k + B) hkB).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun η => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (linPow_Bbase0_nn n (k + B) hkB _)]
    exact le_trans (hM _) (le_max_left _ _)

/-! ## Summability side conditions. -/

/-- Single-index summability of the linear expansion series at a fixed `ξ`. -/
theorem expansion_summable_lin (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun m : ℕ =>
      (multM k m : ℝ) * alphaC n ^ (k + m) * linPow (Bbase0 n) (k + m) ξ) := by
  set q : ℝ := alphaC n * Gint n with hq
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hgint : 0 ≤ Gint n := Gint_nonneg n
  have hqnn : 0 ≤ q := alphaGint_nonneg n
  have hqlt : q < 1 := alphaGint_lt_one n hn
  have hbase : Summable (fun m : ℕ => ((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m) :=
    summable_choose_mul_geometric_of_norm_lt_one (k - 1)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt)
  have hdom : Summable (fun m : ℕ =>
      alphaC n * q ^ (k - 1) * (((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m)) := hbase.mul_left _
  apply Summable.of_nonneg_of_le _ _ hdom
  · intro m
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hann _))
      (linPow_Bbase0_nn n (k + m) (by omega) ξ)
  · intro m
    have hmult : (multM k m : ℝ) = ((m + (k - 1)).choose (k - 1) : ℝ) := by
      rw [multM_choose k m hk]
    have hpb := linPow_Bbase0_sup_bound n hn (k + m) (by omega) ξ
    have key : (multM k m : ℝ) * alphaC n ^ (k + m) * linPow (Bbase0 n) (k + m) ξ
        ≤ (multM k m : ℝ) * alphaC n ^ (k + m) * (Gint n) ^ (k + m - 1) :=
      mul_le_mul_of_nonneg_left hpb (mul_nonneg (by positivity) (pow_nonneg hann _))
    refine le_trans key (le_of_eq ?_)
    rw [hmult, show k + m - 1 = (k - 1) + m by omega, hq]
    rw [mul_pow, mul_pow]
    rw [show alphaC n ^ (k + m) = alphaC n * (alphaC n ^ (k - 1) * alphaC n ^ m) by
      rw [← pow_add, ← pow_succ']; congr 1; omega]
    rw [pow_add]
    ring

/-- 2-D joint summability of the linear induction-step double family (the `hsumm`
side-condition of `step_collapse`). -/
theorem step_summable_lin (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ((multM k p.1 : ℝ) * alphaC n ^ (k + p.1))
        * (alphaC n ^ (p.2 + 1) * linPow (Bbase0 n) ((k + p.1) + (p.2 + 1)) ξ)) := by
  set q : ℝ := alphaC n * Gint n with hq
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hgint : 0 ≤ Gint n := Gint_nonneg n
  have hqnn : 0 ≤ q := alphaGint_nonneg n
  have hqlt : q < 1 := alphaGint_lt_one n hn
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt
  have hfB : Summable (fun B : ℕ => q ^ k * (((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B)) :=
    (summable_choose_mul_geometric_of_norm_lt_one (k - 1) hnorm).mul_left _
  have hga : Summable (fun a : ℕ => alphaC n * q ^ a) :=
    (summable_geometric_of_lt_one hqnn hqlt).mul_left _
  have hmaj : Summable (fun p : ℕ × ℕ =>
      (q ^ k * (((p.1 + (k - 1)).choose (k - 1) : ℝ) * q ^ p.1)) * (alphaC n * q ^ p.2)) :=
    hfB.mul_of_nonneg hga (fun B => by positivity) (fun a => by positivity)
  apply Summable.of_nonneg_of_le _ _ hmaj
  · intro p
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hann _))
      (mul_nonneg (pow_nonneg hann _)
        (linPow_Bbase0_nn n _ (by omega) ξ))
  · rintro ⟨B, a⟩
    simp only
    have hpb := linPow_Bbase0_sup_bound n hn ((k + B) + (a + 1)) (by omega) ξ
    have hmult : (multM k B : ℝ) = ((B + (k - 1)).choose (k - 1) : ℝ) := by
      rw [multM_choose k B hk]
    calc ((multM k B : ℝ) * alphaC n ^ (k + B))
            * (alphaC n ^ (a + 1) * linPow (Bbase0 n) ((k + B) + (a + 1)) ξ)
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B))
            * (alphaC n ^ (a + 1) * (Gint n) ^ ((k + B) + (a + 1) - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpb (pow_nonneg hann _))
            (mul_nonneg (by positivity) (pow_nonneg hann _))
      _ = (q ^ k * (((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B)) * (alphaC n * q ^ a) := by
          rw [hmult, hq, show (k + B) + (a + 1) - 1 = (k + B) + a by omega]
          rw [mul_pow, mul_pow, mul_pow]
          rw [show alphaC n ^ (k + B) = alphaC n ^ k * alphaC n ^ B by rw [← pow_add]]
          rw [show alphaC n ^ (a + 1) = alphaC n * alphaC n ^ a by rw [← pow_succ']]
          rw [show (Gint n) ^ ((k + B) + a)
              = (Gint n) ^ k * (Gint n) ^ B * (Gint n) ^ a by rw [← pow_add, ← pow_add]]
          ring

/-- LEFT-distribution summability: `B ↦ ∫ ‖u_B η · Glin(ξ-η)‖` is summable,
where `u_B η = multM k B · αC^{k+B} · linPow (Bbase0 n)(k+B) η`. -/
theorem stepL_summ_lin (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun B : ℕ => ∫ η,
      ‖((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η)
        * Glin n (ξ - η)‖) := by
  obtain ⟨M, hM0, hMle⟩ := Glin_bdd n hn
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hgint : 0 ≤ Gint n := Gint_nonneg n
  set q : ℝ := alphaC n * Gint n with hq
  have hqnn : 0 ≤ q := alphaGint_nonneg n
  have hqlt : q < 1 := alphaGint_lt_one n hn
  -- Dominating summable sequence in B.
  have hdom : Summable (fun B : ℕ =>
      M * ((multM k B : ℝ) * alphaC n ^ (k + B) * (Gint n) ^ (k + B))) := by
    have hbase : Summable (fun B : ℕ => ((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B) :=
      summable_choose_mul_geometric_of_norm_lt_one (k - 1)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt)
    have : Summable (fun B : ℕ =>
        (M * q ^ k) * (((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B)) := hbase.mul_left _
    apply this.congr
    intro B
    rw [multM_choose k B hk, hq]
    rw [mul_pow, mul_pow]
    rw [show alphaC n ^ (k + B) = alphaC n ^ k * alphaC n ^ B by rw [← pow_add]]
    rw [show (Gint n) ^ (k + B) = (Gint n) ^ k * (Gint n) ^ B by rw [← pow_add]]
    ring
  apply Summable.of_nonneg_of_le (fun B => by positivity) _ hdom
  intro B
  have hint_lhs : MeasureTheory.Integrable
      (fun η => ‖((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η)
        * Glin n (ξ - η)‖) :=
    (stepL_int_lin n hn k hk ξ B).norm
  have hcoef_nn : (0 : ℝ) ≤ (multM k B : ℝ) * alphaC n ^ (k + B) * M := by positivity
  have hpt : ∀ η,
      ‖((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η) * Glin n (ξ - η)‖
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * linPow (Bbase0 n) (k + B) η := by
    intro η
    have hpb : 0 ≤ linPow (Bbase0 n) (k + B) η :=
      linPow_Bbase0_nn n (k + B) (by omega) η
    have hgv0 : 0 ≤ Glin n (ξ - η) := Glin_nonneg n (ξ - η)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η) * Glin n (ξ - η)
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η) * M :=
      mul_le_mul_of_nonneg_left (hMle _) (by positivity)
    calc ((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η) * Glin n (ξ - η)
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η) * M := this
      _ = ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * linPow (Bbase0 n) (k + B) η := by ring
  have hintw : MeasureTheory.Integrable (linPow (Bbase0 n) (k + B)) :=
    linPow_Bbase0_int n hn (k + B) (by omega)
  calc (∫ η, ‖((multM k B : ℝ) * alphaC n ^ (k + B) * linPow (Bbase0 n) (k + B) η)
        * Glin n (ξ - η)‖)
      ≤ ∫ η, ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * linPow (Bbase0 n) (k + B) η := by
        apply MeasureTheory.integral_mono hint_lhs (hintw.const_mul _) hpt
    _ = ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * ∫ η, linPow (Bbase0 n) (k + B) η := by
        rw [MeasureTheory.integral_const_mul]
    _ = ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * (Gint n) ^ (k + B) := by
        rw [linPow_Bbase0_L1_eq n hn (k + B) (by omega)]
    _ = M * ((multM k B : ℝ) * alphaC n ^ (k + B) * (Gint n) ^ (k + B)) := by ring

/-- RIGHT-distribution summability (fixed `B`): `a ↦ ∫ ‖v_a η · linPow (Bbase0 n)(k+B)(ξ-η)‖`
is summable, where `v_a η = αC^{a+1} · linPow (Bbase0 n)(a+1) η`. -/
theorem stepR_summ_lin (n : ℕ) (hn : 1 ≤ n) (k B : ℕ) (hkB : 1 ≤ k + B) (ξ : ℝ) :
    Summable (fun a : ℕ => ∫ η,
      ‖((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η))
        * linPow (Bbase0 n) (k + B) (ξ - η)‖) := by
  obtain ⟨M, hM⟩ := linPow_Bbase0_bdd n hn (k + B) hkB
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hgint : 0 ≤ Gint n := Gint_nonneg n
  have hMnn : 0 ≤ max M 0 := le_max_right _ _
  set q : ℝ := alphaC n * Gint n with hq
  have hqnn : 0 ≤ q := alphaGint_nonneg n
  have hqlt : q < 1 := alphaGint_lt_one n hn
  -- dominating geometric sequence in a:  (max M 0) * q^(a+1)
  have hdom : Summable (fun a : ℕ => (max M 0) * q ^ (a + 1)) := by
    have hgeo : Summable (fun a : ℕ => q ^ (a + 1)) := by
      have := (summable_geometric_of_lt_one hqnn hqlt).mul_left q
      apply this.congr; intro a; rw [pow_succ]; ring
    exact hgeo.mul_left _
  apply Summable.of_nonneg_of_le (fun a => by positivity) _ hdom
  intro a
  have hint_lhs : MeasureTheory.Integrable
      (fun η => ‖((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η))
        * linPow (Bbase0 n) (k + B) (ξ - η)‖) :=
    (stepR_int_lin n hn k B hkB ξ a).norm
  have hpt : ∀ η,
      ‖((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η))
        * linPow (Bbase0 n) (k + B) (ξ - η)‖
        ≤ (max M 0) * (alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η) := by
    intro η
    have hpa : 0 ≤ linPow (Bbase0 n) (a + 1) η :=
      linPow_Bbase0_nn n (a + 1) (by omega) η
    have hpb : 0 ≤ linPow (Bbase0 n) (k + B) (ξ - η) :=
      linPow_Bbase0_nn n (k + B) hkB (ξ - η)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η))
            * linPow (Bbase0 n) (k + B) (ξ - η)
        ≤ ((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η)) * (max M 0) :=
          mul_le_mul_of_nonneg_left (le_trans (hM _) (le_max_left _ _)) (by positivity)
      _ = (max M 0) * (alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η) := by ring
  have hintw : MeasureTheory.Integrable (linPow (Bbase0 n) (a + 1)) :=
    linPow_Bbase0_int n hn (a + 1) (by omega)
  calc (∫ η, ‖((alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η))
          * linPow (Bbase0 n) (k + B) (ξ - η)‖)
      ≤ ∫ η, (max M 0) * (alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η) := by
        apply MeasureTheory.integral_mono hint_lhs ((hintw.const_mul _).const_mul _) hpt
    _ = (max M 0) * (alphaC n ^ (a + 1) * ∫ η, linPow (Bbase0 n) (a + 1) η) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = (max M 0) * (alphaC n ^ (a + 1) * (Gint n) ^ (a + 1)) := by
        rw [linPow_Bbase0_L1_eq n hn (a + 1) (by omega)]
    _ = (max M 0) * q ^ (a + 1) := by
        rw [hq, mul_pow]

/-! ## The linear multiplicity expansion (Step 1, linear half). -/

/-- **Linear multiplicity expansion.** For `k ≥ 1`,
`linPow (Glin n) k ξ = ∑'_m (multM k m) · αC^{k+m} · linPow (Bbase0 n)(k+m) ξ`. -/
theorem lin_expansion (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → ∀ ξ : ℝ,
      linPow (Glin n) k ξ
        = ∑' m : ℕ, ((multM k m : ℝ) * alphaC n ^ (k + m)) * linPow (Bbase0 n) (k + m) ξ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro ξ; exact expansion_base_lin n ξ
  | succ k hk ih =>
    intro ξ
    -- Unfold the (k+1)-st linear power.
    rw [linPow_succ_eq_linConv (Glin n) k hk]
    -- Rewrite the left argument as the IH series.
    have hleft : linPow (Glin n) k
        = fun η => ∑' B : ℕ,
            ((multM k B : ℝ) * alphaC n ^ (k + B)) * linPow (Bbase0 n) (k + B) η := by
      funext η; exact ih η
    rw [hleft]
    show linConv (fun η => ∑' B : ℕ,
        ((multM k B : ℝ) * alphaC n ^ (k + B)) * linPow (Bbase0 n) (k + B) η) (Glin n) ξ = _
    -- LEFT-distribution: pull the tsum (over B) out of linConv's left argument.
    rw [linConv_tsum_left
        (fun B η => ((multM k B : ℝ) * alphaC n ^ (k + B)) * linPow (Bbase0 n) (k + B) η)
        (Glin n) ξ (fun B => stepL_int_lin n hn k hk ξ B) (stepL_summ_lin n hn k hk ξ)]
    -- Per-B: pull the scalar out, then distribute the RIGHT argument (Glin = ∑'_a v_a).
    have hperB : ∀ B : ℕ,
        linConv (fun η => ((multM k B : ℝ) * alphaC n ^ (k + B)) * linPow (Bbase0 n) (k + B) η)
            (Glin n) ξ
          = ∑' a : ℕ, ((multM k B : ℝ) * alphaC n ^ (k + B))
              * (alphaC n ^ (a + 1) * linPow (Bbase0 n) ((k + B) + (a + 1)) ξ) := by
      intro B
      rw [linConv_const_mul_left]
      have hGlin : Glin n = fun η => ∑' a : ℕ, alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η := by
        funext η; rfl
      rw [hGlin]
      have hkB1 : 1 ≤ k + B := by omega
      rw [linConv_tsum_right (linPow (Bbase0 n) (k + B))
          (fun a η => alphaC n ^ (a + 1) * linPow (Bbase0 n) (a + 1) η) ξ
          (fun a => stepR_int_lin n hn k B hkB1 ξ a)
          (stepR_summ_lin n hn k B hkB1 ξ)]
      rw [tsum_mul_left]
      apply congrArg
      apply tsum_congr; intro a
      -- pull αC^{a+1} out (it is in the RIGHT argument) via commutativity.
      rw [linConv_comm]
      rw [linConv_const_mul_left]
      -- now linConv (linPow(Bbase0)(a+1)) (linPow(Bbase0)(k+B)) ξ
      rw [linPow_add (good_Bbase0 n hn) (a + 1) (k + B) (by omega) hkB1]
      rw [show (a + 1) + (k + B) = (k + B) + (a + 1) by omega]
    rw [tsum_congr hperB]
    rw [step_collapse (alphaC n) (fun m => linPow (Bbase0 n) m ξ) k hk (step_summable_lin n hn k hk ξ)]

/-! ## Reconciliation: circular k-power ≤ periodised linear k-power. -/

/-- Inner-`s` summability of the periodised linear power at a fixed argument. -/
theorem periodised_linPow_summable (n : ℕ) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    Summable (fun s : ℤ => linPow (Bbase0 n) m (ξ + 2 * Real.pi * (s : ℝ))) := by
  apply periodised_summable_of_compact_support (linPow (Bbase0 n) m) ((m : ℝ) * Real.pi)
  intro y hy
  exact linPow_Bbase0_supp n m hm y hy

end LinMultiplicityExpansion
