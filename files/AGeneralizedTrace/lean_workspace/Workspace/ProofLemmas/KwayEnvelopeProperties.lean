import Mathlib
import Workspace.ProofLemmas.PeriodicBaseKfoldPeriodisation
import Workspace.ProofLemmas.GlinWeightedMGF
import Workspace.ProofLemmas.GenvConvergence
import Workspace.ProofLemmas.LinMultiplicityExpansion
import Workspace.ProofLemmas.CircMultiplicityExpansion
import Workspace.PriorWork.PrekopaLogConcave

/-!
# Properties of the k-fold linear self-convolution `linPow (Glin n) k`

This file establishes the analytic properties of the *sound* periodisation envelope
`linPow (Glin n) k` (the k-fold linear self-convolution of the linear binomial-Fourier
envelope `Glin n`) that are needed to apply
`HFourierKwayBoundFromMGFAndLogConcavity` to `h := linPow (Glin n) k`.

The key tool is `LinMultiplicityExpansion.lin_expansion`:
  `linPow (Glin n) k ξ = ∑'_m (multM k m · αC^{k+m}) · linPow (Bbase0 n) (k+m) ξ`,
which reduces every property of `linPow (Glin n) k` to the corresponding property of
the *compactly supported* iterated convolutions `linPow (Bbase0 n) m` (which have a
factorizing MGF and finite support, unlike `Glin n` itself).
-/

open MeasureTheory
open scoped Real

namespace Workspace.ProofLemmas.KwayEnvelopeProperties

open PeriodicBaseKfoldPeriodisation GlinWeightedMGF GenvConvergence
open LinMultiplicityExpansion PerFactorFourierModulus T4ToCircPowRPeriodic
open CircMultiplicityExpansion

/-! ## Evenness of the base `Bbase0 n`. -/

/-- `Bbase0 n` is even. On `|x| ≤ π` it equals `cos(x/2)^n` (an even function of `x`);
off the symmetric interval it is `0`. -/
theorem Bbase0_even (n : ℕ) (hn : 1 ≤ n) : ∀ x : ℝ, Bbase0 n (-x) = Bbase0 n x := by
  intro x
  unfold Bbase0
  rw [abs_neg]
  by_cases hx : |x| ≤ Real.pi
  · rw [if_pos hx, if_pos hx]
    rw [Bbase_eq_cos_pow n hn (-x) (by rwa [abs_neg]), Bbase_eq_cos_pow n hn x hx]
    rw [show (-x) / 2 = -(x / 2) by ring, Real.cos_neg]
  · rw [if_neg hx, if_neg hx]

/-! ## Evenness of `linPow g0 m` for an even base `g0`. -/

/-- The k-fold linear self-convolution of an *even* function is even.
Proved by induction using the convolution recurrence and the change of variables
`y ↦ -y` (`integral_neg_eq_self`). -/
theorem linPow_even (g0 : ℝ → ℝ) (hg0_even : ∀ x, g0 (-x) = g0 x) :
    ∀ m : ℕ, ∀ x : ℝ, linPow g0 m (-x) = linPow g0 m x := by
  intro m
  induction m with
  | zero => intro x; simp [linPow]
  | succ j ih =>
    match j with
    | 0 => intro x; simpa [linPow] using hg0_even x
    | (i + 1) =>
      intro x
      simp only [linPow_succ_succ]
      -- linPow g0 (i+2) (-x) = ∫ y, linPow g0 (i+1) y * g0 (-x - y)
      -- change of variables y ↦ -y, then use ih and hg0_even.
      have key : (∫ y, linPow g0 (i + 1) y * g0 (-x - y)) =
                 (∫ y, linPow g0 (i + 1) (-y) * g0 (-x - (-y))) := by
        rw [← MeasureTheory.integral_neg_eq_self
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (fun y => linPow g0 (i + 1) y * g0 (-x - y))]
      rw [key]
      apply congr_arg (MeasureTheory.integral _)
      funext y
      rw [ih y]
      congr 1
      have harg : -x - (-y) = -(x - y) := by ring
      rw [harg, hg0_even]

/-! ## Non-negativity, evenness, integrability of `linPow (Glin n) k`. -/

/-- `linPow (Glin n) k` is non-negative. -/
theorem linPow_Glin_nn (n : ℕ) (k : ℕ) : ∀ x : ℝ, 0 ≤ linPow (Glin n) k x :=
  fun x => linPow_nn (Glin n) (Glin_nonneg n) k x

/-- `Glin n` is even (each summand `linPow (Bbase0 n) (b+1)` is even since `Bbase0 n`
is even). -/
theorem Glin_even (n : ℕ) (hn : 1 ≤ n) : ∀ x : ℝ, Glin n (-x) = Glin n x := by
  intro x
  unfold Glin
  apply tsum_congr
  intro b
  congr 1
  exact linPow_even (Bbase0 n) (Bbase0_even n hn) (b + 1) x

/-- `linPow (Glin n) k` is even. -/
theorem linPow_Glin_even (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    ∀ x : ℝ, linPow (Glin n) k (-x) = linPow (Glin n) k x :=
  linPow_even (Glin n) (Glin_even n hn) k

/-! ## Log-concavity package for `Glin n` (from `BinomialPmfFourierLogConcave`).

Apply the paper's own log-concavity step to the *compactly supported* base
`Bbase0 n` (supported on `[-π,π]`, even, integrable) with `α := alphaC n` and the
iterated convolution `Hconv := linPow (Bbase0 n)`.  Since
`Glin n η = ∑'_b alphaC^{b+1} · linPow (Bbase0 n) (b+1) η`, this yields
non-negativity, integrability, log-concavity, evenness, and antitonicity-on-[0,∞)
of `Glin n` itself. -/

theorem alphaC_pos (n : ℕ) (hn : 1 ≤ n) : 0 < alphaC n := by
  unfold alphaC
  apply mul_pos
  · apply div_pos one_pos
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (Real.exp_pos _))
      (Real.sqrt_pos.mpr (by positivity))
  · exact Real.sqrt_pos.mpr (by exact_mod_cast hn)

/-- `Glin n` is integrable.

Sound proof (no log-concavity axiom): `Glin n η = ∑'_b αC^{b+1}·linPow(Bbase0 n)(b+1) η`
is a non-negative, summable-in-L¹ series of compactly-supported integrable terms.
Each term `F b := fun η => αC^{b+1}·linPow(Bbase0 n)(b+1) η` is integrable with
`∫‖F b‖ = αC^{b+1}·Gint^{b+1} = (αC·Gint)^{b+1}`, a geometric series with ratio
`q := αC·Gint ∈ [0,1)`. Finiteness of `∫⁻ ofReal (Glin n)` follows from
`lintegral_tsum` + `ENNReal.ofReal_tsum_of_nonneg`, hence integrability via
`lintegral_ofReal_ne_top_iff_integrable`. -/
theorem Glin_integrable (n : ℕ) (hn : 1 ≤ n) : MeasureTheory.Integrable (Glin n) := by
  -- Per-term: F b η = αC^{b+1} · linPow (Bbase0 n) (b+1) η.
  set F : ℕ → ℝ → ℝ :=
    fun b η => alphaC n ^ (b + 1) * linPow (Bbase0 n) (b + 1) η with hF
  set q : ℝ := alphaC n * Gint n with hq
  have hq_nn : 0 ≤ q := alphaGint_nonneg n
  have hq_lt : q < 1 := alphaGint_lt_one n hn
  have hF_nn : ∀ b η, 0 ≤ F b η := by
    intro b η
    exact mul_nonneg (pow_nonneg (alphaC_nonneg n) _)
      (linPow_Bbase0_nn n (b + 1) (by omega) η)
  have hF_int : ∀ b, MeasureTheory.Integrable (F b) := by
    intro b
    exact (linPow_Bbase0_integrable' n hn (b + 1) (by omega)).const_mul _
  -- ∫ F b = αC^{b+1} · Gint^{b+1} = q^{b+1}.
  have hF_integral : ∀ b, (∫ η, F b η) = q ^ (b + 1) := by
    intro b
    rw [hF, MeasureTheory.integral_const_mul, linPow_Bbase0_L1_eq n hn (b + 1) (by omega)]
    rw [hq, mul_pow]
  -- Pointwise: Glin n η = ∑' b, F b η.
  have hpt : ∀ η, Glin n η = ∑' b, F b η := fun η => rfl
  -- Pointwise summability of fun b => F b η (dominated by the geometric majorant).
  have h_sm_pt : ∀ η, Summable (fun b => F b η) := by
    intro η
    exact Summable.of_nonneg_of_le (fun b => hF_nn b η)
      (fun b => Glin_term_le n hn b η)
      (Glin_majorant_summable n hn)
  -- AEStronglyMeasurable of Glin n.
  have h_meas : MeasureTheory.AEStronglyMeasurable (Glin n) MeasureTheory.volume :=
    (Glin_continuous n hn).aestronglyMeasurable
  have h_nn : ∀ η, 0 ≤ Glin n η := Glin_nonneg n
  -- Geometric summability of the integral norms.
  have hgeo : Summable (fun b : ℕ => q ^ (b + 1)) := by
    have := (summable_geometric_of_lt_one hq_nn hq_lt).mul_left q
    apply this.congr; intro b; rw [pow_succ]; ring
  -- Finite lintegral of ofReal (Glin n): equals ofReal (∑' b, q^{b+1}) < ⊤.
  have h_lint : (∫⁻ η, ENNReal.ofReal (Glin n η))
      = ENNReal.ofReal (∑' b, q ^ (b + 1)) := by
    have hpt_enn : ∀ η, ENNReal.ofReal (Glin n η) = ∑' b, ENNReal.ofReal (F b η) := by
      intro η
      rw [hpt η, ENNReal.ofReal_tsum_of_nonneg (fun b => hF_nn b η) (h_sm_pt η)]
    simp_rw [hpt_enn]
    rw [MeasureTheory.lintegral_tsum
      (fun b => ((hF_int b).aestronglyMeasurable.aemeasurable.ennreal_ofReal))]
    have hterm : ∀ b, ∫⁻ η, ENNReal.ofReal (F b η)
        = ENNReal.ofReal (q ^ (b + 1)) := by
      intro b
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF_int b)
        (Filter.Eventually.of_forall (fun η => hF_nn b η))]
      rw [hF_integral b]
    rw [show (fun b => ∫⁻ η, ENNReal.ofReal (F b η))
          = (fun b => ENNReal.ofReal (q ^ (b + 1))) from by funext b; rw [hterm b]]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun b => pow_nonneg hq_nn _) hgeo]
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable h_meas
    (Filter.Eventually.of_forall h_nn)).mp
    (by rw [h_lint]; exact ENNReal.ofReal_ne_top)

/-! ## Integrability of `linPow (Glin n) k` (k-fold convolution of integrable `Glin`). -/

/-- `linPow (Glin n) k` is integrable for `k ≥ 1`: a `k`-fold linear self-convolution
of the integrable function `Glin n`. -/
theorem linPow_Glin_int (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → MeasureTheory.Integrable (linPow (Glin n) k) := by
  have hG_int := Glin_integrable n hn
  intro k hk
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  clear hk
  induction k' with
  | zero =>
    show MeasureTheory.Integrable (linPow (Glin n) 1)
    rw [linPow_one]; exact hG_int
  | succ k ih =>
    have heq : linPow (Glin n) (k + 1 + 1) =
        MeasureTheory.convolution (linPow (Glin n) (k + 1)) (Glin n)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      funext η
      rw [show k + 1 + 1 = k + 2 from rfl, linPow_succ_succ]
      rw [MeasureTheory.convolution_lsmul]
      simp [smul_eq_mul]
    rw [heq]
    exact MeasureTheory.Integrable.integrable_convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) ih hG_int

/-! ## MGF bound: `∫ e^{√n ξ} · linPow (Glin n) k ξ ≤ 1`. -/

/-- The scalar multiplicity-weighted geometric sum bound:
`∑'_m multM k m · q^{k+m} = (q/(1-q))^k ≤ 1` whenever `0 ≤ q ≤ 1/2`. -/
theorem mgf_scalar_sum_le_one (k : ℕ) (hk : 1 ≤ k) (q : ℝ)
    (hq_nn : 0 ≤ q) (hq_half : q ≤ 1 / 2) :
    (∑' m : ℕ, (multM k m : ℝ) * q ^ (k + m)) ≤ 1 := by
  have hq_lt : q < 1 := by linarith
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq_nn]; exact hq_lt
  -- Pull q^k out and apply tsum_choose.
  have hrw : (∑' m : ℕ, (multM k m : ℝ) * q ^ (k + m))
      = q ^ k * (∑' m : ℕ, ((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro m
    rw [multM_choose k m hk, pow_add]; ring
  rw [hrw, tsum_choose_mul_geometric_of_norm_lt_one (k - 1) hqnorm]
  -- q^k * (1/(1-q)^((k-1)+1)) = (q/(1-q))^k ≤ 1.
  have hk1 : (k - 1) + 1 = k := by omega
  rw [hk1]
  have h1mq_pos : 0 < 1 - q := by linarith
  rw [show q ^ k * (1 / (1 - q) ^ k) = (q / (1 - q)) ^ k by
    rw [div_pow]; ring]
  apply pow_le_one₀ (by positivity)
  rw [div_le_one h1mq_pos]; linarith

/-- The per-`m` weighted summand of the MGF of `linPow (Glin n) k`. -/
private noncomputable def G2term (n k : ℕ) (m : ℕ) : ℝ → ℝ :=
  fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) *
    (((multM k m : ℝ) * alphaC n ^ (k + m)) * linPow (Bbase0 n) (k + m) ξ)

theorem G2term_nonneg (n k : ℕ) (hk : 1 ≤ k) (m : ℕ) (ξ : ℝ) : 0 ≤ G2term n k m ξ := by
  unfold G2term
  apply mul_nonneg (Real.exp_pos _).le
  apply mul_nonneg
  · exact mul_nonneg (by positivity) (pow_nonneg (alphaC_nonneg n) _)
  · exact linPow_Bbase0_nn n (k + m) (by omega) ξ

theorem G2term_integrable (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    MeasureTheory.Integrable (G2term n k m) := by
  unfold G2term
  have hb : k + m = (k + m - 1) + 1 := by omega
  rw [show (fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) *
        (((multM k m : ℝ) * alphaC n ^ (k + m)) * linPow (Bbase0 n) (k + m) ξ))
      = (fun ξ => ((multM k m : ℝ) * alphaC n ^ (k + m)) *
          (Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Bbase0 n) (k + m) ξ)) from by
        funext ξ; ring]
  apply MeasureTheory.Integrable.const_mul
  rw [hb]
  exact weighted_linPow_integrable n hn (k + m - 1)

theorem G2term_integral (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    (∫ ξ, G2term n k m ξ)
      = ((multM k m : ℝ) * alphaC n ^ (k + m)) * Gweight n (Real.sqrt (n : ℝ)) ^ (k + m) := by
  unfold G2term
  rw [show (fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) *
        (((multM k m : ℝ) * alphaC n ^ (k + m)) * linPow (Bbase0 n) (k + m) ξ))
      = (fun ξ => ((multM k m : ℝ) * alphaC n ^ (k + m)) *
          (Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Bbase0 n) (k + m) ξ)) from by
        funext ξ; ring]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hb : k + m = (k + m - 1) + 1 := by omega
  rw [hb, linPow_Bbase0_mgf n hn (Real.sqrt (n : ℝ)) (k + m - 1)]

/-- **MGF gate for the k-fold linear power.**
`∫ e^{√n ξ} · linPow (Glin n) k ξ ≤ 1` for `k ≥ 1`. -/
theorem linPow_Glin_mgf_le_one (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (∫ ξ, Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Glin n) k ξ) ≤ 1 := by
  set q : ℝ := alphaC n * Gweight n (Real.sqrt (n : ℝ)) with hq
  have hq_nn : 0 ≤ q := mul_nonneg (alphaC_nonneg n) (Gweight_nonneg n _)
  have hq_half : q ≤ 1 / 2 := alphaGweight_le_half n hn
  have hq_lt : q < 1 := by linarith
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq_nn]; exact hq_lt
  -- ∫ G2term = multM · q^{k+m}.
  have hint_eq : ∀ m, (∫ ξ, G2term n k m ξ) = (multM k m : ℝ) * q ^ (k + m) := by
    intro m
    rw [G2term_integral n hn k hk m, hq, mul_pow]
    ring
  -- Each G2term integrable.
  have hint : ∀ m, MeasureTheory.Integrable (G2term n k m) := fun m => G2term_integrable n hn k hk m
  -- ∫‖G2term‖ = multM·q^{k+m}, summable.
  have hnorm_eq : ∀ m, (∫ ξ, ‖G2term n k m ξ‖) = (multM k m : ℝ) * q ^ (k + m) := by
    intro m
    have : (∫ ξ, ‖G2term n k m ξ‖) = ∫ ξ, G2term n k m ξ := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ; simp only []; rw [Real.norm_of_nonneg (G2term_nonneg n k hk m ξ)]
    rw [this, hint_eq m]
  have hsumm : Summable (fun m => ∫ ξ, ‖G2term n k m ξ‖) := by
    apply Summable.congr (f := fun m => (multM k m : ℝ) * q ^ (k + m))
    · -- summable via choose-geometric
      have hbase : Summable (fun m : ℕ => ((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m) :=
        summable_choose_mul_geometric_of_norm_lt_one (k - 1) hqnorm
      have : (fun m : ℕ => (multM k m : ℝ) * q ^ (k + m))
          = (fun m : ℕ => q ^ k * (((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m)) := by
        funext m; rw [multM_choose k m hk, pow_add]; ring
      rw [this]; exact hbase.mul_left _
    · intro m; rw [hnorm_eq m]
  -- Swap ∫ and ∑'.
  have hswap : (∑' m, ∫ ξ, G2term n k m ξ) = ∫ ξ, ∑' m, G2term n k m ξ :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm
  -- The pointwise sum equals e^{√n ξ} · linPow (Glin n) k ξ.
  have hpt : ∀ ξ, (∑' m, G2term n k m ξ)
      = Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Glin n) k ξ := by
    intro ξ
    unfold G2term
    rw [lin_expansion n hn k hk ξ, ← tsum_mul_left]
  rw [show (fun ξ => Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Glin n) k ξ)
        = (fun ξ => ∑' m, G2term n k m ξ) from by funext ξ; rw [hpt ξ]]
  rw [← hswap]
  -- ∑'_m ∫ G2term = ∑'_m multM·q^{k+m} ≤ 1.
  have hval : (∑' m, ∫ ξ, G2term n k m ξ) = ∑' m, (multM k m : ℝ) * q ^ (k + m) := by
    apply tsum_congr; intro m; rw [hint_eq m]
  rw [hval]
  exact mgf_scalar_sum_le_one k hk q hq_nn hq_half

/-- The exponentially weighted `k`-fold power `e^{√n η} · linPow (Glin n) k η` is
integrable on the whole line (the per-`m` terms `G2term` are integrable and
`∑'_m ∫‖G2term‖` converges). -/
theorem linPow_Glin_weighted_int (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    MeasureTheory.Integrable
      (fun η : ℝ => Real.exp (Real.sqrt (n : ℝ) * η) * linPow (Glin n) k η) := by
  set q : ℝ := alphaC n * Gweight n (Real.sqrt (n : ℝ)) with hq
  have hq_nn : 0 ≤ q := mul_nonneg (alphaC_nonneg n) (Gweight_nonneg n _)
  have hq_half : q ≤ 1 / 2 := alphaGweight_le_half n hn
  have hq_lt : q < 1 := by linarith
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq_nn]; exact hq_lt
  have hint : ∀ m, MeasureTheory.Integrable (G2term n k m) := fun m => G2term_integrable n hn k hk m
  have hnorm_eq : ∀ m, (∫ ξ, ‖G2term n k m ξ‖) = (multM k m : ℝ) * q ^ (k + m) := by
    intro m
    have : (∫ ξ, ‖G2term n k m ξ‖) = ∫ ξ, G2term n k m ξ := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ; simp only []; rw [Real.norm_of_nonneg (G2term_nonneg n k hk m ξ)]
    rw [this, G2term_integral n hn k hk m, hq, mul_pow]; ring
  have hsumm : Summable (fun m => ∫ ξ, ‖G2term n k m ξ‖) := by
    apply Summable.congr (f := fun m => (multM k m : ℝ) * q ^ (k + m))
    · have hbase : Summable (fun m : ℕ => ((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m) :=
        summable_choose_mul_geometric_of_norm_lt_one (k - 1) hqnorm
      have : (fun m : ℕ => (multM k m : ℝ) * q ^ (k + m))
          = (fun m : ℕ => q ^ k * (((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m)) := by
        funext m; rw [multM_choose k m hk, pow_add]; ring
      rw [this]; exact hbase.mul_left _
    · intro m; rw [hnorm_eq m]
  have hpt : ∀ ξ, (∑' m, G2term n k m ξ)
      = Real.exp (Real.sqrt (n : ℝ) * ξ) * linPow (Glin n) k ξ := by
    intro ξ
    unfold G2term
    rw [lin_expansion n hn k hk ξ, ← tsum_mul_left]
  -- AEStronglyMeasurable of the weighted function.
  have h_meas : MeasureTheory.AEStronglyMeasurable
      (fun η => Real.exp (Real.sqrt (n : ℝ) * η) * linPow (Glin n) k η)
      MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.mul
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · exact (linPow_Glin_int n hn k hk).aestronglyMeasurable
  have h_nn : ∀ η, 0 ≤ Real.exp (Real.sqrt (n : ℝ) * η) * linPow (Glin n) k η := fun η =>
    mul_nonneg (Real.exp_pos _).le (linPow_Glin_nn n k η)
  -- Finite lintegral via the per-m decomposition.
  have h_lint : ∫⁻ η, ENNReal.ofReal
      (Real.exp (Real.sqrt (n : ℝ) * η) * linPow (Glin n) k η) ≤ 1 := by
    have h_sm_pt : ∀ η, Summable (fun m => G2term n k m η) := by
      intro η
      exact Summable.of_nonneg_of_le (fun m => G2term_nonneg n k hk m η)
        (fun m => by show G2term n k m η ≤ _; unfold G2term; rw [mul_assoc])
        ((expansion_summable_lin n hn k hk η).mul_left
          (Real.exp (Real.sqrt (n : ℝ) * η)))
    have hpt_enn : ∀ η, ENNReal.ofReal
        (Real.exp (Real.sqrt (n : ℝ) * η) * linPow (Glin n) k η)
        = ∑' m, ENNReal.ofReal (G2term n k m η) := by
      intro η
      rw [← hpt η, ENNReal.ofReal_tsum_of_nonneg (fun m => G2term_nonneg n k hk m η)
        (h_sm_pt η)]
    simp_rw [hpt_enn]
    rw [MeasureTheory.lintegral_tsum (fun m => ((hint m).aestronglyMeasurable.aemeasurable.ennreal_ofReal))]
    have hterm : ∀ m, ∫⁻ η, ENNReal.ofReal (G2term n k m η)
        = ENNReal.ofReal ((multM k m : ℝ) * q ^ (k + m)) := by
      intro m
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint m)
        (Filter.Eventually.of_forall (fun η => G2term_nonneg n k hk m η))]
      rw [G2term_integral n hn k hk m, hq, mul_pow, mul_assoc]
    rw [show (fun m => ∫⁻ η, ENNReal.ofReal (G2term n k m η))
          = (fun m => ENNReal.ofReal ((multM k m : ℝ) * q ^ (k + m))) from by
        funext m; rw [hterm m]]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · apply ENNReal.ofReal_le_one.mpr
      exact mgf_scalar_sum_le_one k hk q hq_nn hq_half
    · intro m; exact mul_nonneg (by positivity) (pow_nonneg hq_nn _)
    · have hbase : Summable (fun m : ℕ => ((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m) :=
        summable_choose_mul_geometric_of_norm_lt_one (k - 1) hqnorm
      have : (fun m : ℕ => (multM k m : ℝ) * q ^ (k + m))
          = (fun m : ℕ => q ^ k * (((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m)) := by
        funext m; rw [multM_choose k m hk, pow_add]; ring
      rw [this]; exact hbase.mul_left _
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable h_meas
    (Filter.Eventually.of_forall h_nn)).mp (ne_top_of_le_ne_top ENNReal.one_ne_top h_lint)

/-! ## Analysis lemma: even + log-concave + nonneg ⇒ antitone on `[0, ∞)`. -/

/-- **Even + log-concave ⇒ antitone on `[0,∞)`.**

If `f : ℝ → ℝ` is non-negative, even, and log-concave (in the multiplicative form),
then `f` is non-increasing on `[0, ∞)`: for `0 ≤ x ≤ y`, `f y ≤ f x`.

Proof: write `x` as the convex combination `x = t·(-y) + (1-t)·y` with
`t = (y - x)/(2y) ∈ [0,1]` (when `y > 0`). Log-concavity gives
`f(-y)^t · f(y)^(1-t) ≤ f(x)`; evenness collapses `f(-y) = f(y)` and the exponents
sum to `1`, so the left side is `f(y)`, yielding `f y ≤ f x`. The cases `y = 0`
(then `x = 0`) and `f y = 0` (then `f y ≤ f x` since `f x ≥ 0`) are immediate. -/
theorem even_logConcave_antitone (f : ℝ → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_even : ∀ x, f (-x) = f x)
    (hf_logc : ∀ x y t, 0 ≤ t → t ≤ 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t * x + (1 - t) * y)) :
    ∀ x y, 0 ≤ x → x ≤ y → f y ≤ f x := by
  intro x y hx hxy
  -- Case y = 0: then x = 0 too.
  rcases eq_or_lt_of_le (le_trans hx hxy) with hy0 | hy_pos
  · -- y = 0, x = 0 (since 0 ≤ x ≤ y = 0)
    have hx0 : x = 0 := le_antisymm (hy0 ▸ hxy) hx
    rw [hx0, ← hy0]
  · -- y > 0.
    rcases eq_or_lt_of_le (hf_nn y) with hfy0 | hfy_pos
    · -- f y = 0 ≤ f x.
      rw [← hfy0]; exact hf_nn x
    · -- f y > 0.
      set t : ℝ := (y - x) / (2 * y) with ht_def
      have ht0 : 0 ≤ t := by
        rw [ht_def]; apply div_nonneg (by linarith) (by linarith)
      have ht1 : t ≤ 1 := by
        rw [ht_def, div_le_one (by linarith)]; linarith
      -- The convex combination t·(-y) + (1-t)·y = y - 2ty = x.
      have hcombo : t * (-y) + (1 - t) * y = x := by
        rw [ht_def]; field_simp; ring
      have hkey := hf_logc (-y) y t ht0 ht1
      rw [hcombo, hf_even y] at hkey
      -- f y ^ t * f y ^ (1 - t) = f y.
      have hpow : f y ^ t * f y ^ (1 - t) = f y := by
        rw [← Real.rpow_add hfy_pos]
        rw [show t + (1 - t) = 1 by ring, Real.rpow_one]
      rw [hpow] at hkey
      exact hkey

end Workspace.ProofLemmas.KwayEnvelopeProperties
