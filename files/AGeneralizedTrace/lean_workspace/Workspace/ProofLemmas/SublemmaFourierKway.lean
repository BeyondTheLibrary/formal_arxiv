import Workspace.ProofLemmas.HFourierKwayBoundFromMGFAndLogConcavity
import Workspace.ProofLemmas.MGFOfHbBoundGaussian
import Workspace.ProofLemmas.MGFCalibrationAtSqrtN
import Workspace.ProofLemmas.MarkovTailFromMGF
import Workspace.ProofLemmas.MGFTailPointwise
import Workspace.ProofLemmas.NonincreasingTailSummation
import Workspace.ProofLemmas.SharpeningInequalityCheck
import Workspace.ProofLemmas.GaussianCosBound
import Workspace.ProofLemmas.GaussianIntegralValue
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.MGFOfIteratedConvolution
import Workspace.PriorWork.BinomialFourierClosedForm
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle
import Workspace.PriorWork.MGFOfConvolution
import Workspace.PriorWork.ConvolutionTheoremDiscrete
import Workspace.PriorWork.PrekopaLogConcave
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.KwayEnvelopeProperties
import Workspace.ProofLemmas.MultiplicityExpansion
import Workspace.ProofLemmas.KwayReconciliation
import Workspace.ProofLemmas.KwayFactorSummable
import Mathlib

open scoped Real Complex

set_option maxHeartbeats 4000000

/--
**Lemma 7 (k-way Fourier-tail bound).**

Fix the constant `c' := 1 / (4 * e^2 * √(2π))` and `α := c' * √n`.
Let `n` be a positive natural number with `n ≡ 1 (mod 8)`, and set
`n_q := (n-1)/4`. For every `k ≥ 0`, every strictly increasing same-parity
tuple `ℓ_1 < … < ℓ_k` of indices in `{1, …, (n-1)/2}`, and every
`ξ ∈ [-π, π]` with `|ξ| ≥ 2`, the function
`T₄(r) := ∏_{j=1..k}  α · bin(n,1/2, r + n_q + ℓ_j)
                     / (1 - α · bin(n,1/2, r + n_q + ℓ_j))`
(extended by zero off support) has discrete circular Fourier transform
satisfying `|T̂₄(ξ)| ≤ 2 · exp(-√n)`.

The function `T4 : ℤ → ℝ` is exposed as a free parameter constrained to the
product expression above (with the support condition `r + n_q + ℓ_j ∈ [0, n]`
on each factor); the conclusion bounds the modulus of its Fourier sum at `ξ`.
-/
theorem SublemmaFourierKway :
    ∀ (n : ℕ), 1 ≤ n → n % 8 = 1 →
      ∀ (k : ℕ) (ℓ : Fin k → ℕ),
        (∀ i j : Fin k, i.val < j.val → ℓ i < ℓ j) →
        (∀ i j : Fin k, ℓ i % 2 = ℓ j % 2) →
        (∀ i : Fin k, 1 ≤ ℓ i ∧ ℓ i ≤ (n - 1) / 2) →
        ∀ (T4 : ℤ → ℝ),
          (∀ r : ℤ,
              T4 r =
                ∏ j : Fin k,
                  (let m : ℤ := r + ((n - 1) / 4 : ℤ) + (ℓ j : ℤ)
                   if 0 ≤ m ∧ m ≤ (n : ℤ) then
                     let i : ℕ := m.toNat
                     let α : ℝ :=
                       (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                         Real.sqrt (n : ℝ)
                     let p : ℝ :=
                       α * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
                     p / (1 - p)
                   else 0)) →
          ∀ ξ : ℝ, |ξ| ≤ Real.pi → (2 : ℝ) ≤ |ξ| →
            ‖∑' r : ℤ,
                (T4 r : ℂ) *
                  Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
              ≤ 2 * Real.exp (- Real.sqrt (n : ℝ)) := by
  intro n hn hn8 k ℓ hℓ_strict hℓ_parity hℓ_range T4 hT4_def ξ hξπ hξ_ge2
  -- ============================================================================
  -- The SOUND periodisation envelope is the k-fold linear self-convolution
  -- `h := linPow (Glin n) k` of the linear binomial-Fourier envelope `Glin n`.
  -- (For `k ≥ 2` the single envelope `Glin n` is NOT a valid upper bound: the
  -- circular multiplicity expansion is strictly larger; the multiplicities are
  -- carried faithfully by the k-fold power, see KwayReconciliation / F70.)
  -- ============================================================================
  -- k = 0: the empty product gives T4 ≡ 1; its Fourier series is non-summable,
  -- so the LHS tsum is 0 ≤ 2 e^{-√n}.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hT4_one : T4 = fun _ : ℤ => (1 : ℝ) := by
      funext r; rw [hT4_def r, Fin.prod_univ_zero]
    rw [hT4_one]
    have h_not_summ : ¬ Summable (fun r : ℤ =>
        ((1 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))) := by
      intro hsumm
      have htendsto := hsumm.tendsto_cofinite_zero
      have hnorm1 : ∀ r : ℤ,
          ‖((1 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖ = 1 := by
        intro r
        rw [Complex.ofReal_one, one_mul, Complex.norm_exp]
        have hre : (-(Complex.I * (ξ : ℂ) * (r : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre, Real.exp_zero]
      have hnt : Filter.Tendsto
          (fun r : ℤ => ‖((1 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖)
          Filter.cofinite (nhds 0) := by
        have := (continuous_norm.tendsto 0).comp htendsto
        simpa using this
      have hnt1 : Filter.Tendsto (fun _ : ℤ => (1 : ℝ)) Filter.cofinite (nhds 0) := by
        apply hnt.congr; intro r; exact hnorm1 r
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnt1)
    rw [tsum_eq_zero_of_not_summable h_not_summ, norm_zero]
    positivity
  -- ============================================================================
  -- k ≥ 1.  The envelope and its analytic properties (KwayEnvelopeProperties).
  -- ============================================================================
  set h : ℝ → ℝ :=
    fun η => PeriodicBaseKfoldPeriodisation.linPow (GlinWeightedMGF.Glin n) k η
    with hh_def
  have hh_nn : ∀ x : ℝ, 0 ≤ h x :=
    fun x => Workspace.ProofLemmas.KwayEnvelopeProperties.linPow_Glin_nn n k x
  have hh_int : MeasureTheory.Integrable h :=
    Workspace.ProofLemmas.KwayEnvelopeProperties.linPow_Glin_int n hn k hkpos
  have hh_even : ∀ x : ℝ, h (-x) = h x :=
    Workspace.ProofLemmas.KwayEnvelopeProperties.linPow_Glin_even n hn k
  have hh_anti : ∀ x y : ℝ, 0 ≤ x → x ≤ y → h y ≤ h x :=
    MultiplicityExpansion.linPow_Glin_antitone_faithful n hn k hkpos
  -- Whole-line weighted integrability.
  have h_M_global_int :
      MeasureTheory.Integrable
        (fun η : ℝ => Real.exp (Real.sqrt (n : ℝ) * η) * h η) :=
    Workspace.ProofLemmas.KwayEnvelopeProperties.linPow_Glin_weighted_int n hn k hkpos
  -- Whole-line MGF bound.
  have h_M_global_bound :
      (∫ η : ℝ, Real.exp (Real.sqrt (n : ℝ) * η) * h η) ≤ 1 :=
    Workspace.ProofLemmas.KwayEnvelopeProperties.linPow_Glin_mgf_le_one n hn k hkpos
  have h_integrand_nn :
      ∀ η : ℝ, 0 ≤ Real.exp (Real.sqrt (n : ℝ) * η) * h η := fun η =>
    mul_nonneg (Real.exp_pos _).le (hh_nn η)
  have hh_int0 :
      MeasureTheory.IntegrableOn
        (fun η : ℝ => Real.exp (Real.sqrt (n : ℝ) * η) * h η)
        (Set.Ici (0 : ℝ)) :=
    h_M_global_int.integrableOn
  have hh_mgf0 :
      (∫ η in Set.Ici (0 : ℝ),
          Real.exp (Real.sqrt (n : ℝ) * η) * h η) ≤ 1 := by
    have h_set_le_global :
        (∫ η in Set.Ici (0 : ℝ), Real.exp (Real.sqrt (n : ℝ) * η) * h η) ≤
          ∫ η : ℝ, Real.exp (Real.sqrt (n : ℝ) * η) * h η :=
      MeasureTheory.setIntegral_le_integral h_M_global_int
        (Filter.Eventually.of_forall h_integrand_nn)
    linarith
  have hh_int1 :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (Real.sqrt (n : ℝ) * u) * h u)
        (Set.Ici (1 : ℝ)) := by
    apply hh_int0.mono_set
    intro x hx; simp only [Set.mem_Ici] at hx ⊢; linarith
  have hh_mgf1 :
      (∫ u in Set.Ici (1 : ℝ),
          Real.exp (Real.sqrt (n : ℝ) * u) * h u) ≤ 1 := by
    have h_mono :
        (∫ u in Set.Ici (1 : ℝ),
            Real.exp (Real.sqrt (n : ℝ) * u) * h u) ≤
        (∫ η in Set.Ici (0 : ℝ),
            Real.exp (Real.sqrt (n : ℝ) * η) * h η) := by
      apply MeasureTheory.setIntegral_mono_set hh_int0
      · exact Filter.Eventually.of_forall h_integrand_nn
      · exact Filter.Eventually.of_forall (fun x hx => le_trans zero_le_one hx)
    linarith
  have hh_summ :
      Summable (fun s : ℤ => h (ξ + 2 * Real.pi * (s : ℝ))) := by
    set twoπ : ℝ := 2 * Real.pi with htwoπ
    have h2π_pos : 0 < twoπ := by
      have : 0 < Real.pi := Real.pi_pos
      simp [twoπ]; linarith
    have h2π_nn : 0 ≤ twoπ := le_of_lt h2π_pos
    have h2π_ne : twoπ ≠ 0 := ne_of_gt h2π_pos
    have h2pinv_nn : 0 ≤ twoπ⁻¹ := le_of_lt (inv_pos.mpr h2π_pos)
    have hint_total_nn : 0 ≤ ∫ u, h u := MeasureTheory.integral_nonneg hh_nn
    have h_summ_pos_helper :
        ∀ (a : ℝ), 0 < a →
          Summable (fun n : ℕ => h (a + twoπ * (n : ℝ))) := by
      intro a ha
      apply summable_of_sum_range_le (c := h a + twoπ⁻¹ * (∫ u, h u))
        (fun n => hh_nn _)
      intro N
      rcases N with _ | M
      · simp
        have h0 : 0 ≤ h a := hh_nn a
        positivity
      · rw [Finset.sum_range_succ' (fun i => h (a + twoπ * ((i : ℕ) : ℝ))) M]
        set g : ℝ → ℝ := fun t => h (a + twoπ * t) with hg_def
        have hg_antitoneOn : AntitoneOn g (Set.Icc 0 (M : ℝ)) := by
          intro x hx y hy hxy
          simp only [g]
          apply hh_anti
          · have : 0 ≤ twoπ * x := mul_nonneg h2π_nn hx.1
            linarith
          · have : twoπ * x ≤ twoπ * y :=
              mul_le_mul_of_nonneg_left hxy h2π_nn
            linarith
        have hsum_le : (∑ i ∈ Finset.range M, g ((0 : ℝ) + ((i + 1 : ℕ) : ℝ)))
            ≤ ∫ x in (0 : ℝ)..((0 : ℝ) + (M : ℝ)), g x := by
          apply AntitoneOn.sum_le_integral
          simpa using hg_antitoneOn
        have hsum_le' : (∑ i ∈ Finset.range M, g (((i + 1 : ℕ) : ℝ)))
            ≤ ∫ x in (0 : ℝ)..(M : ℝ), g x := by
          simpa using hsum_le
        have hcov : ∫ x in (0 : ℝ)..(M : ℝ), g x
            = twoπ⁻¹ * ∫ u in a..(a + twoπ * (M : ℝ)), h u := by
          have hh' := intervalIntegral.integral_comp_add_mul (a := (0 : ℝ)) (b := (M : ℝ))
            (c := twoπ) (d := a) (f := h) h2π_ne
          simp only [mul_zero, add_zero] at hh'
          have hgform : (fun x => h (a + twoπ * x)) = g := by funext; rfl
          rw [hgform] at hh'
          rw [hh']
          simp [smul_eq_mul]
        rw [hcov] at hsum_le'
        have hM_nn : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
        have hupper : a ≤ a + twoπ * (M : ℝ) := by
          have : 0 ≤ twoπ * (M : ℝ) := mul_nonneg h2π_nn hM_nn
          linarith
        have hint_eq : ∫ u in a..(a + twoπ * (M : ℝ)), h u
            = ∫ u in Set.Ioc a (a + twoπ * (M : ℝ)), h u := by
          rw [intervalIntegral.integral_of_le hupper]
        have hsubset_le : ∫ u in Set.Ioc a (a + twoπ * (M : ℝ)), h u
            ≤ ∫ u, h u := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
          apply MeasureTheory.integral_mono
          · exact MeasureTheory.Integrable.indicator hh_int measurableSet_Ioc
          · exact hh_int
          · intro u
            by_cases h_in : u ∈ Set.Ioc a (a + twoπ * (M : ℝ))
            · simp [Set.indicator_of_mem h_in]
            · simp [Set.indicator_of_notMem h_in, hh_nn]
        have hbound1 : twoπ⁻¹ * ∫ u in a..(a + twoπ * (M : ℝ)), h u
            ≤ twoπ⁻¹ * ∫ u, h u := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hsubset_le h2pinv_nn
        have hLHS_bound : (∑ i ∈ Finset.range M, g (((i + 1 : ℕ) : ℝ)))
            ≤ twoπ⁻¹ * ∫ u, h u := le_trans hsum_le' hbound1
        have hg_eq : ∀ i : ℕ, g (((i + 1 : ℕ) : ℝ))
            = h (a + twoπ * ((i + 1 : ℕ) : ℝ)) := by intro i; rfl
        simp only [hg_eq] at hLHS_bound
        have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (↑i : ℝ) + 1 := by
          intro i; push_cast; ring
        simp only [hcast] at hLHS_bound
        have h0eq : a + twoπ * ((0 : ℕ) : ℝ) = a := by push_cast; ring
        rw [h0eq]
        linarith
    have hξ'_pos : 0 < ξ + twoπ := by
      have : Real.pi ≤ twoπ := by simp [twoπ]; linarith [Real.pi_pos]
      have hπ_pos : 0 < Real.pi := Real.pi_pos
      have : -ξ ≤ Real.pi := by
        have := abs_le.mp hξπ
        linarith
      linarith
    have h_summ_nat : Summable (fun n : ℕ => h (ξ + twoπ * ((n : ℝ)))) := by
      rw [← summable_nat_add_iff (k := 1)]
      have hshift_summ : Summable (fun m : ℕ => h ((ξ + twoπ) + twoπ * (m : ℝ))) :=
        h_summ_pos_helper (ξ + twoπ) hξ'_pos
      convert hshift_summ using 1
      funext m
      congr 1
      push_cast; ring
    have hξ₂_pos : 0 < -ξ + twoπ := by
      have hπ_pos : 0 < Real.pi := Real.pi_pos
      have hπ_le_twoπ : Real.pi ≤ twoπ := by simp [twoπ]; linarith
      have : ξ ≤ Real.pi := by
        have := abs_le.mp hξπ
        linarith
      linarith
    have h_summ_neg : Summable (fun n : ℕ => h (ξ + twoπ * (-(n : ℝ)))) := by
      rw [← summable_nat_add_iff (k := 1)]
      have hshift_summ : Summable (fun m : ℕ => h ((-ξ + twoπ) + twoπ * (m : ℝ))) :=
        h_summ_pos_helper (-ξ + twoπ) hξ₂_pos
      convert hshift_summ using 1
      funext m
      have h_arg_neg : ξ + twoπ * (-((m + 1 : ℕ) : ℝ))
          = -((-ξ + twoπ) + twoπ * (m : ℝ)) := by
        push_cast; ring
      rw [h_arg_neg, hh_even]
    have h_summ_int : Summable (fun s : ℤ => h (ξ + twoπ * (s : ℝ))) := by
      apply Summable.of_nat_of_neg
      · convert h_summ_nat using 1
      · convert h_summ_neg using 1
        funext n
        push_cast
        ring_nf
    exact h_summ_int
  -- ============================================================================
  -- Apply HFourierKwayBoundFromMGFAndLogConcavity (h := linPow (Glin n) k).
  -- ============================================================================
  have h_periodisation_bound :
      (∑' s : ℤ, h (ξ + 2 * Real.pi * (s : ℝ)))
        ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) :=
    HFourierKwayBoundFromMGFAndLogConcavity n hn h hh_nn hh_int hh_even hh_anti
      hh_int0 hh_mgf0 hh_int1 hh_mgf1 ξ hξπ hξ_ge2 hh_summ
  -- ============================================================================
  -- BRIDGE: |T̂₄(ξ)| ≤ circPowR (Genv n) k ξ ≤ ∑_s linPow (Glin n) k (ξ+2πs).
  --   link A : GenvConvergence.T4_modulus_le_circPowR_uncond  (Step 1)
  --   link B : KwayReconciliation.circPowR_Genv_le_periodised_linPow_Glin  (Part 2)
  -- ============================================================================
  have h_bridge :
      ‖∑' r : ℤ,
          (T4 r : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
        ≤ ∑' s : ℤ, h (ξ + 2 * Real.pi * (s : ℝ)) := by
    -- Rewrite T4 r as the product of `factor`s (definitional equality).
    have hT4_factor : ∀ r : ℤ,
        (T4 r : ℂ) = ((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ) : ℂ) := by
      intro r; rw [hT4_def r]; rfl
    have h_rw : (∑' r : ℤ, (T4 r : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
        = ∑' r : ℤ, (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ)
            * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))) := by
      apply tsum_congr; intro r; rw [hT4_factor r]
    rw [h_rw]
    -- link A then link B.
    refine le_trans (GenvConvergence.T4_modulus_le_circPowR_uncond n k ℓ hn hkpos ξ) ?_
    exact KwayReconciliation.circPowR_Genv_le_periodised_linPow_Glin n hn k hkpos ξ hξπ
  exact le_trans h_bridge h_periodisation_bound
