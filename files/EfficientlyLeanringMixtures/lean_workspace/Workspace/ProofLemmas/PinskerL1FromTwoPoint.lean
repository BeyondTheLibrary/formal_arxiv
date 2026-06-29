import Mathlib
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.PinskerTwoPointBound
import Workspace.ProofLemmas.PinskerScheffeIdentity
import Workspace.ProofLemmas.PinskerDataProcessingInequality

open MeasureTheory

set_option maxHeartbeats 1200000

/-- Boundary case of `PinskerTwoPointBound` with `p = 1`:
    `2 (1 - q)^2 ≤ -log q` for `q ∈ (0, 1]`. -/
private lemma pinsker_boundary_p_one
    (q : ℝ) (hq_pos : 0 < q) (hq_le_one : q ≤ 1) :
    2 * (1 - q) ^ 2 ≤ -Real.log q := by
  by_cases hq_eq : q = 1
  · rw [hq_eq]; simp
  have hq_lt : q < 1 := lt_of_le_of_ne hq_le_one hq_eq

  set F : ℝ → ℝ := fun t => -Real.log t - 2 * (1 - t) ^ 2 with hFdef
  set F' : ℝ → ℝ := fun t => -1/t + 4 * (1 - t) with hF'def

  have hF1 : F 1 = 0 := by simp [hFdef]

  have hF'_nonpos : ∀ t ∈ Set.Ioo (0:ℝ) 1, F' t ≤ 0 := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    simp only [hF'def]
    have hkey : 0 ≤ (2*t - 1)^2 := sq_nonneg _
    have hexpand : (2*t - 1)^2 = 4*t^2 - 4*t + 1 := by ring
    rw [hexpand] at hkey
    have h4t : 4 * t * (1 - t) ≤ 1 := by nlinarith
    have ht_pos : 0 < t := ht0
    have hkey2 : 4 * (1 - t) ≤ 1 / t := by
      rw [le_div_iff₀ ht_pos]
      linarith
    have : -1/t = -(1/t) := by ring
    rw [this]
    linarith

  have hF_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt F (F' t) t := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have d_neglog : HasDerivAt (fun s : ℝ => -Real.log s) (-(1/t)) t := by
      have := Real.hasDerivAt_log ht0.ne'
      simpa using this.neg
    have d_sq : HasDerivAt (fun s : ℝ => 2 * (1 - s)^2) (-(4*(1-t))) t := by
      have h1 : HasDerivAt (fun s : ℝ => (1 - s)^2) (2 * (1-t) * (-1)) t := by
        have hu : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
          simpa using (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
        have := hu.pow 2
        simpa [pow_succ, pow_zero, one_mul] using this
      have h2 := h1.const_mul 2
      have hsimp : 2 * (2 * (1 - t) * (-1)) = -(4 * (1-t)) := by ring
      rw [hsimp] at h2
      exact h2
    have hsum := d_neglog.sub d_sq
    have hsimp : -(1/t) - -(4 * (1-t)) = -1/t + 4 * (1-t) := by ring
    rw [hsimp] at hsum
    exact hsum

  have hF_continuous_on : ContinuousOn F (Set.Icc q 1) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht_pos : 0 < t := lt_of_lt_of_le hq_pos ht1
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact (Real.continuousAt_log ht_pos.ne').neg
    · exact ((continuous_const.sub continuous_id).pow 2).continuousAt.const_mul 2

  have ⟨c, hc, hMVT⟩ := exists_hasDerivAt_eq_slope F F' hq_lt hF_continuous_on
    (fun t ht => hF_deriv t ⟨lt_of_lt_of_le hq_pos ht.1.le, ht.2⟩)
  rw [hF1] at hMVT
  have h1mq : 0 < 1 - q := by linarith
  have hc_io : c ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_lt_of_le hq_pos hc.1.le, hc.2⟩
  have hF'c_nonpos : F' c ≤ 0 := hF'_nonpos c hc_io
  rw [hMVT] at hF'c_nonpos
  have h_eq : (0 - F q) / (1 - q) = -F q / (1 - q) := by ring
  rw [h_eq] at hF'c_nonpos
  have hFq_nn : 0 ≤ F q := by
    have hdiv : -F q / (1 - q) ≤ 0 := hF'c_nonpos
    rw [div_nonpos_iff] at hdiv
    rcases hdiv with ⟨hneg, hpos⟩ | ⟨hpos, hneg⟩
    · linarith
    · linarith
  simp only [hFdef] at hFq_nn
  linarith

theorem PinskerL1FromTwoPoint :
    ∀ (f g : ℝ → ℝ),
      Measurable f → Measurable g →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      Integrable f volume → Integrable g volume →
      (∫ x, f x ∂volume) = 1 → (∫ x, g x ∂volume) = 1 →
      (∀ᵐ x ∂volume, 0 < g x) →
      Integrable (fun x => f x * Real.log (f x / g x)) volume →
      0 ≤ ∫ x, f x * Real.log (f x / g x) ∂volume →
      Workspace.Types.L1AndTVDistance.L1Norm (fun x => f x - g x) ≤
        Real.sqrt (2 * ∫ x, f x * Real.log (f x / g x) ∂volume) := by
  intro f g hf hg hfnn hgnn hfi hgi hfint hgint hg_pos hflog_int hX_nn
  set X : ℝ := ∫ x, f x * Real.log (f x / g x) ∂volume with hXdef
  have hL1_nn : 0 ≤ Workspace.Types.L1AndTVDistance.L1Norm (fun x => f x - g x) := by
    unfold Workspace.Types.L1AndTVDistance.L1Norm
    apply integral_nonneg
    intro x; exact abs_nonneg _
  set A : Set ℝ := {x : ℝ | f x > g x} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_lt hg hf
  set p : ℝ := ∫ x in A, f x ∂volume with hpdef
  set q : ℝ := ∫ x in A, g x ∂volume with hqdef
  have hScheffe := PinskerScheffeIdentity f g hf hg hfnn hgnn hfi hgi hfint hgint
  have hL1_eq : Workspace.Types.L1AndTVDistance.L1Norm (fun x => f x - g x) = 2 * (p - q) := by
    convert hScheffe using 2
  have hp_nn : 0 ≤ p := integral_nonneg (fun x => hfnn x)
  have hq_nn : 0 ≤ q := integral_nonneg (fun x => hgnn x)
  have hfi_ae : 0 ≤ᵐ[volume] f := Filter.Eventually.of_forall hfnn
  have hgi_ae : 0 ≤ᵐ[volume] g := Filter.Eventually.of_forall hgnn
  have hp_le_one : p ≤ 1 := by
    calc p = ∫ x in A, f x ∂volume := rfl
      _ ≤ ∫ x, f x ∂volume := MeasureTheory.setIntegral_le_integral hfi hfi_ae
      _ = 1 := hfint
  have hq_le_one : q ≤ 1 := by
    calc q = ∫ x in A, g x ∂volume := rfl
      _ ≤ ∫ x, g x ∂volume := MeasureTheory.setIntegral_le_integral hgi hgi_ae
      _ = 1 := hgint
  have hp_ge_q : q ≤ p := by
    apply setIntegral_mono_on hgi.integrableOn hfi.integrableOn hAmeas
    intro x hx; exact le_of_lt hx
  have hPDPI := PinskerDataProcessingInequality f g A hf hg hfnn hgnn hfi hgi hfint hgint
                hg_pos hflog_int hAmeas
  simp only at hPDPI
  -- hPDPI is now: (∫ x in A, f x) * log(...) + (1 - ∫ x in A, f x) * log(...) ≤ X
  -- Convert it back to use p and q
  have hPDPI' : p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ X := hPDPI
  -- Case 1: p ≤ q (so L1Norm = 0)
  rcases le_or_gt p q with hpq | hpq
  · have hpq_eq : p = q := le_antisymm hpq hp_ge_q
    rw [hL1_eq, hpq_eq]
    have : 2 * (q - q) = 0 := by ring
    rw [this]
    exact Real.sqrt_nonneg _
  -- Case 2: p > q
  have hq_pos : 0 < q := by
    by_contra hq_npos
    push_neg at hq_npos
    have hq_zero : q = 0 := le_antisymm hq_npos hq_nn
    have hgnn_restrict : 0 ≤ᵐ[volume.restrict A] g :=
      ae_restrict_of_ae hgi_ae
    have hgi_on : IntegrableOn g A volume := hgi.integrableOn
    have hg_zero_on_A : g =ᵐ[volume.restrict A] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae hgnn_restrict hgi_on).mp hq_zero
    have hg_pos_restrict : ∀ᵐ x ∂(volume.restrict A), 0 < g x :=
      ae_restrict_of_ae hg_pos
    have hfilter_bot : ∀ᵐ x ∂(volume.restrict A), False := by
      filter_upwards [hg_zero_on_A, hg_pos_restrict] with x hx0 hxpos
      rw [hx0] at hxpos
      exact lt_irrefl 0 hxpos
    have hae_bot : MeasureTheory.ae (volume.restrict A) = ⊥ :=
      Filter.eventually_false_iff_eq_bot.mp hfilter_bot
    have hA_meas_zero : volume A = 0 := MeasureTheory.ae_restrict_eq_bot.mp hae_bot
    have hp_zero : p = 0 := by
      show (∫ x in A, f x ∂volume) = 0
      exact setIntegral_measure_zero f hA_meas_zero
    linarith
  -- Now 0 < q ≤ p, p > q.
  rcases lt_or_eq_of_le hp_le_one with hp_lt | hp_eq
  · -- p < 1
    have hp_pos : 0 < p := lt_of_le_of_lt hq_nn hpq
    have hq_lt_one : q < 1 := lt_of_lt_of_le hpq hp_le_one
    have hPTPB := PinskerTwoPointBound p q hp_pos hp_lt hq_pos hq_lt_one
    have hkl_le : p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ X := hPDPI'
    have hsq_le : (p - q) ^ 2 ≤ (1/2) * X := by
      calc (p - q) ^ 2
          ≤ (1/2) * (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := hPTPB
        _ ≤ (1/2) * X := by linarith
    have hL1sq : (2 * (p - q)) ^ 2 ≤ 2 * X := by nlinarith [hsq_le]
    rw [hL1_eq]
    exact Real.le_sqrt_of_sq_le hL1sq
  · -- p = 1
    have hq_lt_one : q < 1 := lt_of_lt_of_le hpq hp_le_one
    have h_boundary := pinsker_boundary_p_one q hq_pos hq_le_one
    -- From hPDPI' with p = 1: 1 * log(1/q) + 0 * log(0/(1-q)) ≤ X
    have hPDPI_p1 : Real.log (1 / q) ≤ X := by
      have hPDPI'' : p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ X := hPDPI'
      rw [hp_eq] at hPDPI''
      simpa using hPDPI''
    have hlog_one_div : Real.log (1 / q) = -Real.log q := by
      rw [Real.log_div one_ne_zero hq_pos.ne', Real.log_one, zero_sub]
    have hneg_log_le : -Real.log q ≤ X := by rw [← hlog_one_div]; exact hPDPI_p1
    have hL1sq : (2 * (p - q)) ^ 2 ≤ 2 * X := by
      rw [hp_eq]
      have heq : (2 * (1 - q))^2 = 4 * (1 - q)^2 := by ring
      rw [heq]
      linarith
    rw [hL1_eq]
    exact Real.le_sqrt_of_sq_le hL1sq
