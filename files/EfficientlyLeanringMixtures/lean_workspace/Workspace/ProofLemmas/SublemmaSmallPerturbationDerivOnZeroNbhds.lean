import Mathlib

namespace Workspace.ProofLemmas

open scoped Real

/-- §6.1 Region R3 substrate (derivative analogue of
    `SublemmaSmallPerturbationOnZeroNbhds`): the DERIVATIVE of the Gaussian
    perturbation `a_k · N(μ_k, v, ·)` decays uniformly to 0 on any compact set
    bounded away from `μ_k` as `v → 0⁺`.

    The explicit derivative of
      `x ↦ a_k · (1/√(2π v)) · exp(−(x − μ_k)²/(2v))`
    is
      `a_k · (1/√(2π v)) · exp(−(x − μ_k)²/(2v)) · (−(x − μ_k)/v)`.
    We bound its absolute value below `η` uniformly on `K`. -/
theorem SublemmaSmallPerturbationDerivOnZeroNbhds
    (μ_k a_k : ℝ) (ha_k : a_k ≠ 0)
    (K : Set ℝ) (hK_compact : IsCompact K) (hμ_k_notin : μ_k ∉ K)
    (η : ℝ) (hη : 0 < η) :
    ∃ v_threshold : ℝ, 0 < v_threshold ∧
      ∀ v : ℝ, 0 < v → v ≤ v_threshold →
        ∀ x ∈ K,
          |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v)| < η := by
  -- Case split on K = ∅
  by_cases hK_empty : K = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro v hv _hv' x hx
    rw [hK_empty] at hx
    exact absurd hx (Set.notMem_empty x)
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  -- distance d² := min over K of (x - μ_k)²
  set g : ℝ → ℝ := fun x => (x - μ_k)^2 with hg_def
  have hg_cont : ContinuousOn g K := by
    intro x _
    exact ((continuous_id.sub continuous_const).pow 2).continuousAt.continuousWithinAt
  obtain ⟨x₀, hx₀_mem, hx₀_min⟩ := hK_compact.exists_isMinOn hK_ne hg_cont
  set d2 : ℝ := g x₀ with hd2_def
  have hd2_pos : 0 < d2 := by
    rw [hd2_def, hg_def]
    have hne : x₀ - μ_k ≠ 0 := by
      intro h; apply hμ_k_notin
      have : x₀ = μ_k := by linarith [h]
      rw [← this]; exact hx₀_mem
    exact sq_pos_of_ne_zero hne
  have hd2_le : ∀ x ∈ K, d2 ≤ (x - μ_k)^2 := fun x hx => hx₀_min hx
  -- bound |x - μ_k| ≤ R on K (K compact ⇒ bounded)
  have hcont_abs : ContinuousOn (fun x => |x - μ_k|) K :=
    (continuous_id.sub continuous_const).abs.continuousOn
  obtain ⟨xR, hxR_mem, hxR_max⟩ := hK_compact.exists_isMaxOn hK_ne hcont_abs
  set R : ℝ := |xR - μ_k| with hR_def
  have hR_pos : 0 < R := by
    rw [hR_def]
    have hne : xR - μ_k ≠ 0 := by
      intro h; apply hμ_k_notin
      have : xR = μ_k := by linarith [h]
      rw [← this]; exact hxR_mem
    exact abs_pos.mpr hne
  have hR_ge : ∀ x ∈ K, |x - μ_k| ≤ R := fun x hx => hxR_max hx
  have hak_pos : 0 < |a_k| := abs_pos.mpr ha_k
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  -- We bound (for x ∈ K, 0 < v):
  --  |a_k·(1/√(2πv))·exp(-(x-μ_k)²/(2v))·(-(x-μ_k)/v)|
  --   = |a_k|·(1/√(2πv))·exp(-(x-μ_k)²/(2v))·(|x-μ_k|/v)
  --   ≤ |a_k|·(1/√(2πv))·exp(-d²/(2v))·(R/v)
  --   ≤ |a_k|·(1/(√(2π)·√v))·(R/v)·(8/(d²/(2v))²)        [exp(-t) ≤ 2/t², t=d²/(2v)]
  -- Let me compute exp(-d²/(2v)) ≤ 2/(d²/(2v))² = 8 v² / d⁴.
  --   = |a_k|·R·8·v²/(√(2π)·√v·v·d⁴)
  --   = (8|a_k|R/(√(2π)·d⁴))·√v
  -- So choose v small: √v < η·√(2π)·d⁴/(8|a_k|R). Let C := that, v_threshold := C²/2.
  set C : ℝ := η * Real.sqrt (2 * Real.pi) * d2^2 / (8 * |a_k| * R) with hC_def
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  refine ⟨C^2 / 2, by positivity, ?_⟩
  intro v hv_pos hv_le x hx
  have h2pi_v_pos : 0 < 2 * Real.pi * v := by positivity
  have hsqrt_v_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv_pos
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr h2pi_v_pos
  have hinv_pos : 0 < 1 / Real.sqrt (2 * Real.pi * v) := by positivity
  -- Step 1: absolute value
  have habs_eq : |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v)|
      = |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v)) * (|x - μ_k| / v) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hinv_pos, abs_of_pos (Real.exp_pos _)]
    rw [abs_div, abs_neg, abs_of_pos hv_pos]
  rw [habs_eq]
  -- Step 2: exp(-(x-μ_k)²/(2v)) ≤ exp(-d²/(2v))
  have h2v_pos : 0 < 2 * v := by linarith
  have hxmu_ge : d2 ≤ (x - μ_k)^2 := hd2_le x hx
  have hexp_le : Real.exp (-(x - μ_k)^2 / (2 * v)) ≤ Real.exp (-d2 / (2 * v)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    have : d2 / (2 * v) ≤ (x - μ_k)^2 / (2 * v) :=
      div_le_div_of_nonneg_right hxmu_ge h2v_pos.le
    linarith
  -- Step 3: exp(-d²/(2v)) ≤ 8 v² / d⁴   [via exp(t) ≥ t²/2]
  have ht_pos : 0 < d2 / (2 * v) := by positivity
  have hexp_lb : (d2 / (2 * v))^2 / 2 ≤ Real.exp (d2 / (2 * v)) := by
    have h := Real.pow_div_factorial_le_exp (d2 / (2 * v)) ht_pos.le 2
    simpa [Nat.factorial] using h
  have hexp_bound : Real.exp (-d2 / (2 * v)) ≤ 8 * v^2 / d2^2 := by
    rw [neg_div, Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have hkey : (1 : ℝ) ≤ (8 * v^2 / d2^2) * ((d2 / (2 * v))^2 / 2) := by
      have hd2_ne : d2 ≠ 0 := ne_of_gt hd2_pos
      have hv_ne : v ≠ 0 := ne_of_gt hv_pos
      rw [show (8 * v^2 / d2^2) * ((d2 / (2 * v))^2 / 2) = 1 from by field_simp; ring]
    calc (1 : ℝ) ≤ (8 * v^2 / d2^2) * ((d2 / (2 * v))^2 / 2) := hkey
      _ ≤ (8 * v^2 / d2^2) * Real.exp (d2 / (2 * v)) :=
        mul_le_mul_of_nonneg_left hexp_lb (by positivity)
  -- Combine exp bounds
  have hexp_total : Real.exp (-(x - μ_k)^2 / (2 * v)) ≤ 8 * v^2 / d2^2 :=
    le_trans hexp_le hexp_bound
  -- Step 4: assemble the full bound
  have hfactor_nn : 0 ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) := by positivity
  have hxmu_div_nn : 0 ≤ |x - μ_k| / v := by positivity
  -- |a_k|·(1/√(2πv))·exp(...)·(|x-μ_k|/v) ≤ |a_k|·(1/√(2πv))·(8v²/d²²)·(R/v)
  have hbound1 :
      |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
        Real.exp (-(x - μ_k)^2 / (2 * v)) * (|x - μ_k| / v)
      ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
        (8 * v^2 / d2^2) * (R / v) := by
    have hstep_exp :
        |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v))
        ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (8 * v^2 / d2^2) :=
      mul_le_mul_of_nonneg_left hexp_total hfactor_nn
    have hxR_le : |x - μ_k| / v ≤ R / v :=
      div_le_div_of_nonneg_right (hR_ge x hx) hv_pos.le
    calc |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v)) * (|x - μ_k| / v)
        ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (8 * v^2 / d2^2) * (|x - μ_k| / v) :=
          mul_le_mul_of_nonneg_right hstep_exp hxmu_div_nn
      _ ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (8 * v^2 / d2^2) * (R / v) :=
          mul_le_mul_of_nonneg_left hxR_le (by positivity)
  -- Step 5: simplify RHS = (8|a_k|R/(√(2π)·d²²))·√v
  have hsqrt_split : Real.sqrt (2 * Real.pi * v) = Real.sqrt (2 * Real.pi) * Real.sqrt v := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hv_split : v = Real.sqrt v * Real.sqrt v := (Real.mul_self_sqrt hv_pos.le).symm
  have hRHS_eq :
      |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (8 * v^2 / d2^2) * (R / v)
      = 8 * |a_k| * R * Real.sqrt v / (Real.sqrt (2 * Real.pi) * d2^2) := by
    have hsqrt_2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
    have hsqrt_v_ne : Real.sqrt v ≠ 0 := ne_of_gt hsqrt_v_pos
    have hd2_ne : d2 ≠ 0 := ne_of_gt hd2_pos
    -- Set w := √v, so v = w*w and √(2πv) = √(2π)*w.
    set w := Real.sqrt v with hw_def
    have hw_pos : 0 < w := hsqrt_v_pos
    have hw_ne : w ≠ 0 := ne_of_gt hw_pos
    have hv_ww : v = w * w := hv_split
    rw [hsqrt_split]
    rw [show (8 * v ^ 2 / d2 ^ 2) = (8 * (w*w) ^ 2 / d2 ^ 2) from by rw [← hv_ww],
        show (R / v) = (R / (w*w)) from by rw [← hv_ww]]
    field_simp
  rw [hRHS_eq] at hbound1
  -- Step 6: (8|a_k|R/(√(2π)·d²²))·√v < η  via √v < C
  have hsqrt_v_lt_C : Real.sqrt v < C := by
    have hv_lt_C2 : v < C^2 := by
      have hC2_pos : 0 < C^2 := by positivity
      linarith
    have := Real.sqrt_lt_sqrt hv_pos.le hv_lt_C2
    rwa [Real.sqrt_sq hC_pos.le] at this
  have hden_pos : 0 < Real.sqrt (2 * Real.pi) * d2^2 := by positivity
  have hnum_pos : 0 < 8 * |a_k| * R := by positivity
  have hstrict :
      8 * |a_k| * R * Real.sqrt v / (Real.sqrt (2 * Real.pi) * d2^2)
      < 8 * |a_k| * R * C / (Real.sqrt (2 * Real.pi) * d2^2) := by
    apply div_lt_div_of_pos_right _ hden_pos
    exact mul_lt_mul_of_pos_left hsqrt_v_lt_C hnum_pos
  have hC_simp : 8 * |a_k| * R * C / (Real.sqrt (2 * Real.pi) * d2^2) = η := by
    rw [hC_def]
    have hsqrt_2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
    have hd2_ne : d2 ≠ 0 := ne_of_gt hd2_pos
    have hak_ne : |a_k| ≠ 0 := ne_of_gt hak_pos
    have hR_ne : R ≠ 0 := ne_of_gt hR_pos
    field_simp
  rw [hC_simp] at hstrict
  linarith

end Workspace.ProofLemmas
