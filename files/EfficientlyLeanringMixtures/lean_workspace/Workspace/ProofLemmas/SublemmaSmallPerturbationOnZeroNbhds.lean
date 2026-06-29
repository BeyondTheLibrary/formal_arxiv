import Mathlib

namespace Workspace.ProofLemmas

/-- §6.1 implicit step (Region R3): a Gaussian density `a_k · N(μ_k, v, ·)` decays
    super-polynomially uniformly on any compact set bounded away from `μ_k`
    as `v → 0⁺`. Concretely, for any `η > 0` there exists a positive variance
    threshold `v_threshold` such that for every `v ∈ (0, v_threshold]` and every
    `x ∈ K`, the absolute value of `a_k · (1/√(2π v)) · exp(−(x − μ_k)² / (2v))`
    is below `η`. The hypothesis `μ_k ∉ K` together with `IsCompact K` gives
    `dist(μ_k, K) > 0`, so no separate distance hypothesis is needed. -/
theorem SublemmaSmallPerturbationOnZeroNbhds
    (μ_k a_k : ℝ) (ha_k : a_k ≠ 0)
    (K : Set ℝ) (hK_compact : IsCompact K) (hμ_k_notin : μ_k ∉ K)
    (η : ℝ) (hη : 0 < η) :
    ∃ v_threshold : ℝ, 0 < v_threshold ∧
      ∀ v : ℝ, 0 < v → v ≤ v_threshold →
        ∀ x ∈ K,
          |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v))| < η := by
  -- Case split on K = ∅
  by_cases hK_empty : K = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro v hv _hv' x hx
    rw [hK_empty] at hx
    exact absurd hx (Set.notMem_empty x)
  -- K is nonempty
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  -- Define g x = (x - μ_k)^2
  set g : ℝ → ℝ := fun x => (x - μ_k)^2 with hg_def
  have hg_cont : ContinuousOn g K := by
    intro x _
    apply ContinuousAt.continuousWithinAt
    exact (continuous_id.sub continuous_const).pow 2 |>.continuousAt
  -- Extract a minimum point of g on K
  obtain ⟨x₀, hx₀_mem, hx₀_min⟩ := hK_compact.exists_isMinOn hK_ne hg_cont
  -- Let d² := g x₀ = (x₀ - μ_k)^2
  set d2 : ℝ := g x₀ with hd2_def
  have hd2_pos : 0 < d2 := by
    rw [hd2_def, hg_def]
    have hne : x₀ - μ_k ≠ 0 := by
      intro h
      apply hμ_k_notin
      have hx_eq : x₀ = μ_k := by linarith [h]
      rw [← hx_eq]; exact hx₀_mem
    exact sq_pos_of_ne_zero hne
  -- For all x ∈ K, (x - μ_k)^2 ≥ d2
  have hd2_le : ∀ x ∈ K, d2 ≤ (x - μ_k)^2 := fun x hx => hx₀_min hx
  -- |a_k| > 0
  have hak_pos : 0 < |a_k| := abs_pos.mpr ha_k
  -- Useful positivity facts
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  -- Choose v_threshold
  -- We bound: |a_k * (1/√(2π v)) * exp(-(x-μ_k)²/(2v))|
  --           ≤ |a_k| * (1/√(2π v)) * exp(-d²/(2v))   [since (x-μ_k)² ≥ d²]
  --           ≤ |a_k| * (1/√(2π v)) * (2v/d²)         [exp(-t) ≤ 1/t for t > 0]
  --           = 2 |a_k| √v / (d² · √(2π))             [v/√(2π v) = √v / √(2π)]
  -- So pick v_threshold so that 2 |a_k| √v / (d² · √(2π)) < η, i.e. √v < η · d² · √(2π) / (2 |a_k|).
  -- Let C := η · d² · √(2π) / (2 |a_k|). Take v_threshold := C² / 2.
  set C : ℝ := η * d2 * Real.sqrt (2 * Real.pi) / (2 * |a_k|) with hC_def
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  refine ⟨C^2 / 2, by positivity, ?_⟩
  intro v hv_pos hv_le x hx
  -- Step 1: replace abs by removing signs (each factor is positive)
  have h2pi_v_pos : 0 < 2 * Real.pi * v := by positivity
  have hsqrt_v_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv_pos
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr h2pi_v_pos
  have hinv_pos : 0 < 1 / Real.sqrt (2 * Real.pi * v) := by positivity
  have habs_eq : |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v))|
      = |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v)) := by
    rw [abs_mul, abs_mul, abs_of_pos hinv_pos, abs_of_pos (Real.exp_pos _)]
  rw [habs_eq]
  -- Step 2: bound exp(-(x-μ_k)²/(2v)) ≤ exp(-d²/(2v))
  have h2v_pos : 0 < 2 * v := by linarith
  have hxmu_ge : d2 ≤ (x - μ_k)^2 := hd2_le x hx
  have hneg_div_le : -(x - μ_k)^2 / (2 * v) ≤ -d2 / (2 * v) := by
    have : d2 / (2 * v) ≤ (x - μ_k)^2 / (2 * v) :=
      div_le_div_of_nonneg_right hxmu_ge h2v_pos.le
    rw [neg_div, neg_div]; linarith
  have hexp_le : Real.exp (-(x - μ_k)^2 / (2 * v)) ≤ Real.exp (-d2 / (2 * v)) :=
    Real.exp_le_exp.mpr hneg_div_le
  -- Step 3: bound exp(-d²/(2v)) ≤ 2v/d²
  -- Use exp(t) ≥ t + 1, so exp(t) ≥ t for t ≥ 0.
  -- exp(-t) = 1/exp(t) ≤ 1/t.
  have ht_pos : 0 < d2 / (2 * v) := by positivity
  have hexp_lb : d2 / (2 * v) ≤ Real.exp (d2 / (2 * v)) := by
    have := Real.add_one_le_exp (d2 / (2 * v))
    linarith
  have hexp_bound : Real.exp (-d2 / (2 * v)) ≤ 2 * v / d2 := by
    rw [neg_div, Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    calc 1 = (2 * v / d2) * (d2 / (2 * v)) := by field_simp
      _ ≤ (2 * v / d2) * Real.exp (d2 / (2 * v)) :=
        mul_le_mul_of_nonneg_left hexp_lb (by positivity)
  -- Step 4: combine: |a_k|·(1/√(2πv))·exp(-(x-μ_k)²/(2v)) ≤ |a_k|·(1/√(2πv))·(2v/d²)
  have hak_factor_nn : 0 ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) := by positivity
  have hcombined :
      |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
        Real.exp (-(x - μ_k)^2 / (2 * v))
      ≤ |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (2 * v / d2) := by
    have h1 :
        |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) ≤
        |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-d2 / (2 * v)) :=
      mul_le_mul_of_nonneg_left hexp_le hak_factor_nn
    have h2 :
        |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-d2 / (2 * v)) ≤
        |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (2 * v / d2) :=
      mul_le_mul_of_nonneg_left hexp_bound hak_factor_nn
    linarith
  -- Step 5: |a_k|·(1/√(2πv))·(2v/d²) < η
  -- Compute RHS: it equals 2 |a_k| √v / (d² √(2π)).
  -- Key fact: √(2π v) = √(2π) · √v and v = √v · √v.
  have hsqrt_split : Real.sqrt (2 * Real.pi * v) = Real.sqrt (2 * Real.pi) * Real.sqrt v := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hv_split : v = Real.sqrt v * Real.sqrt v := (Real.mul_self_sqrt hv_pos.le).symm
  -- Show RHS = 2 |a_k| √v / (d² √(2π))
  have hRHS_eq :
      |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * (2 * v / d2)
      = 2 * |a_k| * Real.sqrt v / (d2 * Real.sqrt (2 * Real.pi)) := by
    have hsqrt_2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
    have hsqrt_v_ne : Real.sqrt v ≠ 0 := ne_of_gt hsqrt_v_pos
    have hd2_ne : d2 ≠ 0 := ne_of_gt hd2_pos
    rw [hsqrt_split]
    -- Replace v on the LHS by √v · √v on the numerator
    conv_lhs => rw [show (2 : ℝ) * v = 2 * (Real.sqrt v * Real.sqrt v) from by rw [← hv_split]]
    field_simp
  rw [hRHS_eq] at hcombined
  -- Now we want: 2 |a_k| √v / (d² √(2π)) < η, equivalently √v < C
  have hsqrt_v_lt_C : Real.sqrt v < C := by
    have hv_lt_C2 : v < C^2 := by
      have hC2_pos : 0 < C^2 := by positivity
      linarith
    have hsqrt_lt : Real.sqrt v < Real.sqrt (C^2) :=
      Real.sqrt_lt_sqrt hv_pos.le hv_lt_C2
    rwa [Real.sqrt_sq hC_pos.le] at hsqrt_lt
  have h2ak_pos : 0 < 2 * |a_k| := by linarith
  have hd2_sqrt_pos : 0 < d2 * Real.sqrt (2 * Real.pi) := by positivity
  -- Strict bound: 2 |a_k| √v / (d² √(2π)) < 2 |a_k| C / (d² √(2π))
  have hnum_lt : 2 * |a_k| * Real.sqrt v < 2 * |a_k| * C :=
    mul_lt_mul_of_pos_left hsqrt_v_lt_C h2ak_pos
  have hstrict :
      2 * |a_k| * Real.sqrt v / (d2 * Real.sqrt (2 * Real.pi))
      < 2 * |a_k| * C / (d2 * Real.sqrt (2 * Real.pi)) :=
    div_lt_div_of_pos_right hnum_lt hd2_sqrt_pos
  -- And 2 |a_k| C / (d² √(2π)) = η
  have hC_simp : 2 * |a_k| * C / (d2 * Real.sqrt (2 * Real.pi)) = η := by
    rw [hC_def]
    have hsqrt_2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
    have hd2_ne : d2 ≠ 0 := ne_of_gt hd2_pos
    have hak_ne : |a_k| ≠ 0 := ne_of_gt hak_pos
    field_simp
  linarith

end Workspace.ProofLemmas
