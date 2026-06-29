import Mathlib

open MeasureTheory

/--
**Non-increasing tail summation (sum-to-integral comparison).**
-/
theorem NonincreasingTailSummation :
    ∀ (f : ℝ → ℝ),
      (∀ x : ℝ, 0 ≤ f x) →
      ∀ (a : ℝ), 0 < a →
        (∀ x y : ℝ, a ≤ x → x ≤ y → f y ≤ f x) →
        (∑' s : {s : ℕ // 1 ≤ s},
            f (a + 2 * Real.pi * (s.val : ℝ)))
          ≤ (1 / (2 * Real.pi)) * ∫ u in Set.Ici a, f u := by
  intro f hf_nonneg a ha hf_anti
  -- Abbreviations
  set twoπ : ℝ := 2 * Real.pi with htwoπ
  have h2π_pos : 0 < twoπ := by
    have : 0 < Real.pi := Real.pi_pos
    simp [twoπ]; linarith
  have h2π_ne : twoπ ≠ 0 := ne_of_gt h2π_pos
  -- The integral over Ici a (which we want to bound)
  set I : ℝ := ∫ u in Set.Ici a, f u with hI
  -- Reindex the sum: {s : ℕ // 1 ≤ s} ≃ ℕ via s ↦ s - 1
  have hreindex :
      (∑' s : {s : ℕ // 1 ≤ s}, f (a + twoπ * (s.val : ℝ)))
        = ∑' n : ℕ, f (a + twoπ * ((n + 1 : ℕ) : ℝ)) := by
    let e : ℕ ≃ {s : ℕ // 1 ≤ s} :=
      { toFun := fun n => ⟨n + 1, Nat.succ_le_succ (Nat.zero_le _)⟩
        invFun := fun s => s.val - 1
        left_inv := fun n => by simp
        right_inv := fun s => by
          obtain ⟨s, hs⟩ := s
          simp
          omega }
    rw [← e.tsum_eq (fun s : {s : ℕ // 1 ≤ s} => f (a + twoπ * (s.val : ℝ)))]
    rfl
  show _ ≤ (1 / twoπ) * I
  rw [hreindex]
  -- Each term is non-negative
  have hf_nonneg' : ∀ n : ℕ, 0 ≤ f (a + twoπ * ((n + 1 : ℕ) : ℝ)) :=
    fun n => hf_nonneg _
  -- Define g(t) = f(a + 2π·t). It is antitone on [0, ∞).
  set g : ℝ → ℝ := fun t => f (a + twoπ * t) with hg_def
  -- g is antitone on Icc 0 M for any M ≥ 0.
  have hg_antitone_on : ∀ M : ℝ, AntitoneOn g (Set.Icc (0 : ℝ) M) := by
    intro M x hx y hy hxy
    simp only [g]
    have hx0 : 0 ≤ x := hx.1
    apply hf_anti
    · have : 0 ≤ twoπ * x := mul_nonneg (le_of_lt h2π_pos) hx0
      linarith
    · have : twoπ * x ≤ twoπ * y :=
        mul_le_mul_of_nonneg_left hxy (le_of_lt h2π_pos)
      linarith
  -- f is antitone on [a, M] for any M ≥ a.
  have hf_anti_on : ∀ M : ℝ, AntitoneOn f (Set.Icc a M) := by
    intro M x hx y hy hxy
    exact hf_anti x y hx.1 hxy
  -- Change of variables: ∫_0^N g(t) dt = (2π)⁻¹ ∫_a^(a+2π·N) f(u) du.
  have hcov : ∀ N : ℝ,
      ∫ x in (0 : ℝ)..N, g x
        = twoπ⁻¹ * ∫ u in a..(a + twoπ * N), f u := by
    intro N
    have h := intervalIntegral.integral_comp_add_mul (a := (0 : ℝ)) (b := N)
      (c := twoπ) (d := a) (f := f) h2π_ne
    -- Simplify a + twoπ * 0 = a
    simp only [mul_zero, add_zero] at h
    have hgform : (fun x => f (a + twoπ * x)) = g := by funext; rfl
    rw [hgform] at h
    rw [h]
    simp [smul_eq_mul]
  -- For each N, ∑_{i<N} g(i+1) ≤ ∫_0^N g
  have hpartial_le_int : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, f (a + twoπ * ((i + 1 : ℕ) : ℝ)))
        ≤ twoπ⁻¹ * ∫ u in a..(a + twoπ * (N : ℝ)), f u := by
    intro N
    have hsum_le : (∑ i ∈ Finset.range N, g ((0 : ℝ) + ((i + 1 : ℕ) : ℝ)))
        ≤ ∫ x in (0 : ℝ)..((0 : ℝ) + (N : ℝ)), g x := by
      apply AntitoneOn.sum_le_integral
      simpa using hg_antitone_on (N : ℝ)
    have hsum_le' : (∑ i ∈ Finset.range N, g ((i + 1 : ℕ) : ℝ))
        ≤ ∫ x in (0 : ℝ)..(N : ℝ), g x := by
      simpa using hsum_le
    -- Apply change of variables
    rw [hcov] at hsum_le'
    -- The LHS is what we want
    have heq : ∀ i, g ((i + 1 : ℕ) : ℝ) = f (a + twoπ * ((i + 1 : ℕ) : ℝ)) := by
      intro i; rfl
    simp only [heq] at hsum_le'
    exact hsum_le'
  -- We split on integrability
  by_cases hint : IntegrableOn f (Set.Ici a) volume
  · -- Integrable case: standard argument
    have hint_Ioi : IntegrableOn f (Set.Ioi a) volume :=
      hint.mono_set Set.Ioi_subset_Ici_self
    -- I = ∫ in Ici a, f = ∫ in Ioi a, f (since {a} has measure 0)
    have hI_eq_Ioi : I = ∫ u in Set.Ioi a, f u :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    apply Real.tsum_le_of_sum_range_le hf_nonneg'
    intro N
    -- Bound ∫_a^(a+2πN) f by I.
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hupper_le : a ≤ a + twoπ * (N : ℝ) := by
      have : 0 ≤ twoπ * (N : ℝ) := mul_nonneg (le_of_lt h2π_pos) hN_nonneg
      linarith
    have hIoc : ∫ u in a..(a + twoπ * (N : ℝ)), f u
        = ∫ u in Set.Ioc a (a + twoπ * (N : ℝ)), f u := by
      rw [intervalIntegral.integral_of_le hupper_le]
    have hIoc_le_Ioi : ∫ u in Set.Ioc a (a + twoπ * (N : ℝ)), f u
        ≤ ∫ u in Set.Ioi a, f u := by
      apply MeasureTheory.setIntegral_mono_set
      · exact hint_Ioi
      · exact ae_of_all _ (fun x => hf_nonneg x)
      · exact ae_of_all _ (fun x hx => hx.1)
    have hint_le : ∫ u in a..(a + twoπ * (N : ℝ)), f u ≤ I := by
      rw [hIoc, hI_eq_Ioi]
      exact hIoc_le_Ioi
    have htwoπinv_pos : 0 ≤ twoπ⁻¹ := le_of_lt (inv_pos.mpr h2π_pos)
    calc (∑ i ∈ Finset.range N, f (a + twoπ * ((i + 1 : ℕ) : ℝ)))
        ≤ twoπ⁻¹ * ∫ u in a..(a + twoπ * (N : ℝ)), f u := hpartial_le_int N
      _ ≤ twoπ⁻¹ * I := mul_le_mul_of_nonneg_left hint_le htwoπinv_pos
      _ = (1 / twoπ) * I := by rw [one_div]
  · -- Non-integrable case: I = 0; we show tsum = 0.
    have hI_zero : I = 0 := integral_undef hint
    rw [hI_zero, mul_zero]
    -- Show: ∑' n, f(a + 2π(n+1)) ≤ 0. We show that the sum is not summable.
    have h_not_summ : ¬ Summable (fun n : ℕ => f (a + twoπ * ((n + 1 : ℕ) : ℝ))) := by
      intro h_summ
      apply hint
      let S : ℝ := ∑' n : ℕ, f (a + twoπ * ((n + 1 : ℕ) : ℝ))
      have hS_nonneg : 0 ≤ S := tsum_nonneg hf_nonneg'
      have hf_a_nonneg : 0 ≤ f a := hf_nonneg a
      -- Bound: ∫_a^(a+2πN) f ≤ 2π * (f(a) + S)
      have hbound : ∀ N : ℕ, ∫ u in a..(a + twoπ * (N : ℝ)), f u ≤ twoπ * (f a + S) := by
        intro N
        have hgsum : ∫ x in (0 : ℝ)..((0 : ℝ) + (N : ℝ)), g x
            ≤ ∑ i ∈ Finset.range N, g ((0 : ℝ) + ((i : ℕ) : ℝ)) := by
          apply AntitoneOn.integral_le_sum
          simpa using hg_antitone_on (N : ℝ)
        have hgsum' : ∫ x in (0 : ℝ)..(N : ℝ), g x
            ≤ ∑ i ∈ Finset.range N, g (i : ℝ) := by
          simpa using hgsum
        -- ∑_{i<N} g(i) ≤ f a + S
        have hsum_bound : (∑ i ∈ Finset.range N, g (i : ℝ)) ≤ f a + S := by
          rcases N with _ | M
          · -- N = 0: sum is empty, so equals 0; need 0 ≤ f a + S
            simp
            linarith
          · -- N = M+1: split off the i=0 term
            rw [Finset.sum_range_succ' (fun i => g ((i : ℕ) : ℝ)) M]
            -- After this: ∑_{i<M} g((i+1):ℕ) + g(0:ℕ) ≤ f a + S
            -- where g((i+1):ℕ) = f(a + twoπ*((i+1):ℕ)) and g(0) = f(a + 0) = f a
            have hg_zero : g ((0 : ℕ) : ℝ) = f a := by
              simp [g]
            have hpartial_le_S : (∑ i ∈ Finset.range M, g (((i + 1 : ℕ) : ℝ))) ≤ S := by
              -- The sum is exactly a partial sum of S
              have hSdef : S = ∑' n : ℕ, f (a + twoπ * ((n + 1 : ℕ) : ℝ)) := rfl
              have heq : (∑ i ∈ Finset.range M, g (((i + 1 : ℕ) : ℝ)))
                  = ∑ i ∈ Finset.range M, f (a + twoπ * ((i + 1 : ℕ) : ℝ)) := by
                apply Finset.sum_congr rfl
                intros i _
                simp [g]
              rw [heq, hSdef]
              exact h_summ.sum_le_tsum (Finset.range M) (fun i _ => hf_nonneg _)
            calc (∑ i ∈ Finset.range M, g (((i + 1 : ℕ) : ℝ))) + g ((0 : ℕ) : ℝ)
                ≤ S + f a := by linarith
              _ = f a + S := by ring
        have hg_int_le : ∫ x in (0 : ℝ)..(N : ℝ), g x ≤ f a + S := le_trans hgsum' hsum_bound
        rw [hcov] at hg_int_le
        -- Now: twoπ⁻¹ * ∫_a^(a+2πN) f ≤ f a + S; multiply both sides by twoπ
        have h := mul_le_mul_of_nonneg_left hg_int_le (le_of_lt h2π_pos)
        rw [← mul_assoc, mul_inv_cancel₀ h2π_ne, one_mul] at h
        exact h
      -- Now use integrableOn_Ioi_of_intervalIntegral_norm_bounded
      -- We need to specify ι := ℕ and l := Filter.atTop explicitly
      have hIoi_int : IntegrableOn f (Set.Ioi a) volume := by
        refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
          (l := (Filter.atTop : Filter ℕ))
          (b := fun N : ℕ => a + twoπ * (N : ℝ))
          (twoπ * (f a + S)) a
          (fun N => ?_) ?_ ?_
        · -- IntegrableOn f (Ioc a (a + twoπ * N)) volume
          have hupper_le : a ≤ a + twoπ * (N : ℝ) := by
            have : 0 ≤ twoπ * (N : ℝ) :=
              mul_nonneg (le_of_lt h2π_pos) (Nat.cast_nonneg _)
            linarith
          have hint_int : IntervalIntegrable f volume a (a + twoπ * (N : ℝ)) := by
            apply AntitoneOn.intervalIntegrable
            rw [Set.uIcc_of_le hupper_le]
            exact hf_anti_on _
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hupper_le).mp hint_int
        · -- Tendsto (b N) atTop atTop
          have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
            tendsto_natCast_atTop_atTop
          have h2 : Filter.Tendsto (fun N : ℕ => twoπ * (N : ℝ)) Filter.atTop Filter.atTop :=
            Filter.Tendsto.const_mul_atTop h2π_pos h1
          exact Filter.tendsto_atTop_add_const_left _ a h2
        · -- Eventually ≤ bound
          refine Filter.Eventually.of_forall (fun N => ?_)
          have hf_norm : ∀ x, ‖f x‖ = f x := fun x => Real.norm_of_nonneg (hf_nonneg x)
          simp only [hf_norm]
          exact hbound N
      -- Convert IntegrableOn (Ioi a) to IntegrableOn (Ici a)
      rw [show (Set.Ici a) = {a} ∪ Set.Ioi a from by
        ext x; simp [Set.mem_Ici, Set.mem_Ioi, eq_comm, le_iff_lt_or_eq]]
      apply MeasureTheory.IntegrableOn.union
      · -- IntegrableOn f {a}
        refine MeasureTheory.integrableOn_singleton ?_ ?_
        · simp
        · simp
      · exact hIoi_int
    -- Hence tsum = 0
    rw [tsum_eq_zero_of_not_summable h_not_summ]
