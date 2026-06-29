import Mathlib
import Workspace.ProofLemmas.MarkovTailFromMGF
import Workspace.ProofLemmas.MGFTailPointwise
import Workspace.ProofLemmas.NonincreasingTailSummation
import Workspace.ProofLemmas.SharpeningInequalityCheck

open MeasureTheory Real

set_option maxHeartbeats 4000000

/-- Helper: WLOG ξ ≥ 2. Given ξ with |ξ| ≥ 2 and |ξ| ≤ π, we have either ξ ≥ 2 or -ξ ≥ 2.
The negative case can be reduced to the positive case via the substitution s ↦ -s in the tsum,
exploiting evenness of h. -/
private lemma neg_int_tsum_eq (h : ℝ → ℝ) (h_even : ∀ x : ℝ, h (-x) = h x) (ξ : ℝ) :
    (∑' s : ℤ, h (ξ + 2 * Real.pi * (s : ℝ))) =
    (∑' s : ℤ, h ((-ξ) + 2 * Real.pi * (s : ℝ))) := by
  rw [show (∑' s : ℤ, h ((-ξ) + 2 * Real.pi * (s : ℝ))) =
      (∑' s : ℤ, h ((-ξ) + 2 * Real.pi * ((-s : ℤ) : ℝ))) from by
    rw [← (Equiv.neg ℤ).tsum_eq (fun s : ℤ => h ((-ξ) + 2 * Real.pi * (s : ℝ)))]
    rfl]
  apply tsum_congr
  intro s
  have : -ξ + 2 * Real.pi * ((-s : ℤ) : ℝ) = -(ξ + 2 * Real.pi * (s : ℝ)) := by
    push_cast; ring
  rw [this, h_even]

/-- Core argument: bound the periodisation sum, assuming ξ ≥ 2 (the symmetric case). -/
private lemma HFourierKwayBoundFromMGFAndLogConcavity_pos
    (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ → ℝ)
    (h_nn : ∀ x : ℝ, 0 ≤ h x)
    (h_int : MeasureTheory.Integrable h)
    (h_even : ∀ x : ℝ, h (-x) = h x)
    (h_anti : ∀ x y : ℝ, 0 ≤ x → x ≤ y → h y ≤ h x)
    (h_int1 : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp (Real.sqrt (n : ℝ) * u) * h u)
      (Set.Ici (1 : ℝ)))
    (h_mgf1 : (∫ u in Set.Ici (1 : ℝ),
        Real.exp (Real.sqrt (n : ℝ) * u) * h u) ≤ 1)
    (h_tail_int : (∫ η in Set.Ici (1 : ℝ), h η) ≤ Real.exp (-Real.sqrt (n : ℝ)))
    (ξ : ℝ) (hξπ : ξ ≤ Real.pi) (hξ_ge2 : 2 ≤ ξ)
    (h_summ : Summable (fun s : ℤ => h (ξ + 2 * Real.pi * (s : ℝ)))) :
    (∑' s : ℤ, h (ξ + 2 * Real.pi * (s : ℝ))) ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
  set t : ℝ := Real.sqrt (n : ℝ) with ht_def
  have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_one : 1 ≤ t := by
    rw [ht_def]
    have : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn_pos
    simpa using this
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_one
  have ht_nn : 0 ≤ t := le_of_lt ht_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2π_pos : 0 < 2 * Real.pi := by linarith
  have h2π_nn : 0 ≤ 2 * Real.pi := le_of_lt h2π_pos
  have hpi_gt3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h_anti1 : ∀ x y : ℝ, 1 ≤ x → x ≤ y → h y ≤ h x := by
    intro x y hx1 hxy
    exact h_anti x y (le_trans zero_le_one hx1) hxy
  -- Pointwise bound for η ≥ 2 via integral on [η-1, η]
  have h_pointwise_ge2 : ∀ η : ℝ, 2 ≤ η → h η ≤ Real.exp (-t) := by
    intro η hη2
    have hη1 : (1 : ℝ) ≤ η := by linarith
    have hη_minus1 : (1 : ℝ) ≤ η - 1 := by linarith
    have hle : η - 1 ≤ η := by linarith
    -- h(η) = ∫_{η-1}^{η} h(η) du ≤ ∫_{η-1}^{η} h(u) du ≤ ∫_{u≥1} h(u) du ≤ exp(-t)
    have h_int_const : ∫ _u in (η - 1)..η, h η = h η := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    have h_intervalint_h : IntervalIntegrable h MeasureTheory.volume (η - 1) η := by
      have : IntegrableOn h (Set.Icc (η - 1) η) MeasureTheory.volume :=
        h_int.integrableOn
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr this
    have h_intervalint_const : IntervalIntegrable (fun _ => h η) MeasureTheory.volume (η - 1) η :=
      intervalIntegrable_const
    have h_int_bound : ∫ _u in (η - 1)..η, h η ≤ ∫ u in (η - 1)..η, h u := by
      apply intervalIntegral.integral_mono_on hle h_intervalint_const h_intervalint_h
      intro u hu
      apply h_anti
      · linarith [hu.1]
      · exact hu.2
    have h_subset_int : ∫ u in (η - 1)..η, h u ≤ ∫ u in Set.Ici (1 : ℝ), h u := by
      rw [intervalIntegral.integral_of_le hle]
      apply MeasureTheory.setIntegral_mono_set
      · exact h_int.integrableOn
      · exact Filter.Eventually.of_forall (fun x => h_nn x)
      · refine Filter.Eventually.of_forall (fun x hx => ?_)
        exact le_trans hη_minus1 (le_of_lt hx.1)
    calc h η = ∫ _u in (η - 1)..η, h η := h_int_const.symm
      _ ≤ ∫ u in (η - 1)..η, h u := h_int_bound
      _ ≤ ∫ u in Set.Ici (1 : ℝ), h u := h_subset_int
      _ ≤ Real.exp (-t) := h_tail_int
  -- Pointwise sharp bound for η > 1
  have h_pointwise_sharp : ∀ η : ℝ, 1 < η → h η ≤ t / (Real.exp (t * η) - Real.exp t) :=
    fun η hη => MGFTailPointwise h h_nn h_anti1 t ht_pos h_int1 h_mgf1 η hη
  -- For η ≥ π, sharpened bound h(η) ≤ exp(-t)/π via SharpeningInequalityCheck.
  have h_pointwise_sharp_π : ∀ η : ℝ, Real.pi ≤ η → h η ≤ Real.exp (-t) / Real.pi := by
    intro η hηπ
    have hη_gt1 : 1 < η := lt_of_lt_of_le (by linarith) hηπ
    have h_bound1 := h_pointwise_sharp η hη_gt1
    have h_sharp := SharpeningInequalityCheck n hn
    -- h_sharp : π · √n · exp(-(√n·(π-1))) ≤ 1 - exp(-(√n·(π-1)))
    -- Note: √n = t, so this is π · t · exp(-(t·(π-1))) ≤ 1 - exp(-(t·(π-1)))
    -- Multiplying by exp(t·(π-1)) > 0: π · t ≤ exp(t·(π-1)) - 1
    have hexp_pos : 0 < Real.exp (t * (Real.pi - 1)) := Real.exp_pos _
    have h_pi_t_le : Real.pi * t ≤ Real.exp (t * (Real.pi - 1)) - 1 := by
      -- From h_sharp, multiplying both sides by exp(t*(π-1)).
      have h_mul := mul_le_mul_of_nonneg_right h_sharp (le_of_lt hexp_pos)
      -- h_mul: π·√n·exp(-(√n·(π-1)))·exp(t·(π-1)) ≤ (1 - exp(-(√n·(π-1))))·exp(t·(π-1))
      have hcomm : Real.exp (-(t * (Real.pi - 1))) * Real.exp (t * (Real.pi - 1)) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have lhs_eq : Real.pi * t * Real.exp (-(t * (Real.pi - 1))) * Real.exp (t * (Real.pi - 1))
                  = Real.pi * t := by
        rw [mul_assoc, hcomm, mul_one]
      have rhs_eq : (1 - Real.exp (-(t * (Real.pi - 1)))) * Real.exp (t * (Real.pi - 1))
                  = Real.exp (t * (Real.pi - 1)) - 1 := by
        rw [sub_mul, one_mul, hcomm]
      have ht_eq : t = Real.sqrt (n : ℝ) := ht_def
      rw [← ht_eq] at h_mul
      rw [lhs_eq, rhs_eq] at h_mul
      exact h_mul
    -- exp(t·(π-1)) = exp(t·π)/exp(t)
    have hexp_t_pos : 0 < Real.exp t := Real.exp_pos _
    have hexp_t_ne : Real.exp t ≠ 0 := ne_of_gt hexp_t_pos
    have hexp_split : Real.exp (t * (Real.pi - 1)) = Real.exp (t * Real.pi) / Real.exp t := by
      rw [show t * (Real.pi - 1) = t * Real.pi - t from by ring, Real.exp_sub]
    -- exp(t·η) ≥ exp(t·π) since η ≥ π and t ≥ 0
    have hexp_mono : Real.exp (t * Real.pi) ≤ Real.exp (t * η) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hηπ ht_nn)
    -- exp(t·η) - exp(t) > 0
    have hD_pos : 0 < Real.exp (t * η) - Real.exp t := by
      have hη_gt_lt : Real.exp t < Real.exp (t * η) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      linarith
    -- π · t ≤ (exp(t·η) - exp(t)) / exp(t)
    have h_key : Real.pi * t ≤ (Real.exp (t * η) - Real.exp t) / Real.exp t := by
      have h1 : Real.exp (t * Real.pi) / Real.exp t - 1 ≤
                (Real.exp (t * η) - Real.exp t) / Real.exp t := by
        rw [div_sub_one hexp_t_ne]
        apply div_le_div_of_nonneg_right _ (le_of_lt hexp_t_pos)
        linarith
      have h_pi_t_le' : Real.pi * t ≤ Real.exp (t * Real.pi) / Real.exp t - 1 := by
        rw [hexp_split] at h_pi_t_le; exact h_pi_t_le
      linarith
    -- Hence h(η) ≤ t / (exp(t·η) - exp(t)) ≤ exp(-t)/π
    have h_target : t / (Real.exp (t * η) - Real.exp t) ≤ Real.exp (-t) / Real.pi := by
      rw [Real.exp_neg]
      rw [div_le_div_iff₀ hD_pos hpi_pos]
      -- Goal: t * π ≤ (exp t)⁻¹ * (exp(t·η) - exp(t))
      rw [show (Real.exp t)⁻¹ * (Real.exp (t * η) - Real.exp t) =
            (Real.exp (t * η) - Real.exp t) / Real.exp t from by
          rw [div_eq_inv_mul]]
      linarith [h_key]
    linarith
  -- Decompose the sum over ℤ.
  -- Define F : ℤ → ℝ, F s := h (ξ + 2π·s).
  set F : ℤ → ℝ := fun s : ℤ => h (ξ + 2 * Real.pi * (s : ℝ)) with hF_def
  -- The sum over ℤ.
  -- F restricted to nat: F ↑n = h (ξ + 2π·n)
  -- F restricted to neg-(n+1): F (-(↑n+1)) = h(ξ + 2π·(-(n+1))) = h(ξ - 2π·(n+1))
  have h_summ_pos_F : Summable (fun n : ℕ => F (n : ℤ)) := by
    have hi : Function.Injective (fun n : ℕ => (n : ℤ)) := by
      intro a b hab
      simpa using hab
    exact h_summ.comp_injective hi
  have h_summ_neg_F : Summable (fun n : ℕ => F (-((n : ℤ) + 1))) := by
    have hi : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
      intro a b hab
      have h0 : ((a : ℤ) + 1 : ℤ) = (b : ℤ) + 1 := by linarith
      have h2 : (a : ℤ) = b := by linarith
      exact_mod_cast h2
    exact h_summ.comp_injective hi
  have h_summ_pos' : Summable (fun n : ℕ => h (ξ + 2 * Real.pi * (n : ℝ))) := by
    convert h_summ_pos_F using 1
  have h_summ_neg' : Summable (fun n : ℕ => h (ξ - 2 * Real.pi * ((n : ℝ) + 1))) := by
    convert h_summ_neg_F using 1
    funext n
    show h (ξ - 2 * Real.pi * ((n : ℝ) + 1)) = h (ξ + 2 * Real.pi * ((-((n : ℤ) + 1) : ℤ) : ℝ))
    push_cast; congr 1; ring
  have h_decomp_F : (∑' s : ℤ, F s) =
      (∑' n : ℕ, F (n : ℤ)) + (∑' n : ℕ, F (-((n : ℤ) + 1))) :=
    tsum_of_nat_of_neg_add_one h_summ_pos_F h_summ_neg_F
  have h_decomp : (∑' s : ℤ, h (ξ + 2 * Real.pi * (s : ℝ))) =
      (∑' n : ℕ, h (ξ + 2 * Real.pi * (n : ℝ))) +
      (∑' n : ℕ, h (ξ - 2 * Real.pi * ((n : ℝ) + 1))) := by
    rw [h_decomp_F]
    congr 1
    apply tsum_congr; intro n
    show h (ξ + 2 * Real.pi * ((-((n : ℤ) + 1) : ℤ) : ℝ)) = h (ξ - 2 * Real.pi * ((n : ℝ) + 1))
    push_cast; congr 1; ring
  rw [h_decomp]
  -- Split positive sum: n=0 (h(ξ)) + tail (n ≥ 1)
  -- Define a function f_pos : ℕ → ℝ with f_pos n = h(ξ + 2π·n).
  set f_pos : ℕ → ℝ := fun n : ℕ => h (ξ + 2 * Real.pi * (n : ℝ)) with hf_pos_def
  have h_summ_shift_pos_f : Summable (fun n : ℕ => f_pos (n + 1)) := by
    -- f_pos (n + 1) = h (ξ + 2π·(n+1)).
    have heq : (fun n : ℕ => f_pos (n + 1)) =
               (fun n : ℕ => h (ξ + 2 * Real.pi * ((n : ℝ) + 1))) := by
      funext n; show h (ξ + 2 * Real.pi * ((n + 1 : ℕ) : ℝ)) = _
      push_cast; ring_nf
    rw [heq]
    -- This is h_summ_pos' shifted by 1.
    have hi : Function.Injective (fun n : ℕ => n + 1) := by
      intro a b hab; exact Nat.succ_injective hab
    have := h_summ_pos'.comp_injective hi
    convert this using 1
    funext n
    show h (ξ + 2 * Real.pi * ((n : ℝ) + 1)) = h (ξ + 2 * Real.pi * ((n + 1 : ℕ) : ℝ))
    push_cast; ring_nf
  have h_split_pos : (∑' n : ℕ, h (ξ + 2 * Real.pi * (n : ℝ))) =
      h ξ + (∑' n : ℕ, h (ξ + 2 * Real.pi * ((n : ℝ) + 1))) := by
    have key := tsum_eq_zero_add' h_summ_shift_pos_f
    -- key : ∑' b : ℕ, f_pos b = f_pos 0 + ∑' b, f_pos (b + 1)
    -- f_pos 0 = h (ξ + 2π·0) = h ξ.
    have hf0 : f_pos 0 = h ξ := by
      show h (ξ + 2 * Real.pi * ((0 : ℕ) : ℝ)) = h ξ
      push_cast; ring_nf
    have hf_eq : ∀ n : ℕ, f_pos (n + 1) = h (ξ + 2 * Real.pi * ((n : ℝ) + 1)) := by
      intro n
      show h (ξ + 2 * Real.pi * ((n + 1 : ℕ) : ℝ)) = h (ξ + 2 * Real.pi * ((n : ℝ) + 1))
      push_cast; ring_nf
    have h_lhs_eq : (∑' b : ℕ, f_pos b) = (∑' n : ℕ, h (ξ + 2 * Real.pi * (n : ℝ))) := by rfl
    have h_rhs_eq : (∑' b : ℕ, f_pos (b + 1)) =
                    (∑' n : ℕ, h (ξ + 2 * Real.pi * ((n : ℝ) + 1))) := by
      apply tsum_congr; exact hf_eq
    rw [← h_lhs_eq]
    rw [key, hf0, h_rhs_eq]
  -- Split negative sum: n=0 (h(ξ - 2π)) + tail (n ≥ 1, h(ξ - 2π(n+2)))
  have h_summ_shift_neg : Summable (fun n : ℕ => h (ξ - 2 * Real.pi * ((n : ℝ) + 2))) := by
    have heq : (fun n : ℕ => h (ξ - 2 * Real.pi * (((n + 1 : ℕ) : ℝ) + 1))) =
               (fun n : ℕ => h (ξ - 2 * Real.pi * ((n : ℝ) + 2))) := by
      funext n; push_cast; ring_nf
    rw [← heq]
    exact h_summ_neg'.comp_injective Nat.succ_injective
  have h_split_neg : (∑' n : ℕ, h (ξ - 2 * Real.pi * ((n : ℝ) + 1))) =
      h (ξ - 2 * Real.pi) +
      (∑' n : ℕ, h (ξ - 2 * Real.pi * ((n : ℝ) + 2))) := by
    have key := tsum_eq_zero_add' (f := fun n : ℕ => h (ξ - 2 * Real.pi * ((n : ℝ) + 1)))
      (by
        have heq : (fun n : ℕ => h (ξ - 2 * Real.pi * (((n + 1 : ℕ) : ℝ)+1))) =
                   (fun n : ℕ => h (ξ - 2 * Real.pi * ((n : ℝ) + 2))) := by
          funext n; push_cast; ring_nf
        rw [heq]
        exact h_summ_shift_neg)
    have hξ0 : h (ξ - 2 * Real.pi * (((0 : ℕ) : ℝ) + 1)) = h (ξ - 2 * Real.pi) := by
      push_cast; ring_nf
    have hreshape : (fun n : ℕ => h (ξ - 2 * Real.pi * (((n + 1 : ℕ) : ℝ) + 1))) =
                    (fun n : ℕ => h (ξ - 2 * Real.pi * ((n : ℝ) + 2))) := by
      funext n; push_cast; ring_nf
    rw [← hξ0]
    rw [← hreshape] at *
    exact key
  rw [h_split_pos, h_split_neg]
  -- Bound h(ξ) ≤ exp(-t)
  have hξ_bound : h ξ ≤ Real.exp (-t) := h_pointwise_ge2 ξ hξ_ge2
  -- Bound h(ξ - 2π): by evenness, h(ξ - 2π) = h(2π - ξ). 2π - ξ ≥ π. Use sharpened.
  have h2π_minus_ξ_ge_π : Real.pi ≤ 2 * Real.pi - ξ := by linarith
  have h_sym_neg : h (ξ - 2 * Real.pi) = h (2 * Real.pi - ξ) := by
    have heq : -(ξ - 2 * Real.pi) = 2 * Real.pi - ξ := by ring
    rw [← heq, h_even]
  have h_neg_sharp_bound : h (ξ - 2 * Real.pi) ≤ Real.exp (-t) / Real.pi := by
    rw [h_sym_neg]
    exact h_pointwise_sharp_π (2 * Real.pi - ξ) h2π_minus_ξ_ge_π
  -- Bound positive tail: ∑'_n h(ξ + 2π(n+1)) ≤ exp(-t)/(2π) by NonincreasingTailSummation.
  have hξ_pos : 0 < ξ := by linarith
  have h_anti_from_ξ : ∀ x y : ℝ, ξ ≤ x → x ≤ y → h y ≤ h x := by
    intro x y hxξ hxy
    exact h_anti x y (le_trans (le_of_lt hξ_pos) hxξ) hxy
  have h_NTS_pos := NonincreasingTailSummation h h_nn ξ hξ_pos h_anti_from_ξ
  -- Reindex: ∑' s : {s : ℕ // 1 ≤ s}, h(ξ + 2π·s.val) = ∑' n : ℕ, h(ξ + 2π·(n+1))
  have h_reindex_pos : (∑' s : {s : ℕ // 1 ≤ s}, h (ξ + 2 * Real.pi * (s.val : ℝ))) =
      (∑' n : ℕ, h (ξ + 2 * Real.pi * ((n : ℝ) + 1))) := by
    let e : ℕ ≃ {s : ℕ // 1 ≤ s} :=
      { toFun := fun n => ⟨n + 1, Nat.succ_le_succ (Nat.zero_le _)⟩
        invFun := fun s => s.val - 1
        left_inv := fun n => by simp
        right_inv := fun s => by
          obtain ⟨s, hs⟩ := s
          simp; omega }
    rw [← e.tsum_eq (fun s : {s : ℕ // 1 ≤ s} => h (ξ + 2 * Real.pi * (s.val : ℝ)))]
    apply tsum_congr
    intro n
    show h (ξ + 2 * Real.pi * (((n + 1 : ℕ) : ℕ) : ℝ)) = h (ξ + 2 * Real.pi * ((n : ℝ) + 1))
    push_cast; ring_nf
  rw [h_reindex_pos] at h_NTS_pos
  have h_int_ξ_le : (∫ u in Set.Ici ξ, h u) ≤ Real.exp (-t) := by
    have h_subset : Set.Ici ξ ⊆ Set.Ici (1 : ℝ) := by
      intro x hx; simp [Set.mem_Ici] at *; linarith
    calc (∫ u in Set.Ici ξ, h u)
        ≤ (∫ u in Set.Ici (1 : ℝ), h u) := by
          apply MeasureTheory.setIntegral_mono_set
          · exact h_int.integrableOn
          · exact Filter.Eventually.of_forall (fun x => h_nn x)
          · exact Filter.Eventually.of_forall h_subset
      _ ≤ Real.exp (-t) := h_tail_int
  have h_inv2π_nn : 0 ≤ (1 / (2 * Real.pi)) := by positivity
  have h_pos_tail_bound :
      (∑' n : ℕ, h (ξ + 2 * Real.pi * ((n : ℝ) + 1))) ≤
      Real.exp (-t) / (2 * Real.pi) := by
    calc (∑' n : ℕ, h (ξ + 2 * Real.pi * ((n : ℝ) + 1)))
        ≤ 1 / (2 * Real.pi) * ∫ u in Set.Ici ξ, h u := h_NTS_pos
      _ ≤ 1 / (2 * Real.pi) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left h_int_ξ_le h_inv2π_nn
      _ = Real.exp (-t) / (2 * Real.pi) := by field_simp
  -- Bound negative tail (n ≥ 1): ∑'_n h(ξ - 2π(n+2)).
  -- By evenness: h(ξ - 2π(n+2)) = h(2π(n+2) - ξ) = h((2π - ξ) + 2π·(n+1)).
  have h_neg_tail_eq : ∀ n : ℕ, h (ξ - 2 * Real.pi * ((n : ℝ) + 2)) =
      h ((2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1)) := by
    intro n
    have heq : -(ξ - 2 * Real.pi * ((n : ℝ) + 2)) =
               (2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1) := by ring
    rw [← heq, h_even]
  rw [tsum_congr h_neg_tail_eq]
  -- Apply NonincreasingTailSummation at a = 2π - ξ ≥ π ≥ 1.
  have ha_pos : 0 < 2 * Real.pi - ξ := by linarith
  have h_anti_from_a : ∀ x y : ℝ, 2 * Real.pi - ξ ≤ x → x ≤ y → h y ≤ h x := by
    intro x y hxa hxy
    exact h_anti x y (le_trans (le_of_lt ha_pos) hxa) hxy
  have h_NTS_neg := NonincreasingTailSummation h h_nn (2 * Real.pi - ξ) ha_pos h_anti_from_a
  have h_reindex_neg : (∑' s : {s : ℕ // 1 ≤ s},
        h ((2 * Real.pi - ξ) + 2 * Real.pi * (s.val : ℝ))) =
      (∑' n : ℕ, h ((2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1))) := by
    let e : ℕ ≃ {s : ℕ // 1 ≤ s} :=
      { toFun := fun n => ⟨n + 1, Nat.succ_le_succ (Nat.zero_le _)⟩
        invFun := fun s => s.val - 1
        left_inv := fun n => by simp
        right_inv := fun s => by
          obtain ⟨s, hs⟩ := s
          simp; omega }
    rw [← e.tsum_eq (fun s : {s : ℕ // 1 ≤ s} =>
        h ((2 * Real.pi - ξ) + 2 * Real.pi * (s.val : ℝ)))]
    apply tsum_congr
    intro n
    show h ((2 * Real.pi - ξ) + 2 * Real.pi * (((n + 1 : ℕ) : ℕ) : ℝ)) =
         h ((2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1))
    push_cast; ring_nf
  rw [h_reindex_neg] at h_NTS_neg
  have h_int_a_le : (∫ u in Set.Ici (2 * Real.pi - ξ), h u) ≤ Real.exp (-t) := by
    have h_subset : Set.Ici (2 * Real.pi - ξ) ⊆ Set.Ici (1 : ℝ) := by
      intro x hx; simp [Set.mem_Ici] at *; linarith
    calc (∫ u in Set.Ici (2 * Real.pi - ξ), h u)
        ≤ (∫ u in Set.Ici (1 : ℝ), h u) := by
          apply MeasureTheory.setIntegral_mono_set
          · exact h_int.integrableOn
          · exact Filter.Eventually.of_forall (fun x => h_nn x)
          · exact Filter.Eventually.of_forall h_subset
      _ ≤ Real.exp (-t) := h_tail_int
  have h_neg_tail_bound :
      (∑' n : ℕ, h ((2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1))) ≤
      Real.exp (-t) / (2 * Real.pi) := by
    calc (∑' n : ℕ, h ((2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1)))
        ≤ 1 / (2 * Real.pi) * ∫ u in Set.Ici (2 * Real.pi - ξ), h u := h_NTS_neg
      _ ≤ 1 / (2 * Real.pi) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left h_int_a_le h_inv2π_nn
      _ = Real.exp (-t) / (2 * Real.pi) := by field_simp
  -- Final assembly:
  have hexp_t_pos : 0 < Real.exp (-t) := Real.exp_pos _
  have h_pi_ge_2 : 2 ≤ Real.pi := by linarith
  have h_2_div_pi_le_1 : 2 / Real.pi ≤ 1 := by
    rw [div_le_one hpi_pos]; exact h_pi_ge_2
  calc h ξ + (∑' n : ℕ, h (ξ + 2 * Real.pi * ((n : ℝ) + 1))) +
        (h (ξ - 2 * Real.pi) +
          (∑' n : ℕ, h ((2 * Real.pi - ξ) + 2 * Real.pi * ((n : ℝ) + 1))))
      ≤ Real.exp (-t) + Real.exp (-t) / (2 * Real.pi) +
        (Real.exp (-t) / Real.pi + Real.exp (-t) / (2 * Real.pi)) := by gcongr
    _ = Real.exp (-t) * (1 + 2 / Real.pi) := by field_simp; ring
    _ ≤ Real.exp (-t) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hexp_t_pos)
        linarith
    _ = 2 * Real.exp (-t) := by ring

theorem HFourierKwayBoundFromMGFAndLogConcavity :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (h : ℝ → ℝ),
        (∀ x : ℝ, 0 ≤ h x) →
        MeasureTheory.Integrable h →
        (∀ x : ℝ, h (-x) = h x) →
        (∀ x y : ℝ, 0 ≤ x → x ≤ y → h y ≤ h x) →
        MeasureTheory.IntegrableOn
          (fun η : ℝ => Real.exp (Real.sqrt (n : ℝ) * η) * h η)
          (Set.Ici (0 : ℝ)) →
        (∫ η in Set.Ici (0 : ℝ),
            Real.exp (Real.sqrt (n : ℝ) * η) * h η) ≤ 1 →
        MeasureTheory.IntegrableOn
          (fun u : ℝ => Real.exp (Real.sqrt (n : ℝ) * u) * h u)
          (Set.Ici (1 : ℝ)) →
        (∫ u in Set.Ici (1 : ℝ),
            Real.exp (Real.sqrt (n : ℝ) * u) * h u) ≤ 1 →
        ∀ (ξ : ℝ), |ξ| ≤ Real.pi → 2 ≤ |ξ| →
          Summable (fun s : ℤ => h (ξ + 2 * Real.pi * (s : ℝ))) →
          (∑' s : ℤ, h (ξ + 2 * Real.pi * (s : ℝ)))
            ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
  intro n hn h h_nn h_int h_even h_anti h_int0 h_mgf0 h_int1 h_mgf1 ξ hξπ hξ2 h_summ
  set t : ℝ := Real.sqrt (n : ℝ) with ht_def
  have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_one : 1 ≤ t := by
    rw [ht_def]
    have : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn_pos
    simpa using this
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_one
  have ht_nn : 0 ≤ t := le_of_lt ht_pos
  -- Markov tail ∫_{η ≥ 1} h(η) ≤ exp(-t)
  have h_tail_int : (∫ η in Set.Ici (1 : ℝ), h η) ≤ Real.exp (-t) := by
    have key := MarkovTailFromMGF h h_nn h_int t ht_nn 1 zero_le_one 1 zero_le_one
      h_int0 h_mgf0
    -- key: ∫_{η ≥ 1} h(η) ≤ 1 * exp(-(t·1)) = exp(-t)
    have heq : (1 : ℝ) * Real.exp (-(t * 1)) = Real.exp (-t) := by ring_nf
    linarith [heq ▸ key]
  -- Reduce to ξ ≥ 2 using evenness.
  by_cases hξ_sign : 0 ≤ ξ
  · -- ξ ≥ 0, so ξ ≥ 2
    have hξ_ge2 : 2 ≤ ξ := by rw [abs_of_nonneg hξ_sign] at hξ2; exact hξ2
    have hξπ' : ξ ≤ Real.pi := by rw [abs_of_nonneg hξ_sign] at hξπ; exact hξπ
    exact HFourierKwayBoundFromMGFAndLogConcavity_pos n hn h h_nn h_int h_even h_anti
      h_int1 h_mgf1 h_tail_int ξ hξπ' hξ_ge2 h_summ
  · -- ξ < 0, so -ξ ≥ 2
    push_neg at hξ_sign
    have hξ_le_neg2 : ξ ≤ -2 := by
      rw [abs_of_neg hξ_sign] at hξ2; linarith
    have hξπ' : -Real.pi ≤ ξ := by
      rw [abs_of_neg hξ_sign] at hξπ; linarith
    -- Replace ξ with -ξ via the substitution s ↦ -s.
    have h_eq := neg_int_tsum_eq h h_even ξ
    rw [h_eq]
    -- Now apply the positive lemma to -ξ.
    have h_summ' : Summable (fun s : ℤ => h ((-ξ) + 2 * Real.pi * (s : ℝ))) := by
      -- Reindex via s ↦ -s. Use evenness: h((-ξ) + 2π·s) = h(ξ + 2π·(-s)).
      have hcomp : (fun s : ℤ => h ((-ξ) + 2 * Real.pi * (s : ℝ))) =
          (fun s : ℤ => h (ξ + 2 * Real.pi * ((Equiv.neg ℤ) s : ℝ))) := by
        funext s
        have heq : (-ξ) + 2 * Real.pi * (s : ℝ) =
            -(ξ + 2 * Real.pi * (((Equiv.neg ℤ) s : ℤ) : ℝ)) := by
          simp [Equiv.neg]; push_cast; ring
        rw [heq, h_even]
      rw [hcomp]
      exact h_summ.comp_injective (Equiv.injective _)
    have h_neg_ξ_ge2 : 2 ≤ -ξ := by linarith
    have h_neg_ξ_le_π : -ξ ≤ Real.pi := by linarith
    exact HFourierKwayBoundFromMGFAndLogConcavity_pos n hn h h_nn h_int h_even h_anti
      h_int1 h_mgf1 h_tail_int (-ξ) h_neg_ξ_le_π h_neg_ξ_ge2 h_summ'
