import Mathlib
import Workspace.Types.LqNorm

open scoped BigOperators
open Workspace.Types.LqNorm

theorem LqNormPartialDerivative_PosBranch_LimitAtZero
    {q : ℝ} (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d)
    (x f : Fin d → ℝ) (j : Fin d)
    (hxj_zero : x j = 0) (hfj_pos : 0 < f j) (hf_nn : ∀ k, 0 ≤ f k)
    (hlq_pos : 0 < lqNorm q (fun k => x k - f k)) :
    HasDerivWithinAt
      (fun t : ℝ => lqNorm q (fun k => Function.update x j t k - f k))
      (-(f j) ^ (q - 1) / (lqNorm q (fun k => x k - f k)) ^ (q - 1))
      (Set.Ici (0 : ℝ)) 0 := by
  -- Setup basic facts
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hfj_ne : f j ≠ 0 := ne_of_gt hfj_pos
  have h_lqq_ne : lqNorm q (fun k => x k - f k) ≠ 0 := ne_of_gt hlq_pos
  have h_lqq_nonneg : 0 ≤ lqNorm q (fun k => x k - f k) := le_of_lt hlq_pos
  -- Define the constant part A = ∑_{k≠j} |x k - f k|^q
  set A : ℝ := ∑ k ∈ Finset.univ.erase j, |x k - f k| ^ q with hA_def
  -- The total sum equals A + (f j)^q (using x j = 0 and f j > 0, so |x j - f j| = |-f j| = f j)
  have h_total_sum : (∑ k, |x k - f k| ^ q) = A + (f j) ^ q := by
    have hj_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
    have h1 : (∑ k, |x k - f k| ^ q) = ∑ k ∈ Finset.univ.erase j, |x k - f k| ^ q
                + |x j - f j| ^ q := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin d))
            (fun k => |x k - f k| ^ q) hj_mem]
    rw [h1, hxj_zero, zero_sub, abs_neg, abs_of_pos hfj_pos]
  -- (lqNorm q (x - f))^q = A + (f j)^q
  have h_lqNorm_q_eq : (lqNorm q (fun k => x k - f k)) ^ q = ∑ k, |x k - f k| ^ q := by
    unfold lqNorm
    rw [← Real.rpow_mul (sum_abs_rpow_nonneg q _), one_div_mul_cancel hq_ne, Real.rpow_one]
  have h_inner_eq : A + (f j) ^ q = (lqNorm q (fun k => x k - f k)) ^ q := by
    rw [← h_total_sum, ← h_lqNorm_q_eq]
  have h_inner_pos : 0 < A + (f j) ^ q := by
    rw [h_inner_eq]
    exact Real.rpow_pos_of_pos hlq_pos q
  have h_inner_ne : A + (f j) ^ q ≠ 0 := ne_of_gt h_inner_pos
  -- Local equality on a nhdsWithin (Set.Ici 0) 0:
  -- for t ∈ [0, f j), the lqNorm equals (A + (f j - t)^q)^(1/q)
  have h_eq_local :
      (fun t : ℝ => lqNorm q (fun k => Function.update x j t k - f k)) =ᶠ[nhdsWithin 0 (Set.Ici (0 : ℝ))]
      (fun t : ℝ => (A + (f j - t) ^ q) ^ ((1 : ℝ) / q)) := by
    -- We use the characterization: ∀ᶠ in nhdsWithin a s ↔ ∀ᶠ in nhds a, x ∈ s → p x.
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Iio (f j), ?_, ?_⟩
    · -- Set.Iio (f j) ∈ nhdsWithin 0 (Set.Ici 0): just need it to be in nhds 0.
      apply mem_nhdsWithin_of_mem_nhds
      exact Iio_mem_nhds hfj_pos
    · -- For t ∈ Iio (f j), the equality holds.
      intro t ht_lt
      have ht_lt' : t < f j := ht_lt
      show lqNorm q (fun k => Function.update x j t k - f k)
        = (A + (f j - t) ^ q) ^ ((1 : ℝ) / q)
      unfold lqNorm
      congr 1
      have hj_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin d))
            (fun k => |Function.update x j t k - f k| ^ q) hj_mem]
      rw [Function.update_self]
      -- Now |t - f j|^q = (f j - t)^q since t - f j < 0
      have h_neg : t - f j < 0 := by linarith
      have h_abs : |t - f j| = f j - t := by
        rw [abs_of_neg h_neg]; ring
      rw [h_abs]
      -- Sum over k ≠ j is unchanged because Function.update at k ≠ j equals x k.
      have h_sum_eq : (∑ k ∈ Finset.univ.erase j,
            |Function.update x j t k - f k| ^ q) = A := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkj : k ≠ j := Finset.ne_of_mem_erase hk
        rw [Function.update_of_ne hkj]
      rw [h_sum_eq]
  -- Compute derivative at 0 of t ↦ A + (f j - t)^q within Set.Ici 0
  -- Step 1: HasDerivAt of t ↦ f j - t at 0 with derivative -1
  have h_sub : HasDerivAt (fun t : ℝ => f j - t) (-1) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    exact h1.const_sub (f j)
  -- Step 2: HasDerivAt of t ↦ (f j - t)^q at 0
  -- Apply rpow_const: HasDerivAt.rpow_const requires h_sub.x ≠ 0 ∨ 1 ≤ q. Since f j ≠ 0 (h_sub at 0 is f j - 0 = f j).
  have h_sub_at_zero : (fun t : ℝ => f j - t) 0 = f j := by simp
  have h_pow : HasDerivAt (fun t : ℝ => (f j - t) ^ q)
      (-1 * q * (f j) ^ (q - 1)) 0 := by
    have h_ne0 : (fun t : ℝ => f j - t) 0 ≠ 0 := by simp [hfj_ne]
    have h := HasDerivAt.rpow_const (p := q) h_sub (Or.inl h_ne0)
    -- h : HasDerivAt (fun y => (f j - y)^q) (-1 * q * (f j - 0)^(q-1)) 0
    have h_simp : (f j - (0 : ℝ)) = f j := by ring
    rw [h_simp] at h
    exact h
  -- Step 3: HasDerivAt of t ↦ A + (f j - t)^q at 0
  have h_A_add : HasDerivAt (fun t : ℝ => A + (f j - t) ^ q)
      (-1 * q * (f j) ^ (q - 1)) 0 := by
    have := h_pow.const_add A
    simpa using this
  -- Step 4: HasDerivAt of t ↦ (A + (f j - t)^q)^(1/q) at 0
  have h_outer : HasDerivAt (fun t : ℝ => (A + (f j - t) ^ q) ^ ((1 : ℝ) / q))
      (-1 * q * (f j) ^ (q - 1) * ((1 : ℝ) / q) *
        (A + (f j - 0) ^ q) ^ ((1 : ℝ) / q - 1)) 0 := by
    have h_at_zero : (fun t : ℝ => A + (f j - t) ^ q) 0 = A + (f j) ^ q := by
      simp
    have h_ne : (fun t : ℝ => A + (f j - t) ^ q) 0 ≠ 0 := by
      rw [h_at_zero]; exact h_inner_ne
    have h := HasDerivAt.rpow_const (p := (1 : ℝ) / q) h_A_add (Or.inl h_ne)
    convert h using 1
  -- Convert HasDerivAt to HasDerivWithinAt
  have h_outer_within : HasDerivWithinAt (fun t : ℝ => (A + (f j - t) ^ q) ^ ((1 : ℝ) / q))
      (-1 * q * (f j) ^ (q - 1) * ((1 : ℝ) / q) *
        (A + (f j - 0) ^ q) ^ ((1 : ℝ) / q - 1)) (Set.Ici (0 : ℝ)) 0 :=
    h_outer.hasDerivWithinAt
  -- Use HasDerivWithinAt.congr_of_eventuallyEq:
  -- HasDerivWithinAt f f' s x → f₁ =ᶠ[nhdsWithin x s] f → f₁ x = f x → HasDerivWithinAt f₁ f' s x
  -- We have HasDerivWithinAt of rpow_form (=: f), and h_eq_local says lqNorm_form =ᶠ rpow_form.
  -- So passing h_eq_local makes lqNorm_form play the role of f₁, and we get HasDerivWithinAt lqNorm_form.
  have h_pointwise : (fun t : ℝ => lqNorm q (fun k => Function.update x j t k - f k)) 0
      = (fun t : ℝ => (A + (f j - t) ^ q) ^ ((1 : ℝ) / q)) 0 := by
    -- At t = 0, Function.update x j 0 = x (since x j = 0).
    have h_upd : Function.update x j (0 : ℝ) = x := by
      ext k
      by_cases hk : k = j
      · subst hk; rw [Function.update_self, hxj_zero]
      · rw [Function.update_of_ne hk]
    show lqNorm q (fun k => Function.update x j 0 k - f k)
        = (A + (f j - 0) ^ q) ^ ((1 : ℝ) / q)
    rw [show (fun k => Function.update x j 0 k - f k) = (fun k => x k - f k) by
          ext k; rw [h_upd]]
    -- now lqNorm q (x - f) = (A + (f j)^q)^(1/q)
    show lqNorm q (fun k => x k - f k) = (A + (f j - 0) ^ q) ^ ((1 : ℝ) / q)
    have : (A + (f j - 0) ^ q) = (lqNorm q (fun k => x k - f k)) ^ q := by
      have : f j - 0 = f j := by ring
      rw [this, h_inner_eq]
    rw [this]
    -- Goal: lqNorm q (x - f) = ((lqNorm q (x - f))^q)^(1/q)
    rw [← Real.rpow_mul h_lqq_nonneg, mul_one_div, div_self hq_ne, Real.rpow_one]
  have h_target : HasDerivWithinAt (fun t : ℝ => lqNorm q (fun k => Function.update x j t k - f k))
      (-1 * q * (f j) ^ (q - 1) * ((1 : ℝ) / q) *
        (A + (f j - 0) ^ q) ^ ((1 : ℝ) / q - 1)) (Set.Ici (0 : ℝ)) 0 :=
    h_outer_within.congr_of_eventuallyEq h_eq_local h_pointwise
  -- Now show the derivative value matches the goal:
  -- -1 * q * (f j)^(q-1) * (1/q) * (A + (f j)^q)^(1/q - 1) = -(f j)^(q-1) / (lqNorm q (x - f))^(q-1)
  convert h_target using 1
  -- Goal: -(f j)^(q-1) / (lqNorm q (x - f))^(q-1)
  --     = -1 * q * (f j)^(q-1) * (1/q) * (A + (f j - 0)^q)^(1/q - 1)
  have h_fj0 : f j - 0 = f j := by ring
  rw [h_fj0]
  rw [h_inner_eq]
  -- Now: ... = -1 * q * (f j)^(q-1) * (1/q) * ((lqNorm q (x - f))^q)^(1/q - 1)
  -- Simplify: q * (1/q) = 1, so: -1 * (f j)^(q-1) * ((lqNorm q (x - f))^q)^(1/q - 1)
  have h_q_simp : (-1 : ℝ) * q * (f j) ^ (q - 1) * ((1 : ℝ) / q)
      = -((f j) ^ (q - 1)) := by
    field_simp
  -- Reorganize the RHS
  have h_pow_simp : ((lqNorm q (fun k => x k - f k)) ^ q) ^ ((1 : ℝ) / q - 1)
      = (lqNorm q (fun k => x k - f k)) ^ (1 - q) := by
    rw [← Real.rpow_mul h_lqq_nonneg]
    congr 1
    field_simp
  have h_neg_pow : (lqNorm q (fun k => x k - f k)) ^ (1 - q)
      = ((lqNorm q (fun k => x k - f k)) ^ (q - 1))⁻¹ := by
    have heq : (1 - q) = -(q - 1) := by ring
    rw [heq, Real.rpow_neg h_lqq_nonneg]
  -- Algebraic manipulation
  rw [show (-1 : ℝ) * q * (f j) ^ (q - 1) * ((1 : ℝ) / q) *
        ((lqNorm q (fun k => x k - f k)) ^ q) ^ ((1 : ℝ) / q - 1)
       = ((-1 : ℝ) * q * (f j) ^ (q - 1) * ((1 : ℝ) / q)) *
         ((lqNorm q (fun k => x k - f k)) ^ q) ^ ((1 : ℝ) / q - 1) by ring]
  rw [h_q_simp, h_pow_simp, h_neg_pow]
  -- Goal: -(f j)^(q-1) / (lqNorm q (x - f))^(q-1) = -((f j)^(q-1)) * ((lqNorm q (x - f))^(q-1))⁻¹
  rw [div_eq_mul_inv, neg_mul]
