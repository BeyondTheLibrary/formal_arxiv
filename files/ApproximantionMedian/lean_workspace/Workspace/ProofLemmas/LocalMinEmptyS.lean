import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LambdaDeltaIdentity

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists
open Workspace.ProofLemmas.LambdaDeltaIdentity

namespace LocalMinEmptyS_Aux2

/-- Helper: For w ≥ 0, q > 1, lambda ∈ (0,1), with K = (1 - lambda^(q/(q-1)))^((q-1)/q),
    we have `(w^q + 1)^(1/q) ≥ K + lambda * w`. Proven via 2-component Hölder. -/
lemma key_holder_one_dim
    {q : ℝ} (hq : 1 < q) {lambda : ℝ} (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {w : ℝ} (hw : 0 ≤ w) :
    (1 - lambda ^ (q / (q - 1))) ^ ((q - 1) / q) + lambda * w
      ≤ (w ^ q + 1) ^ ((1 : ℝ) / q) := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_sub_pos : 0 < q - 1 := by linarith
  have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hq_sub_pos
  set p : ℝ := q / (q - 1) with hp_def
  have hp_pos : 0 < p := by simp [hp_def]; exact div_pos hq_pos hq_sub_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hp_gt1 : 1 < p := by
    rw [hp_def]
    rw [lt_div_iff₀ hq_sub_pos]
    linarith
  have hpinv_q : p⁻¹ + q⁻¹ = 1 := by
    rw [hp_def]
    field_simp
    ring
  have h_hc : Real.HolderConjugate p q := by
    rw [Real.holderConjugate_iff]
    exact ⟨hp_gt1, hpinv_q⟩
  -- lambda^p = lambda^(q/(q-1))
  set lp : ℝ := lambda ^ p with hlp_def
  have hlam_nn : (0 : ℝ) ≤ lambda := le_of_lt hlam0
  have hlp_pos : 0 < lp := Real.rpow_pos_of_pos hlam0 _
  have hlp_nn : 0 ≤ lp := le_of_lt hlp_pos
  -- lambda^p ≤ 1
  have hlp_le_one : lp ≤ 1 := by
    rw [hlp_def]
    have h1 : lambda ^ p ≤ lambda ^ (0 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge hlam0 (le_of_lt hlam1)
      linarith
    simpa using h1
  have h_one_sub_lp_nn : 0 ≤ 1 - lp := by linarith
  -- K = (1 - lp)^((q-1)/q)
  set K : ℝ := (1 - lp) ^ ((q - 1) / q) with hK_def
  have hK_nn : 0 ≤ K := Real.rpow_nonneg h_one_sub_lp_nn _
  let fH : Fin 2 → ℝ := fun i => if i = 0 then lambda else K
  let gH : Fin 2 → ℝ := fun i => if i = 0 then w else 1
  have hfH_nn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ fH i := by
    intro i _
    fin_cases i
    · simp [fH]; exact hlam_nn
    · simp [fH]; exact hK_nn
  have hgH_nn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ gH i := by
    intro i _
    fin_cases i
    · simp [gH]; exact hw
    · simp [gH]
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg
    (Finset.univ : Finset (Fin 2)) h_hc hfH_nn hgH_nn
  -- Compute the sums explicitly
  have hsum_fg : ∑ i, fH i * gH i = lambda * w + K * 1 := by
    rw [Fin.sum_univ_two]
    simp [fH, gH]
  have hsum_f : ∑ i, fH i ^ p = lambda ^ p + K ^ p := by
    rw [Fin.sum_univ_two]
    simp [fH]
  have hsum_g : ∑ i, gH i ^ q = w ^ q + 1 ^ q := by
    rw [Fin.sum_univ_two]
    simp [gH]
  rw [hsum_fg, hsum_f, hsum_g] at hHolder
  -- Show lambda^p + K^p = 1.
  have hKp : K ^ p = 1 - lp := by
    rw [hK_def]
    rw [← Real.rpow_mul h_one_sub_lp_nn]
    have hprod : ((q - 1) / q) * p = 1 := by
      rw [hp_def]; field_simp
    rw [hprod, Real.rpow_one]
  have hsum_one : lambda ^ p + K ^ p = 1 := by
    rw [hKp, ← hlp_def]; ring
  rw [hsum_one] at hHolder
  have h_one_pinv : (1 : ℝ) ^ (1 / p) = 1 := Real.one_rpow _
  rw [h_one_pinv, one_mul] at hHolder
  have h_one_q : (1 : ℝ) ^ q = 1 := Real.one_rpow _
  rw [h_one_q] at hHolder
  rw [mul_one] at hHolder
  linarith [hHolder]

/-- Helper: For u ≥ v ≥ 0 and q ≥ 1, `u^q ≥ (u-v)^q + v^q`. -/
lemma sub_rpow_le {q : ℝ} (hq : 1 ≤ q) {u v : ℝ} (hv : 0 ≤ v) (huv : v ≤ u) :
    (u - v) ^ q + v ^ q ≤ u ^ q := by
  have h_uvnn : 0 ≤ u - v := by linarith
  have h := Real.add_rpow_le_rpow_add h_uvnn hv hq
  have heq : (u - v) + v = u := by ring
  rw [heq] at h
  exact h

end LocalMinEmptyS_Aux2

open LocalMinEmptyS_Aux2

theorem LocalMinEmptyS
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (T : Finset (Fin d)) (hT_ne : T.Nonempty)
    (c' : ℝ) (hc' : 1 < c')
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j ∈ T, -(p_star j) = f j / (c' - 1))
    (hp_out : ∀ j ∉ T, p_star j = 0)
    (hp_nonpos : ∀ j, p_star j ≤ 0) :
    (1 - lambda ^ (q / (q - 1))) ^ ((q - 1) / q) ≤ g_lambda q lambda f p_star := by
  classical
  have hq_le : 1 ≤ q := le_of_lt hq
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_inv_pos : 0 < 1 / q := by positivity
  have hq_inv_nn : 0 ≤ 1 / q := le_of_lt hq_inv_pos
  have hc'_sub_pos : 0 < c' - 1 := by linarith
  have hc'_sub_ne : c' - 1 ≠ 0 := ne_of_gt hc'_sub_pos
  have hc'_pos : 0 < c' := by linarith
  -- Set c = c'/(c'-1) > 1.
  set c : ℝ := c' / (c' - 1) with hc_def
  have hc_pos : 0 < c := div_pos hc'_pos hc'_sub_pos
  have hc_gt1 : 1 < c := by
    rw [hc_def, lt_div_iff₀ hc'_sub_pos]; linarith
  have hc_nn : 0 ≤ c := le_of_lt hc_pos
  have hc_sub1 : c - 1 = 1 / (c' - 1) := by
    rw [hc_def]; field_simp; ring
  -- |p_star j| for j ∈ T equals f j / (c'-1).
  have habs_in : ∀ j ∈ T, |p_star j| = f j / (c' - 1) := by
    intro j hj
    have h1 : -(p_star j) = f j / (c' - 1) := hp_in j hj
    have h2 : p_star j = -(f j / (c' - 1)) := by linarith
    rw [h2, abs_neg]
    have h3 : 0 ≤ f j / (c' - 1) := div_nonneg (hf_nn j) (le_of_lt hc'_sub_pos)
    rw [abs_of_nonneg h3]
  have habs_out : ∀ j ∉ T, |p_star j| = 0 := by
    intro j hj
    rw [hp_out j hj, abs_zero]
  -- |p_star j - f j| for j ∈ T equals f j * c'/(c'-1) = c * f j.
  -- For j ∉ T equals f j.
  have hsub_in : ∀ j ∈ T, |p_star j - f j| = c * f j := by
    intro j hj
    have h1 : -(p_star j) = f j / (c' - 1) := hp_in j hj
    have h2 : p_star j = -(f j / (c' - 1)) := by linarith
    rw [h2]
    have h3 : -(f j / (c' - 1)) - f j = -(f j * (c'/(c'-1))) := by
      field_simp
      ring
    rw [h3, abs_neg]
    have h4 : 0 ≤ f j * c := mul_nonneg (hf_nn j) hc_nn
    have heq : f j * (c'/(c'-1)) = f j * c := by rw [hc_def]
    rw [heq]
    rw [abs_of_nonneg h4]
    ring
  have hsub_out : ∀ j ∉ T, |p_star j - f j| = f j := by
    intro j hj
    rw [hp_out j hj, zero_sub, abs_neg]
    rw [abs_of_nonneg (hf_nn j)]
  -- Define S_T = ∑ j ∈ T, f_j ^ q
  set S_T : ℝ := ∑ j ∈ T, (f j) ^ q with hST_def
  have hST_nn : 0 ≤ S_T := by
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (hf_nn j) q
  -- 1 - S_T = ∑ j ∉ T (over univ \ T), f_j ^ q
  have hST_le_one : S_T ≤ 1 := by
    rw [← hf_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact T.subset_univ
    · intro j _ _
      exact Real.rpow_nonneg (hf_nn j) q
  -- Compute lqNorm q p_star ^ q = (c-1)^q * S_T
  have h_pstar_norm_pow : (∑ j, |p_star j| ^ q) = (c - 1) ^ q * S_T := by
    rw [hST_def]
    rw [← Finset.sum_compl_add_sum T (fun j => |p_star j| ^ q)]
    have h_left : ∑ j ∈ Tᶜ, |p_star j| ^ q = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjT : j ∉ T := Finset.mem_compl.mp hj
      rw [habs_out j hjT]
      exact Real.zero_rpow hq_ne
    rw [h_left, zero_add]
    have h_right : ∑ j ∈ T, |p_star j| ^ q = ∑ j ∈ T, ((c - 1) ^ q) * (f j) ^ q := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [habs_in j hj]
      have h1 : f j / (c' - 1) = (1 / (c' - 1)) * f j := by ring
      rw [h1]
      have h2 : 1 / (c' - 1) = c - 1 := by rw [hc_sub1]
      rw [h2]
      have h_cm1 : 0 ≤ c - 1 := by linarith
      have h_fj : 0 ≤ f j := hf_nn j
      rw [Real.mul_rpow h_cm1 h_fj]
    rw [h_right, ← Finset.mul_sum]
  -- Compute lqNorm q (p_star - f) ^ q = c^q * S_T + (1 - S_T)
  have h_psf_norm_pow : (∑ j, |p_star j - f j| ^ q) = c ^ q * S_T + (1 - S_T) := by
    rw [← Finset.sum_compl_add_sum T (fun j => |p_star j - f j| ^ q)]
    have h_left : ∑ j ∈ Tᶜ, |p_star j - f j| ^ q = 1 - S_T := by
      have heq : ∑ j ∈ Tᶜ, |p_star j - f j| ^ q = ∑ j ∈ Tᶜ, (f j) ^ q := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjT : j ∉ T := Finset.mem_compl.mp hj
        rw [hsub_out j hjT]
      rw [heq]
      have hsum_split : ∑ j ∈ T, (f j) ^ q + ∑ j ∈ Tᶜ, (f j) ^ q = 1 := by
        rw [add_comm]
        rw [Finset.sum_compl_add_sum T (fun j => (f j) ^ q)]
        exact hf_sum
      linarith [hsum_split, hST_def]
    rw [h_left]
    have h_right : ∑ j ∈ T, |p_star j - f j| ^ q = c ^ q * S_T := by
      have heq : ∑ j ∈ T, |p_star j - f j| ^ q = ∑ j ∈ T, c ^ q * (f j) ^ q := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsub_in j hj]
        rw [Real.mul_rpow hc_nn (hf_nn j)]
      rw [heq, ← Finset.mul_sum]
    rw [h_right]
    ring
  -- Now compute lqNorm q p_star and lqNorm q (p_star - f) using these.
  -- Define u = c * S_T^(1/q), v = S_T^(1/q).
  set v : ℝ := S_T ^ ((1 : ℝ) / q) with hv_def
  have hv_nn : 0 ≤ v := Real.rpow_nonneg hST_nn _
  -- v^q = S_T
  have hv_q : v ^ q = S_T := by
    rw [hv_def, ← Real.rpow_mul hST_nn]
    rw [one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
  -- v ≤ 1 since S_T ≤ 1 and (·)^(1/q) is monotone on [0, ∞)
  have hv_le_one : v ≤ 1 := by
    rw [hv_def]
    have h1 : S_T ^ ((1 : ℝ) / q) ≤ (1 : ℝ) ^ ((1 : ℝ) / q) :=
      Real.rpow_le_rpow hST_nn hST_le_one hq_inv_nn
    rw [Real.one_rpow] at h1
    exact h1
  set u : ℝ := c * v with hu_def
  have hu_nn : 0 ≤ u := mul_nonneg hc_nn hv_nn
  have hu_ge_v : v ≤ u := by
    rw [hu_def]
    nlinarith [hv_nn, hc_gt1]
  -- u^q = c^q * v^q = c^q * S_T
  have hu_q : u ^ q = c ^ q * S_T := by
    rw [hu_def, Real.mul_rpow hc_nn hv_nn, hv_q]
  -- lqNorm q (p_star - f) ^ q = u^q + 1 - v^q = u^q + (1 - v^q)
  have h_psf_pow_eq : (∑ j, |p_star j - f j| ^ q) = u ^ q + (1 - v ^ q) := by
    rw [h_psf_norm_pow, hu_q, hv_q]
  -- Bound: u^q ≥ (u-v)^q + v^q  (so u^q + 1 - v^q ≥ (u-v)^q + 1).
  have h_uv_bound : (u - v) ^ q + 1 ≤ u ^ q + (1 - v ^ q) := by
    have h := sub_rpow_le hq_le hv_nn hu_ge_v
    -- h: (u - v)^q + v^q ≤ u^q
    linarith
  -- (∑ j, |p_star j - f j|^q)^(1/q) ≥ ((u-v)^q + 1)^(1/q)
  have h_psf_norm_ge : ((u - v) ^ q + 1) ^ ((1 : ℝ) / q)
                        ≤ (∑ j, |p_star j - f j| ^ q) ^ ((1 : ℝ) / q) := by
    rw [h_psf_pow_eq]
    have h_lhs_nn : 0 ≤ (u - v) ^ q + 1 := by
      have hl1 : 0 ≤ (u - v) ^ q :=
        Real.rpow_nonneg (by linarith) q
      linarith
    exact Real.rpow_le_rpow h_lhs_nn h_uv_bound hq_inv_nn
  -- (∑ j, |p_star j|^q)^(1/q) = (c-1) * S_T^(1/q) = u - v
  have hc_sub1_nn : 0 ≤ c - 1 := by linarith
  have h_pstar_norm_eq : (∑ j, |p_star j| ^ q) ^ ((1 : ℝ) / q) = u - v := by
    rw [h_pstar_norm_pow]
    have hcm1_q_nn : 0 ≤ (c - 1) ^ q := Real.rpow_nonneg hc_sub1_nn _
    rw [Real.mul_rpow hcm1_q_nn hST_nn]
    have h_cm1_qq : ((c - 1) ^ q) ^ ((1 : ℝ) / q) = c - 1 := by
      rw [← Real.rpow_mul hc_sub1_nn]
      rw [mul_one_div, div_self hq_ne, Real.rpow_one]
    rw [h_cm1_qq]
    -- Goal: (c - 1) * S_T ^ (1/q) = u - v
    -- u - v = c * v - v = (c - 1) * v = (c - 1) * S_T^(1/q)
    rw [hu_def, hv_def]
    ring
  -- Now use the key Hölder inequality on w = u - v.
  have h_w_nn : 0 ≤ u - v := by linarith
  have h_key := key_holder_one_dim hq hlam0 hlam1 h_w_nn
  -- h_key: K + lambda * (u - v) ≤ ((u - v)^q + 1)^(1/q)
  -- Combine: K ≤ ((u-v)^q + 1)^(1/q) - lambda*(u-v) ≤ lqNorm q (p_star - f) - lambda*lqNorm q p_star
  -- = g_lambda.
  unfold g_lambda lqNorm
  rw [h_pstar_norm_eq]
  linarith [h_key, h_psf_norm_ge]
