import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.BinomialPmfMaxBound

set_option maxHeartbeats 4000000

open Classical
open Workspace.Types.AlternatingSumExpression

/-- Helper: For `x ∈ [0, 1/2]`, `Real.exp (-2 * x) ≤ 1 - x`. -/
private lemma exp_neg_two_mul_le_one_sub_aux (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have hg_mono : MonotoneOn (fun t : ℝ => Real.exp (2 * t) * (1 - t)) (Set.Icc (0 : ℝ) (1/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1/2))
    · apply ContinuousOn.mul
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      · exact (continuous_const.sub continuous_id).continuousOn
    · intro t _
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := by
        have := (Real.hasDerivAt_exp (2 * t)).comp t
                ((hasDerivAt_id t).const_mul 2)
        simpa using this
      have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
        have := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
        simpa using this
      have h3 := h1.mul h2
      have heq : Real.exp (2 * t) * 2 * (1 - t) + Real.exp (2 * t) * (-1)
                  = Real.exp (2 * t) * (1 - 2 * t) := by ring
      rw [heq] at h3
      exact h3.hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) (1/2) := by rw [interior_Icc] at ht; exact ht
      have hexp_pos : 0 < Real.exp (2 * t) := Real.exp_pos _
      have h1 : 0 ≤ 1 - 2 * t := by linarith [ht'.2]
      exact mul_nonneg hexp_pos.le h1
  have h0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := by constructor <;> norm_num
  have hx_in : x ∈ Set.Icc (0 : ℝ) (1/2) := ⟨hx, hx2⟩
  have hg_at_0 : (fun t : ℝ => Real.exp (2 * t) * (1 - t)) 0 = 1 := by simp [Real.exp_zero]
  have hgx_ge : (fun t : ℝ => Real.exp (2 * t) * (1 - t)) 0
                ≤ (fun t : ℝ => Real.exp (2 * t) * (1 - t)) x := hg_mono h0_in hx_in hx
  rw [hg_at_0] at hgx_ge
  have hexp_pos : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hinv_eq : Real.exp (-(2 * x)) = (Real.exp (2 * x))⁻¹ := by rw [← Real.exp_neg]
  rw [hinv_eq, inv_le_iff_one_le_mul₀ hexp_pos]
  linarith [hgx_ge]

/-- Helper: `binPMFInt n (1/2) k ≤ √(2/(π·n))` for any `k`, `n ≥ 1`. -/
private lemma binPMFInt_half_le_sqrt (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    binPMFInt n (1/2) k ≤ Real.sqrt (2 / (Real.pi * n)) := by
  unfold binPMFInt binPMF
  by_cases hk : 0 ≤ k ∧ k ≤ (n : ℤ)
  · simp only [hk, ↓reduceIte]
    by_cases hkn : k.toNat ≤ n
    · simp only [hkn]
      have hbase : ((Nat.choose n k.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ Real.sqrt (2 / (Real.pi * n)) :=
        BinomialPmfMaxBound n hn k.toNat
      have hpow : ((1 : ℝ) / 2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat) = ((2 : ℝ) ^ n)⁻¹ := by
        rw [show (1 : ℝ) - 1/2 = 1/2 by ring]
        rw [← pow_add]
        rw [Nat.add_sub_cancel' hkn]
        rw [one_div, inv_pow]
      calc (Nat.choose n k.toNat : ℝ) * ((1 : ℝ)/2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat)
          = (Nat.choose n k.toNat : ℝ) * (((1 : ℝ)/2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat)) := by ring
        _ = (Nat.choose n k.toNat : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rw [hpow]
        _ ≤ Real.sqrt (2 / (Real.pi * n)) := hbase
    · simp only [hkn, ↓reduceIte]
      exact Real.sqrt_nonneg _
  · simp only [hk, ↓reduceIte]
    exact Real.sqrt_nonneg _

/-- Helper: `binPMFInt n (1/2) k ≥ 0`. -/
private lemma binPMFInt_nonneg (n : ℕ) (k : ℤ) :
    0 ≤ binPMFInt n (1/2) k := by
  unfold binPMFInt binPMF
  split_ifs with h hkn
  · positivity
  · exact le_refl 0
  · exact le_refl 0

/-- Helper: `binPMF n (1/2) k ≥ 0`. -/
private lemma binPMF_half_nonneg (n : ℕ) (k : ℕ) :
    0 ≤ binPMF n (1/2) k := by
  unfold binPMF
  split_ifs
  · positivity
  · exact le_refl 0

/-- Helper: total binomial mass is 1. -/
private lemma sum_binPMF_half_eq_one (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), binPMF n (1/2) k = 1 := by
  have hadd : ((1 : ℝ)/2 + 1/2) ^ n = 1 := by norm_num
  have hap := add_pow ((1 : ℝ)/2) (1/2) n
  rw [hadd] at hap
  -- hap : 1 = ∑ m ∈ range (n+1), (1/2)^m * (1/2)^(n-m) * choose n m
  -- Convert each binPMF term to the add_pow form, then conclude.
  have hcongr : ∀ k ∈ Finset.range (n + 1),
      binPMF n (1/2) k = ((1 : ℝ)/2) ^ k * ((1 : ℝ)/2) ^ (n - k) * (n.choose k : ℝ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
    unfold binPMF
    simp only [hkn, ↓reduceIte]
    have h12 : (1 : ℝ) - 1/2 = 1/2 := by ring
    rw [h12]
    ring
  rw [Finset.sum_congr rfl hcongr]
  exact hap.symm

/-- Helper: `∑_{j ∈ Icc 1 n_h} binPMFInt n (1/2) (r + n/4 + j) ≤ 1`. -/
private lemma sum_binPMFInt_shift_le_one (n : ℕ) (hn : 1 ≤ n) (r : ℤ) :
    ∑ j ∈ Finset.Icc 1 (n / 2), binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
      ≤ 1 := by
  -- We show the sum is ≤ ∑ k ∈ range(n+1), binPMF n (1/2) k = 1.
  -- Strategy: split Icc 1 (n/2) into "valid" (where 0 ≤ r+n/4+j ≤ n) and "invalid";
  -- on valid indices, binPMFInt = binPMF n (1/2) ((r+n/4+j).toNat); on invalid, = 0.
  -- Use Finset.sum_image with the injection j ↦ (r+n/4+j).toNat.
  set valid : Finset ℕ := (Finset.Icc 1 (n / 2)).filter
    (fun j => 0 ≤ r + ((n : ℤ) / 4) + (j : ℤ) ∧ r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ))
    with hvalid_def
  -- Step 1: sum over Icc = sum over valid (since invalid terms are 0).
  have hvsub : valid ⊆ Finset.Icc 1 (n / 2) := Finset.filter_subset _ _
  have hsum_split : ∑ j ∈ valid, binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
      = ∑ j ∈ Finset.Icc 1 (n / 2), binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) := by
    apply Finset.sum_subset hvsub
    intro j hj hjnv
    simp only [hvalid_def, Finset.mem_filter] at hjnv
    have hcontra : ¬(0 ≤ r + ((n : ℤ) / 4) + (j : ℤ) ∧ r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ)) := by
      intro h
      exact hjnv ⟨hj, h⟩
    unfold binPMFInt
    simp only [ite_eq_right_iff]
    intro hcond
    exact absurd hcond hcontra
  rw [← hsum_split]
  -- Step 2: on valid, binPMFInt = binPMF (toNat).
  set f : ℕ → ℕ := fun j => (r + ((n : ℤ) / 4) + (j : ℤ)).toNat with hf
  have hsum_eq : ∑ j ∈ valid, binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
      = ∑ j ∈ valid, binPMF n (1/2) (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hvalid_def, Finset.mem_filter] at hj
    have h1 : 0 ≤ r + ((n : ℤ) / 4) + (j : ℤ) := hj.2.1
    have h2 : r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ) := hj.2.2
    unfold binPMFInt
    simp only [h1, h2, and_self, ↓reduceIte]
    rfl
  rw [hsum_eq]
  -- Step 3: f is injective on valid.
  have hf_inj : Set.InjOn f (valid : Set ℕ) := by
    intros a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hvalid_def] at ha hb
    have ha1 : 0 ≤ r + ((n : ℤ) / 4) + (a : ℤ) := ha.2.1
    have hb1 : 0 ≤ r + ((n : ℤ) / 4) + (b : ℤ) := hb.2.1
    simp only [hf] at hab
    have heq : r + ((n : ℤ) / 4) + (a : ℤ) = r + ((n : ℤ) / 4) + (b : ℤ) := by
      have heqa : ((r + ((n : ℤ) / 4) + (a : ℤ)).toNat : ℤ) = r + ((n : ℤ) / 4) + (a : ℤ) :=
        Int.toNat_of_nonneg ha1
      have heqb : ((r + ((n : ℤ) / 4) + (b : ℤ)).toNat : ℤ) = r + ((n : ℤ) / 4) + (b : ℤ) :=
        Int.toNat_of_nonneg hb1
      rw [← heqa, ← heqb]
      exact_mod_cast hab
    omega
  -- Step 4: image of valid under f ⊆ range (n+1).
  have himg_sub : valid.image f ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_image] at hk
    obtain ⟨j, hjvalid, hjk⟩ := hk
    simp only [hvalid_def, Finset.mem_filter] at hjvalid
    have h2 : r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ) := hjvalid.2.2
    rw [Finset.mem_range, ← hjk, hf]
    have hle : (r + ((n : ℤ) / 4) + (j : ℤ)).toNat ≤ n := Int.toNat_le.mpr h2
    show (r + ((n : ℤ) / 4) + (j : ℤ)).toNat < n + 1
    omega
  -- Step 5: Sum over valid via image.
  have himg : (∑ j ∈ valid, binPMF n (1/2) (f j)) = ∑ k ∈ valid.image f, binPMF n (1/2) k :=
    (Finset.sum_image (fun a ha b hb h => hf_inj (by exact_mod_cast ha) (by exact_mod_cast hb) h)).symm
  rw [himg]
  -- Step 6: bound by total sum, which equals 1.
  calc ∑ k ∈ valid.image f, binPMF n (1/2) k
      ≤ ∑ k ∈ Finset.range (n + 1), binPMF n (1/2) k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg_sub
        intros k _ _
        exact binPMF_half_nonneg n k
    _ = 1 := sum_binPMF_half_eq_one n

/-- Helper: `Real.exp 2 ≥ 7.389`. -/
private lemma exp_two_lower : (7.389 : ℝ) ≤ Real.exp 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  -- We'll bound via Real.exp 2 = (Real.exp 1)^2.
  have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]
  rw [he2]
  have hpos : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  have h2 : (2.7182818283 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := by
    exact pow_le_pow_left₀ hpos h1.le 2
  have h3 : (7.389 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
  linarith

/-- Helper: `Real.sqrt (2 * Real.pi) ≥ 2.5`. -/
private lemma sqrt_two_pi_lower : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h1 : (6.28 : ℝ) ≤ 2 * Real.pi := by linarith
  have h2 : (2.5 : ℝ) ^ 2 = 6.25 := by norm_num
  have h3 : (6.25 : ℝ) ≤ 6.28 := by norm_num
  have h4 : (2.5 : ℝ) ^ 2 ≤ 2 * Real.pi := by linarith
  exact Real.le_sqrt_of_sq_le h4

/-- Main theorem. -/
theorem NormaliserBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let n_h : ℕ := n / 2
      let S_er : ℤ → ℕ → ℝ := fun r j =>
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
          Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ))
      let Zprime_er : ℤ → ℝ := fun r =>
        ∏ j ∈ Finset.Icc 1 (n / 2), (1 - S_er r j)
      ∀ (r : ℤ),
        -((n : ℤ) / 4) ≤ r → r ≤ ((n : ℤ) / 4) →
        (Zprime_er r)⁻¹ ≤ Real.exp (2 * c' * Real.sqrt n)
          ∧ 2 * c' ≤ (1 : ℝ) / 32 := by
  intro n hn hmod c' α n_h S_er Zprime_er r hr1 hr2
  -- Setup useful facts
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqn_nn : 0 ≤ Real.sqrt n := hsqn_pos.le
  have hexp_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have hexp2_lb : (7.389 : ℝ) ≤ Real.exp 2 := exp_two_lower
  have hsq2pi_lb : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := sqrt_two_pi_lower
  have hsq2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by linarith
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h_denom_pos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hc'_pos : 0 < c' := by simp only [c']; positivity
  have hc'_nn : 0 ≤ c' := hc'_pos.le
  have hα_pos : 0 < α := by simp only [α]; positivity
  have hα_eq : α = c' * Real.sqrt n := by simp only [α, c']
  -- Part 2 first: 2 * c' ≤ 1/32.
  have part2 : 2 * c' ≤ (1 : ℝ) / 32 := by
    -- 2 c' = 2 / (4 e² √(2π)) = 1 / (2 e² √(2π)).
    -- Need: 1 / (2 e² √(2π)) ≤ 1/32 ⟺ 32 ≤ 2 e² √(2π) ⟺ 16 ≤ e² √(2π).
    have h_prod_lb : (16 : ℝ) ≤ Real.exp 2 * Real.sqrt (2 * Real.pi) := by
      -- e² ≥ 7.389, √(2π) ≥ 2.5, so e²·√(2π) ≥ 7.389·2.5 = 18.4725 ≥ 16.
      have h1 : (7.389 : ℝ) * 2.5 ≤ Real.exp 2 * Real.sqrt (2 * Real.pi) := by
        apply mul_le_mul hexp2_lb hsq2pi_lb (by norm_num) hexp_pos.le
      linarith
    -- Now manipulate 2 * c' = 1 / (2 * e² * √(2π))
    have hc_eq : 2 * c' = 1 / (2 * Real.exp 2 * Real.sqrt (2 * Real.pi)) := by
      simp only [c']
      field_simp
      ring
    rw [hc_eq]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [h_prod_lb]
  refine ⟨?_, part2⟩
  -- Part 1: (Zprime_er r)⁻¹ ≤ exp (2 c' √n).
  -- Strategy: show Zprime_er r ≥ exp(-2 c' √n) > 0; then take inverse.
  -- Step 1: Bound each S_er r j ≤ c' · √(2/π) ≤ 1/2.
  have hα_eq' : α = c' * Real.sqrt n := hα_eq
  -- Each S_er r j ≤ α · √(2/(πn)) (from binPMFInt_half_le_sqrt).
  have hSer_bound : ∀ j : ℕ, S_er r j ≤ α * Real.sqrt (2 / (Real.pi * n)) := by
    intro j
    simp only [S_er]
    rw [show ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) = α from rfl]
    apply mul_le_mul_of_nonneg_left _ hα_pos.le
    exact binPMFInt_half_le_sqrt n hn1 _
  -- α · √(2/(πn)) = c' · √n · √(2/(πn)) = c' · √(2/π).
  have h_alpha_sqrt : α * Real.sqrt (2 / (Real.pi * n)) = c' * Real.sqrt (2 / Real.pi) := by
    rw [hα_eq]
    -- c' * √n * √(2/(π·n)) = c' * (√n · √(2/(π·n))) = c' · √(n · 2/(π·n)) = c' * √(2/π)
    rw [mul_assoc]
    congr 1
    have hnn : 0 ≤ (2 : ℝ) / (Real.pi * n) := by positivity
    have hnnn : (0 : ℝ) ≤ n := hnpos.le
    rw [← Real.sqrt_mul hnnn (2 / (Real.pi * n))]
    congr 1
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hpine : Real.pi ≠ 0 := ne_of_gt hpi_pos
    field_simp
  have hSer_simpl : ∀ j : ℕ, S_er r j ≤ c' * Real.sqrt (2 / Real.pi) := by
    intro j
    have := hSer_bound j
    rw [h_alpha_sqrt] at this
    exact this
  have hSer_nn : ∀ j : ℕ, 0 ≤ S_er r j := by
    intro j
    simp only [S_er]
    apply mul_nonneg
    · simp only [α] at hα_pos; positivity
    · exact binPMFInt_nonneg n _
  -- Bound c' · √(2/π) ≤ 1/2. Actually we need ≤ 1/2.
  -- c' = 1/(4 e² √(2π)), so c' · √(2/π) = √(2/π) / (4 e² √(2π))
  --                                     = 1/(4 e² √π) (since √(2π)·√π = π√2 hmm no)
  -- Let me compute: c' · √(2/π) = (1/(4 e² √(2π))) · √(2/π)
  --                            = √(2/π) / (4 e² √(2π))
  --                            = √((2/π) / (2π)) / (4 e²)  (using √a/√b = √(a/b))
  --                            = √(1/π²) / (4 e²)
  --                            = (1/π) / (4 e²)
  --                            = 1 / (4 e² π).
  -- Numerically: 1/(4 · 7.389 · 3.14) ≈ 1/92.8 ≈ 0.0108 < 1/2. ✓
  have hSer_le_half : ∀ j : ℕ, S_er r j ≤ 1/2 := by
    intro j
    have hb := hSer_simpl j
    -- Show c' · √(2/π) ≤ 1/2
    have hsq : Real.sqrt (2 / Real.pi) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one hpi_pos]
      linarith [Real.pi_gt_d2]
    have hsq_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
    have hc'_le : c' ≤ 1/2 := by
      simp only [c']
      rw [div_le_iff₀ h_denom_pos]
      -- Need: 1 ≤ (1/2) * (4 * e² * √(2π)) = 2 * e² * √(2π).
      -- 2 * 7.389 * 2.5 = 36.945 ≥ 1.
      have h_lb : (1 : ℝ) ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
        have hh1 : (2 : ℝ) * 7.389 * 2.5 ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
          have hh : (2 : ℝ) * 7.389 ≤ 2 * Real.exp 2 := by linarith
          apply mul_le_mul hh hsq2pi_lb (by norm_num) (by linarith)
        linarith
      linarith
    calc S_er r j ≤ c' * Real.sqrt (2 / Real.pi) := hb
      _ ≤ c' * 1 := by apply mul_le_mul_of_nonneg_left hsq hc'_nn
      _ = c' := by ring
      _ ≤ 1/2 := hc'_le
  -- Step 2: Each factor (1 - S_er r j) ≥ exp(-2 · S_er r j) > 0.
  have hfactor_lb : ∀ j : ℕ, Real.exp (-(2 * S_er r j)) ≤ 1 - S_er r j := by
    intro j
    exact exp_neg_two_mul_le_one_sub_aux _ (hSer_nn j) (hSer_le_half j)
  have hfactor_pos : ∀ j : ℕ, 0 < 1 - S_er r j := by
    intro j
    have : S_er r j ≤ 1/2 := hSer_le_half j
    linarith
  -- Step 3: Take product.
  -- ∏ j ∈ Icc 1 (n/2), exp(-2 S_er r j) = exp(-2 · ∑ S_er r j) ≤ ∏ j (1 - S_er r j) = Zprime_er r.
  have hZ_pos : 0 < Zprime_er r := by
    simp only [Zprime_er]
    apply Finset.prod_pos
    intro j _
    exact hfactor_pos j
  have hexp_prod_le : Real.exp (-(2 * ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j))
      ≤ Zprime_er r := by
    -- exp(-2·Σ) = ∏ exp(-2·S_er) ≤ ∏ (1 - S_er) = Zprime_er.
    have hexp_prod : Real.exp (-(2 * ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j))
        = ∏ j ∈ Finset.Icc 1 (n / 2), Real.exp (-(2 * S_er r j)) := by
      have hrw : -(2 * ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j)
                  = ∑ j ∈ Finset.Icc 1 (n / 2), -(2 * S_er r j) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [hrw, Real.exp_sum]
    rw [hexp_prod]
    simp only [Zprime_er]
    apply Finset.prod_le_prod
    · intros j _
      exact (Real.exp_pos _).le
    · intros j _
      exact hfactor_lb j
  -- Step 4: ∑ S_er ≤ α (≤ c' √n).
  have hsum_Ser : ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j ≤ α := by
    -- S_er r j = α · binPMFInt n (1/2) (r + n/4 + j); ∑ binPMFInt ≤ 1.
    have hsum_eq : ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j
        = α * ∑ j ∈ Finset.Icc 1 (n / 2), binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) := by
      rw [Finset.mul_sum]
    rw [hsum_eq]
    have hbnd : ∑ j ∈ Finset.Icc 1 (n / 2), binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ 1 :=
      sum_binPMFInt_shift_le_one n hn1 r
    calc α * ∑ j ∈ Finset.Icc 1 (n / 2), binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        ≤ α * 1 := by apply mul_le_mul_of_nonneg_left hbnd hα_pos.le
      _ = α := by ring
  -- Step 5: Combine: exp(-2 c' √n) ≤ exp(-2 · ∑ S_er) ≤ Zprime_er, so (Zprime_er)⁻¹ ≤ exp(2 c' √n).
  have hexp_lb : Real.exp (-(2 * α)) ≤ Zprime_er r := by
    have h1 : -(2 * α) ≤ -(2 * ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j) := by
      have : 2 * ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j ≤ 2 * α := by
        linarith [hsum_Ser]
      linarith
    have hmono : Real.exp (-(2 * α)) ≤ Real.exp (-(2 * ∑ j ∈ Finset.Icc 1 (n / 2), S_er r j)) :=
      Real.exp_monotone h1
    linarith [hexp_prod_le, hmono]
  -- (Zprime_er r)⁻¹ ≤ (exp(-(2*α)))⁻¹ = exp(2*α) = exp(2 c' √n).
  have hexp_pos' : 0 < Real.exp (-(2 * α)) := Real.exp_pos _
  have hinv_le : (Zprime_er r)⁻¹ ≤ (Real.exp (-(2 * α)))⁻¹ := by
    apply (inv_le_inv₀ hZ_pos hexp_pos').mpr hexp_lb
  have hinv_eq : (Real.exp (-(2 * α)))⁻¹ = Real.exp (2 * α) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hα_swap : 2 * α = 2 * c' * Real.sqrt n := by
    rw [hα_eq]; ring
  rw [← hα_swap]
  calc (Zprime_er r)⁻¹ ≤ (Real.exp (-(2 * α)))⁻¹ := hinv_le
    _ = Real.exp (2 * α) := hinv_eq
