import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.Types.StirlingAxioms
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.NormaliserBound

set_option maxHeartbeats 8000000

open Classical
open Workspace.Types.AlternatingSumExpression

/-! Helper lemmas. -/

private lemma binPMF_half_nonneg' (n : ℕ) (k : ℕ) :
    0 ≤ binPMF n (1/2) k := by
  unfold binPMF; split_ifs
  · positivity
  · exact le_refl 0

private lemma binPMFInt_nonneg' (n : ℕ) (k : ℤ) :
    0 ≤ binPMFInt n (1/2) k := by
  unfold binPMFInt binPMF
  split_ifs
  · positivity
  · exact le_refl 0
  · exact le_refl 0

private lemma binPMFInt_half_le_sqrt' (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
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
        rw [← pow_add, Nat.add_sub_cancel' hkn, one_div, inv_pow]
      calc (Nat.choose n k.toNat : ℝ) * ((1 : ℝ)/2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat)
          = (Nat.choose n k.toNat : ℝ) * (((1 : ℝ)/2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat)) := by ring
        _ = (Nat.choose n k.toNat : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rw [hpow]
        _ ≤ Real.sqrt (2 / (Real.pi * n)) := hbase
    · simp only [hkn, ↓reduceIte]; exact Real.sqrt_nonneg _
  · simp only [hk, ↓reduceIte]; exact Real.sqrt_nonneg _

private lemma exp_two_lower' : (7.389 : ℝ) ≤ Real.exp 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]
  rw [he2]
  have hpos : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  have h2 : (2.7182818283 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ hpos h1.le 2
  have h3 : (7.389 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
  linarith

private lemma sqrt_two_pi_lower' : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h4 : (2.5 : ℝ) ^ 2 ≤ 2 * Real.pi := by nlinarith
  exact Real.le_sqrt_of_sq_le h4

private lemma sqrt_plus_sqrt_one_sub_le_exp (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt x + Real.sqrt (1 - x) ≤ Real.exp (Real.sqrt x) := by
  have h1 : Real.sqrt (1 - x) ≤ 1 := by
    have h1x : 1 - x ≤ 1 := by linarith
    calc Real.sqrt (1 - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1x
      _ = 1 := Real.sqrt_one
  have h2 : Real.sqrt x + 1 ≤ Real.exp (Real.sqrt x) := Real.add_one_le_exp (Real.sqrt x)
  linarith

/-- Sum of √products over powerset = product of sums of √. -/
private lemma sum_sqrt_prod_eq_prod_add_sqrt
    (n_h : ℕ) (a b : ℕ → ℝ) (ha : ∀ j ∈ Finset.Icc 1 n_h, 0 ≤ a j)
    (hb : ∀ j ∈ Finset.Icc 1 n_h, 0 ≤ b j) :
    (∑ ℓ ∈ ((Finset.Icc 1 n_h).powerset),
      Real.sqrt (∏ j ∈ Finset.Icc 1 n_h, (if j ∈ ℓ then a j else b j)))
      = ∏ j ∈ Finset.Icc 1 n_h, (Real.sqrt (a j) + Real.sqrt (b j)) := by
  have hcongr : ∀ ℓ ∈ ((Finset.Icc 1 n_h).powerset),
      Real.sqrt (∏ j ∈ Finset.Icc 1 n_h, (if j ∈ ℓ then a j else b j))
        = ∏ j ∈ Finset.Icc 1 n_h, (if j ∈ ℓ then Real.sqrt (a j) else Real.sqrt (b j)) := by
    intros ℓ _
    have hnn : ∀ j ∈ Finset.Icc 1 n_h, 0 ≤ (if j ∈ ℓ then a j else b j) := by
      intros j hj
      by_cases hjℓ : j ∈ ℓ
      · simp [hjℓ]; exact ha j hj
      · simp [hjℓ]; exact hb j hj
    rw [Real.sqrt_prod _ hnn]
    apply Finset.prod_congr rfl
    intros j _
    by_cases hjℓ : j ∈ ℓ
    · simp [hjℓ]
    · simp [hjℓ]
  rw [Finset.sum_congr rfl hcongr]
  rw [Finset.prod_add (fun j => Real.sqrt (a j)) (fun j => Real.sqrt (b j)) (Finset.Icc 1 n_h)]
  apply Finset.sum_congr rfl
  intros ℓ hℓ
  rw [Finset.mem_powerset] at hℓ
  -- Goal: ∏ j ∈ Icc 1 n_h, (if j ∈ ℓ then √(a j) else √(b j))
  --     = (∏ i ∈ ℓ, √(a i)) * ∏ i ∈ Icc 1 n_h \ ℓ, √(b i)
  have hsplit : ∏ j ∈ Finset.Icc 1 n_h, (if j ∈ ℓ then Real.sqrt (a j) else Real.sqrt (b j))
      = (∏ j ∈ ℓ, (if j ∈ ℓ then Real.sqrt (a j) else Real.sqrt (b j)))
        * (∏ j ∈ Finset.Icc 1 n_h \ ℓ, (if j ∈ ℓ then Real.sqrt (a j) else Real.sqrt (b j))) := by
    conv_lhs => rw [show Finset.Icc 1 n_h = ℓ ∪ (Finset.Icc 1 n_h \ ℓ) from
        (Finset.union_sdiff_of_subset hℓ).symm]
    exact Finset.prod_union Finset.disjoint_sdiff
  rw [hsplit]
  congr 1
  · apply Finset.prod_congr rfl; intros j hj; simp [hj]
  · apply Finset.prod_congr rfl; intros j hj
    rw [Finset.mem_sdiff] at hj; simp [hj.2]

/-- `∑_{j∈Icc 1 (n/2)} √binPMFInt(n,1/2,r+n/4+j) ≤ (2πn)^{1/4}`. -/
private lemma sum_sqrt_binPMFInt_shift_le (n : ℕ) (hn : 1 ≤ n) (r : ℤ) :
    ∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))
      ≤ (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  set valid : Finset ℕ := (Finset.Icc 1 (n / 2)).filter
    (fun j => 0 ≤ r + ((n : ℤ) / 4) + (j : ℤ) ∧ r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ))
    with hvalid_def
  have hvsub : valid ⊆ Finset.Icc 1 (n / 2) := Finset.filter_subset _ _
  have hsum_split : ∑ j ∈ valid, Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))
      = ∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))) := by
    apply Finset.sum_subset hvsub
    intro j hj hjnv
    simp only [hvalid_def, Finset.mem_filter] at hjnv
    have hcontra : ¬(0 ≤ r + ((n : ℤ) / 4) + (j : ℤ) ∧ r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ)) :=
      fun h => hjnv ⟨hj, h⟩
    have hzero : binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) = 0 := by
      unfold binPMFInt; simp only [ite_eq_right_iff]; intro hcond; exact absurd hcond hcontra
    rw [hzero, Real.sqrt_zero]
  rw [← hsum_split]
  set f : ℕ → ℕ := fun j => (r + ((n : ℤ) / 4) + (j : ℤ)).toNat with hf
  have hsum_eq : ∑ j ∈ valid, Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))
      = ∑ j ∈ valid, Real.sqrt (binPMF n (1/2) (f j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hvalid_def, Finset.mem_filter] at hj
    have h1 : 0 ≤ r + ((n : ℤ) / 4) + (j : ℤ) := hj.2.1
    have h2 : r + ((n : ℤ) / 4) + (j : ℤ) ≤ (n : ℤ) := hj.2.2
    have heq : binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) = binPMF n (1/2) (f j) := by
      unfold binPMFInt; simp only [h1, h2, and_self, ↓reduceIte]; rfl
    rw [heq]
  rw [hsum_eq]
  have hf_inj : Set.InjOn f (valid : Set ℕ) := by
    intros a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hvalid_def] at ha hb
    have ha1 : 0 ≤ r + ((n : ℤ) / 4) + (a : ℤ) := ha.2.1
    have hb1 : 0 ≤ r + ((n : ℤ) / 4) + (b : ℤ) := hb.2.1
    simp only [hf] at hab
    have heq : r + ((n : ℤ) / 4) + (a : ℤ) = r + ((n : ℤ) / 4) + (b : ℤ) := by
      have heqa := Int.toNat_of_nonneg ha1
      have heqb := Int.toNat_of_nonneg hb1
      rw [← heqa, ← heqb]; exact_mod_cast hab
    omega
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
  have himg : (∑ j ∈ valid, Real.sqrt (binPMF n (1/2) (f j)))
      = ∑ k ∈ valid.image f, Real.sqrt (binPMF n (1/2) k) := by
    rw [Finset.sum_image (f := fun k => Real.sqrt (binPMF n (1/2) k))
        (fun a ha b hb h => hf_inj ha hb h)]
  rw [himg]
  calc ∑ k ∈ valid.image f, Real.sqrt (binPMF n (1/2) k)
      ≤ ∑ k ∈ Finset.range (n + 1), Real.sqrt (binPMF n (1/2) k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg_sub
        intros k _ _; exact Real.sqrt_nonneg _
    _ ≤ (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) := by
        have hcongr : ∀ k ∈ Finset.range (n + 1),
            Real.sqrt (binPMF n (1/2) k) = Real.sqrt ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) := by
          intros k hk
          rw [Finset.mem_range] at hk
          have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
          have heq : binPMF n (1/2) k = (Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹ := by
            unfold binPMF
            simp only [hkn, ↓reduceIte]
            have hpow : ((1 : ℝ) / 2) ^ k * ((1 : ℝ) - 1/2) ^ (n - k) = (2 ^ n : ℝ)⁻¹ := by
              rw [show (1 : ℝ) - 1/2 = 1/2 by ring]
              rw [← pow_add, Nat.add_sub_cancel' hkn, one_div, inv_pow]
            calc (Nat.choose n k : ℝ) * ((1 : ℝ)/2) ^ k * ((1 : ℝ) - 1/2) ^ (n - k)
                = (Nat.choose n k : ℝ) * (((1 : ℝ)/2) ^ k * ((1 : ℝ) - 1/2) ^ (n - k)) := by ring
              _ = (Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹ := by rw [hpow]
          rw [heq]
        rw [Finset.sum_congr rfl hcongr]
        exact Workspace.Types.StirlingAxioms.binomial_pmf_l_half_sum_bound hn

/-- Algebra step: `√α · (2πn)^{1/4} = √n / (2e)`, where `α := c'·√n`,
`c' := 1/(4·e²·√(2π))`. -/
private lemma alpha_sqrt_2pin_eq_sqrtn_div_2e (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
      * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)
      = Real.sqrt n / (2 * Real.exp 1) := by
  have hexp_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hexp1_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have hsq2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt_n_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h_denom_pos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  have hc'_pos : 0 < c' := by simp only [hc'_def]; positivity
  set α : ℝ := c' * Real.sqrt n with hα_def
  have hα_pos : 0 < α := by simp only [hα_def]; positivity
  have hα_nn : 0 ≤ α := hα_pos.le
  have h2pin_nn : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
  -- (2πn)^{1/4} = √(√(2πn))
  have h_quarter_eq : (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (2 * Real.pi * n)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    -- Simpler: ((2πn)^{1/2})^{1/2} = (2πn)^{1/2 · 1/2} = (2πn)^{1/4}
    rw [← Real.rpow_mul h2pin_nn]
    norm_num
  have h_lhs_change : Real.sqrt α * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)
      = Real.sqrt α * Real.sqrt (Real.sqrt (2 * Real.pi * n)) := by rw [h_quarter_eq]
  show Real.sqrt α * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) = Real.sqrt n / (2 * Real.exp 1)
  rw [h_lhs_change]
  -- √α · √(√(2πn)) = √(α · √(2πn))
  rw [← Real.sqrt_mul hα_nn (Real.sqrt (2 * Real.pi * n))]
  -- α · √(2πn) = c'·√n · √(2πn) = c'·n·√(2π) = n / (4 e²).
  have h_alpha_sqrt2pin : α * Real.sqrt (2 * Real.pi * n) = (n : ℝ) / (4 * Real.exp 2) := by
    rw [hα_def]
    -- c'·√n · √(2πn) = c' · √(n · 2πn).
    rw [mul_assoc]
    rw [show Real.sqrt n * Real.sqrt (2 * Real.pi * n) = Real.sqrt (n * (2 * Real.pi * n)) from
        (Real.sqrt_mul hn_pos.le _).symm]
    rw [show (n : ℝ) * (2 * Real.pi * n) = 2 * Real.pi * (n : ℝ)^2 by ring]
    rw [show 2 * Real.pi * (n : ℝ)^2 = 2 * Real.pi * ((n : ℝ)^2) from rfl]
    rw [Real.sqrt_mul h2pi_pos.le ((n : ℝ)^2)]
    rw [Real.sqrt_sq hn_pos.le]
    rw [hc'_def]
    field_simp
  rw [h_alpha_sqrt2pin]
  -- √(n / (4 e²)) = √n / (2 e).
  rw [show (4 * Real.exp 2 : ℝ) = (2 * Real.exp 1)^2 by
        rw [show Real.exp 2 = (Real.exp 1)^2 by
            rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]]
        ring]
  rw [Real.sqrt_div hn_pos.le ((2 * Real.exp 1)^2)]
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1)]

/-- The shifted L^{1/2} sum bound for the product Bernoulli measure. -/
private lemma shifted_sqrt_sum_bound (n : ℕ) (hn1 : 1 ≤ n) (r : ℤ)
    (hSer_nn : ∀ j : ℕ, (0 : ℝ) ≤
      ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
        binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))
    (hSer_le_half : ∀ j : ℕ,
      ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
        binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ 1/2) :
    (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset),
      Real.sqrt (∏ j ∈ Finset.Icc 1 (n / 2),
        (if j ∈ ℓ then
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
            binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        else
          (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
            binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))))))
      ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1)) := by
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα_def
  set S_er : ℕ → ℝ := fun j => α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) with hS_er_def
  have hexp_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have hsq2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqn_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hα_pos : 0 < α := by simp only [hα_def]; positivity
  have hα_nn : 0 ≤ α := hα_pos.le
  have hOneMinusSer_nn : ∀ j : ℕ, 0 ≤ 1 - S_er j := fun j => by
    have : S_er j ≤ 1/2 := hSer_le_half j; linarith
  have hSer_le_one : ∀ j : ℕ, S_er j ≤ 1 := fun j => by
    have : S_er j ≤ 1/2 := hSer_le_half j; linarith
  -- Step 1: Express LHS as a product (using S_er names).
  have hstep1 : (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset),
      Real.sqrt (∏ j ∈ Finset.Icc 1 (n / 2),
        (if j ∈ ℓ then S_er j else (1 - S_er j))))
        = ∏ j ∈ Finset.Icc 1 (n / 2), (Real.sqrt (S_er j) + Real.sqrt (1 - S_er j)) := by
    apply sum_sqrt_prod_eq_prod_add_sqrt
    · intros j _; exact hSer_nn j
    · intros j _; exact hOneMinusSer_nn j
  show (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset),
      Real.sqrt (∏ j ∈ Finset.Icc 1 (n / 2),
        (if j ∈ ℓ then S_er j else (1 - S_er j))))
      ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1))
  rw [hstep1]
  -- Step 2: bound product by exp(∑ √S_er j).
  have hstep2 : ∏ j ∈ Finset.Icc 1 (n / 2), (Real.sqrt (S_er j) + Real.sqrt (1 - S_er j))
      ≤ ∏ j ∈ Finset.Icc 1 (n / 2), Real.exp (Real.sqrt (S_er j)) := by
    apply Finset.prod_le_prod
    · intros j _
      have h1 : 0 ≤ Real.sqrt (S_er j) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (1 - S_er j) := Real.sqrt_nonneg _
      linarith
    · intros j _; exact sqrt_plus_sqrt_one_sub_le_exp (S_er j) (hSer_nn j) (hSer_le_one j)
  have hstep3 : ∏ j ∈ Finset.Icc 1 (n / 2), Real.exp (Real.sqrt (S_er j))
      = Real.exp (∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (S_er j)) := by
    rw [← Real.exp_sum]
  -- Step 4: bound ∑ √(S_er j) ≤ √α · (2πn)^{1/4} = √n/(2e).
  have hstep4 : ∀ j : ℕ, Real.sqrt (S_er j)
      = Real.sqrt α * Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))) := by
    intro j
    show Real.sqrt (α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))
        = Real.sqrt α * Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))
    exact Real.sqrt_mul hα_nn _
  have hstep5 : ∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (S_er j)
      = Real.sqrt α * ∑ j ∈ Finset.Icc 1 (n / 2),
          Real.sqrt (binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros j _; exact hstep4 j
  have hsumshift := sum_sqrt_binPMFInt_shift_le n hn1 r
  have hsqrt_α_nn : 0 ≤ Real.sqrt α := Real.sqrt_nonneg _
  have hstep6 : ∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (S_er j)
      ≤ Real.sqrt α * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) := by
    rw [hstep5]; exact mul_le_mul_of_nonneg_left hsumshift hsqrt_α_nn
  have hstep7 : Real.sqrt α * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) = Real.sqrt n / (2 * Real.exp 1) :=
    alpha_sqrt_2pin_eq_sqrtn_div_2e n hn1
  have hstep8 : ∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (S_er j)
      ≤ Real.sqrt n / (2 * Real.exp 1) := by rw [← hstep7]; exact hstep6
  -- Combine.
  calc ∏ j ∈ Finset.Icc 1 (n / 2), (Real.sqrt (S_er j) + Real.sqrt (1 - S_er j))
      ≤ ∏ j ∈ Finset.Icc 1 (n / 2), Real.exp (Real.sqrt (S_er j)) := hstep2
    _ = Real.exp (∑ j ∈ Finset.Icc 1 (n / 2), Real.sqrt (S_er j)) := hstep3
    _ ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1)) := Real.exp_le_exp.mpr hstep8

theorem RareSupportShifted :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      let S_er : ℤ → ℕ → ℝ := fun r j =>
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
          Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ))
      let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j))
      ∀ (r : ℤ),
        -((n : ℤ) / 4) ≤ r → r ≤ ((n : ℤ) / 4) →
        (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
              (fun ℓ => widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))),
            widetildeMu_er r ℓ)
          ≤ Real.exp (-(Real.sqrt n / 16)) := by
  intro n hn hmod S_er widetildeMu_er r hr1 hr2
  have hn1 : 1 ≤ n := by
    have : (1 : ℕ) ≤ 10 ^ 12 := by norm_num
    exact this.trans hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqn_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hexp_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have hsq2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hexp2_lb : (7.389 : ℝ) ≤ Real.exp 2 := exp_two_lower'
  have hsq2pi_lb : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := sqrt_two_pi_lower'
  have h_denom_pos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  have hc'_pos : 0 < c' := by simp only [hc'_def]; positivity
  have hc'_nn : 0 ≤ c' := hc'_pos.le
  -- Pointwise nonnegativity of S_er.
  have hSer_nn : ∀ j : ℕ, 0 ≤ S_er r j := by
    intro j
    show 0 ≤ ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
      binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
    apply mul_nonneg
    · positivity
    · exact binPMFInt_nonneg' n _
  -- Show S_er r j ≤ 1/2.
  have hSer_le_half : ∀ j : ℕ, S_er r j ≤ 1/2 := by
    intro j
    show ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
      binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ 1/2
    have hbnd : binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ Real.sqrt (2 / (Real.pi * n)) :=
      binPMFInt_half_le_sqrt' n hn1 _
    have hα_nn : 0 ≤ c' * Real.sqrt n := by positivity
    have hbn : 0 ≤ binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) := binPMFInt_nonneg' n _
    have hsqrt_nn : 0 ≤ Real.sqrt (2 / (Real.pi * n)) := Real.sqrt_nonneg _
    have hstep1 : c' * Real.sqrt n * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) :=
      mul_le_mul_of_nonneg_left hbnd hα_nn
    have hstep2 : c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = c' * Real.sqrt (2 / Real.pi) := by
      rw [mul_assoc]
      congr 1
      rw [← Real.sqrt_mul hn_pos.le (2 / (Real.pi * n))]
      congr 1
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hpine : Real.pi ≠ 0 := ne_of_gt hpi_pos
      field_simp
    have hstep3 : c' * Real.sqrt (2 / Real.pi) ≤ 1/2 := by
      have hsq : Real.sqrt (2 / Real.pi) ≤ 1 := by
        rw [Real.sqrt_le_one]; rw [div_le_one hpi_pos]; linarith [Real.pi_gt_d2]
      have hsq_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
      have hc'_le_half : c' ≤ 1/2 := by
        simp only [hc'_def]
        rw [div_le_iff₀ h_denom_pos]
        have h_lb : (1 : ℝ) ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
          have hh1 : (2 : ℝ) * 7.389 * 2.5 ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
            have hh : (2 : ℝ) * 7.389 ≤ 2 * Real.exp 2 := by linarith
            apply mul_le_mul hh hsq2pi_lb (by norm_num) (by linarith)
          linarith
        linarith
      calc c' * Real.sqrt (2 / Real.pi) ≤ c' * 1 :=
              mul_le_mul_of_nonneg_left hsq hc'_nn
        _ = c' := by ring
        _ ≤ 1/2 := hc'_le_half
    have h_eq : ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
        = c' * Real.sqrt n := by simp only [hc'_def]
    rw [h_eq]
    calc c' * Real.sqrt n * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) := hstep1
      _ = c' * Real.sqrt (2 / Real.pi) := hstep2
      _ ≤ 1/2 := hstep3
  -- Pointwise (1 - S_er) ≥ 0.
  have hOneMinusSer_nn : ∀ j : ℕ, 0 ≤ 1 - S_er r j := by
    intro j; have : S_er r j ≤ 1/2 := hSer_le_half j; linarith
  -- widetildeMu_er ≥ 0.
  have hMu_nn : ∀ ℓ : Finset ℕ, 0 ≤ widetildeMu_er r ℓ := by
    intro ℓ
    show 0 ≤ ∏ j ∈ Finset.Icc 1 (n / 2), (if j ∈ ℓ then S_er r j else (1 - S_er r j))
    apply Finset.prod_nonneg
    intro j _
    by_cases hj : j ∈ ℓ
    · simp [hj]; exact hSer_nn j
    · simp [hj]; linarith [hOneMinusSer_nn j]
  -- Define light set L (the rare-support set).
  set L : Finset (Finset ℕ) := ((Finset.Icc 1 (n / 2)).powerset).filter
    (fun ℓ => widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))) with hL_def
  -- Bound 1: For ℓ ∈ L, widetildeMu_er r ℓ ≤ exp(-√n/4) · √widetildeMu_er r ℓ.
  have hLbound : ∀ ℓ ∈ L, widetildeMu_er r ℓ
      ≤ Real.exp (-(Real.sqrt n / 4)) * Real.sqrt (widetildeMu_er r ℓ) := by
    intro ℓ hℓ
    rw [hL_def, Finset.mem_filter] at hℓ
    have hμx : widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)) := hℓ.2
    have hμx_le : widetildeMu_er r ℓ ≤ Real.exp (-(Real.sqrt n / 2)) := le_of_lt hμx
    have hsqrt_le : Real.sqrt (widetildeMu_er r ℓ) ≤ Real.sqrt (Real.exp (-(Real.sqrt n / 2))) :=
      Real.sqrt_le_sqrt hμx_le
    have hexp_half : Real.sqrt (Real.exp (-(Real.sqrt n / 2)))
        = Real.exp (-(Real.sqrt n / 4)) := by
      rw [← Real.exp_half (-(Real.sqrt n / 2))]; congr 1; ring
    have hsqrt_le' : Real.sqrt (widetildeMu_er r ℓ) ≤ Real.exp (-(Real.sqrt n / 4)) :=
      hsqrt_le.trans hexp_half.le
    have hsqrt_nn : 0 ≤ Real.sqrt (widetildeMu_er r ℓ) := Real.sqrt_nonneg _
    have hsq : widetildeMu_er r ℓ
        = Real.sqrt (widetildeMu_er r ℓ) * Real.sqrt (widetildeMu_er r ℓ) :=
      (Real.mul_self_sqrt (hMu_nn ℓ)).symm
    calc widetildeMu_er r ℓ
        = Real.sqrt (widetildeMu_er r ℓ) * Real.sqrt (widetildeMu_er r ℓ) := hsq
      _ ≤ Real.exp (-(Real.sqrt n / 4)) * Real.sqrt (widetildeMu_er r ℓ) :=
          mul_le_mul_of_nonneg_right hsqrt_le' hsqrt_nn
  -- Bound 2: ∑_{ℓ ∈ L} √widetildeMu_er ≤ ∑_{ℓ ⊆ Icc 1 (n/2)} √widetildeMu_er ≤ exp(√n / (2e)).
  have hL_subset : L ⊆ (Finset.Icc 1 (n / 2)).powerset := Finset.filter_subset _ _
  have hsum_sqrt_le_full : (∑ ℓ ∈ L, Real.sqrt (widetildeMu_er r ℓ))
      ≤ ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset), Real.sqrt (widetildeMu_er r ℓ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hL_subset
    intros ℓ _ _; exact Real.sqrt_nonneg _
  have hsqrt_full_bound : (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset),
      Real.sqrt (widetildeMu_er r ℓ))
      ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1)) := by
    show (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset),
      Real.sqrt (∏ j ∈ Finset.Icc 1 (n / 2),
        (if j ∈ ℓ then
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
            binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        else
          (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
            binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))))))
      ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1))
    exact shifted_sqrt_sum_bound n hn1 r hSer_nn hSer_le_half
  -- Combine bounds.
  have hsum1 : (∑ ℓ ∈ L, widetildeMu_er r ℓ)
      ≤ ∑ ℓ ∈ L, Real.exp (-(Real.sqrt n / 4)) * Real.sqrt (widetildeMu_er r ℓ) :=
    Finset.sum_le_sum hLbound
  have hsum2 : (∑ ℓ ∈ L, Real.exp (-(Real.sqrt n / 4)) * Real.sqrt (widetildeMu_er r ℓ))
      = Real.exp (-(Real.sqrt n / 4)) * (∑ ℓ ∈ L, Real.sqrt (widetildeMu_er r ℓ)) := by
    rw [Finset.mul_sum]
  have hexp_pos' : 0 < Real.exp (-(Real.sqrt n / 4)) := Real.exp_pos _
  have hsum3 : Real.exp (-(Real.sqrt n / 4)) * (∑ ℓ ∈ L, Real.sqrt (widetildeMu_er r ℓ))
      ≤ Real.exp (-(Real.sqrt n / 4)) * Real.exp (Real.sqrt n / (2 * Real.exp 1)) :=
    mul_le_mul_of_nonneg_left (hsum_sqrt_le_full.trans hsqrt_full_bound) hexp_pos'.le
  have hcombined : (∑ ℓ ∈ L, widetildeMu_er r ℓ)
      ≤ Real.exp (-(Real.sqrt n / 4)) * Real.exp (Real.sqrt n / (2 * Real.exp 1)) :=
    hsum1.trans (hsum2 ▸ hsum3)
  have hexp_combine :
      Real.exp (-(Real.sqrt n / 4)) * Real.exp (Real.sqrt n / (2 * Real.exp 1))
        = Real.exp (-(Real.sqrt n / 4) + Real.sqrt n / (2 * Real.exp 1)) := by
    rw [← Real.exp_add]
  rw [hexp_combine] at hcombined
  -- Reduction: -√n/4 + √n/(2e) ≤ -√n/16.
  have he9 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h2e_pos : 0 < 2 * Real.exp 1 := by linarith
  have hbound_const : 1 / (2 * Real.exp 1) ≤ 3 / 16 := by
    rw [div_le_div_iff₀ h2e_pos (by norm_num : (0:ℝ) < 16)]
    nlinarith [he9]
  have hexp_ineq :
      -(Real.sqrt n / 4) + Real.sqrt n / (2 * Real.exp 1) ≤ -(Real.sqrt n / 16) := by
    have hkey : Real.sqrt n / (2 * Real.exp 1) ≤ Real.sqrt n * (3 / 16) := by
      have hmul : Real.sqrt n * (1 / (2 * Real.exp 1)) ≤ Real.sqrt n * (3 / 16) :=
        mul_le_mul_of_nonneg_left hbound_const hsqn_nn
      calc Real.sqrt n / (2 * Real.exp 1)
          = Real.sqrt n * (1 / (2 * Real.exp 1)) := by rw [div_eq_mul_inv, one_div]
        _ ≤ Real.sqrt n * (3 / 16) := hmul
    linarith [hkey, hsqn_nn]
  have hexp_final :
      Real.exp (-(Real.sqrt n / 4) + Real.sqrt n / (2 * Real.exp 1))
        ≤ Real.exp (-(Real.sqrt n / 16)) :=
    Real.exp_le_exp.mpr hexp_ineq
  show (∑ ℓ ∈ L, widetildeMu_er r ℓ) ≤ Real.exp (-(Real.sqrt n / 16))
  exact hcombined.trans hexp_final
