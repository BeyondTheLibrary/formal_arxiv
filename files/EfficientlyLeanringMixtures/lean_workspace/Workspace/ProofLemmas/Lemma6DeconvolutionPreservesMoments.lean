import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.MixtureRawMoments
import Workspace.ProofLemmas.SublemmaLemma6ConvolutionCase
import Workspace.ProofLemmas.SublemmaDeconvolutionMomentIdentity
import Workspace.ProofLemmas.SublemmaCentralMomentN0Tau
import Workspace.ProofLemmas.SublemmaBinomialCoefficientBound
import Workspace.ProofLemmas.M0OfMixtureDifferenceIsZero

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas

/-- Auxiliary: `Nat.doubleFactorial` step bound. -/
private lemma doubleFactorial_step_l6 (n : ℕ) :
    Nat.doubleFactorial n ≤ Nat.doubleFactorial (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | (m + 2) =>
      rw [Nat.doubleFactorial_add_two,
          show m + 2 + 1 = m + 1 + 2 from rfl,
          Nat.doubleFactorial_add_two]
      have h_ihm : Nat.doubleFactorial m ≤ Nat.doubleFactorial (m + 1) :=
        ih m (by omega)
      have h_le : (m + 2 : ℕ) ≤ m + 3 := by omega
      calc (m + 2) * Nat.doubleFactorial m
          ≤ (m + 2) * Nat.doubleFactorial (m + 1) :=
            Nat.mul_le_mul_left _ h_ihm
        _ ≤ (m + 3) * Nat.doubleFactorial (m + 1) :=
            Nat.mul_le_mul_right _ h_le

/-- Auxiliary: `Nat.doubleFactorial` is monotone. -/
private lemma doubleFactorial_le_of_le_l6 : ∀ {a b : ℕ}, a ≤ b →
    Nat.doubleFactorial a ≤ Nat.doubleFactorial b := by
  intro a b hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    have hrw : a + d + 1 = a + (d + 1) := by omega
    calc Nat.doubleFactorial a
        ≤ Nat.doubleFactorial (a + d) := ih
      _ ≤ Nat.doubleFactorial (a + d + 1) := doubleFactorial_step_l6 (a + d)
      _ = Nat.doubleFactorial (a + (d + 1)) := by rw [hrw]

/--
Paper's Lemma 6 (Moitra--Valiant). Deconvolution at parameter `α` preserves
moment gaps up to a `k · 2^k · (k-1)!!` multiplicative factor: for two-component
Gaussian mixtures `F`, `F'` whose every constituent variance lies in `[α, 1]`
and `α ≥ -1`, every integer `k ≥ 1` satisfies

  Σ_{i=0}^{k-1} |M_{i+1}(F_α(F)) − M_{i+1}(F_α(F'))|
    ≤ (k · 2^k · (k-1)!!) · Σ_{i=0}^{k-1} |M_{i+1}(F) − M_{i+1}(F')|.

The constant `k · 2^k · (k-1)!!` is the actual achievable constant arising from
the paper's explicit chain `C(j,i) < 2^k` combined with Equation (17).

The hypothesis `h_α_ge : (-1 : ℝ) ≤ α` is essential: without a lower bound on
α, the α < 0 case has deconvolved variances `σ² − α = σ² + |α|` that grow
without bound, breaking the moment estimates. The bound α ≥ -1 keeps the
deconvolved variances controlled (≤ 2) and matches the regime used by the
caller (Lemma 5).

For `k = 6`, the constant evaluates to `6 · 64 · 15 = 5760`.
-/
theorem Lemma6DeconvolutionPreservesMoments
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (α : ℝ)
    (h_F  : α < min F.comp1.varSq F.comp2.varSq)
    (h_F' : α < min F'.comp1.varSq F'.comp2.varSq)
    (h_α_ge : (-1 : ℝ) ≤ α)
    (h_var_upper : F.comp1.varSq ≤ 1 ∧ F.comp2.varSq ≤ 1
                    ∧ F'.comp1.varSq ≤ 1 ∧ F'.comp2.varSq ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    (Finset.range k).sum (fun i =>
        |Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
            (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F) (i + 1)
         - Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
            (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F') (i + 1)|)
    ≤ ((k : ℝ) * (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ))
       * (Finset.range k).sum (fun i =>
           |Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F (i + 1)
            - Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F' (i + 1)|) := by
  -- Case split on the sign of α. The α ≤ 0 case is handled directly by
  -- SublemmaLemma6ConvolutionCase, which now requires h_α_ge.
  by_cases hα : α ≤ 0
  · exact SublemmaLemma6ConvolutionCase F F' α h_F h_F' hα h_α_ge h_var_upper k hk
  -- α > 0 case.
  push_neg at hα
  -- Bind locals.
  set M : ℕ → ℝ := fun n => Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F n
    with hM_def
  set M' : ℕ → ℝ := fun n => Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F' n
    with hM'_def
  set Mα : ℕ → ℝ := fun n =>
    Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F) n
    with hMα_def
  set Mα' : ℕ → ℝ := fun n =>
    Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F') n
    with hMα'_def
  set Gα : Workspace.Types.GaussianPDF.GaussianPDF := ⟨0, α, hα⟩ with hGα_def
  set MG : ℕ → ℝ := fun j =>
    Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα j with hMG_def
  set sgn : ℕ → ℝ := fun j =>
    if j % 4 = 0 then (1 : ℝ) else if j % 4 = 2 then (-1 : ℝ) else 0 with hsgn_def
  -- Expansions of Mα n and Mα' n via SublemmaDeconvolutionMomentIdentity.
  have expand_F : ∀ n : ℕ, Mα n =
      (Finset.range (n + 1)).sum (fun j =>
        (Nat.choose n j : ℝ) * M (n - j) * (sgn j * MG j)) := by
    intro n
    simpa [hMα_def, hM_def, hMG_def, hGα_def, hsgn_def]
      using SublemmaDeconvolutionMomentIdentity F α hα h_F n
  have expand_F' : ∀ n : ℕ, Mα' n =
      (Finset.range (n + 1)).sum (fun j =>
        (Nat.choose n j : ℝ) * M' (n - j) * (sgn j * MG j)) := by
    intro n
    simpa [hMα'_def, hM'_def, hMG_def, hGα_def, hsgn_def]
      using SublemmaDeconvolutionMomentIdentity F' α hα h_F' n
  -- Difference identity.
  have diff_eq : ∀ n : ℕ, Mα n - Mα' n =
      (Finset.range (n + 1)).sum (fun j =>
        (Nat.choose n j : ℝ) * (M (n - j) - M' (n - j)) * (sgn j * MG j)) := by
    intro n
    rw [expand_F n, expand_F' n, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Bound |sgn j| ≤ 1.
  have hsgn_abs_le : ∀ j : ℕ, |sgn j| ≤ 1 := by
    intro j
    simp only [hsgn_def]
    split_ifs <;> norm_num
  -- α ≤ 1 from variance hypotheses.
  have hα_le_one : α ≤ 1 := by
    have h1 : α < F.comp1.varSq :=
      lt_of_lt_of_le h_F (min_le_left _ _)
    linarith [h_var_upper.1]
  -- √α ≤ 1.
  have h_sqrt_α_nonneg : 0 ≤ Real.sqrt α := Real.sqrt_nonneg _
  have h_sqrt_α_le_one : Real.sqrt α ≤ 1 := by
    have h : Real.sqrt α ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hα_le_one
    simpa using h
  -- Power bound: √α^j ≤ 1 for all j.
  have h_sqrt_α_pow_le_one : ∀ j : ℕ, Real.sqrt α ^ j ≤ 1 := by
    intro j
    exact pow_le_one₀ h_sqrt_α_nonneg h_sqrt_α_le_one
  -- |MG j| ≤ (j-1)!! for all j.
  have hCentral := SublemmaCentralMomentN0Tau α hα
  have hMG_abs_le : ∀ j : ℕ, |MG j| ≤ (Nat.doubleFactorial (j - 1) : ℝ) := by
    intro j
    have hj := hCentral j
    rcases Nat.even_or_odd j with he | ho
    · -- Even
      have hval : MG j = (Nat.doubleFactorial (j - 1) : ℝ) * Real.sqrt α ^ j := by
        simpa [hMG_def, hGα_def] using hj.2 he
      rw [hval, abs_mul]
      have h1 : |(Nat.doubleFactorial (j - 1) : ℝ)| = (Nat.doubleFactorial (j - 1) : ℝ) := by
        apply abs_of_nonneg
        exact_mod_cast Nat.zero_le _
      rw [h1]
      have h2 : |Real.sqrt α ^ j| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg h_sqrt_α_nonneg _)]
        exact h_sqrt_α_pow_le_one j
      have hDFnn : (0 : ℝ) ≤ (Nat.doubleFactorial (j - 1) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      calc (Nat.doubleFactorial (j - 1) : ℝ) * |Real.sqrt α ^ j|
          ≤ (Nat.doubleFactorial (j - 1) : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left h2 hDFnn
        _ = (Nat.doubleFactorial (j - 1) : ℝ) := by ring
    · -- Odd
      have hzero : MG j = 0 := by
        simpa [hMG_def, hGα_def] using hj.1 ho
      rw [hzero, abs_zero]
      exact_mod_cast Nat.zero_le _
  -- |sgn j * MG j| ≤ (j-1)!!.
  have hsgn_MG_abs_le : ∀ j : ℕ, |sgn j * MG j| ≤ (Nat.doubleFactorial (j - 1) : ℝ) := by
    intro j
    rw [abs_mul]
    have hDFnn : (0 : ℝ) ≤ (Nat.doubleFactorial (j - 1) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    calc |sgn j| * |MG j|
        ≤ 1 * (Nat.doubleFactorial (j - 1) : ℝ) :=
          mul_le_mul (hsgn_abs_le j) (hMG_abs_le j) (abs_nonneg _) (by norm_num)
      _ = (Nat.doubleFactorial (j - 1) : ℝ) := by ring
  -- Bound |sgn j MG j| ≤ (k-1)!! for j ≤ k.
  have hsgn_MG_abs_le_k : ∀ j : ℕ, j ≤ k →
      |sgn j * MG j| ≤ (Nat.doubleFactorial (k - 1) : ℝ) := by
    intro j hjk
    refine (hsgn_MG_abs_le j).trans ?_
    have : Nat.doubleFactorial (j - 1) ≤ Nat.doubleFactorial (k - 1) :=
      doubleFactorial_le_of_le_l6 (by omega)
    exact_mod_cast this
  -- Bound (n choose j) ≤ 2^k for n ≤ k, j ≤ n.
  have hChoose_le : ∀ j n : ℕ, j ≤ n → n ≤ k → (Nat.choose n j : ℝ) ≤ (2 : ℝ) ^ k := by
    intro j n hjn hnk
    have := SublemmaBinomialCoefficientBound j n k hjn hnk
    exact_mod_cast this
  -- Triangle on the sum: bound |Mα n - Mα' n| for n ≤ k.
  have abs_diff_bound : ∀ n : ℕ, 1 ≤ n → n ≤ k →
      |Mα n - Mα' n| ≤
        (Finset.range (n + 1)).sum (fun j =>
          (Nat.choose n j : ℝ) * |M (n - j) - M' (n - j)| *
            (Nat.doubleFactorial (k - 1) : ℝ)) := by
    intro n _hn1 hnk
    rw [diff_eq n]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := by omega
    have hprod_abs : |(Nat.choose n j : ℝ) * (M (n - j) - M' (n - j)) * (sgn j * MG j)|
          = (Nat.choose n j : ℝ) * |M (n - j) - M' (n - j)| * |sgn j * MG j| := by
      rw [abs_mul, abs_mul]
      have h1 : |(Nat.choose n j : ℝ)| = (Nat.choose n j : ℝ) := by
        apply abs_of_nonneg
        exact_mod_cast Nat.zero_le _
      rw [h1]
    rw [hprod_abs]
    have h_choose_nn : (0 : ℝ) ≤ (Nat.choose n j : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_diff_nn : (0 : ℝ) ≤ |M (n - j) - M' (n - j)| := abs_nonneg _
    have h_prod_nn : (0 : ℝ) ≤ (Nat.choose n j : ℝ) * |M (n - j) - M' (n - j)| :=
      mul_nonneg h_choose_nn h_diff_nn
    exact mul_le_mul_of_nonneg_left
      (hsgn_MG_abs_le_k j (hjn.trans hnk)) h_prod_nn
  -- Now bound the choose factor by 2^k as well.
  have abs_diff_bound2 : ∀ n : ℕ, 1 ≤ n → n ≤ k →
      |Mα n - Mα' n| ≤
        (Finset.range (n + 1)).sum (fun j =>
          (2 : ℝ) ^ k * |M (n - j) - M' (n - j)| *
            (Nat.doubleFactorial (k - 1) : ℝ)) := by
    intro n hn1 hnk
    refine (abs_diff_bound n hn1 hnk).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := by omega
    have h_choose := hChoose_le j n hjn hnk
    have h_diff_nn : (0 : ℝ) ≤ |M (n - j) - M' (n - j)| := abs_nonneg _
    have hDF_nn : (0 : ℝ) ≤ (Nat.doubleFactorial (k - 1) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have step1 : (Nat.choose n j : ℝ) * |M (n - j) - M' (n - j)| ≤
        (2 : ℝ) ^ k * |M (n - j) - M' (n - j)| :=
      mul_le_mul_of_nonneg_right h_choose h_diff_nn
    exact mul_le_mul_of_nonneg_right step1 hDF_nn
  -- M(0) = M'(0) from M0OfMixtureDifferenceIsZero.
  have hM0 := M0OfMixtureDifferenceIsZero F F'
  have hM0_eq : M 0 = M' 0 := by
    simp only [hM_def, hM'_def]
    linarith [hM0.1, hM0.2.1]
  have h_M0_diff_zero : |M 0 - M' 0| = 0 := by rw [hM0_eq, sub_self, abs_zero]
  -- Set S as the RHS sum.
  set S : ℝ := (Finset.range k).sum (fun i => |M (i + 1) - M' (i + 1)|) with hS_def
  have hS_nn : 0 ≤ S := by
    apply Finset.sum_nonneg
    intros; exact abs_nonneg _
  -- Inner sum lemma: for each n with n ≤ k,
  --   Σ_{m=0}^{n} |M(m) - M'(m)| ≤ S.
  have inner_sum_bound : ∀ n : ℕ, n ≤ k →
      (Finset.range (n + 1)).sum (fun m => |M m - M' m|) ≤ S := by
    intro n hnk
    rw [Finset.sum_range_succ']
    -- Σ_{i in range n} |M(i+1) - M'(i+1)| + |M(0) - M'(0)|
    rw [h_M0_diff_zero, add_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intros; exact abs_nonneg _
  -- inner_bound: for each n with n ≤ k,
  --   Σ_{j=0}^{n} 2^k · |M(n-j) - M'(n-j)| · (k-1)!! ≤ 2^k · (k-1)!! · S.
  have inner_bound : ∀ n : ℕ, n ≤ k →
      (Finset.range (n + 1)).sum (fun j =>
        (2 : ℝ) ^ k * |M (n - j) - M' (n - j)| * (Nat.doubleFactorial (k - 1) : ℝ))
        ≤ (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S := by
    intro n hnk
    -- First, the inner sum equals 2^k · (k-1)!! · Σ_{j=0}^{n} |M(n-j) - M'(n-j)|.
    have eq_step : (Finset.range (n + 1)).sum (fun j =>
        (2 : ℝ) ^ k * |M (n - j) - M' (n - j)| * (Nat.doubleFactorial (k - 1) : ℝ))
      = (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) *
          (Finset.range (n + 1)).sum (fun j => |M (n - j) - M' (n - j)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros j _
      ring
    rw [eq_step]
    -- Reindex via Finset.sum_flip: Σ_{j=0}^{n} f(n-j) = Σ_{j=0}^{n} f(j).
    have reindex_eq :
        (Finset.range (n + 1)).sum (fun j => |M (n - j) - M' (n - j)|)
          = (Finset.range (n + 1)).sum (fun m => |M m - M' m|) :=
      Finset.sum_flip (fun m => |M m - M' m|)
    rw [reindex_eq]
    have h := inner_sum_bound n hnk
    have h_pos : (0 : ℝ) ≤ (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) := by
      apply mul_nonneg
      · exact pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _
      · exact_mod_cast Nat.zero_le _
    exact mul_le_mul_of_nonneg_left h h_pos
  -- Outer sum bound: ≤ k · 2^k · (k-1)!! · S.
  have outer_bound :
      (Finset.range k).sum (fun i => |Mα (i + 1) - Mα' (i + 1)|)
        ≤ (k : ℝ) * ((2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S) := by
    have outer_chain :
        (Finset.range k).sum (fun i => |Mα (i + 1) - Mα' (i + 1)|)
          ≤ (Finset.range k).sum (fun (_ : ℕ) =>
            (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S) := by
      apply Finset.sum_le_sum
      intros i hi
      rw [Finset.mem_range] at hi
      have h1 : 1 ≤ i + 1 := by omega
      have h2 : i + 1 ≤ k := by omega
      calc |Mα (i + 1) - Mα' (i + 1)|
          ≤ (Finset.range ((i + 1) + 1)).sum (fun j =>
              (2 : ℝ) ^ k * |M ((i + 1) - j) - M' ((i + 1) - j)| *
                (Nat.doubleFactorial (k - 1) : ℝ)) :=
            abs_diff_bound2 (i + 1) h1 h2
        _ ≤ (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S :=
            inner_bound (i + 1) h2
    refine outer_chain.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- The new constant is exactly k · 2^k · (k-1)!! — outer_bound suffices.
  have h_reorder :
      (k : ℝ) * ((2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S)
        = ((k : ℝ) * (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ)) * S := by ring
  rw [h_reorder] at outer_bound
  exact outer_bound

end Workspace.ProofLemmas
