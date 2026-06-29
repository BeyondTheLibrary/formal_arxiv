/-
Attempt 7 — fix structure equality proofs using `congr 1` after rewriting to `shiftGaussian` form.
-/
import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.MixtureRawMoments
import Workspace.ProofLemmas.SublemmaMomentOfSumOfIndependents
import Workspace.ProofLemmas.SublemmaMixtureMomentLinearity
import Workspace.ProofLemmas.SublemmaCentralMomentN0Tau
import Workspace.ProofLemmas.SublemmaBinomialCoefficientBound
import Workspace.ProofLemmas.M0OfMixtureDifferenceIsZero

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas

/-- Auxiliary: `Nat.doubleFactorial` step bound. -/
private lemma doubleFactorial_step_conv (n : ℕ) :
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
private lemma doubleFactorial_le_of_le_conv : ∀ {a b : ℕ}, a ≤ b →
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
      _ ≤ Nat.doubleFactorial (a + d + 1) := doubleFactorial_step_conv (a + d)
      _ = Nat.doubleFactorial (a + (d + 1)) := by rw [hrw]

/-- 1 ≤ doubleFactorial n for all n. -/
private lemma one_le_doubleFactorial : ∀ n : ℕ, 1 ≤ Nat.doubleFactorial n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | (m + 2) =>
      rw [Nat.doubleFactorial_add_two]
      have hdf : 1 ≤ Nat.doubleFactorial m := ih m (by omega)
      have : 1 = 1 * 1 := by ring
      rw [this]
      exact Nat.mul_le_mul (by omega) hdf

/-- α = 0 case helper: deconv with α = 0 doesn't change moments. -/
private lemma deconv_zero_moment_eq
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (h : (0 : ℝ) < min F.comp1.varSq F.comp2.varSq) (i : ℕ) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F 0 h) i
      = Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F i := by
  unfold Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
  congr 1
  ext x
  congr 1
  rw [Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq,
      Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq]
  simp [Workspace.Types.MixtureDeconvolution.deconvMixture2,
        Workspace.Types.MixtureDeconvolution.shiftGaussian,
        Workspace.Types.GaussianPDF.GaussianPDF.density_eq]

theorem SublemmaLemma6ConvolutionCase
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (α : ℝ)
    (h_F  : α < min F.comp1.varSq F.comp2.varSq)
    (h_F' : α < min F'.comp1.varSq F'.comp2.varSq)
    (h_α_le : α ≤ 0)
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
  set S : ℝ := (Finset.range k).sum (fun i => |M (i + 1) - M' (i + 1)|) with hS_def
  have hS_nn : 0 ≤ S := by
    apply Finset.sum_nonneg; intros; exact abs_nonneg _
  rcases lt_or_eq_of_le h_α_le with hα_neg | hα_zero
  · -- α < 0 case
    set α' : ℝ := -α with hα'_def
    have hα'_pos : 0 < α' := by rw [hα'_def]; linarith
    have hα'_le_one : α' ≤ 1 := by rw [hα'_def]; linarith
    have h_sqrt_α'_nonneg : 0 ≤ Real.sqrt α' := Real.sqrt_nonneg _
    have h_sqrt_α'_le_one : Real.sqrt α' ≤ 1 := by
      have h : Real.sqrt α' ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hα'_le_one
      simpa using h
    have h_sqrt_α'_pow_le_one : ∀ j : ℕ, Real.sqrt α' ^ j ≤ 1 :=
      fun j => pow_le_one₀ h_sqrt_α'_nonneg h_sqrt_α'_le_one
    set G0 : Workspace.Types.GaussianPDF.GaussianPDF := ⟨0, α', hα'_pos⟩ with hG0_def
    set MG : ℕ → ℝ := fun j =>
      Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G0 j with hMG_def
    -- |MG j| ≤ (j-1)!!
    have hCentral := SublemmaCentralMomentN0Tau α' hα'_pos
    have hMG_abs_le : ∀ j : ℕ, |MG j| ≤ (Nat.doubleFactorial (j - 1) : ℝ) := by
      intro j
      have hj := hCentral j
      rcases Nat.even_or_odd j with he | ho
      · have hval : MG j = (Nat.doubleFactorial (j - 1) : ℝ) * Real.sqrt α' ^ j := by
          simpa [hMG_def, hG0_def] using hj.2 he
        rw [hval, abs_mul]
        have h1 : |(Nat.doubleFactorial (j - 1) : ℝ)| = (Nat.doubleFactorial (j - 1) : ℝ) := by
          apply abs_of_nonneg; exact_mod_cast Nat.zero_le _
        rw [h1]
        have h2 : |Real.sqrt α' ^ j| ≤ 1 := by
          rw [abs_of_nonneg (pow_nonneg h_sqrt_α'_nonneg _)]
          exact h_sqrt_α'_pow_le_one j
        have hDFnn : (0 : ℝ) ≤ (Nat.doubleFactorial (j - 1) : ℝ) := by
          exact_mod_cast Nat.zero_le _
        calc (Nat.doubleFactorial (j - 1) : ℝ) * |Real.sqrt α' ^ j|
            ≤ (Nat.doubleFactorial (j - 1) : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left h2 hDFnn
          _ = (Nat.doubleFactorial (j - 1) : ℝ) := by ring
      · have hzero : MG j = 0 := by simpa [hMG_def, hG0_def] using hj.1 ho
        rw [hzero, abs_zero]
        exact_mod_cast Nat.zero_le _
    have hMG_abs_le_k : ∀ j : ℕ, j ≤ k →
        |MG j| ≤ (Nat.doubleFactorial (k - 1) : ℝ) := by
      intro j hjk
      refine (hMG_abs_le j).trans ?_
      have : Nat.doubleFactorial (j - 1) ≤ Nat.doubleFactorial (k - 1) :=
        doubleFactorial_le_of_le_conv (by omega)
      exact_mod_cast this
    -- Sum-identity for each component
    have hsum_comp1_F : ∀ n : ℕ,
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
            (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp1 n
          = (Finset.range (n + 1)).sum (fun j =>
              (Nat.choose n j : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F.comp1 (n - j) *
                MG j) := by
      intro n
      have hsum := SublemmaMomentOfSumOfIndependents F.comp1 G0 n
      have h_param_eq :
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp1
            = (⟨F.comp1.mean + G0.mean, F.comp1.varSq + G0.varSq,
                add_pos F.comp1.varSq_pos G0.varSq_pos⟩
              : Workspace.Types.GaussianPDF.GaussianPDF) := by
        rw [show (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp1
              = Workspace.Types.MixtureDeconvolution.shiftGaussian F.comp1 α
                  (lt_of_lt_of_le h_F (min_le_left _ _)) from rfl]
        congr 1 <;>
          simp [hG0_def, hα'_def, Workspace.Types.MixtureDeconvolution.shiftGaussian] <;>
            linarith
      rw [h_param_eq]
      simpa [hMG_def] using hsum
    have hsum_comp2_F : ∀ n : ℕ,
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
            (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp2 n
          = (Finset.range (n + 1)).sum (fun j =>
              (Nat.choose n j : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F.comp2 (n - j) *
                MG j) := by
      intro n
      have hsum := SublemmaMomentOfSumOfIndependents F.comp2 G0 n
      have h_param_eq :
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp2
            = (⟨F.comp2.mean + G0.mean, F.comp2.varSq + G0.varSq,
                add_pos F.comp2.varSq_pos G0.varSq_pos⟩
              : Workspace.Types.GaussianPDF.GaussianPDF) := by
        rw [show (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp2
              = Workspace.Types.MixtureDeconvolution.shiftGaussian F.comp2 α
                  (lt_of_lt_of_le h_F (min_le_right _ _)) from rfl]
        congr 1 <;>
          simp [hG0_def, hα'_def, Workspace.Types.MixtureDeconvolution.shiftGaussian] <;>
            linarith
      rw [h_param_eq]
      simpa [hMG_def] using hsum
    have hsum_comp1_F' : ∀ n : ℕ,
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
            (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp1 n
          = (Finset.range (n + 1)).sum (fun j =>
              (Nat.choose n j : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F'.comp1 (n - j) *
                MG j) := by
      intro n
      have hsum := SublemmaMomentOfSumOfIndependents F'.comp1 G0 n
      have h_param_eq :
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp1
            = (⟨F'.comp1.mean + G0.mean, F'.comp1.varSq + G0.varSq,
                add_pos F'.comp1.varSq_pos G0.varSq_pos⟩
              : Workspace.Types.GaussianPDF.GaussianPDF) := by
        rw [show (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp1
              = Workspace.Types.MixtureDeconvolution.shiftGaussian F'.comp1 α
                  (lt_of_lt_of_le h_F' (min_le_left _ _)) from rfl]
        congr 1 <;>
          simp [hG0_def, hα'_def, Workspace.Types.MixtureDeconvolution.shiftGaussian] <;>
            linarith
      rw [h_param_eq]
      simpa [hMG_def] using hsum
    have hsum_comp2_F' : ∀ n : ℕ,
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
            (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp2 n
          = (Finset.range (n + 1)).sum (fun j =>
              (Nat.choose n j : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F'.comp2 (n - j) *
                MG j) := by
      intro n
      have hsum := SublemmaMomentOfSumOfIndependents F'.comp2 G0 n
      have h_param_eq :
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp2
            = (⟨F'.comp2.mean + G0.mean, F'.comp2.varSq + G0.varSq,
                add_pos F'.comp2.varSq_pos G0.varSq_pos⟩
              : Workspace.Types.GaussianPDF.GaussianPDF) := by
        rw [show (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp2
              = Workspace.Types.MixtureDeconvolution.shiftGaussian F'.comp2 α
                  (lt_of_lt_of_le h_F' (min_le_right _ _)) from rfl]
        congr 1 <;>
          simp [hG0_def, hα'_def, Workspace.Types.MixtureDeconvolution.shiftGaussian] <;>
            linarith
      rw [h_param_eq]
      simpa [hMG_def] using hsum
    -- Mixture-level linearity
    have hMα_linearity : ∀ n : ℕ,
        Mα n = F.weight1 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp1 n
              + F.weight2 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp2 n := by
      intro n
      have h := SublemmaMixtureMomentLinearity
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F) n
      simp only [hMα_def]
      simp only [Workspace.Types.MixtureDeconvolution.deconvMixture2_weight1,
                 Workspace.Types.MixtureDeconvolution.deconvMixture2_weight2] at h
      exact h
    have hMα'_linearity : ∀ n : ℕ,
        Mα' n = F'.weight1 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp1 n
              + F'.weight2 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp2 n := by
      intro n
      have h := SublemmaMixtureMomentLinearity
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F') n
      simp only [hMα'_def]
      simp only [Workspace.Types.MixtureDeconvolution.deconvMixture2_weight1,
                 Workspace.Types.MixtureDeconvolution.deconvMixture2_weight2] at h
      exact h
    have hM_linearity : ∀ n : ℕ,
        M n = F.weight1 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F.comp1 n
              + F.weight2 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F.comp2 n := by
      intro n
      simp only [hM_def]
      exact SublemmaMixtureMomentLinearity F n
    have hM'_linearity : ∀ n : ℕ,
        M' n = F'.weight1 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F'.comp1 n
              + F'.weight2 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F'.comp2 n := by
      intro n
      simp only [hM'_def]
      exact SublemmaMixtureMomentLinearity F' n
    have expand_F : ∀ n : ℕ,
        Mα n = (Finset.range (n + 1)).sum (fun j =>
                (Nat.choose n j : ℝ) * M (n - j) * MG j) := by
      intro n
      rw [hMα_linearity n, hsum_comp1_F n, hsum_comp2_F n]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hM_nj := hM_linearity (n - j)
      rw [hM_nj]
      ring
    have expand_F' : ∀ n : ℕ,
        Mα' n = (Finset.range (n + 1)).sum (fun j =>
                (Nat.choose n j : ℝ) * M' (n - j) * MG j) := by
      intro n
      rw [hMα'_linearity n, hsum_comp1_F' n, hsum_comp2_F' n]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hM'_nj := hM'_linearity (n - j)
      rw [hM'_nj]
      ring
    have diff_eq : ∀ n : ℕ, Mα n - Mα' n =
        (Finset.range (n + 1)).sum (fun j =>
          (Nat.choose n j : ℝ) * (M (n - j) - M' (n - j)) * MG j) := by
      intro n
      rw [expand_F n, expand_F' n, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hChoose_le : ∀ j n : ℕ, j ≤ n → n ≤ k → (Nat.choose n j : ℝ) ≤ (2 : ℝ) ^ k := by
      intro j n hjn hnk
      have := SublemmaBinomialCoefficientBound j n k hjn hnk
      exact_mod_cast this
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
      have hprod_abs : |(Nat.choose n j : ℝ) * (M (n - j) - M' (n - j)) * MG j|
            = (Nat.choose n j : ℝ) * |M (n - j) - M' (n - j)| * |MG j| := by
        rw [abs_mul, abs_mul]
        have h1 : |(Nat.choose n j : ℝ)| = (Nat.choose n j : ℝ) := by
          apply abs_of_nonneg; exact_mod_cast Nat.zero_le _
        rw [h1]
      rw [hprod_abs]
      have h_choose_nn : (0 : ℝ) ≤ (Nat.choose n j : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_diff_nn : (0 : ℝ) ≤ |M (n - j) - M' (n - j)| := abs_nonneg _
      have h_prod_nn : (0 : ℝ) ≤ (Nat.choose n j : ℝ) * |M (n - j) - M' (n - j)| :=
        mul_nonneg h_choose_nn h_diff_nn
      exact mul_le_mul_of_nonneg_left
        (hMG_abs_le_k j (hjn.trans hnk)) h_prod_nn
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
    have hM0 := M0OfMixtureDifferenceIsZero F F'
    have hM0_eq : M 0 = M' 0 := by
      simp only [hM_def, hM'_def]
      linarith [hM0.1, hM0.2.1]
    have h_M0_diff_zero : |M 0 - M' 0| = 0 := by rw [hM0_eq, sub_self, abs_zero]
    have inner_sum_bound : ∀ n : ℕ, n ≤ k →
        (Finset.range (n + 1)).sum (fun m => |M m - M' m|) ≤ S := by
      intro n hnk
      rw [Finset.sum_range_succ']
      rw [h_M0_diff_zero, add_zero]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
      · intros; exact abs_nonneg _
    have inner_bound : ∀ n : ℕ, n ≤ k →
        (Finset.range (n + 1)).sum (fun j =>
          (2 : ℝ) ^ k * |M (n - j) - M' (n - j)| * (Nat.doubleFactorial (k - 1) : ℝ))
          ≤ (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S := by
      intro n hnk
      have eq_step : (Finset.range (n + 1)).sum (fun j =>
          (2 : ℝ) ^ k * |M (n - j) - M' (n - j)| * (Nat.doubleFactorial (k - 1) : ℝ))
        = (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) *
            (Finset.range (n + 1)).sum (fun j => |M (n - j) - M' (n - j)|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros j _
        ring
      rw [eq_step]
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
    have h_reorder :
        (k : ℝ) * ((2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) * S)
          = ((k : ℝ) * (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ)) * S := by ring
    rw [h_reorder] at outer_bound
    exact outer_bound
  · -- α = 0 case
    subst hα_zero
    have hMα_eq : ∀ n, Mα n = M n := by
      intro n; simp only [Mα, M]
      exact deconv_zero_moment_eq F h_F n
    have hMα'_eq : ∀ n, Mα' n = M' n := by
      intro n; simp only [Mα', M']
      exact deconv_zero_moment_eq F' h_F' n
    have h_lhs_eq :
        (Finset.range k).sum (fun i => |Mα (i + 1) - Mα' (i + 1)|) = S := by
      simp only [hS_def]
      apply Finset.sum_congr rfl
      intro i _
      rw [hMα_eq, hMα'_eq]
    show (Finset.range k).sum (fun i => |Mα (i + 1) - Mα' (i + 1)|)
      ≤ ((k : ℝ) * (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ)) * S
    rw [h_lhs_eq]
    have h_const : (1 : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ) := by
      have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
        one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
      have hDF : (1 : ℝ) ≤ (Nat.doubleFactorial (k - 1) : ℝ) := by
        have : 1 ≤ Nat.doubleFactorial (k - 1) := one_le_doubleFactorial _
        exact_mod_cast this
      have h1 : (1 : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ k := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (k : ℝ) * (2 : ℝ) ^ k :=
              mul_le_mul hk_real h2k (by norm_num) (by linarith)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((k : ℝ) * (2 : ℝ) ^ k) * (Nat.doubleFactorial (k - 1) : ℝ) :=
            mul_le_mul h1 hDF (by norm_num) (by linarith)
    calc S = 1 * S := by ring
      _ ≤ ((k : ℝ) * (2 : ℝ) ^ k * (Nat.doubleFactorial (k - 1) : ℝ)) * S :=
          mul_le_mul_of_nonneg_right h_const hS_nn

end Workspace.ProofLemmas
