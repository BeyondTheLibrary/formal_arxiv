/-
Attempt 7 — Complete proof of the deconvolution moment identity, fixing
the 11 errors found in Attempt 5 (mostly: surplus `ring`/`ring_nf`/`linarith`
after a tactic already closed the goal, mishandled `mod_cast` on factorial
products, wrong tactic signature for `Finset.sum_nbij'`, and an outdated
`Finset.range_succ` name).
-/
import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureRawMoments
import Workspace.Types.MixtureDeconvolution
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian
import Workspace.ProofLemmas.SublemmaCentralMomentN0Tau
import Workspace.ProofLemmas.SublemmaMixtureMomentLinearity
import Workspace.ProofLemmas.SublemmaMomentOfSumOfIndependents

set_option maxHeartbeats 8000000

namespace Workspace.ProofLemmas

open MeasureTheory ProbabilityTheory

/-! ### Signed moments b_j (formal moments of N(0, -α)) -/

private noncomputable def signedMomN (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (n + 2) => -((n : ℝ) + 1) * α * signedMomN α n

private lemma signedMomN_zero (α : ℝ) : signedMomN α 0 = 1 := rfl
private lemma signedMomN_one (α : ℝ) : signedMomN α 1 = 0 := rfl
private lemma signedMomN_add_two (α : ℝ) (n : ℕ) :
    signedMomN α (n + 2) = -((n : ℝ) + 1) * α * signedMomN α n := rfl

private lemma signedMomN_odd (α : ℝ) (j : ℕ) (hodd : Odd j) :
    signedMomN α j = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => exact absurd hodd (by decide)
    | 1 => rfl
    | (n + 2) =>
      rw [signedMomN_add_two]
      have hn_odd : Odd n := by
        rcases hodd with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      rw [ih n (by omega) hn_odd]
      ring

private lemma signedMomN_even (α : ℝ) (k : ℕ) :
    signedMomN α (2 * k) = (-α)^k * (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
  induction k with
  | zero => simp [signedMomN_zero, Nat.doubleFactorial]
  | succ k ih =>
    have h2k_eq : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2k_eq]
    show -((2 * k : ℕ) + 1 : ℝ) * α * signedMomN α (2 * k) = (-α)^(k+1) * (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ)
    rw [ih]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp [Nat.doubleFactorial]
    · have h1 : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
      have hDF_eq : Nat.doubleFactorial (2 * (k + 1) - 1) =
          (2 * k - 1 + 2) * Nat.doubleFactorial (2 * k - 1) := by
        rw [h1, Nat.doubleFactorial_add_two]
      have hcast : ((2 * k - 1 + 2 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by
        have : 2 * k - 1 + 2 = 2 * k + 1 := by omega
        rw [this]; push_cast; ring
      rw [hDF_eq]
      push_cast [hcast]
      ring

/-! ### Closed forms for moments of N(0,α) -/

private lemma momentN0_even (α : ℝ) (hα_pos : 0 < α) (k : ℕ) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        ⟨(0 : ℝ), α, hα_pos⟩ (2 * k)
      = (Nat.doubleFactorial (2 * k - 1) : ℝ) * α ^ k := by
  have hCentral := SublemmaCentralMomentN0Tau α hα_pos (2 * k)
  have h_even_2k : Even (2 * k) := ⟨k, by ring⟩
  have hM_even := hCentral.2 h_even_2k
  rw [hM_even]
  have hsqrt_sq : Real.sqrt α ^ (2 * k) = α ^ k := by
    have h1 : Real.sqrt α ^ (2 * k) = (Real.sqrt α ^ 2) ^ k := by
      rw [← pow_mul, mul_comm]
    rw [h1, Real.sq_sqrt (le_of_lt hα_pos)]
  rw [hsqrt_sq]

private lemma momentN0_odd (α : ℝ) (hα_pos : 0 < α) (j : ℕ) (hodd : Odd j) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        ⟨(0 : ℝ), α, hα_pos⟩ j = 0 := by
  exact (SublemmaCentralMomentN0Tau α hα_pos j).1 hodd

private lemma signedMomN_eq_c_M (α : ℝ) (hα_pos : 0 < α) (j : ℕ) :
    signedMomN α j =
      (if j % 4 = 0 then (1 : ℝ) else if j % 4 = 2 then (-1 : ℝ) else 0) *
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
          ⟨(0 : ℝ), α, hα_pos⟩ j := by
  rcases Nat.even_or_odd j with hjeven | hjodd
  · obtain ⟨k, hk⟩ := hjeven
    have hj_eq : j = 2 * k := by omega
    rw [hj_eq, signedMomN_even, momentN0_even α hα_pos]
    have hc_eq : (if (2 * k) % 4 = 0 then (1 : ℝ) else if (2 * k) % 4 = 2 then (-1 : ℝ) else 0)
        = (-1) ^ k := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · have h1 : (2 * k) % 4 = 0 := by omega
        simp [h1]
        rw [show k = 2 * m from by omega, pow_mul]
        norm_num
      · have h1 : (2 * k) % 4 = 2 := by omega
        simp [h1]
        rw [show k = 2 * m + 1 from hm, pow_add, pow_mul]
        simp [pow_one]
    rw [hc_eq, show (-α)^k = (-1)^k * α^k from by rw [neg_pow]]
    ring
  · rw [signedMomN_odd α j hjodd, momentN0_odd α hα_pos j hjodd]
    ring

/-! ### Key combinatorial identity -/

/-- `Σ_{m=0..k} (-1)^(k-m) / (m! (k-m)!) = 0` for k ≥ 1. -/
private lemma alt_sum_inv_fact_zero (k : ℕ) (hk : 1 ≤ k) :
    (Finset.range (k + 1)).sum (fun m =>
      ((-1 : ℝ) ^ (k - m)) / ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) = 0 := by
  have h_fact_k_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h_fact_k_ne : (Nat.factorial k : ℝ) ≠ 0 := ne_of_gt h_fact_k_pos
  -- Multiply by k!.
  have h_pow_zero : ((1 + (-1) : ℝ)) ^ k = 0 := by
    have h1plusneg1 : (1 + (-1) : ℝ) = 0 := by norm_num
    rw [h1plusneg1]
    exact zero_pow (by omega)
  have h_add_pow : ((1 + (-1) : ℝ)) ^ k =
      (Finset.range (k + 1)).sum (fun m =>
        (1 : ℝ) ^ m * (-1 : ℝ) ^ (k - m) * (Nat.choose k m : ℝ)) :=
    add_pow 1 (-1) k
  rw [h_pow_zero] at h_add_pow
  have h_sum_zero : (Finset.range (k + 1)).sum (fun m =>
      (Nat.choose k m : ℝ) * (-1 : ℝ) ^ (k - m)) = 0 := by
    have h_eq : (Finset.range (k + 1)).sum (fun m =>
        (1 : ℝ) ^ m * (-1 : ℝ) ^ (k - m) * (Nat.choose k m : ℝ))
        = (Finset.range (k + 1)).sum (fun m =>
          (Nat.choose k m : ℝ) * (-1 : ℝ) ^ (k - m)) := by
      apply Finset.sum_congr rfl
      intros m _hm
      ring
    rw [h_eq] at h_add_pow
    linarith
  -- Σ_m (-1)^(k-m) / (m!(k-m)!) * k! = Σ_m C(k,m) (-1)^(k-m).
  -- Divide.
  have h_eq_sum : (Finset.range (k + 1)).sum (fun m =>
      ((-1 : ℝ) ^ (k - m)) / ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) *
      (Nat.factorial k : ℝ) = 0 := by
    rw [Finset.sum_mul]
    have h_terms : ∀ m ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ (k - m)) / ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ)) *
          (Nat.factorial k : ℝ)
          = (Nat.choose k m : ℝ) * (-1 : ℝ) ^ (k - m) := by
      intros m hm
      rw [Finset.mem_range] at hm
      have hm_le_k : m ≤ k := by omega
      have h_choose_eq_nat : Nat.choose k m * (m.factorial * (k - m).factorial) = k.factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial hm_le_k
        linarith
      have h_choose_def : (Nat.choose k m : ℝ) =
          (Nat.factorial k : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ)) := by
        have h_fact_pos : (0 : ℝ) <
            (Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ) := by
          apply mul_pos
          · exact_mod_cast Nat.factorial_pos _
          · exact_mod_cast Nat.factorial_pos _
        have h_eq_real : (Nat.choose k m : ℝ) *
            ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))
            = (Nat.factorial k : ℝ) := by
          exact_mod_cast h_choose_eq_nat
        field_simp
        linarith [h_eq_real]
      rw [h_choose_def]
      field_simp
    rw [Finset.sum_congr rfl h_terms, h_sum_zero]
  have h_zero_div := h_eq_sum
  have h_factor : (Finset.range (k + 1)).sum (fun m =>
      ((-1 : ℝ) ^ (k - m)) / ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) =
      ((Finset.range (k + 1)).sum (fun m =>
        ((-1 : ℝ) ^ (k - m)) / ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) *
        (Nat.factorial k : ℝ)) / (Nat.factorial k : ℝ) := by
    field_simp
  rw [h_factor, h_zero_div, zero_div]

/-- Closed-form expansion for each even-index term. -/
private lemma term_closed_form (α : ℝ) (k m : ℕ) (hm : m ≤ k) :
    (Nat.choose (2 * k) (2 * m) : ℝ) *
      ((Nat.doubleFactorial (2 * m - 1) : ℝ) * α ^ m) *
      ((-α : ℝ) ^ (k - m) * (Nat.doubleFactorial (2 * (k - m) - 1) : ℝ)) =
    ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) *
      ((-1 : ℝ) ^ (k - m) * α ^ k) := by
  -- We use: (2m)! = 2^m · m! · (2m-1)!! and similarly (2(k-m))! = 2^(k-m) (k-m)! (2(k-m)-1)!!.
  have h_2m_fact_eq : ((2 * m).factorial : ℝ)
      = (2 : ℝ) ^ m * (m.factorial : ℝ) * (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp [Nat.doubleFactorial, Nat.factorial]
    · have h1 : 2 * m = (2 * m - 1) + 1 := by omega
      have h2 : Nat.doubleFactorial (2 * m) = 2 ^ m * m.factorial :=
        Nat.doubleFactorial_two_mul m
      have h3 : ((2 * m - 1) + 1).factorial = ((2 * m - 1) + 1).doubleFactorial *
          (2 * m - 1).doubleFactorial := Nat.factorial_eq_mul_doubleFactorial (2 * m - 1)
      have h4 : (2 * m).factorial = Nat.doubleFactorial (2 * m) * Nat.doubleFactorial (2 * m - 1) := by
        conv_lhs => rw [h1]
        rw [h3]
        rw [show (2 * m - 1) + 1 = 2 * m from by omega]
      rw [h4, h2]
      push_cast
      ring
  have h_2km_fact_eq : ((2 * (k - m)).factorial : ℝ)
      = (2 : ℝ) ^ (k - m) * ((k - m).factorial : ℝ) *
          (Nat.doubleFactorial (2 * (k - m) - 1) : ℝ) := by
    rcases Nat.eq_zero_or_pos (k - m) with hkm0 | hkm0
    · rw [hkm0]
      simp [Nat.doubleFactorial, Nat.factorial]
    · have h1 : 2 * (k - m) = (2 * (k - m) - 1) + 1 := by omega
      have h2 : Nat.doubleFactorial (2 * (k - m)) = 2 ^ (k - m) * (k - m).factorial :=
        Nat.doubleFactorial_two_mul (k - m)
      have h3 : ((2 * (k - m) - 1) + 1).factorial =
          ((2 * (k - m) - 1) + 1).doubleFactorial * (2 * (k - m) - 1).doubleFactorial :=
        Nat.factorial_eq_mul_doubleFactorial (2 * (k - m) - 1)
      have h4 : (2 * (k - m)).factorial =
          Nat.doubleFactorial (2 * (k - m)) * Nat.doubleFactorial (2 * (k - m) - 1) := by
        conv_lhs => rw [h1]
        rw [h3]
        rw [show (2 * (k - m) - 1) + 1 = 2 * (k - m) from by omega]
      rw [h4, h2]
      push_cast
      ring
  have h_le : 2 * m ≤ 2 * k := by omega
  have h_sub : 2 * k - 2 * m = 2 * (k - m) := by omega
  have h_choose_eq_nat : Nat.choose (2 * k) (2 * m) * ((2 * m).factorial * (2 * (k - m)).factorial) =
      (2 * k).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial h_le
    rw [h_sub] at h
    linarith
  have h_choose_def : (Nat.choose (2 * k) (2 * m) : ℝ) =
      ((2 * k).factorial : ℝ) /
        (((2 * m).factorial : ℝ) * ((2 * (k - m)).factorial : ℝ)) := by
    have h_fact_pos : (0 : ℝ) < ((2 * m).factorial : ℝ) * ((2 * (k - m)).factorial : ℝ) := by
      apply mul_pos
      · exact_mod_cast Nat.factorial_pos _
      · exact_mod_cast Nat.factorial_pos _
    have h_eq_real : (Nat.choose (2 * k) (2 * m) : ℝ) *
        (((2 * m).factorial : ℝ) * ((2 * (k - m)).factorial : ℝ))
        = ((2 * k).factorial : ℝ) := by
      exact_mod_cast h_choose_eq_nat
    field_simp
    linarith [h_eq_real]
  have h_pow2 : (2 : ℝ) ^ m * (2 : ℝ) ^ (k - m) = (2 : ℝ) ^ k := by
    rw [← pow_add]; congr 1; omega
  have h_pow_α : α ^ m * α ^ (k - m) = α ^ k := by
    rw [← pow_add]; congr 1; omega
  have h_neg_pow : (-α : ℝ) ^ (k - m) = (-1 : ℝ) ^ (k - m) * α ^ (k - m) := by
    rw [neg_pow]
  -- Use the factorial identities.
  rw [h_choose_def, h_neg_pow, h_2m_fact_eq, h_2km_fact_eq]
  have h_fact_m_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h_fact_km_pos : (0 : ℝ) < (Nat.factorial (k - m) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hDF1ne : (Nat.doubleFactorial (2 * m - 1) : ℝ) ≠ 0 := by
    have : 0 < Nat.doubleFactorial (2 * m - 1) := Nat.doubleFactorial_pos _
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hDF2ne : (Nat.doubleFactorial (2 * (k - m) - 1) : ℝ) ≠ 0 := by
    have : 0 < Nat.doubleFactorial (2 * (k - m) - 1) := Nat.doubleFactorial_pos _
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have h2pow_m_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
  have h2pow_km_ne : (2 : ℝ) ^ (k - m) ≠ 0 := by positivity
  have hfact_m_ne : (Nat.factorial m : ℝ) ≠ 0 := ne_of_gt h_fact_m_pos
  have hfact_km_ne : (Nat.factorial (k - m) : ℝ) ≠ 0 := ne_of_gt h_fact_km_pos
  -- Both sides equal the same expression. Use field_simp and ring after substituting pow_α and pow2.
  rw [show (-1 : ℝ) ^ (k - m) * α ^ (k - m) = α ^ (k - m) * (-1) ^ (k - m) from by ring]
  field_simp
  rw [show α ^ k = α ^ m * α ^ (k - m) from h_pow_α.symm,
      show (2 : ℝ) ^ k = (2 : ℝ) ^ m * (2 : ℝ) ^ (k - m) from h_pow2.symm]
  ring

/-- Sum of even-index terms in closed form. -/
private lemma sum_even_terms_closed (α : ℝ) (hα_pos : 0 < α) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun m =>
      (Nat.choose (2 * k) (2 * m) : ℝ) *
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
          ⟨(0 : ℝ), α, hα_pos⟩ (2 * m) *
        signedMomN α (2 * k - 2 * m))
    = ((Nat.factorial (2 * k) : ℝ) / (2 : ℝ) ^ k) * α ^ k *
      (Finset.range (k + 1)).sum (fun m =>
        ((-1 : ℝ) ^ (k - m)) / ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros m hm
  rw [Finset.mem_range] at hm
  have hm_le : m ≤ k := by omega
  have h_sub_eq : 2 * k - 2 * m = 2 * (k - m) := by omega
  rw [momentN0_even α hα_pos m, h_sub_eq, signedMomN_even α (k - m)]
  rw [term_closed_form α k m hm_le]
  have h_fact_m_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h_fact_km_pos : (0 : ℝ) < (Nat.factorial (k - m) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp

/-- The key combinatorial identity. -/
private lemma convolve_signed_moments_vanish (α : ℝ) (hα_pos : 0 < α) (l : ℕ) (hl : 1 ≤ l) :
    (Finset.range (l + 1)).sum (fun j =>
      (Nat.choose l j : ℝ) *
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
          ⟨(0 : ℝ), α, hα_pos⟩ j *
        signedMomN α (l - j)) = 0 := by
  rcases Nat.even_or_odd l with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- l = 2k, k ≥ 1
    have hl_eq : l = 2 * k := by omega
    have hk1 : 1 ≤ k := by omega
    rw [hl_eq]
    -- Reindex sum to even indices only.
    have h_reindex : (Finset.range (2 * k + 1)).sum (fun j =>
        (Nat.choose (2 * k) j : ℝ) *
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
            ⟨(0 : ℝ), α, hα_pos⟩ j *
          signedMomN α (2 * k - j))
        = (Finset.range (k + 1)).sum (fun m =>
          (Nat.choose (2 * k) (2 * m) : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
              ⟨(0 : ℝ), α, hα_pos⟩ (2 * m) *
            signedMomN α (2 * k - 2 * m)) := by
      have h_split : (Finset.range (2 * k + 1)).sum (fun j =>
            (Nat.choose (2 * k) j : ℝ) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                ⟨(0 : ℝ), α, hα_pos⟩ j *
              signedMomN α (2 * k - j))
          = ((Finset.range (2 * k + 1)).filter (fun j => j % 2 = 0)).sum (fun j =>
            (Nat.choose (2 * k) j : ℝ) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                ⟨(0 : ℝ), α, hα_pos⟩ j *
              signedMomN α (2 * k - j)) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * k + 1))
            (fun j => j % 2 = 0)]
        have h_odd_zero : (((Finset.range (2 * k + 1)).filter (fun j => ¬ j % 2 = 0))).sum
            (fun j =>
              (Nat.choose (2 * k) j : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                  ⟨(0 : ℝ), α, hα_pos⟩ j *
                signedMomN α (2 * k - j)) = 0 := by
          apply Finset.sum_eq_zero
          intros j hj
          rw [Finset.mem_filter] at hj
          have hjodd : Odd j := by
            rw [Nat.odd_iff]; omega
          rw [momentN0_odd α hα_pos j hjodd]
          ring
        rw [h_odd_zero, add_zero]
      rw [h_split]
      -- Now bijection between even j ∈ range(2k+1) and m ∈ range(k+1) via j ↦ j/2.
      symm
      apply Finset.sum_bij (fun (m : ℕ) (_ : m ∈ _) => 2 * m)
      · intros m hm
        rw [Finset.mem_range] at hm
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by omega⟩
      · intros m1 hm1 m2 hm2 h
        omega
      · intros j hj
        rw [Finset.mem_filter, Finset.mem_range] at hj
        refine ⟨j / 2, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · intros m hm
        simp only
    rw [h_reindex]
    rw [sum_even_terms_closed α hα_pos k]
    rw [alt_sum_inv_fact_zero k hk1]
    ring
  · -- l = 2k + 1, odd: all terms vanish.
    have hl_eq : l = 2 * k + 1 := by omega
    rw [hl_eq]
    apply Finset.sum_eq_zero
    intros j hj
    rw [Finset.mem_range] at hj
    rcases Nat.even_or_odd j with hjeven | hjodd
    · obtain ⟨m, hm⟩ := hjeven
      have hlj_odd : Odd (2 * k + 1 - j) := by
        refine ⟨k - m, ?_⟩
        omega
      rw [signedMomN_odd α (2 * k + 1 - j) hlj_odd]
      ring
    · rw [momentN0_odd α hα_pos j hjodd]
      ring

/-! ### Per-Gaussian deconvolution moment identity -/

private lemma deconv_moment_identity_gaussian_signedMomN
    (G : Workspace.Types.GaussianPDF.GaussianPDF)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < G.varSq) (i : ℕ) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        (Workspace.Types.MixtureDeconvolution.shiftGaussian G α hα_lt) i
      = (Finset.range (i + 1)).sum (fun j =>
          (Nat.choose i j : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G (i - j) *
            signedMomN α j) := by
  set Gα : Workspace.Types.GaussianPDF.GaussianPDF := ⟨0, α, hα_pos⟩ with hGα_def
  set Gd : Workspace.Types.GaussianPDF.GaussianPDF :=
    Workspace.Types.MixtureDeconvolution.shiftGaussian G α hα_lt with hGd_def
  -- Forward identity.
  have h_forward : ∀ n : ℕ,
      Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G n =
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : ℝ) *
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (n - k) *
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα k) := by
    intro n
    have h_sum := SublemmaMomentOfSumOfIndependents Gd Gα n
    simp only at h_sum
    have h_mean : Gd.mean + Gα.mean = G.mean := by
      simp [hGd_def, hGα_def, Workspace.Types.MixtureDeconvolution.shiftGaussian]
    have h_var : Gd.varSq + Gα.varSq = G.varSq := by
      simp [hGd_def, hGα_def, Workspace.Types.MixtureDeconvolution.shiftGaussian]
    have hG_eq : Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G n =
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
          (⟨Gd.mean + Gα.mean, Gd.varSq + Gα.varSq, add_pos Gd.varSq_pos Gα.varSq_pos⟩ :
            Workspace.Types.GaussianPDF.GaussianPDF) n := by
      unfold Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
      congr 1
      funext x
      congr 1
      rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq,
          Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
      show (1 / Real.sqrt (2 * Real.pi * G.varSq)) *
            Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))
          = (1 / Real.sqrt (2 * Real.pi * (Gd.varSq + Gα.varSq))) *
            Real.exp (-(x - (Gd.mean + Gα.mean)) ^ 2 / (2 * (Gd.varSq + Gα.varSq)))
      rw [h_mean, h_var]
    rw [hG_eq, h_sum]
  -- Strong induction.
  have h_Mα_0 : Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα 0 = 1 := by
    rw [hGα_def]
    have h := momentN0_even α hα_pos 0
    simp at h
    rw [show (0 : ℕ) = 2 * 0 from rfl]
    convert h using 1
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    set RHS : ℝ := (Finset.range (i + 1)).sum (fun j =>
        (Nat.choose i j : ℝ) *
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G (i - j) *
          signedMomN α j) with hRHS_def
    -- Expand RHS via h_forward.
    have h_RHS_expand : RHS =
        (Finset.range (i + 1)).sum (fun j =>
          (Nat.choose i j : ℝ) *
            ((Finset.range ((i - j) + 1)).sum (fun p =>
              (Nat.choose (i - j) p : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (i - j - p) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα p)) *
            signedMomN α j) := by
      rw [hRHS_def]
      apply Finset.sum_congr rfl
      intros j _hj
      rw [h_forward (i - j)]
    rw [h_RHS_expand]
    -- Distribute.
    have h_distrib :
        (Finset.range (i + 1)).sum (fun j =>
          (Nat.choose i j : ℝ) *
            ((Finset.range ((i - j) + 1)).sum (fun p =>
              (Nat.choose (i - j) p : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (i - j - p) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα p)) *
            signedMomN α j)
        = (Finset.range (i + 1)).sum (fun j =>
          (Finset.range ((i - j) + 1)).sum (fun p =>
            (Nat.choose i j : ℝ) * (Nat.choose (i - j) p : ℝ) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (i - j - p) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα p *
              signedMomN α j)) := by
      apply Finset.sum_congr rfl
      intros j _hj
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros p _hp
      ring
    rw [h_distrib]
    -- Swap sums: introduce l = i - j - p, m = p. Then j = i - l - m, signedMomN α j = signedMomN α (i - l - m).
    have h_swap :
        (Finset.range (i + 1)).sum (fun j =>
          (Finset.range ((i - j) + 1)).sum (fun p =>
            (Nat.choose i j : ℝ) * (Nat.choose (i - j) p : ℝ) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (i - j - p) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα p *
              signedMomN α j))
        = (Finset.range (i + 1)).sum (fun l =>
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd l *
          (Finset.range ((i - l) + 1)).sum (fun m =>
            (Nat.choose i l : ℝ) * (Nat.choose (i - l) m : ℝ) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
              signedMomN α (i - l - m))) := by
      -- Convert both sides to sigma sums.
      have lhs_sig := Finset.sum_sigma (s := Finset.range (i + 1))
        (t := fun j => Finset.range ((i - j) + 1))
        (f := fun (jp : (_ : ℕ) × ℕ) =>
          (Nat.choose i jp.1 : ℝ) * (Nat.choose (i - jp.1) jp.2 : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (i - jp.1 - jp.2) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα jp.2 *
            signedMomN α jp.1)
      rw [← lhs_sig]
      have rhs_pre :
          (Finset.range (i + 1)).sum (fun l =>
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd l *
            (Finset.range ((i - l) + 1)).sum (fun m =>
              (Nat.choose i l : ℝ) * (Nat.choose (i - l) m : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
                signedMomN α (i - l - m)))
          = (Finset.range (i + 1)).sum (fun l =>
            (Finset.range ((i - l) + 1)).sum (fun m =>
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd l *
              ((Nat.choose i l : ℝ) * (Nat.choose (i - l) m : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
                signedMomN α (i - l - m)))) := by
        apply Finset.sum_congr rfl
        intros l _hl
        rw [Finset.mul_sum]
      rw [rhs_pre]
      have rhs_sig := Finset.sum_sigma (s := Finset.range (i + 1))
        (t := fun l => Finset.range ((i - l) + 1))
        (f := fun (lm : (_ : ℕ) × ℕ) =>
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd lm.1 *
          ((Nat.choose i lm.1 : ℝ) * (Nat.choose (i - lm.1) lm.2 : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα lm.2 *
            signedMomN α (i - lm.1 - lm.2)))
      rw [← rhs_sig]
      -- Now both sides are sums over sigma. Use sum_bij' (dependent form).
      apply Finset.sum_bij'
        (fun (jp : (_ : ℕ) × ℕ) (_ : jp ∈ _) =>
          (⟨i - jp.1 - jp.2, jp.2⟩ : (_ : ℕ) × ℕ))
        (fun (lm : (_ : ℕ) × ℕ) (_ : lm ∈ _) =>
          (⟨i - lm.1 - lm.2, lm.2⟩ : (_ : ℕ) × ℕ))
      · intros jp hjp
        rw [Finset.mem_sigma] at hjp ⊢
        simp only [Finset.mem_range] at hjp ⊢
        obtain ⟨hj, hp⟩ := hjp
        refine ⟨by omega, by omega⟩
      · intros lm hlm
        rw [Finset.mem_sigma] at hlm ⊢
        simp only [Finset.mem_range] at hlm ⊢
        obtain ⟨hl, hm⟩ := hlm
        refine ⟨by omega, by omega⟩
      · intros jp hjp
        rw [Finset.mem_sigma] at hjp
        simp only [Finset.mem_range] at hjp
        obtain ⟨hj, hp⟩ := hjp
        ext
        · simp; omega
        · simp
      · intros lm hlm
        rw [Finset.mem_sigma] at hlm
        simp only [Finset.mem_range] at hlm
        obtain ⟨hl, hm⟩ := hlm
        ext
        · simp; omega
        · simp
      · intros jp hjp
        rw [Finset.mem_sigma] at hjp
        simp only [Finset.mem_range] at hjp
        obtain ⟨hj, hp⟩ := hjp
        have hjpfst : jp.1 ≤ i := by omega
        have h_jpsnd_le : jp.2 ≤ i - jp.1 := by omega
        have h_signed_eq : i - (i - jp.1 - jp.2) - jp.2 = jp.1 := by omega
        have h_i_minus : i - (i - jp.1 - jp.2) = jp.1 + jp.2 := by omega
        have h_choose_id : (Nat.choose i jp.1 : ℝ) * (Nat.choose (i - jp.1) jp.2 : ℝ)
            = (Nat.choose i (i - jp.1 - jp.2) : ℝ) *
              (Nat.choose (jp.1 + jp.2) jp.2 : ℝ) := by
          have h_jp_le : jp.2 ≤ jp.1 + jp.2 := by omega
          have h_jpp_le_i : jp.1 + jp.2 ≤ i := by omega
          have hm1 : Nat.choose i (jp.1 + jp.2) * Nat.choose (jp.1 + jp.2) jp.2 =
              Nat.choose i jp.2 * Nat.choose (i - jp.2) (jp.1 + jp.2 - jp.2) :=
            Nat.choose_mul h_jp_le
          have h_sub_eq : jp.1 + jp.2 - jp.2 = jp.1 := by omega
          rw [h_sub_eq] at hm1
          have hm2 : Nat.choose i (i - jp.1) * Nat.choose (i - jp.1) jp.2 =
              Nat.choose i jp.2 * Nat.choose (i - jp.2) ((i - jp.1) - jp.2) :=
            Nat.choose_mul h_jpsnd_le
          have h_sub_eq2 : (i - jp.1) - jp.2 = i - jp.1 - jp.2 := by omega
          rw [h_sub_eq2] at hm2
          have h_sym_i : Nat.choose i (i - jp.1) = Nat.choose i jp.1 :=
            Nat.choose_symm hjpfst
          rw [h_sym_i] at hm2
          have h_le_ip : jp.1 ≤ i - jp.2 := by omega
          have h_sym_jp : Nat.choose (i - jp.2) jp.1 = Nat.choose (i - jp.2) (i - jp.1 - jp.2) := by
            have hk := Nat.choose_symm h_le_ip
            -- hk : (i - jp.2).choose (i - jp.2 - jp.1) = (i - jp.2).choose jp.1
            have h_eq_idx : i - jp.2 - jp.1 = i - jp.1 - jp.2 := by omega
            rw [← hk, h_eq_idx]
          rw [h_sym_jp] at hm1
          have h_eq : Nat.choose i jp.1 * Nat.choose (i - jp.1) jp.2 =
              Nat.choose i (jp.1 + jp.2) * Nat.choose (jp.1 + jp.2) jp.2 := by
            rw [hm2, hm1]
          have h_sym_jpp : Nat.choose i (jp.1 + jp.2) = Nat.choose i (i - jp.1 - jp.2) := by
            have hk := Nat.choose_symm h_jpp_le_i
            -- hk : i.choose (i - (jp.1 + jp.2)) = i.choose (jp.1 + jp.2)
            have h_eq_idx : i - (jp.1 + jp.2) = i - jp.1 - jp.2 := by omega
            rw [← hk, h_eq_idx]
          rw [h_sym_jpp] at h_eq
          exact_mod_cast h_eq
        simp only
        rw [h_signed_eq, h_i_minus]
        linear_combination
          (Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd (i - jp.1 - jp.2) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα jp.2 *
            signedMomN α jp.1) * h_choose_id
    rw [h_swap]
    -- Isolate l = i term.
    have h_range : Finset.range (i + 1) = insert i (Finset.range i) :=
      Finset.range_add_one
    rw [h_range, Finset.sum_insert (by simp : i ∉ Finset.range i)]
    have h_l_eq_i_term :
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd i *
        (Finset.range ((i - i) + 1)).sum (fun m =>
          (Nat.choose i i : ℝ) * (Nat.choose (i - i) m : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
            signedMomN α (i - i - m))
        = Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd i := by
      have h_sub : i - i = 0 := by omega
      rw [h_sub]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self,
                 Nat.choose_zero_right, Nat.cast_one, zero_tsub]
      rw [signedMomN_zero, h_Mα_0]
      ring
    rw [h_l_eq_i_term]
    have h_other_zero : (Finset.range i).sum (fun l =>
        Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gd l *
        (Finset.range ((i - l) + 1)).sum (fun m =>
          (Nat.choose i l : ℝ) * (Nat.choose (i - l) m : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
            signedMomN α (i - l - m))) = 0 := by
      apply Finset.sum_eq_zero
      intros l hl
      rw [Finset.mem_range] at hl
      have hil : 1 ≤ i - l := by omega
      have h_pull : (Finset.range ((i - l) + 1)).sum (fun m =>
          (Nat.choose i l : ℝ) * (Nat.choose (i - l) m : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
            signedMomN α (i - l - m))
          = (Nat.choose i l : ℝ) *
            (Finset.range ((i - l) + 1)).sum (fun m =>
              (Nat.choose (i - l) m : ℝ) *
                Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
                signedMomN α (i - l - m)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros m _hm
        ring
      rw [h_pull]
      have h_inner_zero : (Finset.range ((i - l) + 1)).sum (fun m =>
          (Nat.choose (i - l) m : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian Gα m *
            signedMomN α (i - l - m)) = 0 := by
        rw [hGα_def]
        exact convolve_signed_moments_vanish α hα_pos (i - l) hil
      rw [h_inner_zero]
      ring
    rw [h_other_zero, add_zero]

/-! ### The main theorem -/

theorem SublemmaDeconvolutionMomentIdentity
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (α : ℝ)
    (hα_pos : 0 < α)
    (hα_lt : α < min F.comp1.varSq F.comp2.varSq)
    (i : ℕ) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α hα_lt) i
      = (Finset.range (i + 1)).sum (fun j =>
          (Nat.choose i j : ℝ) *
            Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F (i - j) *
            ((if j % 4 = 0 then (1 : ℝ) else if j % 4 = 2 then (-1 : ℝ) else 0) *
              Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
                ⟨(0 : ℝ), α, hα_pos⟩ j)) := by
  have hα_lt1 : α < F.comp1.varSq := lt_of_lt_of_le hα_lt (min_le_left _ _)
  have hα_lt2 : α < F.comp2.varSq := lt_of_lt_of_le hα_lt (min_le_right _ _)
  have hLHS_split :=
    SublemmaMixtureMomentLinearity
      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α hα_lt) i
  have hcomp1 := deconv_moment_identity_gaussian_signedMomN F.comp1 α hα_pos hα_lt1 i
  have hcomp2 := deconv_moment_identity_gaussian_signedMomN F.comp2 α hα_pos hα_lt2 i
  have e1 :
      Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α hα_lt).comp1 i =
      Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        (Workspace.Types.MixtureDeconvolution.shiftGaussian F.comp1 α hα_lt1) i := rfl
  have e2 :
      Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α hα_lt).comp2 i =
      Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
        (Workspace.Types.MixtureDeconvolution.shiftGaussian F.comp2 α hα_lt2) i := rfl
  rw [hLHS_split]
  rw [show (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α hα_lt).weight1 =
        F.weight1 from rfl,
      show (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α hα_lt).weight2 =
        F.weight2 from rfl, e1, e2, hcomp1, hcomp2]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [SublemmaMixtureMomentLinearity F (i - j)]
  rw [← signedMomN_eq_c_M α hα_pos j]
  ring

end Workspace.ProofLemmas
