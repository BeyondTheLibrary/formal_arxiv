import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.L1AndTVDistance
import Workspace.Types.MixtureRawMoments
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.MixtureDifferenceAsSignedCombination
import Workspace.ProofLemmas.MomentIntegralLinearity
import Workspace.ProofLemmas.Lemma9TailBound
import Workspace.ProofLemmas.SublemmaSignedDensityL1TailBound
import Workspace.ProofLemmas.SublemmaSGCDensityIntegrable
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian
import Workspace.ProofLemmas.TailBoundExpDecay
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.ZeroCountAfterPerturbation
import Workspace.ProofLemmas.SignChangeBoundedPolynomialPairingPiecewise
import Workspace.ProofLemmas.SublemmaSignedGaussianDensityZerosFinite
import Workspace.ProofLemmas.SublemmaExtractSortedZeroList
import Workspace.ProofLemmas.DerivativeBoundOfSignedCombination
import Workspace.ProofLemmas.M0OfMixtureDifferenceIsZero

set_option maxHeartbeats 4000000
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open MeasureTheory

namespace Workspace.ProofLemmas.Lemma9MomentGap

open Workspace.Types.MixtureRawMoments
open Workspace.Types.SignedGaussianCombination

/-- Integrability of `x^j * S.density x` for a signed Gaussian combination. -/
lemma integrable_xpow_signed
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j * S.density x) volume := by
  have e : (fun x : ℝ => x ^ j * S.density x)
      = (fun x : ℝ =>
          (S.components.map
            (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              q.1 * (x ^ j * q.2.density x))).sum) := by
    funext x
    rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq]
    induction S.components with
    | nil => simp
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ← ih]; ring
  rw [e]
  induction S.components with
  | nil => simpa using (integrable_zero ℝ ℝ volume)
  | cons q rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((SublemmaIntegrabilityXPowGaussian q.2 j).const_mul q.1).add ih

/-- Integrability of `eval x p * S.density x` for a polynomial `p`. -/
lemma integrable_evalpoly_signed
    (p : Polynomial ℝ)
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination) :
    Integrable (fun x : ℝ => Polynomial.eval x p * S.density x) volume := by
  have e : (fun x : ℝ => Polynomial.eval x p * S.density x)
      = (fun x : ℝ => ∑ k ∈ Finset.range (p.natDegree + 1),
          p.coeff k * (x ^ k * S.density x)) := by
    funext x; rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [e]
  apply MeasureTheory.integrable_finset_sum
  intro k _
  exact (integrable_xpow_signed S k).const_mul _

/-- Bridge: the `i`-th signed-combination moment of the difference combination
equals the difference of the two mixture moments. -/
private lemma rawMoment_signed_diff_eq
    (Fα Fα' : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (hS : ∀ x : ℝ, S.density x = Fα.density x - Fα'.density x)
    (i : ℕ) :
    rawMoment_ofSigned S i
      = rawMoment_ofMixture2 Fα i - rawMoment_ofMixture2 Fα' i := by
  rw [rawMoment_ofSigned_def, rawMoment_ofMixture2_def, rawMoment_ofMixture2_def]
  have hint1 : Integrable (fun x : ℝ => x ^ i * Fα.density x) volume := by
    have e : (fun x : ℝ => x ^ i * Fα.density x)
        = (fun x => Fα.weight1 * (x ^ i * Fα.comp1.density x))
          + (fun x => Fα.weight2 * (x ^ i * Fα.comp2.density x)) := by
      funext x
      simp only [Pi.add_apply, Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq]
      ring
    rw [e]
    exact (((SublemmaIntegrabilityXPowGaussian Fα.comp1 i).const_mul _).add
      ((SublemmaIntegrabilityXPowGaussian Fα.comp2 i).const_mul _))
  have hint2 : Integrable (fun x : ℝ => x ^ i * Fα'.density x) volume := by
    have e : (fun x : ℝ => x ^ i * Fα'.density x)
        = (fun x => Fα'.weight1 * (x ^ i * Fα'.comp1.density x))
          + (fun x => Fα'.weight2 * (x ^ i * Fα'.comp2.density x)) := by
      funext x
      simp only [Pi.add_apply, Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq]
      ring
    rw [e]
    exact (((SublemmaIntegrabilityXPowGaussian Fα'.comp1 i).const_mul _).add
      ((SublemmaIntegrabilityXPowGaussian Fα'.comp2 i).const_mul _))
  rw [← integral_sub hint1 hint2]
  apply integral_congr_ae
  filter_upwards with x
  rw [hS x]; ring

/-- The interval-L¹ bound: from the full-line L¹ gap and the tail bound, for ε
small enough (relative to K) the bounded-interval L¹ mass is at least `(K/2)·ε⁴`. -/
private lemma interval_L1_lower
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (ε K : ℝ) (hε_pos : 0 < ε)
    (hL1 : K * ε ^ 4 ≤ ∫ x, |S.density x|)
    (hdom : (∫ x in {x : ℝ | 2 / ε ≤ |x|}, |S.density x|) ≤ K * ε ^ 4 / 2) :
    K * ε ^ 4 / 2 ≤ ∫ x in {x : ℝ | |x| ≤ 2 / ε}, |S.density x| := by
  set R : ℝ := 2 / ε with hR_def
  set g : ℝ → ℝ := fun x => |S.density x| with hg_def
  have hg_int : Integrable g volume := (SublemmaSGCDensityIntegrable S).abs
  have hg_nn : ∀ x, 0 ≤ g x := fun x => abs_nonneg _
  have hmeas_le : MeasurableSet {x : ℝ | |x| ≤ R} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hsplit :
      (∫ x, g x) = (∫ x in {x : ℝ | |x| ≤ R}, g x)
        + ∫ x in {x : ℝ | ¬ |x| ≤ R}, g x := by
    rw [← MeasureTheory.integral_add_compl hmeas_le hg_int]
    rfl
  have hcompl_subset : {x : ℝ | ¬ |x| ≤ R} ⊆ {x : ℝ | 2 / ε ≤ |x|} := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_le] at hx ⊢
    exact le_of_lt hx
  have hcompl_le : (∫ x in {x : ℝ | ¬ |x| ≤ R}, g x)
      ≤ ∫ x in {x : ℝ | 2 / ε ≤ |x|}, g x := by
    apply MeasureTheory.setIntegral_mono_set hg_int.integrableOn
    · filter_upwards with x using hg_nn x
    · exact HasSubset.Subset.eventuallyLE hcompl_subset
  have : K * ε ^ 4 ≤ (∫ x in {x : ℝ | |x| ≤ R}, g x) + K * ε ^ 4 / 2 := by
    calc K * ε ^ 4 ≤ ∫ x, g x := hL1
      _ = (∫ x in {x : ℝ | |x| ≤ R}, g x) + ∫ x in {x : ℝ | ¬ |x| ≤ R}, g x := hsplit
      _ ≤ (∫ x in {x : ℝ | |x| ≤ R}, g x) + ∫ x in {x : ℝ | 2 / ε ≤ |x|}, g x := by
          linarith [hcompl_le]
      _ ≤ (∫ x in {x : ℝ | |x| ≤ R}, g x) + K * ε ^ 4 / 2 := by linarith [hdom]
  linarith

/-- The piecewise test polynomial `∑_{i : Fin 7} C(c i) X^i` (degrees 0..6,
matching the piecewise Markov–Chebyshev pairing's coefficient vector). -/
noncomputable def pwPoly (c : Fin 7 → ℝ) : Polynomial ℝ :=
  ∑ i : Fin 7, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

lemma pwPoly_eval (c : Fin 7 → ℝ) (x : ℝ) :
    Polynomial.eval x (pwPoly c) = ∑ i : Fin 7, c i * x ^ (i : ℕ) := by
  simp [pwPoly, Polynomial.eval_finset_sum]

lemma pwPoly_natDegree (c : Fin 7 → ℝ) : (pwPoly c).natDegree ≤ 6 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (c i) (i : ℕ)) (by omega)

lemma pwPoly_coeff_le (c : Fin 7 → ℝ) (hc : ∀ i, |c i| ≤ 1) (k : ℕ) :
    |(pwPoly c).coeff k| ≤ 1 := by
  rw [pwPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hk : ∃ x : Fin 7, k = (x : ℕ)
  · obtain ⟨x0, hx0⟩ := hk
    rw [Finset.sum_eq_single x0]
    · rw [if_pos hx0]; exact hc x0
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.val_injective (by omega : (b : ℕ) = (x0 : ℕ)))
    · intro h; exact absurd (Finset.mem_univ x0) h
  · push_neg at hk
    have hz : ∑ x : Fin 7, (if k = (x : ℕ) then c x else 0) = 0 := by
      apply Finset.sum_eq_zero; intro x _; rw [if_neg (hk x)]
    rw [hz]; simp

/-- The full-line pairing of the piecewise polynomial against `S` equals the
linear combination of all 7 moments `M_0, …, M_6`. -/
lemma pwPoly_pairing_eq_moments
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (ε : ℝ) (c : Fin 7 → ℝ)
    (hε_pos : 0 < ε)
    (hε_le : ε ≤ 2 ^ ((1 : ℝ) / 12))
    (hS_len : S.components.length ≤ 4)
    (hS_bounds : ∀ q ∈ S.components,
        |q.fst| ≤ 1 ∧ |q.snd.mean| ≤ 1 / ε
        ∧ ε ^ 12 ≤ q.snd.varSq ∧ q.snd.varSq ≤ 2) :
    (∫ x, Polynomial.eval x (pwPoly c) * S.density x)
      = ∑ i : Fin 7, c i * rawMoment_ofSigned S (i : ℕ) := by
  have h_int_eq : (∫ x, Polynomial.eval x (pwPoly c) * S.density x)
      = ∫ x, (Finset.univ : Finset (Fin 7)).sum (fun i => c i * x ^ (i : ℕ))
              * S.density x := by
    apply integral_congr_ae; filter_upwards with x; rw [pwPoly_eval]
  rw [h_int_eq, MomentIntegralLinearity S ε hε_pos hε_le hS_len hS_bounds c]

/-- Threshold helper: for `A, B, K > 0`, there is `ε₀ > 0` such that for all
`0 < ε ≤ ε₀`, `A * (1/ε)^12 * exp(-1/(4ε²)) ≤ B * K * ε^n`. -/
lemma tail_threshold (A B K : ℝ) (n : ℕ) (hA : 0 < A) (hB : 0 < B) (hK : 0 < K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      A * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) ≤ B * K * ε ^ n := by
  obtain ⟨ε₀, hε₀_pos, hbound⟩ :=
    TailBoundExpDecay 4 (A / (B * K)) (n + 12) (by norm_num) (by positivity)
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro ε hε_pos hε_le
  have hbk : 0 < B * K := mul_pos hB hK
  have h := hbound ε hε_pos hε_le
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hpow_split : ε ^ (n + 12) = ε ^ n * ε ^ 12 := by rw [pow_add]
  have hinv12 : (1 / ε) ^ 12 = 1 / ε ^ 12 := by rw [div_pow, one_pow]
  have hε12_pos : 0 < ε ^ 12 := by positivity
  have h2 : A * Real.exp (-1 / (4 * ε ^ 2)) ≤ B * K * ε ^ (n + 12) := by
    calc A * Real.exp (-1 / (4 * ε ^ 2))
        = A / (B * K) * Real.exp (-1 / (4 * ε ^ 2)) * (B * K) := by
          field_simp
      _ ≤ ε ^ (n + 12) * (B * K) := by
          apply mul_le_mul_of_nonneg_right h (le_of_lt hbk)
      _ = B * K * ε ^ (n + 12) := by ring
  rw [hinv12]
  rw [show A * (1 / ε ^ 12) * Real.exp (-1 / (4 * ε ^ 2))
        = (A * Real.exp (-1 / (4 * ε ^ 2))) / ε ^ 12 from by ring]
  rw [div_le_iff₀ hε12_pos]
  calc A * Real.exp (-1 / (4 * ε ^ 2))
      ≤ B * K * ε ^ (n + 12) := h2
    _ = B * K * ε ^ n * ε ^ 12 := by rw [hpow_split]; ring

/-- Pure power threshold: for `c > 0` and `n ≥ 1`, there is `ε₀ > 0` with
`ε^n ≤ c` for all `0 < ε ≤ ε₀`. -/
lemma pow_threshold (c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 1 ≤ n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ε ^ n ≤ c := by
  refine ⟨min 1 (c ^ ((1 : ℝ) / n)), by
    have : 0 < c ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hc _
    positivity, ?_⟩
  intro ε hε_pos hε_le
  have hε1 : ε ≤ 1 := le_trans hε_le (min_le_left _ _)
  have hεc : ε ≤ c ^ ((1 : ℝ) / n) := le_trans hε_le (min_le_right _ _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcrpow : (c ^ ((1 : ℝ) / n)) ^ (n : ℝ) = c := by
    rw [← Real.rpow_mul hc.le, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one]
  calc ε ^ n = ε ^ (n : ℝ) := (Real.rpow_natCast ε n).symm
    _ ≤ (c ^ ((1 : ℝ) / n)) ^ (n : ℝ) :=
        Real.rpow_le_rpow hε_pos.le hεc (le_of_lt hnpos)
    _ = c := hcrpow

open Workspace.Types.GaussianMixture2
open Workspace.Types.EpsilonStandardPair
open Workspace.Types.MixtureDeconvolution
open Workspace.Types.L1AndTVDistance

/-- **Lemma 9 (genuine, threshold form).**
There is an absolute constant `K₉ > 0` such that for every `K > 0` there is a
threshold `ε_max > 0` such that for every ε-standard pair and admissible
deconvolution parameter, with each post-deconvolution variance `≥ ε^{12}`,
`α ≥ -1`, `ε ≤ ε_max`, and an `L¹` gap `≥ K·ε⁴`, some moment of order
`i ∈ {1,…,6}` of the deconvolved mixtures differs by at least `K₉·K·ε^{66}`.

The threshold `ε_max` honestly depends on `K`: the Gaussian tail
`exp(-1/(4ε²))` is absolute in `K`, so the bound only holds once ε is small
enough relative to `K` for the (sub-polynomial) tail to be dominated by the
bulk. -/
theorem Lemma9MomentGap :
    ∃ K₉ : ℝ, 0 < K₉ ∧
      ∀ K : ℝ, 0 < K → ∃ ε_max : ℝ, 0 < ε_max ∧
        ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2)
          (ε α : ℝ)
          (h_F : α < min F.comp1.varSq F.comp2.varSq)
          (h_F' : α < min F'.comp1.varSq F'.comp2.varSq),
          0 < ε →
          ε ≤ ε_max →
          Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε →
          ε ^ 12 ≤
              min
                (min
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp1.varSq
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp2.varSq)
                (min
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp1.varSq
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp2.varSq) →
          (-1 : ℝ) ≤ α →
          K * ε ^ 4 ≤
              Workspace.Types.L1AndTVDistance.L1NormMixtureDiff
                (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F)
                (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F') →
          ∃ i ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
            K₉ * K * ε ^ 66 ≤
              |Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F) i
               - Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
                  (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F') i| := by
  -- Constants from the (genuinely proven) inputs.
  -- Piecewise Markov–Chebyshev pairing (no simple zeros, no false axiom):
  obtain ⟨K_CM, hK_CM_pos, hCM⟩ := signChangePolynomialPairingPiecewise
  obtain ⟨K_T, hK_T_pos, hTailL1⟩ := SublemmaSignedDensityL1TailBound
  obtain ⟨K_tail, hK_tail_pos, hTailP⟩ := Lemma9TailBound
  -- bulk constant: K_CM·δ⁴/M³·R⁻⁶ with δ=Kε⁴/2, M=4/ε¹², R=2/ε gives
  -- K_CM·K⁴·ε⁵⁸ / 65536.  Set B_bulk = K_CM/65536, K₉ = B_bulk/12.
  set B_bulk : ℝ := K_CM / 65536 with hBbulk_def
  have hBbulk_pos : 0 < B_bulk := by rw [hBbulk_def]; positivity
  refine ⟨B_bulk / 12, by positivity, ?_⟩
  intro K hK_pos
  -- thresholds (all may depend on K since the statement is `∀ K, ∃ ε_max`).
  obtain ⟨ε1, hε1_pos, hthr1⟩ := tail_threshold K_T (1/2) K 4 hK_T_pos (by norm_num) hK_pos
  -- tail of the polynomial pairing: need ≤ (B_bulk/2)·K⁴·ε⁵⁸.  tail_threshold gives
  -- A·(1/ε)¹²·exp ≤ B·K·εⁿ; take n=58, B = B_bulk·K³/2, C=1.
  obtain ⟨ε2, hε2_pos, hthr2⟩ :=
    tail_threshold K_tail (B_bulk * K ^ 3 / 2) K 58 hK_tail_pos (by positivity) hK_pos
  -- ε⁸ ≤ K³  (to convert ε⁵⁸·K⁴ ≥ ε⁶⁶·K with K₉ = B_bulk/12).
  obtain ⟨ε3, hε3_pos, hthr3⟩ := pow_threshold (K ^ 3) 8 (by positivity) (by norm_num)
  -- K·ε¹⁶ ≤ 8  (to get δ ≤ M, i.e. Kε⁴/2 ≤ 4/ε¹²).
  obtain ⟨ε4, hε4_pos, hthr4⟩ := pow_threshold (8 / K) 16 (by positivity) (by norm_num)
  refine ⟨min 1 (min (min ε1 ε2) (min ε3 ε4)), by positivity, ?_⟩
  intro F F' ε α h_F h_F' hε_pos hε_le h_std hvar_lb hα_ge hL1
  set Fα := Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F with hFα_def
  set Fα' := Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F' with hFα'_def
  -- ε bounds
  have hε_le1 : ε ≤ 1 := le_trans hε_le (min_le_left _ _)
  have hε_le_ε1 : ε ≤ ε1 :=
    le_trans hε_le (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hε_le_ε2 : ε ≤ ε2 :=
    le_trans hε_le (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_le_ε3 : ε ≤ ε3 :=
    le_trans hε_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε_le_ε4 : ε ≤ ε4 :=
    le_trans hε_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have h_one_le_212 : (1 : ℝ) ≤ 2 ^ ((1 : ℝ) / 12) := by
    have : (1 : ℝ) ^ ((1 : ℝ) / 12) ≤ 2 ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
    simpa using this
  have hε_le_212 : ε ≤ 2 ^ ((1 : ℝ) / 12) := le_trans hε_le1 h_one_le_212
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  -- The difference signed combination.
  obtain ⟨S, hS_len_eq, hS_density, hS_comp⟩ :=
    Workspace.ProofLemmas.MixtureDifferenceAsSignedCombination Fα Fα'
  have hS_len : S.components.length ≤ 4 := by rw [hS_len_eq]
  -- Weight facts.
  have hw_sum : F.weight1 + F.weight2 = 1 := F.weights_sum_one
  have hw'_sum : F'.weight1 + F'.weight2 = 1 := F'.weights_sum_one
  have hw1_nn : 0 ≤ F.weight1 := F.weight1_nonneg
  have hw2_nn : 0 ≤ F.weight2 := F.weight2_nonneg
  have hw1'_nn : 0 ≤ F'.weight1 := F'.weight1_nonneg
  have hw2'_nn : 0 ≤ F'.weight2 := F'.weight2_nonneg
  -- mean / variance bounds from EpsilonStandardPair and hypotheses.
  have hμ1 : |F.comp1.mean| ≤ 1 / ε := h_std.means_and_vars_bounded.2.1
  have hμ2 : |F.comp2.mean| ≤ 1 / ε := h_std.means_and_vars_bounded.2.2.1
  have hμ1' : |F'.comp1.mean| ≤ 1 / ε := h_std.means_and_vars_bounded.2.2.2.1
  have hμ2' : |F'.comp2.mean| ≤ 1 / ε := h_std.means_and_vars_bounded.2.2.2.2
  have hv1_le : F.comp1.varSq ≤ 1 := h_std.means_and_vars_bounded.1.1
  have hv2_le : F.comp2.varSq ≤ 1 := h_std.means_and_vars_bounded.1.2.1
  have hv1'_le : F'.comp1.varSq ≤ 1 := h_std.means_and_vars_bounded.1.2.2.1
  have hv2'_le : F'.comp2.varSq ≤ 1 := h_std.means_and_vars_bounded.1.2.2.2
  -- post-deconvolution variance lower bounds, from hvar_lb.
  have hVlo1 : ε ^ 12 ≤ Fα.comp1.varSq :=
    le_trans hvar_lb (le_trans (min_le_left _ _) (min_le_left _ _))
  have hVlo2 : ε ^ 12 ≤ Fα.comp2.varSq :=
    le_trans hvar_lb (le_trans (min_le_left _ _) (min_le_right _ _))
  have hVlo1' : ε ^ 12 ≤ Fα'.comp1.varSq :=
    le_trans hvar_lb (le_trans (min_le_right _ _) (min_le_left _ _))
  have hVlo2' : ε ^ 12 ≤ Fα'.comp2.varSq :=
    le_trans hvar_lb (le_trans (min_le_right _ _) (min_le_right _ _))
  -- post-deconvolution variance upper bounds ≤ 2.
  have hVhi1 : Fα.comp1.varSq ≤ 2 := by
    rw [hFα_def]; simp only [deconvMixture2_comp1_varSq]; linarith
  have hVhi2 : Fα.comp2.varSq ≤ 2 := by
    rw [hFα_def]; simp only [deconvMixture2_comp2_varSq]; linarith
  have hVhi1' : Fα'.comp1.varSq ≤ 2 := by
    rw [hFα'_def]; simp only [deconvMixture2_comp1_varSq]; linarith
  have hVhi2' : Fα'.comp2.varSq ≤ 2 := by
    rw [hFα'_def]; simp only [deconvMixture2_comp2_varSq]; linarith
  -- means of deconvolved comps equal originals
  have hM1 : Fα.comp1.mean = F.comp1.mean := by rw [hFα_def]; simp
  have hM2 : Fα.comp2.mean = F.comp2.mean := by rw [hFα_def]; simp
  have hM1' : Fα'.comp1.mean = F'.comp1.mean := by rw [hFα'_def]; simp
  have hM2' : Fα'.comp2.mean = F'.comp2.mean := by rw [hFα'_def]; simp
  -- weights of deconvolved comps equal originals
  have hW1 : Fα.weight1 = F.weight1 := by rw [hFα_def]; simp
  have hW2 : Fα.weight2 = F.weight2 := by rw [hFα_def]; simp
  have hW1' : Fα'.weight1 = F'.weight1 := by rw [hFα'_def]; simp
  have hW2' : Fα'.weight2 = F'.weight2 := by rw [hFα'_def]; simp
  -- Now establish hS_bounds via the explicit component list.
  have hS_bounds : ∀ q ∈ S.components,
      |q.fst| ≤ 1 ∧ |q.snd.mean| ≤ 1 / ε
      ∧ ε ^ 12 ≤ q.snd.varSq ∧ q.snd.varSq ≤ 2 := by
    rw [hS_comp]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · subst h; refine ⟨?_, ?_, ?_, ?_⟩
      · rw [abs_of_nonneg (hW1 ▸ hw1_nn)]; rw [hW1]; linarith
      · rw [hM1]; exact hμ1
      · exact hVlo1
      · exact hVhi1
    · subst h; refine ⟨?_, ?_, ?_, ?_⟩
      · rw [abs_of_nonneg (hW2 ▸ hw2_nn)]; rw [hW2]; linarith
      · rw [hM2]; exact hμ2
      · exact hVlo2
      · exact hVhi2
    · subst h; refine ⟨?_, ?_, ?_, ?_⟩
      · rw [abs_neg, abs_of_nonneg (hW1' ▸ hw1'_nn)]; rw [hW1']; linarith
      · rw [hM1']; exact hμ1'
      · exact hVlo1'
      · exact hVhi1'
    · subst h; refine ⟨?_, ?_, ?_, ?_⟩
      · rw [abs_neg, abs_of_nonneg (hW2' ▸ hw2'_nn)]; rw [hW2']; linarith
      · rw [hM2']; exact hμ2'
      · exact hVlo2'
      · exact hVhi2'
  -- Step 1: full-line L¹ in terms of S.density.
  have hL1' : K * ε ^ 4 ≤ ∫ x, |S.density x| := by
    have heq : (∫ x, |S.density x|) = L1NormMixtureDiff Fα Fα' := by
      rw [L1NormMixtureDiff_def, L1Norm_def]
      apply integral_congr_ae; filter_upwards with x; rw [hS_density x]
    rw [heq]; exact hL1
  -- Step 2: tail-domination of the L¹ mass.
  have hdom : (∫ x in {x : ℝ | 2 / ε ≤ |x|}, |S.density x|) ≤ K * ε ^ 4 / 2 := by
    have h1 := hTailL1 S ε hε_pos hε_le1 hS_len hS_bounds
    have h2 := hthr1 ε hε_pos hε_le_ε1
    -- h2 : K_T * (1/ε)^12 * exp ≤ 1/2 * K * ε^4
    calc (∫ x in {x : ℝ | 2 / ε ≤ |x|}, |S.density x|)
        ≤ K_T * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := h1
      _ ≤ 1 / 2 * K * ε ^ 4 := h2
      _ = K * ε ^ 4 / 2 := by ring
  -- Step 3: bounded-interval L¹ lower bound.
  have hIntL1 : K * ε ^ 4 / 2 ≤ ∫ x in {x : ℝ | |x| ≤ 2 / ε}, |S.density x| :=
    interval_L1_lower S ε K hε_pos hL1' hdom
  -- Step 4: Chebyshev test polynomial.
  have hR_ge : (1 : ℝ) ≤ 2 / ε := by
    rw [le_div_iff₀ hε_pos]; linarith
  have hδ_nn : 0 ≤ K * ε ^ 4 / 2 := by positivity
  -- Step 3.5: discharge the "≤ 6 zeros" hypothesis of the (corrected) Chebyshev–Markov
  -- test-function lemma.  `S` is a signed combination of 4 Gaussians whose coefficients
  -- are the four mixing weights (deconvolution preserves weights), all ≥ ε > 0 by the
  -- ε-standard-pair hypothesis, hence all nonzero; and `∫ |S.density| ≥ K·ε⁴ > 0` forces
  -- `S.density` not identically zero.  `ZeroCountAfterPerturbation` (Proposition 7 of
  -- Moitra–Valiant, valid without a distinct-variance assumption via the internal
  -- infinitesimal perturbation) then bounds the zeros of `S.density` by
  -- `2·(4-1) = 6`.
  -- S.density not identically zero, since ∫|S.density| ≥ K·ε⁴ > 0.
  have h_density_nonzero : ∃ x, S.density x ≠ 0 := by
    by_contra hno
    push_neg at hno
    have hzero : (∫ x, |S.density x|) = 0 := by
      have : (fun x => |S.density x|) = (fun _ : ℝ => (0 : ℝ)) := by
        funext x; rw [hno x]; simp
      rw [this]; simp
    have hpos : 0 < K * ε ^ 4 := by positivity
    linarith [hL1', hzero]
  have hzeros : Workspace.Types.ZeroCount.hasAtMostNZeros S.density 6 := by
    -- All four weights are ≥ ε > 0.
    have hw1_pos : 0 < F.weight1 := lt_of_lt_of_le hε_pos h_std.weights_bounded.1
    have hw2_pos : 0 < F.weight2 := lt_of_lt_of_le hε_pos h_std.weights_bounded.2.1
    have hw1'_pos : 0 < F'.weight1 := lt_of_lt_of_le hε_pos h_std.weights_bounded.2.2.1
    have hw2'_pos : 0 < F'.weight2 := lt_of_lt_of_le hε_pos h_std.weights_bounded.2.2.2
    -- nonzero coefficients of S.
    have h_nonzero_coeffs : ∀ q ∈ S.components, q.fst ≠ 0 := by
      rw [hS_comp]
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with h | h | h | h
      · subst h; simp only; rw [hW1]; exact ne_of_gt hw1_pos
      · subst h; simp only; rw [hW2]; exact ne_of_gt hw2_pos
      · subst h; simp only; rw [hW1']; exact neg_ne_zero.mpr (ne_of_gt hw1'_pos)
      · subst h; simp only; rw [hW2']; exact neg_ne_zero.mpr (ne_of_gt hw2'_pos)
    -- length of S.components = 4 ≥ 1.
    have hm : 1 ≤ S.components.length := by rw [hS_len_eq]; norm_num
    have hzc := ZeroCountAfterPerturbation S h_nonzero_coeffs h_density_nonzero hm
    rw [hS_len_eq] at hzc
    simpa using hzc
  -- ====== PIECEWISE MARKOV–CHEBYSHEV REWIRE ======
  set R : ℝ := 2 / ε with hR_def
  set δ : ℝ := K * ε ^ 4 / 2 with hδ_def
  set M : ℝ := 4 / ε ^ 12 with hM_def
  have hε12_pos : (0:ℝ) < ε ^ 12 := by positivity
  have hM_pos : 0 < M := by rw [hM_def]; positivity
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδM : δ ≤ M := by
    rw [hδ_def, hM_def, div_le_div_iff₀ (by norm_num) hε12_pos]
    have h16 : ε ^ 16 ≤ 8 / K := hthr4 ε hε_pos hε_le_ε4
    rw [le_div_iff₀ hK_pos] at h16
    nlinarith [h16, pow_nonneg hε_pos.le 16, pow_nonneg hε_pos.le 4,
      pow_nonneg hε_pos.le 12]
  obtain ⟨hS_diff, hS_deriv_bd⟩ :=
    DerivativeBoundOfSignedCombination S ε hε_pos hε_le_212 hS_len
      (fun q hq => ⟨(hS_bounds q hq).1, (hS_bounds q hq).2.2.1⟩)
  have hlip : LipschitzWith (Real.toNNReal M) S.density := by
    apply lipschitzWith_of_nnnorm_deriv_le hS_diff
    intro x
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM_pos.le, coe_nnnorm, Real.norm_eq_abs]
    exact hS_deriv_bd x
  have hS_cont : Continuous S.density := hS_diff.continuous
  have hfin : Set.Finite ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}) :=
    SublemmaSignedGaussianDensityZerosFinite S h_density_nonzero _ _
  have hncard : ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}).ncard ≤ 6 := by
    have hsub : {x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}
        ⊆ Workspace.Types.ZeroCount.zeroSet S.density := by
      intro y hy; exact hy.2
    have hmono : ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}).encard
        ≤ (Workspace.Types.ZeroCount.zeroSet S.density).encard := Set.encard_mono hsub
    have hle6 : ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}).encard ≤ ((6 : ℕ) : ℕ∞) := by
      have : ((6 : ℕ) : ℕ∞) = (6 : ℕ∞) := by norm_cast
      rw [this]; exact le_trans hmono hzeros
    exact (Set.encard_le_coe_iff_finite_ncard_le.mp hle6).2
  obtain ⟨zsAll, hzs_sorted, hzs_len, hzs_props, hzs_complete⟩ :=
    SublemmaExtractSortedZeroList S ε hε_pos hfin hncard
  have hzs_in : ∀ x ∈ zsAll, -R ≤ x ∧ x ≤ R := by
    intro x hx; rw [hR_def]; exact ⟨(hzs_props x hx).1, (hzs_props x hx).2.1⟩
  have hzs_zero : ∀ x ∈ zsAll, S.density x = 0 := fun x hx => (hzs_props x hx).2.2
  have hzs_complete' : ∀ x : ℝ, -R ≤ x → x ≤ R → S.density x = 0 → x ∈ zsAll := by
    intro x hx1 hx2 hxz; rw [hR_def] at hx1 hx2; exact hzs_complete x hx1 hx2 hxz
  have hmass : δ ≤ ∫ x in {x : ℝ | |x| ≤ R}, |S.density x| := by
    rw [hδ_def, hR_def]; exact hIntL1
  obtain ⟨c, hc_le, hbulk⟩ :=
    hCM R δ M S.density zsAll hR_ge hδ_pos.le hδM hM_pos hS_cont hlip hzs_len hzs_sorted
      hzs_in hzs_zero hzs_complete' hmass
  set p : Polynomial ℝ := pwPoly c with hp_def
  have hp_deg : p.natDegree ≤ 6 := pwPoly_natDegree c
  have hp_coeff : ∀ i ≤ 6, |p.coeff i| ≤ 1 * (1 / ε) ^ (6 - i) := by
    intro i hi
    have h1 : |p.coeff i| ≤ 1 := pwPoly_coeff_le c hc_le i
    have h2 : (1 : ℝ) ≤ (1 / ε) ^ (6 - i) := by
      apply one_le_pow₀; rw [le_div_iff₀ hε_pos]; linarith
    calc |p.coeff i| ≤ 1 := h1
      _ = 1 * 1 := by ring
      _ ≤ 1 * (1 / ε) ^ (6 - i) := by nlinarith [h2]
  set I_int : ℝ := ∫ x in {x : ℝ | |x| ≤ R}, Polynomial.eval x p * S.density x with hI_def
  have hbulk' : B_bulk * K ^ 4 * ε ^ 58 ≤ |I_int| := by
    have heq_integrand : I_int
        = ∫ x in {x : ℝ | |x| ≤ R}, (∑ i : Fin 7, c i * x ^ (i : ℕ)) * S.density x := by
      rw [hI_def]; apply setIntegral_congr_fun
      · exact measurableSet_le continuous_abs.measurable measurable_const
      · intro x _; simp only [hp_def, pwPoly_eval]
    rw [heq_integrand]
    have hRzpow : R ^ (-(6:ℤ)) = (R ^ 6)⁻¹ := by
      rw [show (-(6:ℤ)) = -(6:ℕ) by norm_num, zpow_neg, zpow_natCast]
    have hRpos : (0:ℝ) < R := by rw [hR_def]; positivity
    have hconst : K_CM * δ ^ 4 / M ^ 3 * R ^ (-(6:ℤ)) = B_bulk * K ^ 4 * ε ^ 58 := by
      rw [hRzpow, hR_def, hδ_def, hM_def, hBbulk_def]
      have hεne : ε ≠ 0 := hε_ne
      field_simp
      ring
    rw [← hconst]
    exact hbulk
  have hpair : (∫ x, Polynomial.eval x p * S.density x)
      = ∑ i : Fin 7, c i * rawMoment_ofSigned S (i : ℕ) := by
    rw [hp_def]; exact pwPoly_pairing_eq_moments S ε c hε_pos hε_le_212 hS_len hS_bounds
  have htail : |∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x|
      ≤ K_tail * 1 * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) :=
    hTailP S p ε 1 hε_pos hε_le1 (by norm_num) hS_len hS_bounds hp_deg hp_coeff
  have htail' : |∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x|
      ≤ B_bulk / 2 * K ^ 4 * ε ^ 58 := by
    have h2 := hthr2 ε hε_pos hε_le_ε2
    calc |∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x|
        ≤ K_tail * 1 * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := htail
      _ = K_tail * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := by ring
      _ ≤ B_bulk * K ^ 3 / 2 * K * ε ^ 58 := h2
      _ = B_bulk / 2 * K ^ 4 * ε ^ 58 := by ring
  have hint_full : Integrable (fun x : ℝ => Polynomial.eval x p * S.density x) volume :=
    integrable_evalpoly_signed p S
  have hmeas_le : MeasurableSet {x : ℝ | |x| ≤ R} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hcompl_eq_tail :
      (∫ x in {x : ℝ | ¬ |x| ≤ R}, Polynomial.eval x p * S.density x)
        = ∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x := by
    apply MeasureTheory.setIntegral_congr_set
    rw [MeasureTheory.ae_eq_set]
    have hnull : volume ({(2 : ℝ) / ε, -(2 / ε)} : Set ℝ) = 0 :=
      ((Set.finite_singleton (-(2 / ε))).insert (2 / ε)).measure_zero _
    constructor
    · have he : {x : ℝ | ¬ |x| ≤ R} \ {x : ℝ | 2 / ε ≤ |x|} = ∅ := by
        ext x
        simp only [hR_def, Set.mem_diff, Set.mem_setOf_eq, not_le, Set.mem_empty_iff_false,
          iff_false, not_and, not_not]
        intro hx; linarith
      rw [he]; simp
    · apply measure_mono_null _ hnull
      intro x hx
      simp only [hR_def, Set.mem_diff, Set.mem_setOf_eq, not_not] at hx
      have hxeq : |x| = 2 / ε := le_antisymm hx.2 hx.1
      have h2εnn : (0 : ℝ) ≤ 2 / ε := by positivity
      rcases (abs_eq h2εnn).mp hxeq with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))
  have hfull_split :
      (∫ x, Polynomial.eval x p * S.density x)
        = I_int + ∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x := by
    rw [hI_def, ← hcompl_eq_tail]
    rw [← MeasureTheory.integral_add_compl hmeas_le hint_full]
    rfl
  have hfull_lb : B_bulk / 2 * K ^ 4 * ε ^ 58 ≤ |∫ x, Polynomial.eval x p * S.density x| := by
    have htri : |I_int| ≤ |∫ x, Polynomial.eval x p * S.density x|
        + |∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x| := by
      have : I_int = (∫ x, Polynomial.eval x p * S.density x)
          - ∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x := by
        rw [hfull_split]; ring
      rw [this]; exact le_trans (abs_sub _ _) (le_refl _)
    nlinarith [htri, hbulk', htail', abs_nonneg (∫ x, Polynomial.eval x p * S.density x)]
  rw [hpair] at hfull_lb
  have hM0 : rawMoment_ofSigned S 0 = 0 := by
    rw [rawMoment_signed_diff_eq Fα Fα' S hS_density 0]
    exact (M0OfMixtureDifferenceIsZero Fα Fα').2.2
  have hsplit0 : (∑ i : Fin 7, c i * rawMoment_ofSigned S (i : ℕ))
      = ∑ i : Fin 6, c i.succ * rawMoment_ofSigned S ((i : ℕ) + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, hM0, mul_zero, zero_add, Fin.val_succ]
  rw [hsplit0] at hfull_lb
  have hsum_abs : |∑ i : Fin 6, c i.succ * rawMoment_ofSigned S ((i : ℕ) + 1)|
      ≤ ∑ i : Fin 6, |rawMoment_ofSigned S ((i : ℕ) + 1)| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    calc |c i.succ| * |rawMoment_ofSigned S ((i : ℕ) + 1)|
        ≤ 1 * |rawMoment_ofSigned S ((i : ℕ) + 1)| := by
          apply mul_le_mul_of_nonneg_right (hc_le i.succ) (abs_nonneg _)
      _ = |rawMoment_ofSigned S ((i : ℕ) + 1)| := by ring
  have hsum_lb : B_bulk / 2 * K ^ 4 * ε ^ 58
      ≤ ∑ i : Fin 6, |rawMoment_ofSigned S ((i : ℕ) + 1)| :=
    le_trans hfull_lb hsum_abs
  have hpigeon : ∃ i : Fin 6,
      B_bulk / 12 * K ^ 4 * ε ^ 58 ≤ |rawMoment_ofSigned S ((i : ℕ) + 1)| := by
    by_contra hno
    push_neg at hno
    have hstrict : ∑ i : Fin 6, |rawMoment_ofSigned S ((i : ℕ) + 1)|
        < ∑ _i : Fin 6, B_bulk / 12 * K ^ 4 * ε ^ 58 := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty
      · intro i _; exact hno i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hstrict
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at hstrict
    have heq6 : (6 : ℝ) * (B_bulk / 12 * K ^ 4 * ε ^ 58) = B_bulk / 2 * K ^ 4 * ε ^ 58 := by ring
    rw [heq6] at hstrict
    linarith
  obtain ⟨i0, hi0⟩ := hpigeon
  refine ⟨(i0 : ℕ) + 1, ?_, ?_⟩
  · have : (i0 : ℕ) < 6 := i0.isLt
    interval_cases h : (i0 : ℕ) <;> decide
  · rw [rawMoment_signed_diff_eq Fα Fα' S hS_density ((i0 : ℕ) + 1)] at hi0
    have hpw : ε ^ 8 ≤ K ^ 3 := hthr3 ε hε_pos hε_le_ε3
    have hKε58_nn : 0 ≤ K * ε ^ 58 := by positivity
    have hbridge : K * ε ^ 66 ≤ K ^ 4 * ε ^ 58 := by
      have e1 : K * ε ^ 66 = (ε ^ 8) * (K * ε ^ 58) := by ring
      have e2 : K ^ 4 * ε ^ 58 = (K ^ 3) * (K * ε ^ 58) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hpw hKε58_nn
    have hBb12_nn : 0 ≤ B_bulk / 12 := by positivity
    calc B_bulk / 12 * K * ε ^ 66
        = B_bulk / 12 * (K * ε ^ 66) := by ring
      _ ≤ B_bulk / 12 * (K ^ 4 * ε ^ 58) := by
          apply mul_le_mul_of_nonneg_left hbridge hBb12_nn
      _ = B_bulk / 12 * K ^ 4 * ε ^ 58 := by ring
      _ ≤ |rawMoment_ofMixture2 Fα ((i0 : ℕ) + 1) - rawMoment_ofMixture2 Fα' ((i0 : ℕ) + 1)| := hi0

end Workspace.ProofLemmas.Lemma9MomentGap
