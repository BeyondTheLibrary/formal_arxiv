import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.Claim1_RuleOutInterior
import Workspace.ProofLemmas.InteriorFOC_Pos
import Workspace.ProofLemmas.InteriorFOC_Neg
import Workspace.ProofLemmas.RightBoundary_ForcesC0
import Workspace.ProofLemmas.LeftBoundary_ForcesFjZero
import Workspace.ProofLemmas.SignIncompatibility
import Workspace.ProofLemmas.PEqZeroNotLocalMin
import Workspace.ProofLemmas.LqNormZeroIffEqZero

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

namespace LocalOptimumCharacterization_CaseSNonemptyProof

/-- Helper: x^(q-1) = y^(q-1) with x, y ≥ 0 and q-1 > 0 implies x = y. -/
private lemma rpow_qm1_inj {q : ℝ} (hqm1 : 0 < q - 1) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (heq : x ^ (q - 1) = y ^ (q - 1)) : x = y := by
  have hq_inv_pos : 0 < 1 / (q - 1) := by positivity
  have h1 : (x ^ (q - 1)) ^ (1 / (q - 1)) = (y ^ (q - 1)) ^ (1 / (q - 1)) := by rw [heq]
  rw [← Real.rpow_mul hx, ← Real.rpow_mul hy] at h1
  have hmul : (q - 1) * (1 / (q - 1)) = 1 := by
    field_simp
  rw [hmul, Real.rpow_one, Real.rpow_one] at h1
  exact h1

/-- Helper: from `(p - f)^(q-1) / N1^(q-1) = lambda * p^(q-1) / N2^(q-1)`
with `p > f ≥ 0`, `N1 > 0`, `N2 > 0`, `lambda > 0`, `q > 1`, derive
`(p - f) / p = lambda^(1/(q-1)) * N1 / N2`. -/
private lemma extract_c_pos {q : ℝ} (hq : 1 < q) {p_j f_j N1 N2 lambda : ℝ}
    (hf_nn : 0 ≤ f_j) (hpf : f_j < p_j) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hlam : 0 < lambda)
    (hkkt : (p_j - f_j) ^ (q - 1) / N1 ^ (q - 1)
            = lambda * (p_j ^ (q - 1) / N2 ^ (q - 1))) :
    (p_j - f_j) / p_j = Real.rpow lambda (1 / (q - 1)) * N1 / N2 := by
  have hp_pos : 0 < p_j := lt_of_le_of_lt hf_nn hpf
  have hpf_pos : 0 < p_j - f_j := by linarith
  have hqm1_pos : 0 < q - 1 := by linarith
  have hN1_pow : 0 < N1 ^ (q - 1) := Real.rpow_pos_of_pos hN1 _
  have hN2_pow : 0 < N2 ^ (q - 1) := Real.rpow_pos_of_pos hN2 _
  have hp_pow : 0 < p_j ^ (q - 1) := Real.rpow_pos_of_pos hp_pos _
  -- Step 1: Multiply both sides by N1^(q-1)/p^(q-1).
  -- ((p-f)/p)^(q-1) = lambda * (N1/N2)^(q-1)
  have hstep1 : ((p_j - f_j) / p_j) ^ (q - 1) = lambda * (N1 / N2) ^ (q - 1) := by
    rw [Real.div_rpow (le_of_lt hpf_pos) (le_of_lt hp_pos)]
    rw [Real.div_rpow (le_of_lt hN1) (le_of_lt hN2)]
    field_simp
    field_simp at hkkt
    linarith
  -- Step 2: Take (q-1)-th roots.
  -- LHS: ((p-f)/p) ≥ 0; RHS: lambda^(1/(q-1)) * N1/N2 ≥ 0.
  have hlhs_nn : 0 ≤ (p_j - f_j) / p_j := div_nonneg (le_of_lt hpf_pos) (le_of_lt hp_pos)
  have hN1N2_nn : 0 ≤ N1 / N2 := div_nonneg (le_of_lt hN1) (le_of_lt hN2)
  have hlam_rpow_nn : 0 ≤ Real.rpow lambda (1 / (q - 1)) := Real.rpow_nonneg (le_of_lt hlam) _
  have hrhs_nn : 0 ≤ Real.rpow lambda (1 / (q - 1)) * (N1 / N2) :=
    mul_nonneg hlam_rpow_nn hN1N2_nn
  -- We'll show: (lambda^(1/(q-1)) * (N1/N2))^(q-1) = lambda * (N1/N2)^(q-1).
  have hrhs_pow : (Real.rpow lambda (1 / (q - 1)) * (N1 / N2)) ^ (q - 1)
      = lambda * (N1 / N2) ^ (q - 1) := by
    rw [Real.mul_rpow hlam_rpow_nn hN1N2_nn]
    -- (lambda^(1/(q-1)))^(q-1) = lambda
    have hlam_pow : Real.rpow lambda (1 / (q - 1)) ^ (q - 1) = lambda := by
      rw [show (Real.rpow lambda (1/(q-1))) ^ (q-1)
            = Real.rpow lambda ((1/(q-1))*(q-1))
            from (Real.rpow_mul (le_of_lt hlam) (1/(q-1)) (q-1)).symm,
          show (1 / (q-1) * (q-1) : ℝ) = 1 from by field_simp]
      exact Real.rpow_one lambda
    rw [hlam_pow]
  -- Now ((p-f)/p)^(q-1) = (lambda^(1/(q-1)) * (N1/N2))^(q-1).
  have heq2 : ((p_j - f_j) / p_j) ^ (q - 1)
      = (Real.rpow lambda (1 / (q - 1)) * (N1 / N2)) ^ (q - 1) := by
    rw [hrhs_pow]; exact hstep1
  have heq3 : (p_j - f_j) / p_j = Real.rpow lambda (1 / (q - 1)) * (N1 / N2) :=
    rpow_qm1_inj hqm1_pos hlhs_nn hrhs_nn heq2
  rw [heq3]; ring

/-- Helper: same for negative branch.
From `(f - p)^(q-1) / N1^(q-1) = lambda * (-p)^(q-1) / N2^(q-1)` with `p < 0`, `f ≥ 0`,
derive `(f - p) / (-p) = lambda^(1/(q-1)) * N1/N2`. -/
private lemma extract_c_neg {q : ℝ} (hq : 1 < q) {p_j f_j N1 N2 lambda : ℝ}
    (hf_nn : 0 ≤ f_j) (hp_neg : p_j < 0) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hlam : 0 < lambda)
    (hkkt : (f_j - p_j) ^ (q - 1) / N1 ^ (q - 1)
            = lambda * ((-p_j) ^ (q - 1) / N2 ^ (q - 1))) :
    (f_j - p_j) / (-p_j) = Real.rpow lambda (1 / (q - 1)) * N1 / N2 := by
  have hnp_pos : 0 < -p_j := by linarith
  have hfp_pos : 0 < f_j - p_j := by linarith
  have hqm1_pos : 0 < q - 1 := by linarith
  have hN1_pow : 0 < N1 ^ (q - 1) := Real.rpow_pos_of_pos hN1 _
  have hN2_pow : 0 < N2 ^ (q - 1) := Real.rpow_pos_of_pos hN2 _
  have hnp_pow : 0 < (-p_j) ^ (q - 1) := Real.rpow_pos_of_pos hnp_pos _
  have hstep1 : ((f_j - p_j) / (-p_j)) ^ (q - 1) = lambda * (N1 / N2) ^ (q - 1) := by
    rw [Real.div_rpow (le_of_lt hfp_pos) (le_of_lt hnp_pos)]
    rw [Real.div_rpow (le_of_lt hN1) (le_of_lt hN2)]
    field_simp
    field_simp at hkkt
    linarith
  have hlhs_nn : 0 ≤ (f_j - p_j) / (-p_j) := div_nonneg (le_of_lt hfp_pos) (le_of_lt hnp_pos)
  have hN1N2_nn : 0 ≤ N1 / N2 := div_nonneg (le_of_lt hN1) (le_of_lt hN2)
  have hlam_rpow_nn : 0 ≤ Real.rpow lambda (1 / (q - 1)) := Real.rpow_nonneg (le_of_lt hlam) _
  have hrhs_nn : 0 ≤ Real.rpow lambda (1 / (q - 1)) * (N1 / N2) :=
    mul_nonneg hlam_rpow_nn hN1N2_nn
  have hrhs_pow : (Real.rpow lambda (1 / (q - 1)) * (N1 / N2)) ^ (q - 1)
      = lambda * (N1 / N2) ^ (q - 1) := by
    rw [Real.mul_rpow hlam_rpow_nn hN1N2_nn]
    have hlam_pow : Real.rpow lambda (1 / (q - 1)) ^ (q - 1) = lambda := by
      rw [show (Real.rpow lambda (1/(q-1))) ^ (q-1)
            = Real.rpow lambda ((1/(q-1))*(q-1))
            from (Real.rpow_mul (le_of_lt hlam) (1/(q-1)) (q-1)).symm,
          show (1 / (q-1) * (q-1) : ℝ) = 1 from by field_simp]
      exact Real.rpow_one lambda
    rw [hlam_pow]
  have heq2 : ((f_j - p_j) / (-p_j)) ^ (q - 1)
      = (Real.rpow lambda (1 / (q - 1)) * (N1 / N2)) ^ (q - 1) := by
    rw [hrhs_pow]; exact hstep1
  have heq3 : (f_j - p_j) / (-p_j) = Real.rpow lambda (1 / (q - 1)) * (N1 / N2) :=
    rpow_qm1_inj hqm1_pos hlhs_nn hrhs_nn heq2
  rw [heq3]; ring

end LocalOptimumCharacterization_CaseSNonemptyProof

open LocalOptimumCharacterization_CaseSNonemptyProof

theorem LocalOptimumCharacterization_CaseSNonempty
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma_i : Fin d → ℝ) (hsigma_pm : ∀ j, sigma_i j = 1 ∨ sigma_i j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma_i j = 1 → 0 ≤ p_star j) ∧
                  (sigma_i j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma_i j = 1 → 0 ≤ p j) ∧
                (sigma_i j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p)
    (S : Finset (Fin d))
    (hS_def : S = Finset.univ.filter (fun j : Fin d => sigma_i j = 1))
    (hS_ne : S.Nonempty) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      (∀ j ∈ S, p_star j = f j / (1 - c)) ∧
      (∀ j ∉ S, p_star j = 0) := by
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq_le
  have hqm1_pos : (0 : ℝ) < q - 1 := by linarith
  have hmemS : ∀ j, j ∈ S ↔ sigma_i j = 1 := by
    intro j; rw [hS_def]; simp [Finset.mem_filter]
  have hnotmemS : ∀ j, j ∉ S ↔ sigma_i j = -1 := by
    intro j
    rw [hmemS]
    constructor
    · intro hne
      rcases hsigma_pm j with h | h
      · exact (hne h).elim
      · exact h
    · intro h heq
      rw [heq] at h; norm_num at h
  have hp_nn_S : ∀ j ∈ S, 0 ≤ p_star j := by
    intro j hj; exact (hp_in j).1 ((hmemS j).mp hj)
  have hp_np_Sc : ∀ j ∉ S, p_star j ≤ 0 := by
    intro j hj; exact (hp_in j).2 ((hnotmemS j).mp hj)
  -- p_star is not identically zero
  have hS_pos : ∃ k, sigma_i k = 1 := by
    obtain ⟨j, hj⟩ := hS_ne
    exact ⟨j, (hmemS j).mp hj⟩
  have hp_not_zero : ¬ (∀ j, p_star j = 0) := by
    intro hzero
    apply PEqZeroNotLocalMin q hq lambda hlam0 hlam1 hd f hf_nn hf_sum sigma_i hsigma_pm hS_pos
    obtain ⟨ε, hε, hloc⟩ := hp_loc
    refine ⟨ε, hε, ?_⟩
    intro p hp_orth hp_close
    have hp_close' : ∀ j, |p j - p_star j| < ε := by
      intro j; have hk := hp_close j; rw [hzero j]; simpa using hk
    have h2 : g_lambda q lambda f p_star ≤ g_lambda q lambda f p := hloc p hp_orth hp_close'
    have hpstar_eq : p_star = (fun _ : Fin d => (0 : ℝ)) := by
      funext j; exact hzero j
    rw [hpstar_eq] at h2
    exact h2
  have hps_pos : 0 < lqNorm q p_star := by
    have hps_nn : 0 ≤ lqNorm q p_star := lqNorm_nonneg hq_le p_star
    rcases lt_or_eq_of_le hps_nn with h | h
    · exact h
    · exfalso
      have heq : lqNorm q p_star = 0 := h.symm
      have hzero : p_star = 0 := (LqNormZeroIffEqZero q hq_le hd p_star).mp heq
      apply hp_not_zero
      intro j; have := congrFun hzero j; simpa using this
  -- Case split on lqNorm q (p - f) = 0.
  by_cases hpf_zero : lqNorm q (fun k => p_star k - f k) = 0
  · -- Case A: p_star = f.
    have hpf_eq : (fun k => p_star k - f k) = 0 :=
      (LqNormZeroIffEqZero q hq_le hd _).mp hpf_zero
    have hpf_ptw : ∀ j, p_star j = f j := by
      intro j
      have := congrFun hpf_eq j
      simp at this
      linarith
    refine ⟨0, le_refl 0, by norm_num, ?_, ?_⟩
    · intro j _hj
      rw [hpf_ptw j]; ring
    · intro j hj
      have hpj_le : p_star j ≤ 0 := hp_np_Sc j hj
      have hpj_eq : p_star j = f j := hpf_ptw j
      have hfj_nn : 0 ≤ f j := hf_nn j
      linarith
  · -- Case B: lqNorm q (p_star - f) > 0.
    have hpf_pos : 0 < lqNorm q (fun k => p_star k - f k) := by
      have hnn : 0 ≤ lqNorm q (fun k => p_star k - f k) := lqNorm_nonneg hq_le _
      rcases lt_or_eq_of_le hnn with h | h
      · exact h
      · exfalso; exact hpf_zero h.symm
    set c : ℝ :=
        Real.rpow lambda (1 / (q - 1)) *
          lqNorm q (fun k => p_star k - f k) / lqNorm q p_star with hc_def
    have hlam_nn : 0 ≤ lambda := le_of_lt hlam0
    have hrpow_nn : 0 ≤ Real.rpow lambda (1 / (q - 1)) := Real.rpow_nonneg hlam_nn _
    have hc_nn : 0 ≤ c := by
      have h1 : 0 ≤ Real.rpow lambda (1 / (q - 1)) *
          lqNorm q (fun k => p_star k - f k) :=
        mul_nonneg hrpow_nn (le_of_lt hpf_pos)
      exact div_nonneg h1 (le_of_lt hps_pos)
    -- Key claim: at any j ∈ Fin d with σ_j = +1, p_star j > f j, we have
    -- (p_star j - f j) / p_star j = c.
    have hc_eq_pos : ∀ (j : Fin d), sigma_i j = 1 → f j < p_star j →
        (p_star j - f j) / p_star j = c := by
      intro j hsig hpf
      have hkkt := InteriorFOC_Pos q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
        sigma_i hsigma_pm p_star hp_in hp_loc hpf_pos hps_pos j hsig hpf
      have := extract_c_pos hq (hf_nn j) hpf hpf_pos hps_pos hlam0 hkkt
      rw [this, hc_def]
    -- Similarly for negative branch.
    have hc_eq_neg : ∀ (j : Fin d), sigma_i j = -1 → p_star j < 0 →
        (f j - p_star j) / (- p_star j) = c := by
      intro j hsig hpneg
      have hkkt := InteriorFOC_Neg q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
        sigma_i hsigma_pm p_star hp_in hp_loc hpf_pos hps_pos j hsig hpneg
      have := extract_c_neg hq (hf_nn j) hpneg hpf_pos hps_pos hlam0 hkkt
      rw [this, hc_def]
    -- Step 5.1.2: For every j ∈ S, (1 - c) p_star j = f j.
    have hS_eq_aux : ∀ j ∈ S, (1 - c) * p_star j = f j := by
      intro j hj
      have hsig : sigma_i j = 1 := (hmemS j).mp hj
      have hp_nn : 0 ≤ p_star j := hp_nn_S j hj
      have hclaim := Claim1_RuleOutInterior q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
        sigma_i hsigma_pm p_star hp_in hp_loc j hsig
      rcases hclaim with hpz | hpf_ge
      · have hfz : f j = 0 := LeftBoundary_ForcesFjZero q hq lambda hlam0 hlam1 hd f
          hf_nn hf_sum sigma_i hsigma_pm p_star hp_in hp_loc hpf_pos j hsig hpz
        rw [hpz, hfz]; ring
      · rcases lt_or_eq_of_le hpf_ge with hgt | heq
        · -- p_star j > f j. Use hc_eq_pos.
          have hcj := hc_eq_pos j hsig hgt
          have hpj_pos : 0 < p_star j := lt_of_le_of_lt (hf_nn j) hgt
          -- hcj : (p_star j - f j)/p_star j = c.
          -- Want: (1-c) * p_star j = f j.
          have : p_star j - f j = c * p_star j := by
            field_simp at hcj
            linarith
          linarith
        · -- p_star j = f j. Sub-cases.
          rcases lt_or_eq_of_le (hf_nn j) with hfp | hfz
          · -- f j > 0. RightBoundary_ForcesC0 contradicts Case B.
            exfalso
            have hcontr := RightBoundary_ForcesC0 q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
              sigma_i hsigma_pm p_star hp_in hp_loc hpf_pos hps_pos j hsig heq.symm hfp
            rw [hcontr] at hpf_pos
            exact lt_irrefl _ hpf_pos
          · -- f j = 0. Then p_star j = 0 too.
            have hfj : f j = 0 := hfz.symm
            have hpj : p_star j = 0 := by linarith
            rw [hpj, hfj]; ring
    -- Step 5.1.3: KEY — there is some j ∈ S with f j > 0 (i.e. the energy on S
    -- is positive). From this, c < 1 follows directly. We package the witness
    -- with the bound f j ≤ p_star j so it doubles as the SignIncompatibility (P)
    -- witness.
    have hPwit : ∃ j ∈ S, f j ≤ p_star j ∧ 0 < f j := by
      -- Helper: at any k ∈ S with f k > 0, we get f k ≤ p_star k.
      have hSwit_of_mem : ∀ k ∈ S, 0 < f k → f k ≤ p_star k := by
        intro k hk_S hfk_pos
        have hsig_k : sigma_i k = 1 := (hmemS k).mp hk_S
        have hcl_k := Claim1_RuleOutInterior q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
          sigma_i hsigma_pm p_star hp_in hp_loc k hsig_k
        rcases hcl_k with hpkz | hpk_ge
        · exfalso
          have hfk_zero := LeftBoundary_ForcesFjZero q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
            sigma_i hsigma_pm p_star hp_in hp_loc hpf_pos k hsig_k hpkz
          linarith
        · exact hpk_ge
      -- It suffices to prove there is some j ∈ S with 0 < f j (positive S-energy).
      rsuffices ⟨j, hj_S, hfj_pos⟩ : ∃ j ∈ S, 0 < f j
      · exact ⟨j, hj_S, hSwit_of_mem j hj_S hfj_pos, hfj_pos⟩
      -- ===================================================================
      -- POSITIVE S-ENERGY  (∃ j ∈ S, 0 < f j).
      --
      -- With the paper's normalization `hf_pos : ∀ j, 0 < f j` (approx.tex
      -- line 9, every optimal facility coordinate is strictly positive), the
      -- degenerate configuration E_S = ∑_{j∈S} f_j^q = 0 cannot occur: S is
      -- nonempty, so pick any witness j ∈ S and `hf_pos j` gives 0 < f j.
      -- ===================================================================
      obtain ⟨j, hj_S⟩ := hS_ne
      exact ⟨j, hj_S, hf_pos j⟩
    -- From hPwit, derive c < 1 and the SignIncompatibility (P) witness.
    obtain ⟨jw, hjw_S, hfjw_le, hfjw_pos⟩ := hPwit
    have hsig_jw : sigma_i jw = 1 := (hmemS jw).mp hjw_S
    have hpjw_pos : 0 < p_star jw := lt_of_lt_of_le hfjw_pos hfjw_le
    -- c < 1: from (1 - c) * p_star jw = f jw > 0 and p_star jw > 0.
    have hc_lt_one : c < 1 := by
      have hq_eq := hS_eq_aux jw hjw_S
      by_contra hge
      push_neg at hge  -- 1 ≤ c
      have h1mc : 1 - c ≤ 0 := by linarith
      have : (1 - c) * p_star jw ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1mc (le_of_lt hpjw_pos)
      rw [hq_eq] at this
      linarith
    -- (P) witness for SignIncompatibility.
    have hP : ∃ j : Fin d, sigma_i j = 1 ∧ f j ≤ p_star j ∧ 0 < f j :=
      ⟨jw, hsig_jw, hfjw_le, hfjw_pos⟩
    -- Step 5.1.5: For every i ∉ S, p_star i = 0.
    have h_pSc_zero : ∀ i, i ∉ S → p_star i = 0 := by
      intro i hi
      have hsig_i : sigma_i i = -1 := (hnotmemS i).mp hi
      have hpi_np : p_star i ≤ 0 := hp_np_Sc i hi
      rcases lt_or_eq_of_le hpi_np with hpi_neg | hpi_zero
      · exfalso
        rcases lt_or_eq_of_le (hf_nn i) with hfi_pos | hfi_zero
        · -- f i > 0, p_star i < 0: SignIncompatibility with the (P) witness.
          have hsi := SignIncompatibility q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
            sigma_i hsigma_pm p_star hp_in hp_loc hpf_pos hps_pos
          apply hsi
          exact ⟨hP, ⟨i, hsig_i, hpi_neg, hfi_pos⟩⟩
        · -- f i = 0, p_star i < 0: negative FOC gives c = 1, contradicting c < 1.
          have hci := hc_eq_neg i hsig_i hpi_neg
          have hfi_eq : f i = 0 := hfi_zero.symm
          rw [hfi_eq, zero_sub] at hci
          have hnpi_ne : -p_star i ≠ 0 := by linarith
          have hci_eq_one : c = 1 := by
            rw [← hci, neg_div_neg_eq, div_self (by linarith : p_star i ≠ 0)]
          linarith
      · exact hpi_zero
    -- Step 5.1.6 + 5.1.7: assemble.
    refine ⟨c, hc_nn, hc_lt_one, ?_, h_pSc_zero⟩
    intro j hj
    have hj_eq := hS_eq_aux j hj
    have h1mc_pos : 0 < 1 - c := by linarith
    have h1mc_ne : (1 - c) ≠ 0 := ne_of_gt h1mc_pos
    field_simp
    linarith
