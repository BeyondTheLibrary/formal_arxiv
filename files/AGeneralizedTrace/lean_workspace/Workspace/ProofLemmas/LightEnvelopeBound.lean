import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.SublemmaImplicitWeightIdentification
import Workspace.ProofLemmas.NormaliserBound
import Workspace.ProofLemmas.RareSupportShifted
import Workspace.ProofLemmas.BinomialPmfMaxBound

set_option maxHeartbeats 8000000

open Classical
open Workspace.Types.AlternatingSumExpression

theorem LightEnvelopeBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let n_h : ℕ := n / 2
      let S_er : ℤ → ℕ → ℝ := fun r j =>
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
          Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ))
      let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j))
      let envelopeW : Finset ℕ → ℝ := fun ℓ =>
        ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ,
            Workspace.Types.AlternatingSumExpression.ellFactor n
              ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1)
      let P_L : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)))
      ∑ ℓ ∈ P_L, envelopeW ℓ ≤ (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) := by
  intro n hn hmod
  intro c' α n_h S_er widetildeMu_er envelopeW P_L
  -- Numeric setup.
  have hn1 : 1 ≤ n := by
    have : (1 : ℕ) ≤ 10 ^ 12 := by norm_num
    exact this.trans hn
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hsqn_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  -- Replace c', α, n_h, S_er, widetildeMu_er, envelopeW, P_L definitions.
  -- These let-bindings are zeta-reduced inside `show`/`change`.
  -- Bring the `NormaliserBound` and `SublemmaImplicitWeightIdentification` into scope.
  have hNB := NormaliserBound n hn hmod
  have hWI := SublemmaImplicitWeightIdentification n hn hmod
  have hRS := RareSupportShifted n hn hmod
  -- Zeta-reduce hNB / hWI / hRS so they are usable.
  simp only at hNB hWI hRS
  -- Define a local Zprime_er.
  set Zprime_er : ℤ → ℝ := fun r =>
    ∏ j ∈ Finset.Icc 1 (n / 2), (1 - S_er r j) with hZprime_er
  -- Reusable facts about S_er.
  -- Each S_er r j ∈ [0, 1/2] (the proof is the same as in NormaliserBound and RareSupportShifted).
  have hexp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have hsq2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hexp2_lb : (7.389 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]
    rw [he2]
    have hpos : (0 : ℝ) ≤ 2.7182818283 := by norm_num
    have h2 : (2.7182818283 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ hpos h1.le 2
    have h3 : (7.389 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
    linarith
  have hsq2pi_lb : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
    have h4 : (2.5 : ℝ) ^ 2 ≤ 2 * Real.pi := by nlinarith
    exact Real.le_sqrt_of_sq_le h4
  have h_denom_pos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hc'_pos : 0 < c' := by
    show 0 < 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    positivity
  -- binPMFInt nonneg
  have hbpInt_nn : ∀ (k : ℤ), 0 ≤ binPMFInt n (1/2) k := by
    intro k
    unfold binPMFInt binPMF
    split_ifs
    · positivity
    · exact le_refl 0
    · exact le_refl 0
  -- binPMFInt ≤ √(2/(πn))
  have hbpInt_le_sqrt : ∀ (k : ℤ), binPMFInt n (1/2) k ≤ Real.sqrt (2 / (Real.pi * n)) := by
    intro k
    unfold binPMFInt binPMF
    by_cases hk : 0 ≤ k ∧ k ≤ (n : ℤ)
    · simp only [hk, ↓reduceIte]
      by_cases hkn : k.toNat ≤ n
      · simp only [hkn]
        have hbase : ((Nat.choose n k.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ Real.sqrt (2 / (Real.pi * n)) :=
          BinomialPmfMaxBound n hn1 k.toNat
        have hpow : ((1 : ℝ) / 2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat) = ((2 : ℝ) ^ n)⁻¹ := by
          rw [show (1 : ℝ) - 1/2 = 1/2 by ring]
          rw [← pow_add, Nat.add_sub_cancel' hkn, one_div, inv_pow]
        calc (Nat.choose n k.toNat : ℝ) * ((1 : ℝ)/2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat)
            = (Nat.choose n k.toNat : ℝ) * (((1 : ℝ)/2) ^ k.toNat * ((1 - (1 : ℝ)/2)) ^ (n - k.toNat)) := by ring
          _ = (Nat.choose n k.toNat : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rw [hpow]
          _ ≤ Real.sqrt (2 / (Real.pi * n)) := hbase
      · simp only [hkn, ↓reduceIte]; exact Real.sqrt_nonneg _
    · simp only [hk, ↓reduceIte]; exact Real.sqrt_nonneg _
  -- Now show S_er r j ∈ [0, 1/2].
  have hSer_nn : ∀ r j, 0 ≤ S_er r j := by
    intros r j
    show 0 ≤ ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
      binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
    apply mul_nonneg
    · positivity
    · exact hbpInt_nn _
  have hSer_le_half : ∀ r j, S_er r j ≤ 1/2 := by
    intros r j
    show ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
      binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ 1/2
    have hα_nn : 0 ≤ c' * Real.sqrt n := by
      show 0 ≤ (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      positivity
    have hbnd : binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ Real.sqrt (2 / (Real.pi * n)) :=
      hbpInt_le_sqrt _
    have hsqrt_nn : 0 ≤ Real.sqrt (2 / (Real.pi * n)) := Real.sqrt_nonneg _
    have hstep1 : c' * Real.sqrt n * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) :=
      mul_le_mul_of_nonneg_left hbnd hα_nn
    have hstep2 : c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = c' * Real.sqrt (2 / Real.pi) := by
      rw [mul_assoc]
      congr 1
      rw [← Real.sqrt_mul hn_pos_real.le (2 / (Real.pi * n))]
      congr 1
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos_real
      have hpine : Real.pi ≠ 0 := ne_of_gt hpi_pos
      field_simp
    have hsq : Real.sqrt (2 / Real.pi) ≤ 1 := by
      rw [Real.sqrt_le_one]; rw [div_le_one hpi_pos]; linarith [Real.pi_gt_d2]
    have hsq_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
    have hc'_le_half : c' ≤ 1/2 := by
      show 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) ≤ 1/2
      rw [div_le_iff₀ h_denom_pos]
      have h_lb : (1 : ℝ) ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
        have hh1 : (2 : ℝ) * 7.389 * 2.5 ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
          have hh : (2 : ℝ) * 7.389 ≤ 2 * Real.exp 2 := by linarith
          apply mul_le_mul hh hsq2pi_lb (by norm_num) (by linarith)
        linarith
      linarith
    have hstep3 : c' * Real.sqrt (2 / Real.pi) ≤ 1/2 := by
      calc c' * Real.sqrt (2 / Real.pi) ≤ c' * 1 :=
              mul_le_mul_of_nonneg_left hsq hc'_pos.le
        _ = c' := by ring
        _ ≤ 1/2 := hc'_le_half
    have h_eq : ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
        = c' * Real.sqrt n := by show _ = _; rfl
    rw [h_eq]
    calc c' * Real.sqrt n * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) := hstep1
      _ = c' * Real.sqrt (2 / Real.pi) := hstep2
      _ ≤ 1/2 := hstep3
  have hSer_lt_one : ∀ r j, S_er r j < 1 := by
    intros r j
    have := hSer_le_half r j
    linarith
  have hOneMinusSer_pos : ∀ r j, 0 < 1 - S_er r j := by
    intros r j
    have := hSer_le_half r j
    linarith
  have hOneMinusSer_nn : ∀ r j, 0 ≤ 1 - S_er r j := fun r j => (hOneMinusSer_pos r j).le
  -- widetildeMu_er ≥ 0.
  have hMu_nn : ∀ r ℓ, 0 ≤ widetildeMu_er r ℓ := by
    intros r ℓ
    show 0 ≤ ∏ j ∈ Finset.Icc 1 (n / 2), (if j ∈ ℓ then S_er r j else (1 - S_er r j))
    apply Finset.prod_nonneg
    intros j _
    by_cases hj : j ∈ ℓ
    · simp [hj]; exact hSer_nn r j
    · simp [hj]; linarith [hOneMinusSer_nn r j]
  -- Zprime_er > 0.
  have hZ_pos : ∀ r, 0 < Zprime_er r := by
    intros r
    show 0 < ∏ j ∈ Finset.Icc 1 (n / 2), (1 - S_er r j)
    apply Finset.prod_pos
    intros j _
    exact hOneMinusSer_pos r j
  -- Combined NB facts.
  have hNB_inv_le : ∀ r, -((n : ℤ) / 4) ≤ r → r ≤ ((n : ℤ) / 4) →
      (Zprime_er r)⁻¹ ≤ Real.exp (2 * c' * Real.sqrt n) := by
    intros r hr1 hr2
    have h := hNB r hr1 hr2
    -- h : (Zprime_er r)⁻¹ ≤ exp(2 c' √n) ∧ 2 c' ≤ 1/32
    -- Zprime_er definition match.
    exact h.1
  have h2c'_le : 2 * c' ≤ (1 : ℝ) / 32 := by
    have h := hNB 0 (by
      have : (0 : ℤ) ≤ (n : ℤ) / 4 := by positivity
      linarith) (by
      have : (0 : ℤ) ≤ (n : ℤ) / 4 := by positivity
      linarith)
    exact h.2
  -- Hence (Zprime_er r)⁻¹ ≤ exp(√n/32).
  have hZ_inv_le_exp : ∀ r, -((n : ℤ) / 4) ≤ r → r ≤ ((n : ℤ) / 4) →
      (Zprime_er r)⁻¹ ≤ Real.exp (Real.sqrt n / 32) := by
    intros r hr1 hr2
    have h1 := hNB_inv_le r hr1 hr2
    have h2 : 2 * c' * Real.sqrt n ≤ Real.sqrt n / 32 := by
      have := mul_le_mul_of_nonneg_right h2c'_le hsqn_nn
      calc 2 * c' * Real.sqrt n ≤ 1/32 * Real.sqrt n := this
        _ = Real.sqrt n / 32 := by ring
    exact h1.trans (Real.exp_le_exp.mpr h2)
  -- ===== (j-1) ENVELOPE REDUCTION TO THE PLAIN-j ENVELOPE =====
  -- The (j-1) per-factor equals the plain factor at a shifted r:
  -- ellFactor n α r (j-1) = ellFactor n α (r-1) j  for 1 ≤ j.
  have ellFactor_shift : ∀ (r : ℤ) (j : ℕ), 1 ≤ j →
      Workspace.Types.AlternatingSumExpression.ellFactor n
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1)
        = Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (r - 1) j := by
    intro r j hj
    unfold Workspace.Types.AlternatingSumExpression.ellFactor
    have hidx : (r + ((n : ℤ) / 4) + ((j - 1 : ℕ) : ℤ))
        = ((r - 1) + ((n : ℤ) / 4) + (j : ℤ)) := by
      have : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
      rw [this]; ring
    simp only [hidx]
  -- ellFactor n α s j ≥ 0  (since the implicit weight S = α·X ∈ [0,1/2], so 1 - S > 0).
  have hellFactor_nn : ∀ (s : ℤ) (j : ℕ),
      0 ≤ Workspace.Types.AlternatingSumExpression.ellFactor n
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j := by
    intro s j
    unfold Workspace.Types.AlternatingSumExpression.ellFactor
    simp only []
    have hnn : 0 ≤ S_er s j := hSer_nn s j
    have hlt : 1 - S_er s j > 0 := hOneMinusSer_pos s j
    have hS_eq : ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
        binPMFInt n (1/2) (s + ((n : ℤ) / 4) + (j : ℤ)) = S_er s j := rfl
    rw [hS_eq]
    positivity
  -- Binomial up-slope monotonicity: binPMFInt(j-1) ≤ binPMFInt(j) for 1 ≤ j ≤ n/2.
  have hbinmono : ∀ (j : ℕ), 1 ≤ j → j ≤ n / 2 →
      binPMFInt n (1/2) ((j : ℤ) - 1) ≤ binPMFInt n (1/2) (j : ℤ) := by
    intro j hj1 hjn
    have hjle : j ≤ n := by omega
    have hj1le : j - 1 ≤ n := by omega
    unfold binPMFInt
    have hc1 : (0 ≤ (j : ℤ) - 1 ∧ (j : ℤ) - 1 ≤ (n : ℤ)) := by
      constructor <;> [omega; exact_mod_cast hj1le]
    have hc2 : (0 ≤ (j : ℤ) ∧ (j : ℤ) ≤ (n : ℤ)) := by
      constructor <;> [positivity; exact_mod_cast hjle]
    simp only [hc1, hc2, and_self, ↓reduceIte]
    have ht1 : ((j : ℤ) - 1).toNat = j - 1 := by omega
    have ht2 : ((j : ℤ)).toNat = j := by omega
    rw [ht1, ht2]
    unfold binPMF
    rw [if_pos hj1le, if_pos hjle]
    have hchoose : Nat.choose n (j - 1) ≤ Nat.choose n j := by
      have := Nat.choose_le_succ_of_lt_half_left (r := j - 1) (n := n) (by omega)
      rwa [Nat.sub_add_cancel hj1] at this
    have hpow1 : ((1:ℝ)/2) ^ (j-1) * (1 - (1:ℝ)/2) ^ (n - (j-1)) = ((2:ℝ)^n)⁻¹ := by
      rw [show (1:ℝ) - 1/2 = 1/2 by ring, ← pow_add, Nat.add_sub_cancel' hj1le, one_div, inv_pow]
    have hpow2 : ((1:ℝ)/2) ^ j * (1 - (1:ℝ)/2) ^ (n - j) = ((2:ℝ)^n)⁻¹ := by
      rw [show (1:ℝ) - 1/2 = 1/2 by ring, ← pow_add, Nat.add_sub_cancel' hjle, one_div, inv_pow]
    rw [show (Nat.choose n (j-1) : ℝ) * ((1:ℝ)/2) ^ (j-1) * (1 - (1:ℝ)/2) ^ (n - (j-1))
          = (Nat.choose n (j-1) : ℝ) * (((1:ℝ)/2) ^ (j-1) * (1 - (1:ℝ)/2) ^ (n - (j-1))) by ring,
        show (Nat.choose n j : ℝ) * ((1:ℝ)/2) ^ j * (1 - (1:ℝ)/2) ^ (n - j)
          = (Nat.choose n j : ℝ) * (((1:ℝ)/2) ^ j * (1 - (1:ℝ)/2) ^ (n - j)) by ring,
        hpow1, hpow2]
    have hchooseR : (Nat.choose n (j-1) : ℝ) ≤ (Nat.choose n j : ℝ) := by exact_mod_cast hchoose
    have hinv : (0:ℝ) ≤ ((2:ℝ)^n)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right hchooseR hinv
  -- Per-factor boundary monotonicity: ellFactor (-(n/4)-1) j ≤ ellFactor (-(n/4)) j on Icc 1 (n/2).
  have hellmono : ∀ (j : ℕ), 1 ≤ j → j ≤ n / 2 →
      Workspace.Types.AlternatingSumExpression.ellFactor n
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4) - 1) j
        ≤ Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j := by
    intro j hj1 hjn
    unfold Workspace.Types.AlternatingSumExpression.ellFactor
    simp only []
    -- index of the (-(n/4)-1) factor is j-1; index of the (-(n/4)) factor is j.
    have hidx1 : (-((n : ℤ) / 4) - 1 + ((n : ℤ) / 4) + (j : ℤ)) = (j : ℤ) - 1 := by ring
    have hidx2 : (-((n : ℤ) / 4) + ((n : ℤ) / 4) + (j : ℤ)) = (j : ℤ) := by ring
    rw [hidx1, hidx2]
    set α₀ : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα₀
    set a := α₀ * binPMFInt n (1/2) ((j : ℤ) - 1) with ha_def
    set b := α₀ * binPMFInt n (1/2) (j : ℤ) with hb_def
    -- a = S_er (-(n/4)-1) j, b = S_er (-(n/4)) j; use existing S bounds via index rewrite.
    have ha_nn : 0 ≤ a := by
      rw [ha_def]; apply mul_nonneg (by rw [hα₀]; positivity) (hbpInt_nn _)
    have hab : a ≤ b := by
      rw [ha_def, hb_def]
      apply mul_le_mul_of_nonneg_left (hbinmono j hj1 hjn) (by rw [hα₀]; positivity)
    have hb_half : b ≤ 1/2 := by
      have := hSer_le_half (-((n : ℤ) / 4)) j
      have heq : S_er (-((n : ℤ) / 4)) j = b := by
        show α₀ * binPMFInt n (1/2) (-((n : ℤ) / 4) + ((n : ℤ) / 4) + (j : ℤ)) = b
        rw [hidx2]
      rw [heq] at this; exact this
    have h1a : (0:ℝ) < 1 - a := by linarith
    have h1b : (0:ℝ) < 1 - b := by linarith
    rw [div_le_div_iff₀ h1a h1b]
    nlinarith [ha_nn, hab, hb_half, mul_nonneg ha_nn (le_of_lt h1b)]
  -- Plain envelope row identity (analogue of the old hellFactor_eq, but on the PLAIN index j):
  -- for ℓ ⊆ Icc 1 (n/2), sameParity, ∏_{j∈ℓ} ellFactor n α s j = widetildeMu_er s ℓ / Zprime_er s.
  have hellFactor_eq : ∀ s, -((n : ℤ) / 4) ≤ s → s ≤ ((n : ℤ) / 4) →
      ∀ ℓ : Finset ℕ, ℓ ⊆ Finset.Icc 1 (n / 2) →
        Workspace.Types.AlternatingSumExpression.sameParity ℓ →
        (∏ j ∈ ℓ,
          Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j)
          = widetildeMu_er s ℓ / Zprime_er s := by
    intros s hs1 hs2 ℓ hℓ_sub hℓ_par
    have h_each : ∀ j,
        Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j
          = S_er s j / (1 - S_er s j) := by
      intro j
      unfold Workspace.Types.AlternatingSumExpression.ellFactor
      rfl
    have h_prod : (∏ j ∈ ℓ,
          Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j)
        = ∏ j ∈ ℓ, S_er s j / (1 - S_er s j) := by
      apply Finset.prod_congr rfl
      intros j _; exact h_each j
    rw [h_prod]
    exact hWI s hs1 hs2 ℓ hℓ_sub hℓ_par (fun j _ => hSer_lt_one s j)
  -- Abstract reindex + boundary-split lemma (proved generically over g).
  have hreduce_abstract : ∀ (g : ℤ → ℝ), (∀ s, 0 ≤ g s) →
      g (-((n : ℤ) / 4) - 1) ≤ g (-((n : ℤ) / 4)) →
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g (r - 1))
        ≤ g (-((n : ℤ) / 4)) + ∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g s := by
    intro g hg_nn hbdy
    set m : ℤ := (n : ℤ) / 4 with hm_def
    have hm_nn : (0 : ℤ) ≤ m := by rw [hm_def]; positivity
    have hreindex : (∑ r ∈ Finset.Icc (-m) m, g (r - 1))
        = ∑ s ∈ Finset.Icc (-m - 1) (m - 1), g s := by
      apply Finset.sum_nbij' (fun r => r - 1) (fun s => s + 1)
      · intro r hr; rw [Finset.mem_Icc] at hr ⊢; omega
      · intro s hs; rw [Finset.mem_Icc] at hs ⊢; omega
      · intro r hr; omega
      · intro s hs; omega
      · intro r hr; rfl
    rw [hreindex]
    have hins : Finset.Icc (-m - 1) (m - 1)
        = insert (-m - 1) (Finset.Icc (-m) (m - 1)) := by
      have h := Finset.insert_Icc_add_one_left_eq_Icc (a := -m - 1) (b := m - 1) (by omega)
      rw [show (-m - 1 + 1 : ℤ) = -m by ring] at h
      exact h.symm
    rw [hins]
    have hnotmem : (-m - 1) ∉ Finset.Icc (-m) (m - 1) := by
      rw [Finset.mem_Icc]; omega
    rw [Finset.sum_insert hnotmem]
    have hsub : Finset.Icc (-m) (m - 1) ⊆ Finset.Icc (-m) m := by
      intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    have hsumle : (∑ s ∈ Finset.Icc (-m) (m - 1), g s) ≤ ∑ s ∈ Finset.Icc (-m) m, g s :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hg_nn i)
    linarith [hbdy, hsumle]
  -- Per-ℓ reduction: envelopeW ℓ ≤ (boundary row at -(n/4)) + envPlain ℓ.
  have henv_reduce : ∀ ℓ : Finset ℕ, ℓ ⊆ Finset.Icc 1 (n / 2) →
      envelopeW ℓ ≤
        (∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j)
        + ∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
              ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j := by
    intro ℓ hℓ_sub
    -- write envelopeW ℓ as ∑_r g(r-1) with g s = ∏_{j∈ℓ} ellFactor n α s j.
    set g : ℤ → ℝ := fun s =>
      ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j with hg_def
    have henv_eq : envelopeW ℓ = ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g (r - 1) := by
      show (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1))
        = ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g (r - 1)
      apply Finset.sum_congr rfl
      intro r _
      rw [hg_def]
      apply Finset.prod_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := by
        have := hℓ_sub hj; rw [Finset.mem_Icc] at this; exact this.1
      exact ellFactor_shift r j hj1
    rw [henv_eq]
    have hg_nn : ∀ s, 0 ≤ g s := by
      intro s; rw [hg_def]
      apply Finset.prod_nonneg
      intro j _; exact hellFactor_nn s j
    have hbdy : g (-((n : ℤ) / 4) - 1) ≤ g (-((n : ℤ) / 4)) := by
      rw [hg_def]
      apply Finset.prod_le_prod
      · intro j _; exact hellFactor_nn _ j
      · intro j hj
        have hjmem := hℓ_sub hj; rw [Finset.mem_Icc] at hjmem
        exact hellmono j hjmem.1 hjmem.2
    exact hreduce_abstract g hg_nn hbdy
  -- Bound a single PLAIN row at fixed s by exp(√n/32)·widetildeMu_er s ℓ.
  have hrow_bound : ∀ s, -((n : ℤ) / 4) ≤ s → s ≤ ((n : ℤ) / 4) →
      ∀ ℓ : Finset ℕ, ℓ ⊆ Finset.Icc 1 (n / 2) →
        Workspace.Types.AlternatingSumExpression.sameParity ℓ →
        (∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j)
          ≤ Real.exp (Real.sqrt n / 32) * widetildeMu_er s ℓ := by
    intro s hs1 hs2 ℓ hℓ_sub hℓ_par
    rw [hellFactor_eq s hs1 hs2 ℓ hℓ_sub hℓ_par]
    rw [div_eq_mul_inv, mul_comm (Real.exp (Real.sqrt n / 32)) (widetildeMu_er s ℓ)]
    apply mul_le_mul_of_nonneg_left
    · exact hZ_inv_le_exp s hs1 hs2
    · exact hMu_nn s ℓ
  -- Properties extracted for ℓ ∈ P_L.
  have hPL_props : ∀ ℓ ∈ P_L, ℓ ⊆ Finset.Icc 1 (n / 2) ∧
      Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
      ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
        widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)) := by
    intro ℓ hℓPL
    have hℓPL' : ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))) := hℓPL
    simp only [Finset.mem_filter, Finset.mem_powerset] at hℓPL'
    exact ⟨hℓPL'.1, hℓPL'.2.1, hℓPL'.2.2⟩
  -- envPlain summed over P_L ≤ card·exp(-√n/32).
  -- Step: per ℓ, envPlain ℓ ≤ exp(√n/32)·∑_r widetildeMu_er r ℓ (sum the row bound over r).
  have henvPlain_le : ∀ ℓ ∈ P_L,
      (∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j)
        ≤ Real.exp (Real.sqrt n / 32) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), widetildeMu_er r ℓ) := by
    intro ℓ hℓPL
    obtain ⟨hℓ_sub, hℓ_par, _⟩ := hPL_props ℓ hℓPL
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact hrow_bound r hr.1 hr.2 ℓ hℓ_sub hℓ_par
  -- Boundary row summed over P_L ≤ exp(-√n/32).
  have hbdy_le : (∑ ℓ ∈ P_L,
        ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j)
      ≤ Real.exp (-(Real.sqrt n / 32)) := by
    have hr0_lb : -((n : ℤ) / 4) ≤ -((n : ℤ) / 4) := le_refl _
    have hr0_ub : -((n : ℤ) / 4) ≤ ((n : ℤ) / 4) := by
      have : (0 : ℤ) ≤ (n : ℤ) / 4 := by positivity
      linarith
    -- each boundary row ≤ exp(√n/32)·widetildeMu_er (-(n/4)) ℓ
    have hstep1 : (∑ ℓ ∈ P_L,
          ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j)
        ≤ ∑ ℓ ∈ P_L, Real.exp (Real.sqrt n / 32) * widetildeMu_er (-((n : ℤ) / 4)) ℓ := by
      apply Finset.sum_le_sum
      intro ℓ hℓPL
      obtain ⟨hℓ_sub, hℓ_par, _⟩ := hPL_props ℓ hℓPL
      exact hrow_bound (-((n : ℤ) / 4)) hr0_lb hr0_ub ℓ hℓ_sub hℓ_par
    have hstep2 : (∑ ℓ ∈ P_L, Real.exp (Real.sqrt n / 32) * widetildeMu_er (-((n : ℤ) / 4)) ℓ)
        = Real.exp (Real.sqrt n / 32) * (∑ ℓ ∈ P_L, widetildeMu_er (-((n : ℤ) / 4)) ℓ) := by
      rw [Finset.mul_sum]
    -- ∑_{ℓ∈P_L} widetildeMu_er (-(n/4)) ℓ ≤ exp(-√n/16)
    have hP_L_sub_rare : P_L ⊆ ((Finset.Icc 1 (n / 2)).powerset).filter
        (fun ℓ => widetildeMu_er (-((n : ℤ) / 4)) ℓ < Real.exp (-(Real.sqrt n / 2))) := by
      intro ℓ hℓPL
      obtain ⟨hℓ_sub, _, hcond⟩ := hPL_props ℓ hℓPL
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hℓ_sub, hcond (-((n : ℤ) / 4)) (Finset.mem_Icc.mpr ⟨hr0_lb, hr0_ub⟩)⟩
    have hRS_inst := hRS (-((n : ℤ) / 4)) hr0_lb hr0_ub
    have hsubsum : (∑ ℓ ∈ P_L, widetildeMu_er (-((n : ℤ) / 4)) ℓ)
        ≤ ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
              (fun ℓ => widetildeMu_er (-((n : ℤ) / 4)) ℓ < Real.exp (-(Real.sqrt n / 2))),
            widetildeMu_er (-((n : ℤ) / 4)) ℓ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hP_L_sub_rare
      intros ℓ _ _; exact hMu_nn (-((n : ℤ) / 4)) ℓ
    have hmu_sum_le : (∑ ℓ ∈ P_L, widetildeMu_er (-((n : ℤ) / 4)) ℓ) ≤ Real.exp (-(Real.sqrt n / 16)) :=
      hsubsum.trans hRS_inst
    have hexp32_nn : (0 : ℝ) ≤ Real.exp (Real.sqrt n / 32) := (Real.exp_pos _).le
    calc (∑ ℓ ∈ P_L,
          ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j)
        ≤ ∑ ℓ ∈ P_L, Real.exp (Real.sqrt n / 32) * widetildeMu_er (-((n : ℤ) / 4)) ℓ := hstep1
      _ = Real.exp (Real.sqrt n / 32) * (∑ ℓ ∈ P_L, widetildeMu_er (-((n : ℤ) / 4)) ℓ) := hstep2
      _ ≤ Real.exp (Real.sqrt n / 32) * Real.exp (-(Real.sqrt n / 16)) :=
          mul_le_mul_of_nonneg_left hmu_sum_le hexp32_nn
      _ = Real.exp (-(Real.sqrt n / 32)) := by
          rw [← Real.exp_add]; congr 1; ring
  -- envPlain summed over P_L ≤ card·exp(-√n/32).
  have hP_L_sub_rare2 : ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
      P_L ⊆ ((Finset.Icc 1 (n / 2)).powerset).filter
        (fun ℓ => widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))) := by
    intros r hr ℓ hℓPL
    obtain ⟨hℓ_sub, _, hcond⟩ := hPL_props ℓ hℓPL
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hℓ_sub, hcond r hr⟩
  have hRS_inner : ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
      (∑ ℓ ∈ P_L, widetildeMu_er r ℓ) ≤ Real.exp (-(Real.sqrt n / 16)) := by
    intros r hr
    rw [Finset.mem_Icc] at hr
    have hRS_inst := hRS r hr.1 hr.2
    have hsub := hP_L_sub_rare2 r (Finset.mem_Icc.mpr ⟨hr.1, hr.2⟩)
    have hsubsum : (∑ ℓ ∈ P_L, widetildeMu_er r ℓ)
        ≤ ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
              (fun ℓ => widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))),
            widetildeMu_er r ℓ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intros ℓ _ _; exact hMu_nn r ℓ
    exact hsubsum.trans hRS_inst
  have hcard_succ_le : (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card + 1 ≤ n := by
    rw [Int.card_Icc]
    have hn_lb : (8 : ℤ) ≤ (n : ℤ) := by
      have : (8 : ℕ) ≤ n := by
        have : (8 : ℕ) ≤ 10 ^ 12 := by norm_num
        exact this.trans hn
      exact_mod_cast this
    have hbnd_int : ((n : ℤ) / 4 + 1 - -((n : ℤ) / 4)).toNat + 1 ≤ n := by
      have h2nd4 : 2 * ((n : ℤ) / 4) + 1 ≤ (n : ℤ) - 4 := by omega
      have : (n : ℤ) / 4 + 1 - -((n : ℤ) / 4) ≤ (n : ℤ) - 1 := by omega
      have htoNat : ((n : ℤ) / 4 + 1 - -((n : ℤ) / 4)).toNat ≤ (n - 1 : ℕ) := by
        rw [Int.toNat_le]
        have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
        rw [this]; omega
      omega
    exact hbnd_int
  have hcard_succ_le_real : ((Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card : ℝ) + 1 ≤ (n : ℝ) := by
    have := hcard_succ_le
    have hcast : ((Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card : ℝ) + 1
        = (((Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]; exact_mod_cast this
  -- ∑_{ℓ∈P_L} envPlain ℓ ≤ card·exp(-√n/32).
  have henvPlain_sum : (∑ ℓ ∈ P_L,
        ∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j)
      ≤ (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card * Real.exp (-(Real.sqrt n / 32)) := by
    have hexp32_nn : (0 : ℝ) ≤ Real.exp (Real.sqrt n / 32) := (Real.exp_pos _).le
    calc (∑ ℓ ∈ P_L,
          ∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
              ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j)
        ≤ ∑ ℓ ∈ P_L, Real.exp (Real.sqrt n / 32) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), widetildeMu_er r ℓ) :=
          Finset.sum_le_sum henvPlain_le
      _ = Real.exp (Real.sqrt n / 32) *
            (∑ ℓ ∈ P_L, ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), widetildeMu_er r ℓ) := by
          rw [Finset.mul_sum]
      _ = Real.exp (Real.sqrt n / 32) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), ∑ ℓ ∈ P_L, widetildeMu_er r ℓ) := by
          rw [Finset.sum_comm]
      _ ≤ Real.exp (Real.sqrt n / 32) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), Real.exp (-(Real.sqrt n / 16))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r hr => hRS_inner r hr)) hexp32_nn
      _ = Real.exp (Real.sqrt n / 32) *
            ((Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card * Real.exp (-(Real.sqrt n / 16))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card * Real.exp (-(Real.sqrt n / 32)) := by
          rw [show Real.exp (Real.sqrt n / 32) *
                ((Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card * Real.exp (-(Real.sqrt n / 16)))
              = (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card *
                (Real.exp (Real.sqrt n / 32) * Real.exp (-(Real.sqrt n / 16))) by ring]
          rw [← Real.exp_add]
          congr 2
          ring
  -- Final assembly: ∑_ℓ envelopeW ≤ ∑_ℓ(boundary + envPlain) ≤ exp(-√n/32) + card·exp(-√n/32)
  --                = (card+1)·exp(-√n/32) ≤ n·exp(-√n/32).
  have hexp_neg_nn : (0 : ℝ) ≤ Real.exp (-(Real.sqrt n / 32)) := (Real.exp_pos _).le
  calc (∑ ℓ ∈ P_L, envelopeW ℓ)
      ≤ ∑ ℓ ∈ P_L,
          ((∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
              ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j)
            + ∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j) := by
        apply Finset.sum_le_sum
        intro ℓ hℓPL
        obtain ⟨hℓ_sub, _, _⟩ := hPL_props ℓ hℓPL
        exact henv_reduce ℓ hℓ_sub
    _ = (∑ ℓ ∈ P_L,
          ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (-((n : ℤ) / 4)) j)
        + (∑ ℓ ∈ P_L,
            ∑ s ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n
                ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) s j) := by
        rw [Finset.sum_add_distrib]
    _ ≤ Real.exp (-(Real.sqrt n / 32))
        + (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card * Real.exp (-(Real.sqrt n / 32)) :=
        add_le_add hbdy_le henvPlain_sum
    _ = (((Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)).card : ℝ) + 1) * Real.exp (-(Real.sqrt n / 32)) := by
        ring
    _ ≤ (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) :=
        mul_le_mul_of_nonneg_right hcard_succ_le_real hexp_neg_nn
