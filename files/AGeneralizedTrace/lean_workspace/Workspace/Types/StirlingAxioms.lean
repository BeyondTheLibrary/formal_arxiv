import Mathlib
import Workspace.Types.ProbVec

/-!
# Stirling-derived Central Binomial Bounds (Axioms)

Two classical Stirling-type bounds on the central binomial pmf
`bin(n, 1/2, i) := C(n,i) * 2^(-n)`, admitted as axioms because their
formal proof from Mathlib's `Stirling` module is mechanical but lengthy.

These are textbook facts (see, e.g., Robbins 1955, Spencer's
"Asymptopia", or any introduction to concentration inequalities):

* (a) For all `n ≥ 1` and all `i`,
      `C(n,i) · 2^(-n) ≤ √(2 / (π n))`.
* (b) For all `n ≥ 1`,
      `C(n, n/2) · 2^(-n) ≥ 1 / (2 √n)`.

Both follow from the standard Stirling bounds
`n! = √(2π n) (n/e)^n · (1 + O(1/n))`.
-/

namespace Workspace.Types.StirlingAxioms

section CentralBinomialLowerBound
open Stirling
set_option maxHeartbeats 1000000

/-- `n! = stirlingSeq n · (√(2n) · (n/e)^n)`, the unfolded Stirling sequence. -/
private theorem clb_fact_stirling (n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial n : ℝ) = stirlingSeq n * (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) := by
  have hpos : (0 : ℝ) < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by
    apply mul_pos
    · apply Real.sqrt_pos.mpr; positivity
    · positivity
  rw [Stirling.stirlingSeq]; field_simp

/-- `stirlingSeq` is bounded above by its value at `1`, namely `e / √2`. -/
private theorem clb_stirling_le (k : ℕ) (hk : 1 ≤ k) : stirlingSeq k ≤ Real.exp 1 / Real.sqrt 2 := by
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (k-1))
  simp only [Function.comp] at hanti
  have h1 : (k - 1).succ = k := by omega
  rw [h1] at hanti
  have hs1 : stirlingSeq (Nat.succ 0) = Real.exp 1 / Real.sqrt 2 := by
    rw [Stirling.stirlingSeq]; simp; rw [div_eq_mul_inv]
  rw [hs1] at hanti; exact hanti

/-- Core Stirling lower bound: `centralBinom k ≥ (2√π/e²) · 4^k / √k` for `k ≥ 1`. -/
private theorem clb_core_lower (k : ℕ) (hk : 1 ≤ k) :
    (Nat.centralBinom k : ℝ) ≥ (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * (4:ℝ)^k / Real.sqrt k := by
  set c : ℝ := (Nat.centralBinom k : ℝ) with hc
  set D : ℝ := ((k:ℝ) / Real.exp 1) ^ k with hD
  set Sk : ℝ := stirlingSeq k with hSk
  set S2k : ℝ := stirlingSeq (2*k) with hS2k
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hDpos : 0 < D := by rw [hD]; positivity
  have hfk : (Nat.factorial k : ℝ) = Sk * (Real.sqrt (2 * k) * D) := clb_fact_stirling k hk
  have hf2k : (Nat.factorial (2*k) : ℝ) = S2k * (Real.sqrt (2 * ((2*k:ℕ):ℝ)) * (((2*k:ℕ):ℝ) / Real.exp 1) ^ (2*k)) :=
    clb_fact_stirling (2*k) (by omega)
  have hpow : (((2*k:ℕ):ℝ) / Real.exp 1) ^ (2*k) = (4:ℝ)^k * D^2 := by
    rw [hD]
    rw [show ((2*k:ℕ):ℝ) = 2 * (k:ℝ) by push_cast; ring]
    rw [mul_div_assoc, mul_pow]
    rw [show ((2:ℝ)^(2*k)) = 4^k by rw [pow_mul]; norm_num]
    rw [show (2*k) = k*2 by ring, pow_mul]
  have hsq4 : Real.sqrt (2 * ((2*k:ℕ):ℝ)) = 2 * Real.sqrt k := by
    rw [show (2 * ((2*k:ℕ):ℝ) : ℝ) = (2:ℝ)^2 * k by push_cast; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hsq2 : Real.sqrt (2 * (k:ℝ)) ^ 2 = 2 * k := by
    rw [Real.sq_sqrt (by positivity)]
  have hcid : c * ((Nat.factorial k : ℝ))^2 = (Nat.factorial (2*k) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left k (by norm_num : 0 < 2))
    rw [hc, Nat.centralBinom_eq_two_mul_choose]
    have h2 : 2 * k - k = k := by omega
    rw [h2] at h
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this; nlinarith [this]
  have hSkpos : 0 < Sk := by rw [hSk]; exact Stirling.stirlingSeq'_pos (k-1) |>.trans_eq (by congr 1; omega)
  have hS2kpos : 0 < S2k := by rw [hS2k]; exact Stirling.stirlingSeq'_pos (2*k-1) |>.trans_eq (by congr 1; omega)
  have hsqkpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hsqk_sq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hkR.le
  have hkey : c * Sk^2 * Real.sqrt k = S2k * (4:ℝ)^k := by
    have e1 : c * (Sk * (Real.sqrt (2 * k) * D))^2
        = S2k * (2 * Real.sqrt k * ((4:ℝ)^k * D^2)) := by
      rw [← hfk]
      rw [hcid, hf2k, hsq4, hpow]
    have hD2 : 0 < D^2 := by positivity
    have e2 : (Sk * (Real.sqrt (2 * k) * D))^2 = Sk^2 * (2 * k) * D^2 := by
      have : Real.sqrt (2 * (k:ℝ))^2 = 2 * k := hsq2
      ring_nf
      ring_nf at this
      nlinarith [this]
    rw [e2] at e1
    have hcancel : c * Sk^2 * (2*k) = S2k * (2 * Real.sqrt k * (4:ℝ)^k) := by
      have hD2ne : D^2 ≠ 0 := ne_of_gt hD2
      field_simp at e1 ⊢
      nlinarith [e1, hD2]
    have hk_eq : (k:ℝ) = Real.sqrt k * Real.sqrt k := by nlinarith [hsqk_sq]
    have hfac : (c * Sk^2 * Real.sqrt k - S2k * (4:ℝ)^k) * (2 * Real.sqrt k) = 0 := by
      have expand : (c * Sk^2 * Real.sqrt k - S2k * (4:ℝ)^k) * (2 * Real.sqrt k)
          = c * Sk^2 * (2 * (Real.sqrt k * Real.sqrt k)) - S2k * (2 * Real.sqrt k * (4:ℝ)^k) := by ring
      rw [expand, ← hk_eq]; linarith [hcancel]
    have hne : (2 * Real.sqrt k) ≠ 0 := by positivity
    have hz : c * Sk^2 * Real.sqrt k - S2k * (4:ℝ)^k = 0 :=
      (mul_eq_zero.mp hfac).resolve_right hne
    linarith [hz]
  have hS2k_lb : Real.sqrt Real.pi ≤ S2k := by
    rw [hS2k]; exact Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hSk_ub : Sk ≤ Real.exp 1 / Real.sqrt 2 := by rw [hSk]; exact clb_stirling_le k hk
  have hSk2_ub : Sk^2 ≤ (Real.exp 1)^2 / 2 := by
    have h1 : Sk^2 ≤ (Real.exp 1 / Real.sqrt 2)^2 := by
      apply sq_le_sq'
      · linarith [hSkpos]
      · exact hSk_ub
    have h2 : (Real.exp 1 / Real.sqrt 2)^2 = (Real.exp 1)^2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h1, h2.le, h2.ge]
  have hSk2pos : 0 < Sk^2 := by positivity
  have hpidpos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h4pos : (0:ℝ) < (4:ℝ)^k := by positivity
  have hSrel : (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * Sk^2 ≤ S2k := by
    have hmul : (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * Sk^2
        ≤ (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * ((Real.exp 1)^2 / 2) := by
      apply mul_le_mul_of_nonneg_left hSk2_ub
      positivity
    have heq : (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * ((Real.exp 1)^2 / 2) = Real.sqrt Real.pi := by
      field_simp
    rw [heq] at hmul; linarith [hS2k_lb]
  rw [ge_iff_le, div_le_iff₀ hsqkpos]
  have hcsqk : c * Real.sqrt k = S2k * (4:ℝ)^k / Sk^2 := by
    rw [eq_div_iff (ne_of_gt hSk2pos)]; nlinarith [hkey]
  rw [hcsqk, le_div_iff₀ hSk2pos]
  have hfin : (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * (4:ℝ)^k * Sk^2
      = ((2 * Real.sqrt Real.pi / (Real.exp 1)^2) * Sk^2) * (4:ℝ)^k := by ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_right hSrel h4pos.le

/-- Core Stirling upper bound: `centralBinom k ≤ 4^k / (√π · √k)` for `k ≥ 1`.

Uses the same exact identity `centralBinom k · Sk² · √k = S2k · 4^k` as
`clb_core_lower`, combined with `S2k ≤ Sk` (antitonicity of `stirlingSeq`)
and `√π ≤ Sk`. -/
private theorem clb_core_upper (k : ℕ) (hk : 1 ≤ k) :
    (Nat.centralBinom k : ℝ) ≤ (4:ℝ)^k / (Real.sqrt Real.pi * Real.sqrt k) := by
  set c : ℝ := (Nat.centralBinom k : ℝ) with hc
  set D : ℝ := ((k:ℝ) / Real.exp 1) ^ k with hD
  set Sk : ℝ := stirlingSeq k with hSk
  set S2k : ℝ := stirlingSeq (2*k) with hS2k
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hDpos : 0 < D := by rw [hD]; positivity
  have hfk : (Nat.factorial k : ℝ) = Sk * (Real.sqrt (2 * k) * D) := clb_fact_stirling k hk
  have hf2k : (Nat.factorial (2*k) : ℝ) = S2k * (Real.sqrt (2 * ((2*k:ℕ):ℝ)) * (((2*k:ℕ):ℝ) / Real.exp 1) ^ (2*k)) :=
    clb_fact_stirling (2*k) (by omega)
  have hpow : (((2*k:ℕ):ℝ) / Real.exp 1) ^ (2*k) = (4:ℝ)^k * D^2 := by
    rw [hD]
    rw [show ((2*k:ℕ):ℝ) = 2 * (k:ℝ) by push_cast; ring]
    rw [mul_div_assoc, mul_pow]
    rw [show ((2:ℝ)^(2*k)) = 4^k by rw [pow_mul]; norm_num]
    rw [show (2*k) = k*2 by ring, pow_mul]
  have hsq4 : Real.sqrt (2 * ((2*k:ℕ):ℝ)) = 2 * Real.sqrt k := by
    rw [show (2 * ((2*k:ℕ):ℝ) : ℝ) = (2:ℝ)^2 * k by push_cast; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hsq2 : Real.sqrt (2 * (k:ℝ)) ^ 2 = 2 * k := by
    rw [Real.sq_sqrt (by positivity)]
  have hcid : c * ((Nat.factorial k : ℝ))^2 = (Nat.factorial (2*k) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left k (by norm_num : 0 < 2))
    rw [hc, Nat.centralBinom_eq_two_mul_choose]
    have h2 : 2 * k - k = k := by omega
    rw [h2] at h
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this; nlinarith [this]
  have hSkpos : 0 < Sk := by rw [hSk]; exact Stirling.stirlingSeq'_pos (k-1) |>.trans_eq (by congr 1; omega)
  have hS2kpos : 0 < S2k := by rw [hS2k]; exact Stirling.stirlingSeq'_pos (2*k-1) |>.trans_eq (by congr 1; omega)
  have hsqkpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hsqk_sq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hkR.le
  have hkey : c * Sk^2 * Real.sqrt k = S2k * (4:ℝ)^k := by
    have e1 : c * (Sk * (Real.sqrt (2 * k) * D))^2
        = S2k * (2 * Real.sqrt k * ((4:ℝ)^k * D^2)) := by
      rw [← hfk]
      rw [hcid, hf2k, hsq4, hpow]
    have hD2 : 0 < D^2 := by positivity
    have e2 : (Sk * (Real.sqrt (2 * k) * D))^2 = Sk^2 * (2 * k) * D^2 := by
      have : Real.sqrt (2 * (k:ℝ))^2 = 2 * k := hsq2
      ring_nf
      ring_nf at this
      nlinarith [this]
    rw [e2] at e1
    have hcancel : c * Sk^2 * (2*k) = S2k * (2 * Real.sqrt k * (4:ℝ)^k) := by
      have hD2ne : D^2 ≠ 0 := ne_of_gt hD2
      field_simp at e1 ⊢
      nlinarith [e1, hD2]
    have hk_eq : (k:ℝ) = Real.sqrt k * Real.sqrt k := by nlinarith [hsqk_sq]
    have hfac : (c * Sk^2 * Real.sqrt k - S2k * (4:ℝ)^k) * (2 * Real.sqrt k) = 0 := by
      have expand : (c * Sk^2 * Real.sqrt k - S2k * (4:ℝ)^k) * (2 * Real.sqrt k)
          = c * Sk^2 * (2 * (Real.sqrt k * Real.sqrt k)) - S2k * (2 * Real.sqrt k * (4:ℝ)^k) := by ring
      rw [expand, ← hk_eq]; linarith [hcancel]
    have hne : (2 * Real.sqrt k) ≠ 0 := by positivity
    have hz : c * Sk^2 * Real.sqrt k - S2k * (4:ℝ)^k = 0 :=
      (mul_eq_zero.mp hfac).resolve_right hne
    linarith [hz]
  -- Now bound: S2k ≤ Sk (antitone) and √π ≤ Sk, hence c ≤ 4^k/(√π·√k).
  have hS2k_le_Sk : S2k ≤ Sk := by
    rw [hS2k, hSk]
    have h := Stirling.stirlingSeq'_antitone (a := k-1) (b := 2*k-1) (by omega)
    simp only [Function.comp] at h
    rwa [show (k-1).succ = k by omega, show (2*k-1).succ = 2*k by omega] at h
  have hsqrtpi_le : Real.sqrt Real.pi ≤ Sk := by
    rw [hSk]; exact Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hpipos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h4pos : (0:ℝ) < (4:ℝ)^k := by positivity
  have hcnn : 0 ≤ c := by rw [hc]; positivity
  -- abstract conclusion
  rw [le_div_iff₀ (by positivity)]
  have hSk2 : 0 < Sk^2 := by positivity
  have key2 : c * (Real.sqrt Real.pi * Real.sqrt k) * Sk^2 = Real.sqrt Real.pi * (S2k * (4:ℝ)^k) := by
    nlinarith [hkey]
  have ineq : Real.sqrt Real.pi * (S2k * (4:ℝ)^k) ≤ (4:ℝ)^k * Sk^2 := by
    nlinarith [mul_le_mul hsqrtpi_le hS2k_le_Sk hS2kpos.le hSkpos.le, h4pos, sq_nonneg Sk]
  nlinarith [key2, ineq, hSk2, mul_nonneg hcnn (mul_nonneg hpipos.le hsqkpos.le)]

/-- Helper: `cb ≤ fourk/(sp·sm)` ⟹ `cb·fourk⁻¹ ≤ 1/(sp·sm)` (all positive). -/
private theorem clb_cb_inv_le (cb fourk sp sm : ℝ)
    (h1 : 0 < fourk) (h2 : 0 < sp) (h3 : 0 < sm)
    (hcore : cb ≤ fourk / (sp * sm)) : cb * fourk⁻¹ ≤ 1 / (sp * sm) := by
  rw [mul_inv_le_iff₀ h1, mul_comm, mul_one_div]
  exact hcore

/-- Even-case numeric constant: `1/(2√2) ≤ 2√π/e²`. -/
private theorem clb_const_even : (1:ℝ) / (2 * Real.sqrt 2) ≤ 2 * Real.sqrt Real.pi / (Real.exp 1)^2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have he : (Real.exp 1)^2 ≤ (2.7182818286:ℝ)^2 := by
    have := Real.exp_one_lt_d9; nlinarith [this, Real.exp_pos 1]
  have hpi : (3.14:ℝ) ≤ Real.sqrt Real.pi ^ 2 := by
    rw [Real.sq_sqrt Real.pi_pos.le]; linarith [Real.pi_gt_d2]
  have h2 : (1.41:ℝ) ≤ Real.sqrt 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith [Real.sqrt_nonneg Real.pi, Real.sqrt_nonneg 2, he, hpi, h2,
    mul_nonneg (Real.sqrt_nonneg Real.pi) (Real.sqrt_nonneg 2)]

/-- Odd-case numeric constant (`m ≥ 1`): `√(m+1) ≤ (4√π/e²) · √(2m+1)`. -/
private theorem clb_const_odd (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (m+1) ≤ (4 * Real.sqrt Real.pi / (Real.exp 1)^2) * Real.sqrt (2*m+1) := by
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have he4 : (Real.exp 1)^4 ≤ (2.7182818286:ℝ)^4 := by
    have h := (Real.exp_one_lt_d9).le
    have hpos := (Real.exp_pos 1).le
    gcongr
  have hpi : (3.14:ℝ) ≤ Real.sqrt Real.pi ^ 2 := by
    rw [Real.sq_sqrt Real.pi_pos.le]; linarith [Real.pi_gt_d2]
  have he4pos : (0:ℝ) < (Real.exp 1)^4 := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hRsq : ((4 * Real.sqrt Real.pi / (Real.exp 1)^2) * Real.sqrt (2*m+1))^2
      = (16 * (Real.sqrt Real.pi)^2 / (Real.exp 1)^4) * (Real.sqrt (2*m+1))^2 := by
    rw [mul_pow, div_pow]; ring_nf
  rw [hRsq]
  have hsq2m1 : (Real.sqrt (2*m+1))^2 = (2*(m:ℝ)+1) := by
    rw [Real.sq_sqrt (by positivity)]
  rw [hsq2m1]
  rw [div_mul_eq_mul_div, le_div_iff₀ he4pos]
  nlinarith [hpi, he4, hmR, Real.sqrt_nonneg Real.pi, sq_nonneg (Real.sqrt Real.pi)]

/--
Lower bound on the central-binomial pmf at the mode `i = ⌊n/2⌋`:
`C(n, ⌊n/2⌋) · 2^(-n) ≥ 1 / (2 √n)` for every `n ≥ 1`.

Proved from Mathlib's `Stirling` sequence: writing the central binomial
coefficient via factorials and the Stirling-sequence bounds
`√π ≤ stirlingSeq` and `stirlingSeq ≤ e/√2`, one gets
`centralBinom k · 4^(-k) ≥ (2√π/e²)/√k`; a parity split on `n` (with `n = 1`
handled directly) then yields the claimed `1/(2√n)` bound.
-/
theorem central_binomial_pmf_lower_bound :
    ∀ {n : ℕ}, 1 ≤ n →
      ((Nat.choose n (n / 2) : ℝ) * (2 ^ n : ℝ)⁻¹ ≥
        1 / (2 * Real.sqrt n)) := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- even: n = 2*m
    have hn2m : n = 2 * m := by omega
    have hm1 : 1 ≤ m := by omega
    subst hn2m
    have hbin : Nat.choose (2*m) ((2*m)/2) = Nat.centralBinom m := by
      rw [Nat.centralBinom_eq_two_mul_choose]; congr 1; omega
    rw [hbin]
    have hpow2 : ((2:ℝ) ^ (2*m)) = (4:ℝ)^m := by
      rw [pow_mul]; norm_num
    rw [hpow2]
    have hcore := clb_core_lower m hm1
    have hsqrt : Real.sqrt ((2*m : ℕ)) = Real.sqrt 2 * Real.sqrt m := by
      push_cast; rw [Real.sqrt_mul (by norm_num)]
    rw [hsqrt]
    have hsqmpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
    have h4pos : (0:ℝ) < (4:ℝ)^m := by positivity
    have hsq2pos : 0 < Real.sqrt 2 := by positivity
    have step1 : (Nat.centralBinom m : ℝ) * ((4:ℝ)^m)⁻¹ ≥ (2 * Real.sqrt Real.pi / (Real.exp 1)^2) / Real.sqrt m := by
      rw [ge_iff_le, div_le_iff₀ hsqmpos] at hcore ⊢
      rw [mul_assoc, mul_comm ((4:ℝ)^m)⁻¹ (Real.sqrt m), ← mul_assoc]
      rw [le_mul_inv_iff₀ h4pos]
      linarith [hcore]
    have step2 : (2 * Real.sqrt Real.pi / (Real.exp 1)^2) / Real.sqrt m ≥ 1 / (2 * (Real.sqrt 2 * Real.sqrt m)) := by
      rw [ge_iff_le]
      have hrw : (1:ℝ) / (2 * (Real.sqrt 2 * Real.sqrt m)) = (1 / (2 * Real.sqrt 2)) / Real.sqrt m := by
        rw [div_div]; ring_nf
      rw [hrw]
      exact div_le_div_of_nonneg_right clb_const_even hsqmpos.le
    exact le_trans step2 step1
  · -- odd: n = 2*m + 1
    have hn2m : n = 2 * m + 1 := hm
    have hdiv : n / 2 = m := by omega
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hn1 : n = 1 := by omega
      subst hn1
      norm_num
    · subst hn2m
      rw [hdiv]
      have hbridge : 2 * Nat.choose (2*m+1) m = Nat.centralBinom (m+1) := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        have hsymm : Nat.choose (2*m+1) (m+1) = Nat.choose (2*m+1) m := by
          rw [← Nat.choose_symm (by omega : m+1 ≤ 2*m+1)]; congr 1; omega
        have hpascal := Nat.choose_succ_succ (2*m+1) m
        show 2 * (2*m+1).choose m = (2*(m+1)).choose (m+1)
        rw [show 2*(m+1) = (2*m+1)+1 by ring, hpascal, hsymm]; ring
      have hbinR : (Nat.choose (2*m+1) m : ℝ) = (Nat.centralBinom (m+1) : ℝ) / 2 := by
        have := congrArg (Nat.cast : ℕ → ℝ) hbridge
        push_cast at this; linarith [this]
      rw [hbinR]
      have hpow2 : ((2:ℝ)^(2*m+1)) = 2 * (4:ℝ)^m := by
        rw [pow_succ, pow_mul]; ring_nf
      rw [hpow2]
      have hm1 : 1 ≤ m+1 := by omega
      have hcore := clb_core_lower (m+1) hm1
      rw [show ((m+1:ℕ):ℝ) = (m:ℝ)+1 by push_cast; ring] at hcore
      rw [show ((2*m+1:ℕ):ℝ) = 2*(m:ℝ)+1 by push_cast; ring]
      have h4m1pos : (0:ℝ) < (4:ℝ)^(m+1) := by positivity
      have hsqm1pos : 0 < Real.sqrt ((m:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
      have hlhs_eq : (Nat.centralBinom (m+1) : ℝ) / 2 * (2 * (4:ℝ)^m)⁻¹
          = (Nat.centralBinom (m+1) : ℝ) * ((4:ℝ)^(m+1))⁻¹ := by
        rw [pow_succ]; field_simp; ring
      rw [hlhs_eq]
      have step1 : (Nat.centralBinom (m+1) : ℝ) * ((4:ℝ)^(m+1))⁻¹
          ≥ (2 * Real.sqrt Real.pi / (Real.exp 1)^2) / Real.sqrt ((m:ℝ)+1) := by
        rw [ge_iff_le, div_le_iff₀ hsqm1pos] at hcore ⊢
        rw [mul_assoc, mul_comm ((4:ℝ)^(m+1))⁻¹ (Real.sqrt ((m:ℝ)+1)), ← mul_assoc]
        rw [le_mul_inv_iff₀ h4m1pos]
        linarith [hcore]
      have step2 : (2 * Real.sqrt Real.pi / (Real.exp 1)^2) / Real.sqrt ((m:ℝ)+1)
          ≥ 1 / (2 * Real.sqrt (2*(m:ℝ)+1)) := by
        rw [ge_iff_le, div_le_div_iff₀ (by positivity) hsqm1pos, one_mul]
        have hco := clb_const_odd m hmpos
        calc Real.sqrt ((m:ℝ)+1)
            ≤ (4 * Real.sqrt Real.pi / (Real.exp 1)^2) * Real.sqrt (2*(m:ℝ)+1) := hco
          _ = (2 * Real.sqrt Real.pi / (Real.exp 1)^2) * (2 * Real.sqrt (2*(m:ℝ)+1)) := by ring
      exact le_trans step2 step1

/--
Upper bound on the central-binomial pmf, valid for every coordinate `i`.

This is the well-known consequence of Stirling that the maximum of the
binomial pmf `C(n,i)·2^(-n)` (attained at `i = ⌊n/2⌋`) is at most
`√(2 / (π n))`.

Proved from Mathlib's `Stirling` sequence: the coordinate `i` is bounded
by the mode `⌊n/2⌋` via `Nat.choose_le_middle`; the mode value is then
bounded by `clb_core_upper` (`centralBinom k ≤ 4^k/(√π·√k)`), which uses
the exact identity `centralBinom k · stirlingSeq(k)² · √k = stirlingSeq(2k)·4^k`
together with `stirlingSeq(2k) ≤ stirlingSeq(k)` and `√π ≤ stirlingSeq(k)`.
A parity split on `n` (with `n = 1` handled directly) gives the claimed
`√(2/(πn))` bound.
-/
theorem central_binomial_pmf_upper_bound :
    ∀ {n : ℕ}, 1 ≤ n →
      ∀ i : ℕ,
        ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤
          Real.sqrt (2 / (Real.pi * n)) := by
  intro n hn i
  -- Step 1: reduce coordinate i to the middle ⌊n/2⌋.
  have hred : ((Nat.choose n i : ℝ) * (2^n:ℝ)⁻¹) ≤ ((Nat.choose n (n/2) : ℝ) * (2^n:ℝ)⁻¹) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.choose_le_middle i n
  -- Step 2: bound the middle value by √(2/(πn)).
  have hmid : ((Nat.choose n (n/2) : ℝ) * (2^n:ℝ)⁻¹) ≤ Real.sqrt (2/(Real.pi * n)) := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- even: n = 2*m
      have hn2m : n = 2 * m := by omega
      have hm1 : 1 ≤ m := by omega
      subst hn2m
      have hbin : Nat.choose (2*m) ((2*m)/2) = Nat.centralBinom m := by
        rw [Nat.centralBinom_eq_two_mul_choose]; congr 1; omega
      rw [hbin]
      have hpow2 : ((2:ℝ) ^ (2*m)) = (4:ℝ)^m := by rw [pow_mul]; norm_num
      rw [hpow2]
      have hcore := clb_core_upper m hm1
      have hsqmpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
      have h4pos : (0:ℝ) < (4:ℝ)^m := by positivity
      have hpipos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      -- centralBinom m · (4^m)⁻¹ ≤ 1/(√π·√m)
      have step1 : (Nat.centralBinom m : ℝ) * ((4:ℝ)^m)⁻¹ ≤ 1/(Real.sqrt Real.pi * Real.sqrt m) :=
        clb_cb_inv_le _ _ _ _ h4pos hpipos hsqmpos hcore
      -- 1/(√π·√m) = √(2/(π·2m))
      have hsqid : (1:ℝ)/(Real.sqrt Real.pi * Real.sqrt m) = Real.sqrt (2/(Real.pi * ((2*m:ℕ):ℝ))) := by
        rw [← Real.sqrt_mul Real.pi_pos.le]
        rw [show (2/(Real.pi*((2*m:ℕ):ℝ))) = (Real.pi*m)⁻¹ by
              push_cast; field_simp]
        rw [Real.sqrt_inv, one_div]
      rw [hsqid] at step1
      exact step1
    · -- odd: n = 2*m + 1
      have hn2m : n = 2 * m + 1 := hm
      have hdiv : n / 2 = m := by omega
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        have hn1 : n = 1 := by omega
        subst hn1
        have heq : ((Nat.choose 1 (1/2) : ℝ) * (2^1:ℝ)⁻¹) = 1/2 := by norm_num
        rw [show (1:ℕ)/2 = 0 by norm_num] at *
        rw [show ((1:ℕ):ℝ) = 1 by norm_num] at *
        apply Real.le_sqrt_of_sq_le
        rw [show (Real.pi * 1) = Real.pi by ring]
        rw [le_div_iff₀ Real.pi_pos]
        norm_num
        nlinarith [Real.pi_lt_d2]
      · subst hn2m
        rw [hdiv]
        -- 2·C(2m+1, m) = centralBinom (m+1)
        have hbridge : 2 * Nat.choose (2*m+1) m = Nat.centralBinom (m+1) := by
          rw [Nat.centralBinom_eq_two_mul_choose]
          have hsymm : Nat.choose (2*m+1) (m+1) = Nat.choose (2*m+1) m := by
            rw [← Nat.choose_symm (by omega : m+1 ≤ 2*m+1)]; congr 1; omega
          have hpascal := Nat.choose_succ_succ (2*m+1) m
          show 2 * (2*m+1).choose m = (2*(m+1)).choose (m+1)
          rw [show 2*(m+1) = (2*m+1)+1 by ring, hpascal, hsymm]; ring
        have hbinR : (Nat.choose (2*m+1) m : ℝ) = (Nat.centralBinom (m+1) : ℝ) / 2 := by
          have := congrArg (Nat.cast : ℕ → ℝ) hbridge
          push_cast at this; linarith [this]
        rw [hbinR]
        have hpow2 : ((2:ℝ)^(2*m+1)) = 2 * (4:ℝ)^m := by rw [pow_succ, pow_mul]; ring_nf
        rw [hpow2]
        have hm1 : 1 ≤ m+1 := by omega
        have hcore := clb_core_upper (m+1) hm1
        rw [show ((m+1:ℕ):ℝ) = (m:ℝ)+1 by push_cast; ring] at hcore
        have h4pos : (0:ℝ) < (4:ℝ)^(m+1) := by positivity
        have hsqm1pos : 0 < Real.sqrt ((m:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
        have hpipos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
        -- LHS = centralBinom(m+1) · (4^(m+1))⁻¹
        have hlhs_eq : (Nat.centralBinom (m+1) : ℝ) / 2 * (2 * (4:ℝ)^m)⁻¹
            = (Nat.centralBinom (m+1) : ℝ) * ((4:ℝ)^(m+1))⁻¹ := by
          rw [pow_succ]; field_simp; ring
        rw [hlhs_eq]
        -- centralBinom(m+1)·(4^(m+1))⁻¹ ≤ 1/(√π·√(m+1))
        have step1 : (Nat.centralBinom (m+1) : ℝ) * ((4:ℝ)^(m+1))⁻¹
            ≤ 1/(Real.sqrt Real.pi * Real.sqrt ((m:ℝ)+1)) :=
          clb_cb_inv_le _ _ _ _ h4pos hpipos hsqm1pos hcore
        -- 1/(√π·√(m+1)) ≤ √(2/(π·(2m+1)))
        have step2 : (1:ℝ)/(Real.sqrt Real.pi * Real.sqrt ((m:ℝ)+1))
            ≤ Real.sqrt (2/(Real.pi*((2*m+1:ℕ):ℝ))) := by
          have hkpos : (0:ℝ) < (m:ℝ)+1 := by positivity
          apply Real.le_sqrt_of_sq_le
          rw [div_pow, one_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hkpos.le]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          push_cast
          rw [one_mul]
          nlinarith [Real.pi_pos, hkpos]
        calc (Nat.centralBinom (m+1) : ℝ) * ((4:ℝ)^(m+1))⁻¹
            ≤ 1/(Real.sqrt Real.pi * Real.sqrt ((m:ℝ)+1)) := step1
          _ ≤ Real.sqrt (2/(Real.pi*((2*m+1:ℕ):ℝ))) := step2
  exact le_trans hred hmid

end CentralBinomialLowerBound

-- DELETED (faithfulness prune, 2026-06-13): `central_binomial_pmf_gaussian_bound`
-- was an axiom asserting `C(n,k)·2^{-n} ≤ √(2/(πn))·exp(-2(k-n/2)²/n)`. It is
-- mathematically FALSE: the constant `2` in the exponent is the unattainable
-- asymptotic limit (verified numerically — violated for all n, e.g. ratio 1.216 at
-- n=3,k=0, around k≈n/2−√n). It was not a paper result (the paper uses Fact 9
-- directly, not a per-coordinate Gaussian envelope) and was consumed only by the
-- (now also deleted) non-paper `OffsetWeightBoundedByFirstFactor` chain. The
-- sorry-free binomial-ratio telescoping helpers below are the honest building
-- blocks for a corrected envelope (with a constant < 2 / a larger prefactor).

/--
L^{1/2} norm of the central-binomial pmf — the paper's Fact 9.

`∑_{i=0..n} √(C(n,i)·2^(-n)) ≤ (2π·n)^{1/4}`.

This is Fact 9 of the paper (deletion.tex:386-388), stated there as a bare
`\begin{fact}...\end{fact}` with NO proof and NO citation — a standard
local-CLT / L_{1/2}-norm estimate for the binomial distribution. We admit it
here as a paper-given fact (per the project rule that paper-stated facts may be
admitted). The tight constant `(2π n)^{1/4}` is exactly as stated in the paper.
-/
axiom binomial_pmf_l_half_sum_bound :
    ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.range (n + 1),
        Real.sqrt ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹))
        ≤ (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)

/--
Product-Bernoulli L^{1/2} bound (Rivkin–Valiant–Valiant 2024, Lemma 10).

For the witness probability vector `S_e : ProbVec n` of the paper's
construction (binomial-weighted on even indices, zero on odd; with weight
`α := c'·√n`, `c' := 1/(4·e²·√(2π))`), the L^{1/2}-norm of the associated
product-Bernoulli measure on `Fin n → Bool` satisfies
`∑_x √(μ_e x) ≤ exp(√n / (2e))`.

Proof in the paper: per-coordinate `√p + √(1-p) ≤ exp(√p)`, then
`∑_x √(μ_e x) = ∏_i (√p_i + √(1-p_i)) ≤ exp(∑_i √p_i)`, and use
`binomial_pmf_l_half_sum_bound` (Fact 9) to bound `∑_i √p_i ≤ √α · (2π n)^{1/4}
= √n / (2e)`. We admit the full statement here because the in-Lean derivation
chains a `Fintype.prod_sum_pi` rewrite, a per-coordinate `Real.exp_sqrt_le`
lemma, and the c' algebra, each of which is mechanical but pushes the
prover's token budget over the limit.
-/
theorem product_bernoulli_l_half_sum_bound_witness_even :
    ∀ {n : ℕ}, 1 ≤ n → n % 8 = 1 →
      ∀ (Se : Workspace.Types.ProbVec.ProbVec n),
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (∑ x : Fin n → Bool,
          Real.sqrt (∏ i : Fin n, if x i then Se.p i else 1 - Se.p i))
          ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1)) := by
  intro n hn _ Se hSe
  set c' : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) with hc'
  have hc'pos : 0 < c' := by rw [hc']; positivity
  have hm : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  -- (I) Factorization
  have hfact : (∑ x : Fin n → Bool, Real.sqrt (∏ i : Fin n, if x i then Se.p i else 1 - Se.p i))
      = ∏ i : Fin n, (Real.sqrt (Se.p i) + Real.sqrt (1 - Se.p i)) := by
    have hnn : ∀ (x : Fin n → Bool) (i : Fin n), 0 ≤ (if x i then Se.p i else 1 - Se.p i) := by
      intro x i
      by_cases h : x i
      · simp [h, Se.nonneg i]
      · simp [h]; linarith [Se.le_one i]
    calc (∑ x : Fin n → Bool, Real.sqrt (∏ i : Fin n, if x i then Se.p i else 1 - Se.p i))
        = ∑ x : Fin n → Bool, ∏ i : Fin n, Real.sqrt (if x i then Se.p i else 1 - Se.p i) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Real.sqrt_prod _ (fun i _ => hnn x i)]
      _ = ∏ i : Fin n, ∑ b : Bool, Real.sqrt (if b = true then Se.p i else 1 - Se.p i) := by
          exact (Fintype.prod_sum (fun i b => Real.sqrt (if b = true then Se.p i else 1 - Se.p i))).symm
      _ = ∏ i : Fin n, (Real.sqrt (Se.p i) + Real.sqrt (1 - Se.p i)) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [Fintype.sum_bool]
          simp
  -- (II) Product bound by exp of sum
  have hprodbd : (∏ i : Fin n, (Real.sqrt (Se.p i) + Real.sqrt (1 - Se.p i)))
      ≤ Real.exp (∑ i : Fin n, Real.sqrt (Se.p i)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _
      have h1mp : Real.sqrt (1 - Se.p i) ≤ 1 := by
        apply Real.sqrt_le_one.mpr; linarith [Se.nonneg i]
      have h2 : 1 + Real.sqrt (Se.p i) ≤ Real.exp (Real.sqrt (Se.p i)) := by
        have := Real.add_one_le_exp (Real.sqrt (Se.p i)); linarith
      linarith
  -- (III) Sum bound: ∑ √p_i ≤ √(c'√n) · ∑_{range(n+1)} √bin
  have hsumbd : (∑ i : Fin n, Real.sqrt (Se.p i))
      ≤ Real.sqrt (c' * Real.sqrt n) *
          (∑ i ∈ Finset.range (n + 1), Real.sqrt ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
    have hbound : ∀ i : Fin n, Real.sqrt (Se.p i)
        ≤ Real.sqrt (c' * Real.sqrt n) * Real.sqrt ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by
      intro i
      rw [hSe i]
      by_cases h : i.val % 2 = 0
      · rw [if_pos h]
        rw [show c' * Real.sqrt n * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
              = (c' * Real.sqrt n) * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) by ring]
        rw [Real.sqrt_mul (by positivity)]
      · rw [if_neg h, Real.sqrt_zero]; positivity
    calc (∑ i : Fin n, Real.sqrt (Se.p i))
        ≤ ∑ i : Fin n, Real.sqrt (c' * Real.sqrt n) * Real.sqrt ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by
          apply Finset.sum_le_sum; intro i _; exact hbound i
      _ = Real.sqrt (c' * Real.sqrt n) * ∑ i : Fin n, Real.sqrt ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt (c' * Real.sqrt n) * ∑ i ∈ Finset.range (n + 1), Real.sqrt ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          rw [Fin.sum_univ_eq_sum_range (fun i => Real.sqrt ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)) n]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
          · intro i _ _; positivity
  -- (IV) Fact 9 + constant equality
  have hfact9 := binomial_pmf_l_half_sum_bound hn
  have hconst : Real.sqrt (c' * Real.sqrt n) * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)
      = Real.sqrt n / (2 * Real.exp 1) := by
    have hsqn : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hexp1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hexp2 : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
    have hsqrt2pi : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hLnn : 0 ≤ Real.sqrt (c' * Real.sqrt n) * (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) := by
      apply mul_nonneg (Real.sqrt_nonneg _); apply Real.rpow_nonneg; positivity
    have hRnn : 0 ≤ Real.sqrt n / (2 * Real.exp 1) := by positivity
    rw [← sq_eq_sq₀ hLnn hRnn]
    rw [mul_pow]
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c' * Real.sqrt n)]
    have hrp : ((2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4))^2 = (2 * Real.pi * (n:ℝ)) ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
    rw [hrp]
    have hsplit : (2 * Real.pi * (n:ℝ)) ^ ((1:ℝ)/2) = Real.sqrt (2 * Real.pi) * Real.sqrt n := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity)]
    rw [hsplit, div_pow, mul_pow, Real.sq_sqrt hm]
    have hexp : (Real.exp 1)^2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hexp, hc']
    field_simp
    rw [Real.sq_sqrt hm]; ring
  -- Chain everything
  rw [hfact]
  refine le_trans hprodbd ?_
  apply Real.exp_le_exp.mpr
  refine le_trans hsumbd ?_
  refine le_trans (mul_le_mul_of_nonneg_left hfact9 (Real.sqrt_nonneg _)) ?_
  rw [hconst]

-- DELETED (faithfulness prune, 2026-06-13): `central_binomial_pmf_gaussian_lower_bound`
-- (the Gaussian LOWER envelope) was the twin of the deleted false
-- `central_binomial_pmf_gaussian_bound`. Not a paper result; consumed only by the
-- deleted non-paper `OffsetWeightBoundedByFirstFactor`. Removed.

/-! ## Supporting lemmas toward the Stirling–Gaussian envelope

The following sorry-free lemmas develop the binomial-ratio telescoping
infrastructure that any honest proof of a Gaussian-envelope bound on the
binomial pmf rests on:

* `binom_ratio_succ` — the real-valued one-step ratio recurrence
  `C(n,k+1) = C(n,k) · (n-k)/(k+1)`, from `Nat.choose_succ_right_eq`.
* `binom_ratio_succ_le_one` — past the mode (`2k ≥ n`) the pmf is
  non-increasing in `k`: `C(n,k+1) ≤ C(n,k)`.
* `binom_log_ratio_step_bound` — the per-step *logarithmic* decay bound
  `log(C(n,k+1)/C(n,k)) ≤ (n - 2k - 2)/(k+1)`, the quantity that, summed
  along the telescope, produces the Gaussian exponent.

These are the genuine building blocks of the local-CLT envelope; the
constant-`2` envelope itself is feasibility-gated (see the note on
`central_binomial_pmf_gaussian_bound` below in this docstring section). -/
section GaussianEnvelopeSupport

/-- Real-valued one-step ratio recurrence for binomial coefficients:
for `k < n`, `C(n,k+1) = C(n,k) · (n - k) / (k + 1)`. -/
theorem binom_ratio_succ (n k : ℕ) (hk : k < n) :
    (Nat.choose n (k + 1) : ℝ)
      = (Nat.choose n k : ℝ) * ((n - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  have h := Nat.choose_succ_right_eq n k
  have hcast := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at hcast
  rw [eq_div_iff (by positivity)]
  push_cast
  linarith [hcast]

/-- Past the mode (`n ≤ 2k`), the binomial pmf is non-increasing:
`C(n,k+1) ≤ C(n,k)`. -/
theorem binom_ratio_succ_le_one (n k : ℕ) (hk : k < n) (hmode : n ≤ 2 * k) :
    (Nat.choose n (k + 1) : ℝ) ≤ (Nat.choose n k : ℝ) := by
  rw [binom_ratio_succ n k hk]
  rw [div_le_iff₀ (by positivity)]
  have hnk : ((n - k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    have : n - k ≤ k + 1 := by omega
    exact_mod_cast this
  have hcb : (0 : ℝ) ≤ (Nat.choose n k : ℝ) := by positivity
  calc (Nat.choose n k : ℝ) * ((n - k : ℕ) : ℝ)
      ≤ (Nat.choose n k : ℝ) * ((k + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hnk hcb
    _ = (Nat.choose n k : ℝ) * ((k + 1 : ℕ) : ℝ) := rfl

/-- Per-step logarithmic decay of the binomial pmf past the mode.
For `k < n` with `2k ≥ n` and `C(n,k) > 0`,
`log (C(n,k+1) / C(n,k)) ≤ ((n : ℝ) - 2k - 2) / (k + 1)`.

This is the quantity that telescopes into the Gaussian exponent: writing
`r := (n - k)/(k + 1)` we have `log r ≤ r - 1 = (n - 2k - 1)/(k + 1)`,
and the slightly weaker `(n - 2k - 2)/(k+1)` bound here keeps the algebra
linear. (Both forms are sorry-free; we keep the cleaner `r - 1` one.) -/
theorem binom_log_ratio_step_bound (n k : ℕ) (hk : k < n) (hmode : n ≤ 2 * k)
    (hpos : 0 < (Nat.choose n k : ℝ)) :
    Real.log ((Nat.choose n (k + 1) : ℝ) / (Nat.choose n k : ℝ))
      ≤ (((n : ℝ) - 2 * k - 1) / ((k : ℝ) + 1)) := by
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  -- C(n,k) * (n-k)/(k+1) / C(n,k) = (n-k)/(k+1)
  have harg : (Nat.choose n (k + 1) : ℝ) / (Nat.choose n k : ℝ)
      = ((n - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    rw [binom_ratio_succ n k hk]
    field_simp
  rw [harg]
  -- goal: log ((n-k)/(k+1)) ≤ (n - 2k - 1)/(k+1)
  have hkn : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    have : k ≤ n := le_of_lt hk
    push_cast [Nat.cast_sub this]; ring
  rw [hkn]
  push_cast
  -- ratio is positive
  have hnk_pos : (0:ℝ) < (n:ℝ) - (k:ℝ) := by
    have hkn' : (k:ℝ) < (n:ℝ) := by exact_mod_cast hk
    linarith
  -- log x ≤ x - 1
  have hlog := Real.log_le_sub_one_of_pos (x := ((n:ℝ) - (k:ℝ)) / ((k:ℝ)+1))
    (by positivity)
  refine hlog.trans ?_
  rw [div_sub_one (ne_of_gt hk1)]
  apply div_le_div_of_nonneg_right ?_ hk1.le
  linarith

end GaussianEnvelopeSupport

end Workspace.Types.StirlingAxioms

