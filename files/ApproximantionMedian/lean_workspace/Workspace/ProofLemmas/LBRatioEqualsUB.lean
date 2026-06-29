import Mathlib
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.LambdaStarDef
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.LBConstruction
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.AStarLessThanOneHalf
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.RelaxedCoreDual
import Workspace.ProofLemmas.LBLambdaStarLtOne

open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.LambdaStarDef
open Workspace.ProofLemmas.UBDef
open Workspace.ProofLemmas.LBConstruction
open Workspace.ProofLemmas.DeltaStarDef
open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.RelaxedCoreDual
open Workspace.ProofLemmas.LBLambdaStarLtOne

namespace Workspace.ProofLemmas.LBRatioEqualsUB

set_option maxHeartbeats 1000000

/-- The limiting ratio of the lower-bound construction equals `UB q = 1/λ*`. -/
theorem LBRatioEqualsUB (q : ℝ) (hq : 1 < q) :
    ( (1 / (1 - c_star q)) * (a_star q) ^ ((1:ℝ)/q) + (1 - 2 * a_star q) )
      / ( (c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q) ) ^ ((1:ℝ)/q)
    = UB q := by
  -- Abbreviations.
  set a : ℝ := a_star q with ha_def
  set μ : ℝ := mu q with hμ_def
  set lam : ℝ := lambda_star q with hlam_def
  set δ : ℝ := delta_star q with hδ_def
  set K : ℝ := Kconst q with hK_def
  set c : ℝ := c_star q with hc_def
  -- Basic arithmetic facts on q.
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hqm1_pos : (0 : ℝ) < q - 1 := by linarith
  have hq_ge1 : (1 : ℝ) ≤ q := le_of_lt hq
  -- a* ∈ (0, 1/2).
  obtain ⟨ha_pos, ha_lt_half⟩ := AStarLessThanOneHalf q hq
  rw [← ha_def] at ha_pos ha_lt_half
  have ha_lt_one : a < 1 := by linarith
  have h1ma_pos : (0 : ℝ) < 1 - a := by linarith
  -- lam*, μ, 1-μ positivity.
  obtain ⟨⟨hlam_pos, hlam_lt_one⟩, ⟨hμ_pos, hμ_lt_one⟩, ⟨h1mμ_pos, _⟩⟩ := LBLambdaStarLtOne q hq
  rw [← hlam_def] at hlam_pos hlam_lt_one
  rw [← hμ_def] at hμ_pos hμ_lt_one
  rw [← hμ_def] at h1mμ_pos
  -- δ* ≥ 1 > 0.
  obtain ⟨hδ_ge_one, h_denom_pos⟩ := DeltaStarDef q hq
  rw [← hδ_def] at hδ_ge_one
  rw [← ha_def] at h_denom_pos
  have hδ_pos : 0 < δ := lt_of_lt_of_le one_pos hδ_ge_one
  -- K > 0.
  have hbaseK_pos : 0 < (1 - a) / a * (μ / (1 - μ)) := by
    apply mul_pos
    · exact div_pos h1ma_pos ha_pos
    · exact div_pos hμ_pos h1mμ_pos
  have hK_eq : K = ((1 - a) / a * (μ / (1 - μ))) ^ ((1 : ℝ) / q) := by
    rw [hK_def, hμ_def, ha_def]; rfl
  have hK_pos : 0 < K := by
    rw [hK_eq]; exact Real.rpow_pos_of_pos hbaseK_pos _
  have h1pK_pos : 0 < 1 + K := by linarith
  have h1pK_ne : (1 : ℝ) + K ≠ 0 := ne_of_gt h1pK_pos
  -- c = K/(1+K).
  have hc_eq : c = K / (1 + K) := by rw [hc_def, hK_def]; rfl
  -- 1 - c = 1/(1+K) > 0.
  have h1mc_eq : 1 - c = 1 / (1 + K) := by
    rw [hc_eq]; field_simp; ring
  have h1mc_pos : 0 < 1 - c := by rw [h1mc_eq]; positivity
  have h1mc_ne : (1 : ℝ) - c ≠ 0 := ne_of_gt h1mc_pos
  -- 1/(1-c) = 1+K.
  have h_inv1mc : 1 / (1 - c) = 1 + K := by
    rw [h1mc_eq]; field_simp
  -- c/(1-c) = K.
  have h_cratio : c / (1 - c) = K := by
    rw [div_eq_mul_inv, ← one_div, h_inv1mc, hc_eq]; field_simp
  -- a^(1/q), (1-a)^(1/q), μ^(1/q), etc. positivity.
  have ha_nn : (0 : ℝ) ≤ a := le_of_lt ha_pos
  have h1ma_nn : (0 : ℝ) ≤ 1 - a := le_of_lt h1ma_pos
  have hμ_nn : (0 : ℝ) ≤ μ := le_of_lt hμ_pos
  have h1mμ_nn : (0 : ℝ) ≤ 1 - μ := le_of_lt h1mμ_pos
  -- ============ DENOMINATOR ============
  -- K^q = (1-a)/a * μ/(1-μ).
  have hKq : K ^ q = (1 - a) / a * (μ / (1 - μ)) := by
    rw [hK_eq]
    rw [← Real.rpow_mul (le_of_lt hbaseK_pos)]
    rw [one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
  -- denominator base = (1-a)/(1-μ).
  have h_denbase : (c / (1 - c)) ^ q * a + (1 - a) = (1 - a) / (1 - μ) := by
    rw [h_cratio, hKq]
    field_simp
    ring
  -- ============ NUMERATOR ============
  -- D1: δ * (1-a)^(1/q) = a^(1/q) + 1 - 2a.
  have hD1 : δ * (1 - a) ^ ((1 : ℝ) / q) = a ^ ((1 : ℝ) / q) + 1 - 2 * a := by
    rw [hδ_def, hδ_def] at *
    have : delta_star q = (a ^ ((1:ℝ)/q) + 1 - 2 * a) / (1 - a) ^ ((1:ℝ)/q) := by
      rw [delta_star, ha_def]
    rw [this]
    field_simp
  -- K * a^(1/q) = (1-a)^(1/q) * (μ/(1-μ))^(1/q).
  have hKa : K * a ^ ((1 : ℝ) / q) = (1 - a) ^ ((1 : ℝ) / q) * (μ / (1 - μ)) ^ ((1 : ℝ) / q) := by
    rw [hK_eq]
    rw [← Real.mul_rpow (le_of_lt hbaseK_pos) ha_nn]
    have hrw : (1 - a) / a * (μ / (1 - μ)) * a = (1 - a) * (μ / (1 - μ)) := by
      field_simp
    rw [hrw]
    rw [Real.mul_rpow h1ma_nn (le_of_lt (div_pos hμ_pos h1mμ_pos))]
  -- Numerator = (1-a)^(1/q) * (δ + (μ/(1-μ))^(1/q)).
  have h_num : (1 / (1 - c)) * a ^ ((1 : ℝ) / q) + (1 - 2 * a)
      = (1 - a) ^ ((1 : ℝ) / q) * (δ + (μ / (1 - μ)) ^ ((1 : ℝ) / q)) := by
    rw [h_inv1mc]
    -- (1+K) * a^(1/q) + (1-2a) = a^(1/q) + K*a^(1/q) + 1 - 2a
    have hexp : (1 + K) * a ^ ((1 : ℝ) / q) + (1 - 2 * a)
        = (a ^ ((1 : ℝ) / q) + 1 - 2 * a) + K * a ^ ((1 : ℝ) / q) := by ring
    rw [hexp, ← hD1, hKa]
    ring
  -- ============ (D2): lam * δ = (1-μ)^((q-1)/q) ============
  have hbridge : delta_of_lambda q lam = δ := by
    rw [hlam_def, hδ_def]; exact deltaOfLambda_lambdaStar_eq q hq
  have hμ_as_pow : μ = lam ^ (q / (q - 1)) := by
    rw [hμ_def, hlam_def]; rfl
  have hLDI := LambdaDeltaIdentity q hq lam hlam_pos (le_of_lt hlam_lt_one)
  rw [hbridge, ← hμ_as_pow] at hLDI
  -- hLDI : lam * δ = (1 - μ)^((q-1)/q)
  have hD2 : lam * δ = (1 - μ) ^ ((q - 1) / q) := hLDI
  -- ============ lam = μ^((q-1)/q) ============
  have hlam_as_μpow : lam = μ ^ ((q - 1) / q) := by
    rw [hμ_as_pow, ← Real.rpow_mul (le_of_lt hlam_pos)]
    have : q / (q - 1) * ((q - 1) / q) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  -- ============ Assemble lam * Numerator = ((1-a)/(1-μ))^(1/q) ============
  -- lam * (μ/(1-μ))^(1/q) = μ * (1-μ)^(-1/q).
  have hlam_term : lam * (μ / (1 - μ)) ^ ((1 : ℝ) / q) = μ * (1 - μ) ^ (-(1 / q) : ℝ) := by
    -- (μ/(1-μ))^(1/q) = μ^(1/q) * (1-μ)^(-(1/q))
    have hsplit : (μ / (1 - μ)) ^ ((1 : ℝ) / q)
        = μ ^ ((1:ℝ)/q) * (1 - μ) ^ (-(1 / q) : ℝ) := by
      rw [Real.div_rpow hμ_nn h1mμ_nn, Real.rpow_neg h1mμ_nn, div_eq_mul_inv]
    rw [hlam_as_μpow, hsplit]
    -- μ^((q-1)/q) * (μ^(1/q) * (1-μ)^(-(1/q)))
    have hcomb : μ ^ ((q - 1) / q) * (μ ^ ((1:ℝ)/q) * (1 - μ) ^ (-(1/q) : ℝ))
        = (μ ^ ((q - 1) / q) * μ ^ ((1:ℝ)/q)) * (1 - μ) ^ (-(1/q) : ℝ) := by ring
    rw [hcomb, ← Real.rpow_add hμ_pos]
    have hsum : (q - 1) / q + (1 : ℝ) / q = 1 := by field_simp; ring
    rw [hsum, Real.rpow_one]
  -- (1-μ)^((q-1)/q) + μ*(1-μ)^(-1/q) = (1-μ)^(-1/q).
  have h_collapse : (1 - μ) ^ ((q - 1) / q) + μ * (1 - μ) ^ (-(1 / q) : ℝ)
      = (1 - μ) ^ (-(1 / q) : ℝ) := by
    have hfac : (1 - μ) ^ ((q - 1) / q) = (1 - μ) ^ (1 + -(1 / q) : ℝ) := by
      congr 1
      field_simp; ring
    rw [hfac, Real.rpow_add h1mμ_pos, Real.rpow_one]
    ring
  -- lam * Numerator.
  have hlam_num : lam * ((1 / (1 - c)) * a ^ ((1 : ℝ) / q) + (1 - 2 * a))
      = ((1 - a) / (1 - μ)) ^ ((1 : ℝ) / q) := by
    rw [h_num]
    -- lam * ((1-a)^(1/q) * (δ + (μ/(1-μ))^(1/q)))
    have hstep : lam * ((1 - a) ^ ((1 : ℝ) / q) * (δ + (μ / (1 - μ)) ^ ((1 : ℝ) / q)))
        = (1 - a) ^ ((1 : ℝ) / q) * (lam * δ + lam * (μ / (1 - μ)) ^ ((1 : ℝ) / q)) := by
      ring
    rw [hstep, hD2, hlam_term, h_collapse]
    -- (1-a)^(1/q) * (1-μ)^(-1/q) = ((1-a)/(1-μ))^(1/q)
    rw [Real.div_rpow h1ma_nn h1mμ_nn, Real.rpow_neg h1mμ_nn]
    ring
  -- ============ Final: ratio = 1/lam = UB q ============
  rw [h_denbase]
  -- Goal: Numerator / ((1-a)/(1-μ))^(1/q) = UB q
  have h_denpow_pos : 0 < ((1 - a) / (1 - μ)) ^ ((1 : ℝ) / q) :=
    Real.rpow_pos_of_pos (div_pos h1ma_pos h1mμ_pos) _
  have h_denpow_ne : ((1 - a) / (1 - μ)) ^ ((1 : ℝ) / q) ≠ 0 := ne_of_gt h_denpow_pos
  -- UB q = 1/lam.
  have hUB : UB q = 1 / lam := by
    rw [hlam_def, UB, if_pos hq_ge1]
  rw [hUB]
  -- Numerator / D = 1/lam  ⟺  lam * Numerator = D  (since lam ≠ 0, D ≠ 0... actually need:)
  rw [div_eq_div_iff h_denpow_ne (ne_of_gt hlam_pos)]
  -- Goal: Numerator * lam = 1 * D
  rw [one_mul, mul_comm]
  exact hlam_num

end Workspace.ProofLemmas.LBRatioEqualsUB
