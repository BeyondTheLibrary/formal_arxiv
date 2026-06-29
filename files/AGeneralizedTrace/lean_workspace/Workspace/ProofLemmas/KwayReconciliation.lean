import Mathlib
import Workspace.ProofLemmas.GenvConvergence
import Workspace.ProofLemmas.CircConvBilinear
import Workspace.ProofLemmas.CircPowMultiplicity
import Workspace.ProofLemmas.GlinWeightedMGF
import Workspace.ProofLemmas.PerBPeriodisation
import Workspace.ProofLemmas.CircMultiplicityExpansion
import Workspace.ProofLemmas.LinMultiplicityExpansion

open scoped Real BigOperators
open MeasureTheory intervalIntegral
open CircConvInfra PeriodicBaseKfoldPeriodisation CircPowMultiplicity CircConvBilinear
open T4ToCircPowRPeriodic GenvConvergence PerFactorFourierModulus GlinWeightedMGF
open PerBPeriodisation CircMultiplicityExpansion LinMultiplicityExpansion

set_option maxHeartbeats 4000000

/-!
# Reconciliation: circular k-power ≤ periodised linear k-power (Lemma 7, Part 2)

`circPowR (Genv n) k ξ ≤ ∑'_s linPow (Glin n) k (ξ + 2π s)` for `|ξ| ≤ π`, `k ≥ 1`.

Route (lean_knowledge F69): rewrite the LHS by `circ_expansion`; per-B
`PerBPeriodisation.circPowR_Bbase_le_periodised_linPow` bounds each circular
power of `Bbase` by the periodised linear power of `Bbase0`; multiply by the
nonnegative coefficient `multM·αC^{k+m}`; sum over `m`; swap `∑'_m ∑'_s` to
`∑'_s ∑'_m` (Tonelli for nonnegative, via `Summable.tsum_comm'`); fold the inner
`∑'_m` back via `lin_expansion` to land on `∑'_s linPow (Glin n) k (ξ+2πs)`.

The one nontrivial summability gap is the ℕ×ℤ joint summability, discharged via
`summable_prod_of_nonneg` with the periodised inner sum bounded through
`periodised_bdd_of_compact_support` and a binomial-geometric domination.
-/

namespace KwayReconciliation

/-- The joint family on `ℕ × ℤ` whose `(m,s)`-entry is the `m`-th expansion
coefficient times the `s`-shifted linear power of `Bbase0`. -/
private noncomputable def Fjoint (n k : ℕ) (ξ : ℝ) : ℕ → ℤ → ℝ :=
  fun m s => ((multM k m : ℝ) * alphaC n ^ (k + m))
    * linPow (Bbase0 n) (k + m) (ξ + 2 * Real.pi * (s : ℝ))

private theorem Fjoint_nonneg (n k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (m : ℕ) (s : ℤ) :
    0 ≤ Fjoint n k ξ m s := by
  unfold Fjoint
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (alphaC_nonneg n) _))
    (linPow_Bbase0_nn n (k + m) (by omega) _)

/-- Inner-`s` summability of the joint family at fixed `m`. -/
private theorem Fjoint_inner_summable (n k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (m : ℕ) :
    Summable (fun s : ℤ => Fjoint n k ξ m s) := by
  unfold Fjoint
  exact (periodised_linPow_summable n (k + m) (by omega) ξ).mul_left _

/-- Periodised bound: the inner-`s` sum at fixed `m` is `≤ coef_m · Gint^{k+m-1} · (k+m+2)`. -/
private theorem Fjoint_marginal_le (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (m : ℕ) :
    (∑' s : ℤ, Fjoint n k ξ m s)
      ≤ ((multM k m : ℝ) * alphaC n ^ (k + m))
          * ((Gint n) ^ (k + m - 1) * (((k + m : ℕ) : ℝ) + 2)) := by
  have hcoef_nn : 0 ≤ (multM k m : ℝ) * alphaC n ^ (k + m) :=
    mul_nonneg (by positivity) (pow_nonneg (alphaC_nonneg n) _)
  have hsum_eq : (∑' s : ℤ, Fjoint n k ξ m s)
      = ((multM k m : ℝ) * alphaC n ^ (k + m))
        * ∑' s : ℤ, linPow (Bbase0 n) (k + m) (ξ + 2 * Real.pi * (s : ℝ)) := by
    unfold Fjoint
    rw [tsum_mul_left]
  rw [hsum_eq]
  apply mul_le_mul_of_nonneg_left _ hcoef_nn
  -- periodised_bdd: R = (k+m)·π, M = Gint^{k+m-1}, bound = M·(R/π + 2) = M·((k+m)+2)
  have hper := periodised_bdd_of_compact_support (linPow (Bbase0 n) (k + m))
    (((k + m : ℕ) : ℝ) * Real.pi) ((Gint n) ^ (k + m - 1))
    (by positivity)
    (fun y => linPow_Bbase0_nn n (k + m) (by omega) y)
    (fun y => linPow_Bbase0_sup_bound n hn (k + m) (by omega) y)
    (fun y hy => linPow_Bbase0_supp n (k + m) (by omega) y hy)
    ξ
  have hsimp : (Gint n) ^ (k + m - 1) * (((k + m : ℕ) : ℝ) * Real.pi / Real.pi + 2)
      = (Gint n) ^ (k + m - 1) * (((k + m : ℕ) : ℝ) + 2) := by
    rw [mul_div_assoc, div_self (ne_of_gt Real.pi_pos), mul_one]
  rw [hsimp] at hper
  exact hper

/-- m-marginal summability: `m ↦ coef_m · Gint^{k+m-1} · (k+m+2)` is summable. -/
private theorem marginal_majorant_summable (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun m : ℕ =>
      ((multM k m : ℝ) * alphaC n ^ (k + m))
        * ((Gint n) ^ (k + m - 1) * (((k + m : ℕ) : ℝ) + 2))) := by
  set q : ℝ := alphaC n * Gint n with hq
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hgint : 0 ≤ Gint n := Gint_nonneg n
  have hqnn : 0 ≤ q := alphaGint_nonneg n
  have hqlt : q < 1 := alphaGint_lt_one n hn
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt
  -- u m := (m + (k-1)).choose (k-1) * (m + k + 2)
  set u : ℕ → ℕ := fun m => (m + (k - 1)).choose (k - 1) * (m + k + 2) with hu
  -- IsBigO side-goal: u m =O[atTop] m^k.  For m ≥ k+2 we have u m ≤ 2^k · m^k.
  have hnat_bound : ∀ m : ℕ, k + 2 ≤ m → u m ≤ 2 ^ k * m ^ k := by
    intro m hm
    have hk1 : k - 1 + 1 = k := by omega
    -- choose ≤ (m+k-1)^{k-1} ≤ (2m)^{k-1} = 2^{k-1} m^{k-1}
    have hch : (m + (k - 1)).choose (k - 1) ≤ (m + (k - 1)) ^ (k - 1) :=
      Nat.choose_le_pow (m + (k - 1)) (k - 1)
    have hmk : m + (k - 1) ≤ 2 * m := by omega
    have hpow1 : (m + (k - 1)) ^ (k - 1) ≤ (2 * m) ^ (k - 1) :=
      Nat.pow_le_pow_left hmk (k - 1)
    have hch2 : (m + (k - 1)).choose (k - 1) ≤ 2 ^ (k - 1) * m ^ (k - 1) := by
      calc (m + (k - 1)).choose (k - 1) ≤ (2 * m) ^ (k - 1) := le_trans hch hpow1
        _ = 2 ^ (k - 1) * m ^ (k - 1) := by rw [Nat.mul_pow]
    have hlin : m + k + 2 ≤ 2 * m := by omega
    calc u m = (m + (k - 1)).choose (k - 1) * (m + k + 2) := rfl
      _ ≤ (2 ^ (k - 1) * m ^ (k - 1)) * (2 * m) := Nat.mul_le_mul hch2 hlin
      _ = 2 ^ (k - 1) * 2 * (m ^ (k - 1) * m) := by ring
      _ = 2 ^ k * m ^ k := by
          rw [← pow_succ, ← pow_succ, hk1]
  have hbigO : (fun m => (u m : ℝ)) =O[Filter.atTop] (fun m => ((m ^ k : ℕ) : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (2 ^ k : ℝ)
    filter_upwards [Filter.eventually_ge_atTop (k + 2)] with m hm
    have hum_nn : (0 : ℝ) ≤ (u m : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hum_nn,
      abs_of_nonneg (by positivity)]
    exact_mod_cast hnat_bound m hm
  have hbase : Summable (fun m : ℕ => ‖(u m : ℝ) * q ^ m‖) :=
    summable_norm_mul_geometric_of_norm_lt_one (k := k) (r := q) hnorm hbigO
  have hbase' : Summable (fun m : ℕ => (u m : ℝ) * q ^ m) := by
    apply hbase.of_norm
  -- dominate the target by alphaC · q^{k-1} · (u m · q^m)
  have hdom : Summable (fun m : ℕ => alphaC n * q ^ (k - 1) * ((u m : ℝ) * q ^ m)) :=
    hbase'.mul_left _
  apply Summable.of_nonneg_of_le _ _ hdom
  · intro m
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hann _))
      (mul_nonneg (pow_nonneg hgint _) (by positivity))
  · intro m
    have hmult : (multM k m : ℝ) = ((m + (k - 1)).choose (k - 1) : ℝ) := by
      rw [multM_choose k m hk]
    apply le_of_eq
    rw [hmult, hu, hq]
    -- LHS = choose · αC^{k+m} · (Gint^{k+m-1} · (k+m+2))
    -- RHS = αC · (αC Gint)^{k-1} · (choose·(m+k+2) · (αC Gint)^m)
    push_cast
    rw [mul_pow, mul_pow]
    rw [show alphaC n ^ (k + m) = alphaC n * (alphaC n ^ (k - 1) * alphaC n ^ m) by
      rw [← pow_add, ← pow_succ']; congr 1; omega]
    rw [show (Gint n) ^ (k + m - 1) = (Gint n) ^ (k - 1) * (Gint n) ^ m by
      rw [← pow_add]; congr 1; omega]
    ring

/-- Joint ℕ×ℤ summability of `Fjoint`. -/
private theorem Fjoint_summable (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun p : ℕ × ℤ => Fjoint n k ξ p.1 p.2) := by
  rw [summable_prod_of_nonneg (fun p => Fjoint_nonneg n k hk ξ p.1 p.2)]
  refine ⟨fun m => Fjoint_inner_summable n k hk ξ m, ?_⟩
  apply Summable.of_nonneg_of_le
    (fun m => tsum_nonneg (fun s => Fjoint_nonneg n k hk ξ m s))
    (fun m => Fjoint_marginal_le n hn k hk ξ m)
    (marginal_majorant_summable n hn k hk)

private theorem Fjoint_uncurry_summable (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (Function.uncurry (Fjoint n k ξ)) :=
  Fjoint_summable n hn k hk ξ

/-- **Reconciliation (Part 2).** For `|ξ| ≤ π` and `k ≥ 1`,
`circPowR (Genv n) k ξ ≤ ∑'_s linPow (Glin n) k (ξ + 2π s)`. -/
theorem circPowR_Genv_le_periodised_linPow_Glin (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (hξ : |ξ| ≤ Real.pi) :
    circPowR (Genv n) k ξ
      ≤ ∑' s : ℤ, linPow (Glin n) k (ξ + 2 * Real.pi * (s : ℝ)) := by
  -- LHS: rewrite by circ_expansion.
  rw [circ_expansion n hn k hk ξ]
  -- Each circular term ≤ periodised linear term: bound term-by-term.
  have hterm_le : ∀ m : ℕ,
      ((multM k m : ℝ) * alphaC n ^ (k + m)) * circPowR (Bbase n) (k + m) ξ
        ≤ ∑' s : ℤ, Fjoint n k ξ m s := by
    intro m
    have hcoef_nn : 0 ≤ (multM k m : ℝ) * alphaC n ^ (k + m) :=
      mul_nonneg (by positivity) (pow_nonneg (alphaC_nonneg n) _)
    have hper := circPowR_Bbase_le_periodised_linPow n hn (k + m) (by omega) ξ hξ
    calc ((multM k m : ℝ) * alphaC n ^ (k + m)) * circPowR (Bbase n) (k + m) ξ
        ≤ ((multM k m : ℝ) * alphaC n ^ (k + m))
            * ∑' s : ℤ, linPow (Bbase0 n) (k + m) (ξ + 2 * Real.pi * (s : ℝ)) :=
          mul_le_mul_of_nonneg_left hper hcoef_nn
      _ = ∑' s : ℤ, Fjoint n k ξ m s := by unfold Fjoint; rw [tsum_mul_left]
  -- Sum over m: LHS summable (expansion_summable), RHS summable (m-marginal of joint).
  have hLHS_summ : Summable (fun m : ℕ =>
      (multM k m : ℝ) * alphaC n ^ (k + m) * circPowR (Bbase n) (k + m) ξ) :=
    expansion_summable n hn k hk ξ
  have hjoint := Fjoint_summable n hn k hk ξ
  have hjointU := Fjoint_uncurry_summable n hn k hk ξ
  have hRHS_summ : Summable (fun m : ℕ => ∑' s : ℤ, Fjoint n k ξ m s) :=
    (summable_prod_of_nonneg (fun p => Fjoint_nonneg n k hk ξ p.1 p.2)).mp hjoint |>.2
  -- per-`s` summability over `m` (for the swap): from the swapped joint family.
  have hjoint_swap : Summable (fun p : ℤ × ℕ => Fjoint n k ξ p.2 p.1) := by
    have h := (Equiv.summable_iff (f := fun p : ℤ × ℕ => Fjoint n k ξ p.2 p.1)
      (Equiv.prodComm ℕ ℤ)).mp
    apply h
    simpa [Function.comp, Equiv.prodComm] using hjoint
  have hcol_summ : ∀ s : ℤ, Summable (fun m : ℕ => Fjoint n k ξ m s) :=
    fun s => hjoint_swap.prod_factor s
  have hsum_le : (∑' m : ℕ, (multM k m : ℝ) * alphaC n ^ (k + m) * circPowR (Bbase n) (k + m) ξ)
      ≤ ∑' m : ℕ, ∑' s : ℤ, Fjoint n k ξ m s :=
    Summable.tsum_le_tsum hterm_le hLHS_summ hRHS_summ
  refine le_trans hsum_le (le_of_eq ?_)
  -- swap ∑'_m ∑'_s to ∑'_s ∑'_m via tsum_comm', then fold via lin_expansion.
  rw [← Summable.tsum_comm' hjointU
      (fun m => Fjoint_inner_summable n k hk ξ m) hcol_summ]
  -- ∑'_s ∑'_m Fjoint = ∑'_s linPow (Glin n) k (ξ+2πs)
  apply tsum_congr
  intro s
  show (∑' m : ℕ, Fjoint n k ξ m s) = linPow (Glin n) k (ξ + 2 * Real.pi * (s : ℝ))
  unfold Fjoint
  rw [(lin_expansion n hn k hk (ξ + 2 * Real.pi * (s : ℝ))).symm]

end KwayReconciliation
