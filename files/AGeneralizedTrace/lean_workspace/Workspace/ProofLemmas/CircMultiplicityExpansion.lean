import Mathlib
import Workspace.ProofLemmas.GenvConvergence
import Workspace.ProofLemmas.CircConvBilinear
import Workspace.ProofLemmas.CircPowMultiplicity

open scoped Real BigOperators
open MeasureTheory intervalIntegral
open CircConvInfra PeriodicBaseKfoldPeriodisation CircPowMultiplicity CircConvBilinear
open T4ToCircPowRPeriodic GenvConvergence PerFactorFourierModulus

set_option maxHeartbeats 4000000

/-!
# Circular multiplicity expansion (Lemma 7, Step 1 — circular half)

`circPowR (Genv n) k ξ = ∑'_m (multM k m) · αC^(k+m) · circPowR (Bbase n) (k+m) ξ`
for `k ≥ 1`, where `Genv n = ∑'_b αC^(b+1) circPowR (Bbase n) (b+1)`.

The combinatorial coefficient `multM k m = C(k+m-1, k-1)` and the scalar collapse of
the induction step are inlined here (they need only `Mathlib`), so the file is
self-contained over the already-built convolution-algebra layer.
-/

namespace CircMultiplicityExpansion

/-! ## Combinatorial core (inlined; Mathlib-only). -/

/-- The multiplicity coefficient `multM k m = C(k+m-1, k-1)`. -/
def multM (k m : ℕ) : ℕ := Nat.choose (k + m - 1) (k - 1)

theorem multM_one (m : ℕ) : multM 1 m = 1 := by unfold multM; simp

/-- Hockey-stick: `∑_{i=0}^m multM k i = multM (k+1) m` for `k ≥ 1`. -/
theorem multM_succ_sum (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), multM k i) = multM (k + 1) m := by
  unfold multM
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hk1 : 1 + K - 1 = K := by omega
  have hk2 : 1 + K + 1 - 1 = K + 1 := by omega
  simp only [hk1, hk2]
  have hidx : ∀ i ∈ Finset.range (m + 1), (1 + K + i - 1).choose K = (i + K).choose K := by
    intro i _; congr 1; omega
  rw [Finset.sum_congr rfl hidx, Nat.sum_range_add_choose m K]
  congr 1; omega

/-- Numerical regrouping of a nonnegative double `tsum` by the sum index. -/
theorem tsum_tsum_regroup (F : ℕ → ℕ → ℝ)
    (hsumm : Summable (fun p : ℕ × ℕ => F p.1 p.2)) :
    (∑' B : ℕ, ∑' a : ℕ, F B a)
      = ∑' C : ℕ, ∑ p ∈ Finset.antidiagonal C, F p.1 p.2 := by
  rw [← hsumm.tsum_prod]
  rw [← (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq (fun p : ℕ × ℕ => F p.1 p.2)]
  have hsumm_sigma : Summable
      (fun x : (C : ℕ) × ↥(Finset.antidiagonal C) =>
        F (Finset.sigmaAntidiagonalEquivProd x).1 (Finset.sigmaAntidiagonalEquivProd x).2) :=
    hsumm.comp_injective (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).injective
  rw [hsumm_sigma.tsum_sigma]
  apply tsum_congr
  intro C
  rw [tsum_eq_sum (s := Finset.univ) (by intro b hb; exact absurd (Finset.mem_univ b) hb)]
  rw [← Finset.sum_attach (Finset.antidiagonal C) (fun p => F p.1 p.2)]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sigmaAntidiagonalEquivProd_apply]

/-- The scalar/combinatorial collapse of the induction step. -/
theorem step_collapse (α : ℝ) (Pb : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hsumm : Summable (fun p : ℕ × ℕ =>
      ((multM k p.1 : ℝ) * α ^ (k + p.1)) * (α ^ (p.2 + 1) * Pb ((k + p.1) + (p.2 + 1))))) :
    (∑' B : ℕ, ∑' a : ℕ,
        ((multM k B : ℝ) * α ^ (k + B)) * (α ^ (a + 1) * Pb ((k + B) + (a + 1))))
      = ∑' m : ℕ, ((multM (k + 1) m : ℝ) * α ^ ((k + 1) + m)) * Pb ((k + 1) + m) := by
  set F : ℕ → ℕ → ℝ := fun B a =>
    ((multM k B : ℝ) * α ^ (k + B)) * (α ^ (a + 1) * Pb ((k + B) + (a + 1))) with hF
  rw [tsum_tsum_regroup F hsumm]
  apply tsum_congr
  intro C
  have hterm : ∀ p ∈ Finset.antidiagonal C,
      F p.1 p.2 = (multM k p.1 : ℝ) * (α ^ ((k + 1) + C) * Pb ((k + 1) + C)) := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    simp only [hF]
    have hidx : (k + p.1) + (p.2 + 1) = (k + 1) + C := by omega
    have hpow : α ^ (k + p.1) * α ^ (p.2 + 1) = α ^ ((k + 1) + C) := by
      rw [← pow_add, hidx]
    rw [hidx]
    rw [show (multM k p.1 : ℝ) * α ^ (k + p.1) * (α ^ (p.2 + 1) * Pb ((k + 1) + C))
        = (multM k p.1 : ℝ) * (α ^ (k + p.1) * α ^ (p.2 + 1)) * Pb ((k + 1) + C) by ring,
      hpow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hcoef : (∑ p ∈ Finset.antidiagonal C, (multM k p.1 : ℝ))
      = (multM (k + 1) C : ℝ) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => (multM k p.1 : ℝ)) C]
    simp only
    rw [← Nat.cast_sum]
    rw [show (∑ i ∈ Finset.range (C + 1), multM k i) = multM (k + 1) C from multM_succ_sum k hk C]
  rw [hcoef]; ring

/-! ## GoodP packaging. -/

theorem goodP_Bbase (n : ℕ) : GoodP (Bbase n) :=
  ⟨Bbase_continuous n, fun x => Bbase_periodic n x⟩

theorem goodP_Genv (n : ℕ) (hn : 1 ≤ n) : GoodP (Genv n) :=
  ⟨Genv_continuous n hn, fun x => Genv_periodic n x⟩

/-! ## Base case `k = 1`. -/

/-- `circPowR (Genv n) 1 ξ = ∑'_m multM 1 m · αC^(1+m) · circPowR (Bbase n) (1+m) ξ`. -/
theorem expansion_base (n : ℕ) (ξ : ℝ) :
    circPowR (Genv n) 1 ξ
      = ∑' m : ℕ, ((multM 1 m : ℝ) * alphaC n ^ (1 + m)) * circPowR (Bbase n) (1 + m) ξ := by
  rw [circPowR_one]
  show Genv n ξ = _
  unfold Genv
  apply tsum_congr
  intro m
  rw [multM_one m]
  push_cast
  rw [show (1 : ℝ) * alphaC n ^ (1 + m) = alphaC n ^ (m + 1) by rw [Nat.add_comm]; ring]
  rw [show 1 + m = m + 1 by omega]

/-! ## `circConvR` distributes a `tsum` in the RIGHT argument (for `GoodP` data). -/

/-- `circConvR f (∑'_a u_a) ξ = ∑'_a circConvR f (u_a) ξ`, via commutativity, when
`f`, every `u_a`, and `∑'_a u_a` are `2π`-periodic and the left-distribution side
conditions hold after the swap. -/
theorem circConvR_tsum_right (f : ℝ → ℝ) (u : ℕ → ℝ → ℝ) (ξ : ℝ)
    (hf_per : ∀ x, f (x + 2 * Real.pi) = f x)
    (hu_per : ∀ a, ∀ x, u a (x + 2 * Real.pi) = u a x)
    (hsum_per : ∀ x, (fun η => ∑' a, u a η) (x + 2 * Real.pi) = (fun η => ∑' a, u a η) x)
    (hint : ∀ a, MeasureTheory.IntegrableOn
      (fun η => u a η * f (ξ - η)) (Set.Ioc (-Real.pi) Real.pi))
    (hsumm : Summable (fun a =>
      ∫ η in Set.Ioc (-Real.pi) Real.pi, ‖u a η * f (ξ - η)‖)) :
    circConvR f (fun η => ∑' a, u a η) ξ = ∑' a, circConvR f (u a) ξ := by
  rw [circConvR_comm hf_per hsum_per]
  rw [circConvR_tsum_left u f ξ hint hsumm]
  apply tsum_congr
  intro a
  rw [circConvR_comm (hu_per a) hf_per]

/-! ## Geometric domination of the expansion terms (for summability). -/

/-- Pointwise geometric majorant for the base power, at a fixed `ξ`:
`circPowR (Bbase n) m ξ ≤ (Gint n / 2π)^(m-1)` (the sup bound). -/
theorem Pb_le_geom (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (ξ : ℝ) :
    circPowR (Bbase n) m ξ ≤ (Gint n / (2 * Real.pi)) ^ (m - 1) :=
  circPowR_Bbase_sup_bound n hn m hm ξ

/-- `multM k m = C(m + (k-1), k-1)` (the shift-free reindex, valid for `k ≥ 1`). -/
theorem multM_choose (k m : ℕ) (hk : 1 ≤ k) :
    multM k m = (m + (k - 1)).choose (k - 1) := by unfold multM; congr 1; omega

/-- **Single-index summability of the circular expansion series** (at a fixed `ξ`):
`m ↦ multM k m · αC^{k+m} · circPowR (Bbase n) (k+m) ξ` is summable, dominated by the
geometric–binomial majorant `αC·q^{k-1} · C(m+(k-1),k-1)·q^m` with `q = αC·Gint/2π < 1`. -/
theorem expansion_summable (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun m : ℕ =>
      (multM k m : ℝ) * alphaC n ^ (k + m) * circPowR (Bbase n) (k + m) ξ) := by
  set q : ℝ := alphaC n * Gint n / (2 * Real.pi) with hq
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hqnn : 0 ≤ q := alphaG_div_two_pi_nonneg n hn
  have hqlt : q < 1 := alphaG_div_two_pi_lt_one n hn
  have hbase : Summable (fun m : ℕ => ((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m) :=
    summable_choose_mul_geometric_of_norm_lt_one (k - 1)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt)
  have hdom : Summable (fun m : ℕ =>
      alphaC n * q ^ (k - 1) * (((m + (k - 1)).choose (k - 1) : ℝ) * q ^ m)) := hbase.mul_left _
  apply Summable.of_nonneg_of_le _ _ hdom
  · intro m
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hann _))
      (circPowR_nonneg (Bbase n) (Bbase_nonneg n) (k + m) (by omega) ξ)
  · intro m
    have hmult : (multM k m : ℝ) = ((m + (k - 1)).choose (k - 1) : ℝ) := by
      rw [multM_choose k m hk]
    have hpb := Pb_le_geom n hn (k + m) (by omega) ξ
    have key : (multM k m : ℝ) * alphaC n ^ (k + m) * circPowR (Bbase n) (k + m) ξ
        ≤ (multM k m : ℝ) * alphaC n ^ (k + m) * (Gint n / (2 * Real.pi)) ^ (k + m - 1) :=
      mul_le_mul_of_nonneg_left hpb (mul_nonneg (by positivity) (pow_nonneg hann _))
    refine le_trans key (le_of_eq ?_)
    rw [hmult, show k + m - 1 = (k - 1) + m by omega, hq]
    rw [show alphaC n * Gint n / (2 * Real.pi) = alphaC n * (Gint n / (2 * Real.pi)) by
      rw [mul_div_assoc]]
    rw [mul_pow, mul_pow]
    rw [show alphaC n ^ (k + m) = alphaC n * (alphaC n ^ (k - 1) * alphaC n ^ m) by
      rw [← pow_add, ← pow_succ']; congr 1; omega]
    rw [pow_add]
    ring

/-- **2-D joint summability of the induction-step double family.**  The nonnegative
`(B,a) ↦ (multM k B · αC^{k+B}) · (αC^{a+1} · circPowR (Bbase n) ((k+B)+(a+1)) ξ)` is
summable on `ℕ × ℕ`, dominated by the separable majorant
`(q^k·C(B+(k-1),k-1)·q^B) · (αC·q^a)`.  This is the `hsumm` side-condition of
`step_collapse`. -/
theorem step_summable (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ((multM k p.1 : ℝ) * alphaC n ^ (k + p.1))
        * (alphaC n ^ (p.2 + 1) * circPowR (Bbase n) ((k + p.1) + (p.2 + 1)) ξ)) := by
  set q : ℝ := alphaC n * Gint n / (2 * Real.pi) with hq
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  have hqnn : 0 ≤ q := alphaG_div_two_pi_nonneg n hn
  have hqlt : q < 1 := alphaG_div_two_pi_lt_one n hn
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt
  have hfB : Summable (fun B : ℕ => q ^ k * (((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B)) :=
    (summable_choose_mul_geometric_of_norm_lt_one (k - 1) hnorm).mul_left _
  have hga : Summable (fun a : ℕ => alphaC n * q ^ a) :=
    (summable_geometric_of_lt_one hqnn hqlt).mul_left _
  have hmaj : Summable (fun p : ℕ × ℕ =>
      (q ^ k * (((p.1 + (k - 1)).choose (k - 1) : ℝ) * q ^ p.1)) * (alphaC n * q ^ p.2)) :=
    hfB.mul_of_nonneg hga (fun B => by positivity) (fun a => by positivity)
  apply Summable.of_nonneg_of_le _ _ hmaj
  · intro p
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hann _))
      (mul_nonneg (pow_nonneg hann _)
        (circPowR_nonneg (Bbase n) (Bbase_nonneg n) _ (by omega) ξ))
  · rintro ⟨B, a⟩
    simp only
    have hpb := Pb_le_geom n hn ((k + B) + (a + 1)) (by omega) ξ
    have hmult : (multM k B : ℝ) = ((B + (k - 1)).choose (k - 1) : ℝ) := by
      rw [multM_choose k B hk]
    calc ((multM k B : ℝ) * alphaC n ^ (k + B))
            * (alphaC n ^ (a + 1) * circPowR (Bbase n) ((k + B) + (a + 1)) ξ)
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B))
            * (alphaC n ^ (a + 1) * (Gint n / (2 * Real.pi)) ^ ((k + B) + (a + 1) - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpb (pow_nonneg hann _))
            (mul_nonneg (by positivity) (pow_nonneg hann _))
      _ = (q ^ k * (((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B)) * (alphaC n * q ^ a) := by
          rw [hmult, hq, show (k + B) + (a + 1) - 1 = (k + B) + a by omega]
          rw [show alphaC n * Gint n / (2 * Real.pi) = alphaC n * (Gint n / (2 * Real.pi)) by
            rw [mul_div_assoc]]
          rw [mul_pow, mul_pow, mul_pow]
          rw [show alphaC n ^ (k + B) = alphaC n ^ k * alphaC n ^ B by rw [← pow_add]]
          rw [show alphaC n ^ (a + 1) = alphaC n * alphaC n ^ a by rw [← pow_succ']]
          rw [show (Gint n / (2 * Real.pi)) ^ ((k + B) + a)
              = (Gint n / (2 * Real.pi)) ^ k * (Gint n / (2 * Real.pi)) ^ B
                * (Gint n / (2 * Real.pi)) ^ a by rw [← pow_add, ← pow_add]]
          ring

/-- `Genv n` is uniformly bounded (continuous + `2π`-periodic). -/
theorem Genv_bdd (n : ℕ) (hn : 1 ≤ n) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, Genv n y ≤ M := by
  have hper : Function.Periodic (Genv n) (2 * Real.pi) := fun x => Genv_periodic n x
  have hbdd := hper.isBounded_of_continuous (by positivity) (Genv_continuous n hn)
  rw [Metric.isBounded_iff_subset_closedBall 0] at hbdd
  obtain ⟨r, hr⟩ := hbdd
  refine ⟨|r|, abs_nonneg r, fun y => ?_⟩
  have hy : Genv n y ∈ Metric.closedBall (0 : ℝ) r := hr ⟨y, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hy
  calc Genv n y ≤ |Genv n y| := le_abs_self _
    _ ≤ r := hy
    _ ≤ |r| := le_abs_self _

/-- `∫_{Ioc} circPowR (Bbase n) m ≤ (2π)·(Gint/2π)^{m-1}` (sup bound × window measure). -/
theorem circint_window_bound (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    (∫ η in Set.Ioc (-Real.pi) Real.pi, circPowR (Bbase n) m η)
      ≤ (2 * Real.pi) * (Gint n / (2 * Real.pi)) ^ (m - 1) := by
  have hcont := circPowR_continuous (Bbase n) (Bbase_continuous n) m hm
  have hIO : MeasureTheory.IntegrableOn (circPowR (Bbase n) m) (Set.Ioc (-Real.pi) Real.pi) :=
    hcont.integrableOn_Ioc
  calc (∫ η in Set.Ioc (-Real.pi) Real.pi, circPowR (Bbase n) m η)
      ≤ ∫ _η in Set.Ioc (-Real.pi) Real.pi, (Gint n / (2 * Real.pi)) ^ (m - 1) := by
        apply MeasureTheory.setIntegral_mono_on hIO
          (MeasureTheory.integrableOn_const
            (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioc
        intro η _; exact Pb_le_geom n hn m hm η
    _ = (2 * Real.pi) * (Gint n / (2 * Real.pi)) ^ (m - 1) := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by linarith [Real.pi_pos]),
          smul_eq_mul]; ring

/-! ## Inductive-step side conditions. -/

/-- Per-`B` integrability of the LEFT-distribution integrand
`η ↦ (multM k B · αC^{k+B} · circPowR (Bbase n)(k+B) η) · Genv n (ξ - η)` on the window. -/
theorem stepL_int (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (B : ℕ) :
    MeasureTheory.IntegrableOn
      (fun η => ((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η)
        * Genv n (ξ - η)) (Set.Ioc (-Real.pi) Real.pi) := by
  have hcont : Continuous (fun η =>
      ((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * Genv n (ξ - η)) := by
    apply Continuous.mul
    · exact (continuous_const.mul
        (circPowR_continuous (Bbase n) (Bbase_continuous n) (k + B) (by omega)))
    · exact (Genv_continuous n hn).comp (continuous_const.sub continuous_id)
  exact hcont.integrableOn_Ioc

/-- Per-`a` integrability of the RIGHT-distribution integrand
`η ↦ (αC^{a+1} · circPowR (Bbase n)(a+1) η) · circPowR (Bbase n)(k+B) (ξ - η)` on the window. -/
theorem stepR_int (n : ℕ) (k B : ℕ) (hkB : 1 ≤ k + B) (ξ : ℝ) (a : ℕ) :
    MeasureTheory.IntegrableOn
      (fun η => ((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
        * circPowR (Bbase n) (k + B) (ξ - η)) (Set.Ioc (-Real.pi) Real.pi) := by
  have hcont : Continuous (fun η =>
      ((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
        * circPowR (Bbase n) (k + B) (ξ - η)) := by
    apply Continuous.mul
    · exact continuous_const.mul
        (circPowR_continuous (Bbase n) (Bbase_continuous n) (a + 1) (by omega))
    · exact (circPowR_continuous (Bbase n) (Bbase_continuous n) (k + B) hkB).comp
        (continuous_const.sub continuous_id)
  exact hcont.integrableOn_Ioc

/-- LEFT-distribution summability: `B ↦ ∫_{Ioc} ‖u_B η · Genv(ξ-η)‖` is summable,
where `u_B η = multM k B · αC^{k+B} · circPowR (Bbase n)(k+B) η`. Dominated by
`M · multM k B · αC^{k+B} · (2π)(Gint/2π)^{k+B-1}`, geometric–binomial in B. -/
theorem stepL_summ (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    Summable (fun B : ℕ => ∫ η in Set.Ioc (-Real.pi) Real.pi,
      ‖((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η)
        * Genv n (ξ - η)‖) := by
  obtain ⟨M, hM0, hMle⟩ := Genv_bdd n hn
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  -- The dominating summable sequence in B.
  have hdom : Summable (fun B : ℕ =>
      M * ((multM k B : ℝ) * alphaC n ^ (k + B) *
        ((2 * Real.pi) * (Gint n / (2 * Real.pi)) ^ (k + B - 1)))) := by
    have hexp := expansion_summable n hn k hk (0 : ℝ)
    -- recombine the bound into a single summable sequence using Pb_le_geom as a constant family
    set q : ℝ := alphaC n * Gint n / (2 * Real.pi) with hq
    have hqnn : 0 ≤ q := alphaG_div_two_pi_nonneg n hn
    have hqlt : q < 1 := alphaG_div_two_pi_lt_one n hn
    have hbase : Summable (fun B : ℕ => ((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B) :=
      summable_choose_mul_geometric_of_norm_lt_one (k - 1)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hqnn]; exact hqlt)
    have : Summable (fun B : ℕ =>
        (M * (2 * Real.pi) * alphaC n * q ^ (k - 1)) *
          (((B + (k - 1)).choose (k - 1) : ℝ) * q ^ B)) := hbase.mul_left _
    apply this.congr
    intro B
    rw [multM_choose k B hk, hq]
    rw [show alphaC n * Gint n / (2 * Real.pi) = alphaC n * (Gint n / (2 * Real.pi)) by
      rw [mul_div_assoc]]
    rw [mul_pow, mul_pow]
    rw [show alphaC n ^ (k + B) = alphaC n * (alphaC n ^ (k - 1) * alphaC n ^ B) by
      rw [← pow_add, ← pow_succ']; congr 1; omega]
    rw [show k + B - 1 = (k - 1) + B by omega, pow_add]
    ring
  apply Summable.of_nonneg_of_le (fun B => by positivity) _ hdom
  intro B
  -- Pull the constant nonneg coefficient out of the integral; bound by M times window integral.
  have hcB : (0 : ℝ) ≤ (multM k B : ℝ) * alphaC n ^ (k + B) := by positivity
  have hpt : ∀ η ∈ Set.Ioc (-Real.pi) Real.pi,
      ‖((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * Genv n (ξ - η)‖
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * circPowR (Bbase n) (k + B) η := by
    intro η _
    have hpb : 0 ≤ circPowR (Bbase n) (k + B) η :=
      circPowR_nonneg (Bbase n) (Bbase_nonneg n) (k + B) (by omega) η
    have hgv0 : 0 ≤ Genv n (ξ - η) :=
      Genv_nonneg n (ξ - η)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * Genv n (ξ - η)
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * M :=
      mul_le_mul_of_nonneg_left (hMle _) (by positivity)
    calc ((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * Genv n (ξ - η)
        ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * M := this
      _ = ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * circPowR (Bbase n) (k + B) η := by ring
  have hintw : MeasureTheory.IntegrableOn (circPowR (Bbase n) (k + B)) (Set.Ioc (-Real.pi) Real.pi) :=
    (circPowR_continuous (Bbase n) (Bbase_continuous n) (k + B) (by omega)).integrableOn_Ioc
  have hint_lhs : MeasureTheory.IntegrableOn
      (fun η => ‖((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η)
        * Genv n (ξ - η)‖) (Set.Ioc (-Real.pi) Real.pi) :=
    (stepL_int n hn k hk ξ B).norm
  calc (∫ η in Set.Ioc (-Real.pi) Real.pi,
        ‖((multM k B : ℝ) * alphaC n ^ (k + B) * circPowR (Bbase n) (k + B) η) * Genv n (ξ - η)‖)
      ≤ ∫ η in Set.Ioc (-Real.pi) Real.pi,
          ((multM k B : ℝ) * alphaC n ^ (k + B) * M) * circPowR (Bbase n) (k + B) η := by
        apply MeasureTheory.setIntegral_mono_on hint_lhs
          ((hintw.const_mul _)) measurableSet_Ioc hpt
    _ = ((multM k B : ℝ) * alphaC n ^ (k + B) * M) *
          ∫ η in Set.Ioc (-Real.pi) Real.pi, circPowR (Bbase n) (k + B) η := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ((multM k B : ℝ) * alphaC n ^ (k + B) * M) *
          ((2 * Real.pi) * (Gint n / (2 * Real.pi)) ^ (k + B - 1)) := by
        apply mul_le_mul_of_nonneg_left (circint_window_bound n hn (k + B) (by omega))
        positivity
    _ = M * ((multM k B : ℝ) * alphaC n ^ (k + B) *
          ((2 * Real.pi) * (Gint n / (2 * Real.pi)) ^ (k + B - 1))) := by ring

/-- RIGHT-distribution summability (fixed `B`): `a ↦ ∫_{Ioc} ‖v_a η · circPowR (Bbase n)(k+B)(ξ-η)‖`
is summable, where `v_a η = αC^{a+1} · circPowR (Bbase n)(a+1) η`. Dominated by
`(Gint/2π)^{k+B-1} · 2π · αC · q^a`, geometric in `a`. -/
theorem stepR_summ (n : ℕ) (hn : 1 ≤ n) (k B : ℕ) (hkB : 1 ≤ k + B) (ξ : ℝ) :
    Summable (fun a : ℕ => ∫ η in Set.Ioc (-Real.pi) Real.pi,
      ‖((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
        * circPowR (Bbase n) (k + B) (ξ - η)‖) := by
  have hann : 0 ≤ alphaC n := alphaC_nonneg n
  set q : ℝ := alphaC n * Gint n / (2 * Real.pi) with hq
  have hqnn : 0 ≤ q := alphaG_div_two_pi_nonneg n hn
  have hqlt : q < 1 := alphaG_div_two_pi_lt_one n hn
  have hC0 : 0 ≤ (Gint n / (2 * Real.pi)) ^ (k + B - 1) := by
    have : 0 ≤ Gint n / (2 * Real.pi) := by
      have := Gint_nonneg n; positivity
    positivity
  -- dominating geometric sequence in a
  have hdom : Summable (fun a : ℕ =>
      ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) * ((2 * Real.pi) * (alphaC n * q ^ a))) := by
    have hga : Summable (fun a : ℕ => alphaC n * q ^ a) :=
      (summable_geometric_of_lt_one hqnn hqlt).mul_left _
    exact (hga.mul_left (((Gint n / (2 * Real.pi)) ^ (k + B - 1)) * (2 * Real.pi))).congr
      (fun a => by ring)
  apply Summable.of_nonneg_of_le (fun a => by positivity) _ hdom
  intro a
  have hPbB : ∀ η, circPowR (Bbase n) (k + B) (ξ - η) ≤ (Gint n / (2 * Real.pi)) ^ (k + B - 1) :=
    fun η => Pb_le_geom n hn (k + B) hkB (ξ - η)
  have hint_lhs : MeasureTheory.IntegrableOn
      (fun η => ‖((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
        * circPowR (Bbase n) (k + B) (ξ - η)‖) (Set.Ioc (-Real.pi) Real.pi) :=
    (stepR_int n k B hkB ξ a).norm
  have hpt : ∀ η ∈ Set.Ioc (-Real.pi) Real.pi,
      ‖((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
        * circPowR (Bbase n) (k + B) (ξ - η)‖
        ≤ ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) *
            (alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η) := by
    intro η _
    have hpa : 0 ≤ circPowR (Bbase n) (a + 1) η :=
      circPowR_nonneg (Bbase n) (Bbase_nonneg n) (a + 1) (by omega) η
    have hpb : 0 ≤ circPowR (Bbase n) (k + B) (ξ - η) :=
      circPowR_nonneg (Bbase n) (Bbase_nonneg n) (k + B) hkB (ξ - η)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
            * circPowR (Bbase n) (k + B) (ξ - η)
        ≤ ((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η)) *
            (Gint n / (2 * Real.pi)) ^ (k + B - 1) :=
          mul_le_mul_of_nonneg_left (hPbB η) (by positivity)
      _ = ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) *
            (alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η) := by ring
  have hintw : MeasureTheory.IntegrableOn (circPowR (Bbase n) (a + 1)) (Set.Ioc (-Real.pi) Real.pi) :=
    (circPowR_continuous (Bbase n) (Bbase_continuous n) (a + 1) (by omega)).integrableOn_Ioc
  calc (∫ η in Set.Ioc (-Real.pi) Real.pi,
        ‖((alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η))
          * circPowR (Bbase n) (k + B) (ξ - η)‖)
      ≤ ∫ η in Set.Ioc (-Real.pi) Real.pi,
          ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) *
            (alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η) := by
        apply MeasureTheory.setIntegral_mono_on hint_lhs _ measurableSet_Ioc hpt
        exact (hintw.const_mul _).const_mul _
    _ = ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) * (alphaC n ^ (a + 1) *
          ∫ η in Set.Ioc (-Real.pi) Real.pi, circPowR (Bbase n) (a + 1) η) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) * (alphaC n ^ (a + 1) *
          ((2 * Real.pi) * (Gint n / (2 * Real.pi)) ^ (a + 1 - 1))) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply mul_le_mul_of_nonneg_left (circint_window_bound n hn (a + 1) (by omega))
        positivity
    _ = ((Gint n / (2 * Real.pi)) ^ (k + B - 1)) * ((2 * Real.pi) * (alphaC n * q ^ a)) := by
        rw [hq, show a + 1 - 1 = a by omega]
        rw [show alphaC n * Gint n / (2 * Real.pi) = alphaC n * (Gint n / (2 * Real.pi)) by
          rw [mul_div_assoc]]
        rw [mul_pow]
        rw [show alphaC n ^ (a + 1) = alphaC n * alphaC n ^ a by rw [← pow_succ']]
        ring

/-! ## The circular multiplicity expansion (Step 1, circular half). -/

/-- **Circular multiplicity expansion.** For `k ≥ 1`,
`circPowR (Genv n) k ξ = ∑'_m (multM k m) · αC^{k+m} · circPowR (Bbase n)(k+m) ξ`. -/
theorem circ_expansion (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → ∀ ξ : ℝ,
      circPowR (Genv n) k ξ
        = ∑' m : ℕ, ((multM k m : ℝ) * alphaC n ^ (k + m)) * circPowR (Bbase n) (k + m) ξ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro ξ; exact expansion_base n ξ
  | succ k hk ih =>
    intro ξ
    -- Unfold the (k+1)-st circular power.
    rw [circPowR_succ_of_pos (Genv n) k hk]
    -- Rewrite the left argument as the IH series.
    have hleft : circPowR (Genv n) k
        = fun η => ∑' B : ℕ,
            ((multM k B : ℝ) * alphaC n ^ (k + B)) * circPowR (Bbase n) (k + B) η := by
      funext η; exact ih η
    rw [hleft]
    beta_reduce
    -- LEFT-distribution: pull the tsum (over B) out of circConvR's left argument.
    rw [circConvR_tsum_left
        (fun B η => ((multM k B : ℝ) * alphaC n ^ (k + B)) * circPowR (Bbase n) (k + B) η)
        (Genv n) ξ (fun B => stepL_int n hn k hk ξ B) (stepL_summ n hn k hk ξ)]
    -- Per-B: pull the scalar out, then distribute the RIGHT argument (Genv = ∑'_a v_a).
    have hperB : ∀ B : ℕ,
        circConvR (fun η => ((multM k B : ℝ) * alphaC n ^ (k + B)) * circPowR (Bbase n) (k + B) η)
            (Genv n) ξ
          = ∑' a : ℕ, ((multM k B : ℝ) * alphaC n ^ (k + B))
              * (alphaC n ^ (a + 1) * circPowR (Bbase n) ((k + B) + (a + 1)) ξ) := by
      intro B
      -- scalar pull-out (left)
      rw [circConvR_const_mul_left]
      -- Genv n = fun η => ∑'_a αC^{a+1} circPowR (Bbase n)(a+1) η
      have hGenv : Genv n = fun η => ∑' a : ℕ, alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η := by
        funext η; rfl
      rw [hGenv]
      -- RIGHT-distribution over a.
      have hkB1 : 1 ≤ k + B := by omega
      rw [circConvR_tsum_right (circPowR (Bbase n) (k + B))
          (fun a η => alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) η) ξ
          (fun x => circPowR_periodic (Bbase n) (Bbase_periodic n) (k + B) hkB1 x)
          (fun a x => by
            simp only
            rw [circPowR_periodic (Bbase n) (Bbase_periodic n) (a + 1) (by omega) x])
          (fun x => by
            show (∑' a : ℕ, alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) (x + 2 * Real.pi))
              = ∑' a : ℕ, alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) x
            apply tsum_congr; intro a
            rw [circPowR_periodic (Bbase n) (Bbase_periodic n) (a + 1) (by omega) x])
          (fun a => by
            have := stepR_int n k B hkB1 ξ a
            -- circConvR's left arg is circPowR(Bbase)(k+B); its integrand uses u_a · f(ξ-η)
            -- with f = circPowR(Bbase)(k+B), u_a η = αC^{a+1}·circPowR(Bbase)(a+1) η. Matches.
            exact this)
          (stepR_summ n hn k B hkB1 ξ)]
      -- now: ∑'_a (multM k B · αC^{k+B}) · circConvR (circPowR(Bbase)(k+B)) (v_a) ξ
      rw [tsum_mul_left]
      apply congrArg
      apply tsum_congr; intro a
      -- circConvR (circPowR(Bbase)(k+B)) (fun η => αC^{a+1}·circPowR(Bbase)(a+1) η) ξ
      -- pull αC^{a+1} out (it is in the RIGHT argument) via commutativity.
      have hkB1' : 1 ≤ k + B := hkB1
      rw [circConvR_comm
            (fun x => circPowR_periodic (Bbase n) (Bbase_periodic n) (k + B) hkB1' x)
            (fun x => by
              show alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) (x + 2 * Real.pi)
                = alphaC n ^ (a + 1) * circPowR (Bbase n) (a + 1) x
              rw [circPowR_periodic (Bbase n) (Bbase_periodic n) (a + 1) (by omega) x])]
      rw [circConvR_const_mul_left]
      -- now circConvR (circPowR(Bbase)(a+1)) (circPowR(Bbase)(k+B)) ξ ;
      -- recombine to circPowR(Bbase)((a+1)+(k+B)) via circPowR_add, then reorder.
      rw [circPowR_add (goodP_Bbase n) (a + 1) (k + B) (by omega) hkB1']
      rw [show (a + 1) + (k + B) = (k + B) + (a + 1) by omega]
    -- Substitute the per-B identity and collapse via step_collapse.
    rw [tsum_congr hperB]
    rw [step_collapse (alphaC n) (fun m => circPowR (Bbase n) m ξ) k hk (step_summable n hn k hk ξ)]

end CircMultiplicityExpansion
