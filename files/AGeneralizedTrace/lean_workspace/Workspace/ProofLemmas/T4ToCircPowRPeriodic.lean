import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.KwayFactorSummable
import Workspace.ProofLemmas.PerFactorFourierModulus
import Workspace.ProofLemmas.PerFactorFTModulus
import Workspace.ProofLemmas.PerFactorFTEnvelope
import Workspace.ProofLemmas.FTConvPow
import Workspace.ProofLemmas.FactorFTSeries
import Workspace.ProofLemmas.CircConvInfra
import Workspace.ProofLemmas.CircConvMono
import Workspace.ProofLemmas.KwayCircModulusStep
import Workspace.ProofLemmas.KModEnvBound
import Workspace.ProofLemmas.KModEnvSingleDominated
import Workspace.ProofLemmas.KwayFTAsKConv
import Workspace.ProofLemmas.KwayLHSToKModEnv
import Workspace.ProofLemmas.PeriodicBaseKfoldPeriodisation

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Bounding the bridge LHS by the k-fold CIRCULAR self-power of the PERIODIC envelope `G`

This file builds the periodic-base analogue of the (structurally-broken,
compact-support-based) `kModEnv → kEnvOf → kEnvOfPeriodisation` chain (F32/F43).
It stays with the **periodic** per-factor Fourier modulus `G` throughout (no
compact-support restriction `e`), so that the correct foundation
`PeriodicBaseKfoldPeriodisation.periodise_kfold` can be applied downstream.

## The common periodic per-factor envelope `G`

The per-factor Fourier transform expands as a circular-geometric series
(`FactorFTSeries.factor_FT_circPow_series`):

  `FT (factor n ℓj) η = ∑' b, α^(b+1) · circPow (FT (binAtom n ℓj)) (b+1) η`.

The modulus of `FT (binAtom n ℓj)` is **ℓj-independent**: by
`PerFactorFTModulus.FT_binAtom`, `FT (binAtom n ℓj) η = e^{iηc} · FT (pBinC n) η`
with `c = (n-1)/4 + ℓj` a unit-modulus phase, so
`‖FT (binAtom n ℓj) η‖ = ‖FT (pBinC n) η‖ =: Bbase n η` for **every** `η` and
**every** `ℓj`.

We define the common periodic envelope as the circular-geometric series of the
modulus-triangle-bounded circular powers of `Bbase`:

  `Genv n η := ∑' b, α^(b+1) · circPowR (Bbase n) (b+1) η`,

where `circPowR` is the real k-fold circular self-power
(`PeriodicBaseKfoldPeriodisation.circPowR`).  Taking moduli of the per-factor
series and bounding `‖circPow (FT binAtom) (b+1)‖ ≤ circPowR (Bbase n) (b+1)`
(iterated modulus-triangle for circular convolution) gives the per-factor bound

  `‖FT (factor n ℓj) η‖ ≤ Genv n η`   for every `η`, **uniformly in `ℓj`**.

Since `G` is ℓj-free, it dominates `‖FT (fseq n k ℓ j)‖` for every factor index
`j < k`, which is exactly the hypothesis `kModEnv_le_kEnvOf` consumes.
-/

namespace T4ToCircPowRPeriodic

open KFoldConvolutionTheorem
open KwayFactorSummable
open PerFactorFourierModulus
open PerFactorFTModulus
open PerFactorFTEnvelope
open FTConvPow
open FactorFTSeries
open CircConvInfra
open KModEnvBound
open KModEnvSingleDominated
open KwayFTAsKConv
open PeriodicBaseKfoldPeriodisation

/-! ## The ℓj-free base modulus `Bbase`. -/

/-- The common per-factor base Fourier modulus, `Bbase n η := ‖FT (pBinC n) η‖`.
It is `ℓj`-free: every `‖FT (binAtom n ℓj) η‖` equals it (the shift phase is of
unit modulus). -/
noncomputable def Bbase (n : ℕ) (η : ℝ) : ℝ := ‖FT (pBinC n) η‖

theorem Bbase_nonneg (n : ℕ) (η : ℝ) : 0 ≤ Bbase n η := norm_nonneg _

/-- `pBinC n` has finite support (vanishes off `{0,…,n}`). -/
theorem pBinC_support (n : ℕ) (s : ℤ) (hs : pBinC n s ≠ 0) :
    s ∈ Finset.Icc (0 : ℤ) (n : ℤ) := by
  by_contra hmem
  apply hs
  unfold pBinC
  rw [if_neg]
  rw [Finset.mem_Icc, not_and_or] at hmem
  rintro ⟨h1, h2⟩
  rcases hmem with hlo | hhi
  · omega
  · omega

/-- `FT (pBinC n)` is continuous (finite support). -/
theorem FT_pBinC_continuous (n : ℕ) : Continuous (fun η : ℝ => FT (pBinC n) η) :=
  FT_continuous_of_finite_support (pBinC n) (Finset.Icc (0 : ℤ) (n : ℤ))
    (pBinC_support n)

/-- `Bbase n` is continuous. -/
theorem Bbase_continuous (n : ℕ) : Continuous (Bbase n) :=
  (FT_pBinC_continuous n).norm

/-- `FT (pBinC n)` is `2π`-periodic. -/
theorem FT_pBinC_periodic (n : ℕ) (η : ℝ) :
    FT (pBinC n) (η + 2 * Real.pi) = FT (pBinC n) η :=
  FT_periodic (pBinC n) η

/-- `Bbase n` is `2π`-periodic. -/
theorem Bbase_periodic (n : ℕ) (η : ℝ) :
    Bbase n (η + 2 * Real.pi) = Bbase n η := by
  unfold Bbase
  rw [FT_pBinC_periodic n η]

/-- **ℓj-independence of the per-factor base modulus.**  For every `η` and every
`ℓj`, `‖FT (binAtom n ℓj) η‖ = Bbase n η`.  Holds on all of `ℝ` (not just
`[-π,π]`): the shift phase `e^{iηc}` is of unit modulus. -/
theorem FT_binAtom_norm_eq_Bbase (n : ℕ) (ℓj : ℕ) (η : ℝ) :
    ‖FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η‖ = Bbase n η := by
  unfold Bbase
  rw [FT_binAtom n ℓj η, norm_mul]
  have h_phase : ‖Complex.exp (Complex.I * (η : ℂ)
      * ((((n : ℤ) - 1) / 4 + (ℓj : ℤ) : ℤ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (Complex.I * (η : ℂ)
        * ((((n : ℤ) - 1) / 4 + (ℓj : ℤ) : ℤ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [h_phase, one_mul]

/-! ## Properties of the complex circular self-power `circPow F`. -/

/-- `circPow F m` is continuous, for continuous `F` and `m ≥ 1`. -/
theorem circPow_continuous (F : ℝ → ℂ) (hF : Continuous F) :
    ∀ m, 1 ≤ m → Continuous (fun ξ => circPow F m ξ) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [circPow_one]; exact hF
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [circPow_succ_succ]
      simp only [circConvC]
      exact circConv_continuous _ _ (ih (by omega)) hF

/-- `circPow F m` is `2π`-periodic, for `2π`-periodic `F` and `m ≥ 1`. -/
theorem circPow_periodic (F : ℝ → ℂ)
    (hFper : ∀ x, F (x + 2 * Real.pi) = F x) :
    ∀ m, 1 ≤ m → ∀ ξ, circPow F m (ξ + 2 * Real.pi) = circPow F m ξ := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [circPow_one]; exact hFper ξ
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [circPow_succ_succ]
      simp only [circConvC]
      exact circConv_periodic (circPow F (m' + 1)) F hFper ξ

/-! ## Properties of the real circular self-power `circPowR g`. -/

/-- `circPowR g m` is non-negative, for non-negative `g` and `m ≥ 1`. -/
theorem circPowR_nonneg (g : ℝ → ℝ) (hg_nn : ∀ x, 0 ≤ g x) :
    ∀ m, 1 ≤ m → ∀ ξ, 0 ≤ circPowR g m ξ := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [circPowR_one]; exact hg_nn ξ
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [circPowR_succ_succ]
      exact circConvR_nonneg _ _ (fun x => ih (by omega) x) hg_nn ξ

/-- `circPowR g m` is continuous, for continuous `g` and `m ≥ 1`. -/
theorem circPowR_continuous (g : ℝ → ℝ) (hg : Continuous g) :
    ∀ m, 1 ≤ m → Continuous (fun ξ => circPowR g m ξ) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [circPowR_one]; exact hg
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [circPowR_succ_succ]
      exact circConvR_continuous _ _ (ih (by omega)) hg

/-- `circPowR g m` is `2π`-periodic, for `2π`-periodic `g` and `m ≥ 1`. -/
theorem circPowR_periodic (g : ℝ → ℝ)
    (hg_per : ∀ x, g (x + 2 * Real.pi) = g x) :
    ∀ m, 1 ≤ m → ∀ ξ, circPowR g m (ξ + 2 * Real.pi) = circPowR g m ξ := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [circPowR_one]; exact hg_per ξ
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [circPowR_succ_succ]
      exact circConvR_periodic (circPowR g (m' + 1)) g hg_per ξ

/-! ## Iterated modulus-triangle: `‖circPow F m‖ ≤ circPowR ‖F‖ m`. -/

open KwayCircModulusStep in
/-- **Iterated modulus-triangle for the circular self-power.**  For a continuous,
`2π`-periodic `F : ℝ → ℂ`, the modulus of the `m`-fold circular self-power is
bounded by the `m`-fold real circular self-power of the modulus `‖F‖`:

  `‖circPow F m η‖ ≤ circPowR (fun x => ‖F x‖) m η`   for every `η`, `m ≥ 1`.

This is `ModulusOfCircularConvolutionTriangle` (packaged as
`circConv_modulus_envelope`) iterated through the circular-power recurrence, with
the inductive envelope `E := circPowR ‖F‖ (m+1)`. -/
theorem circPow_norm_le_circPowR (F : ℝ → ℂ)
    (hF : Continuous F) (hFper : ∀ x, F (x + 2 * Real.pi) = F x) :
    ∀ m, 1 ≤ m → ∀ η, ‖circPow F m η‖ ≤ circPowR (fun x => ‖F x‖) m η := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ η
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [circPow_one, circPowR_one]
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      have ih' : ∀ x, ‖circPow F (m' + 1) x‖ ≤ circPowR (fun x => ‖F x‖) (m' + 1) x :=
        ih (by omega)
      rw [circPow_succ_succ, circPowR_succ_succ]
      simp only [circConvC, circConvR]
      -- ‖circConv (circPow F (m'+1)) F η‖
      --   ≤ (1/2π) ∫ E·‖F(η-·)‖  = (1/2π) ∫ (circPowR ‖F‖ (m'+1))·‖F(η-·)‖
      have hbound := circConv_modulus_envelope
        (circPow F (m' + 1)) F (circPowR (fun x => ‖F x‖) (m' + 1))
        (circPow_periodic F hFper (m' + 1) (by omega))
        hFper
        ((circPow_continuous F hF (m' + 1) (by omega)).continuousOn.integrableOn_compact
          isCompact_Icc)
        hF
        ((circPowR_continuous (fun x => ‖F x‖) hF.norm (m' + 1)
          (by omega)).continuousOn.integrableOn_compact isCompact_Icc)
        ih'
        η
      -- hbound's RHS is exactly (1/2π) ∫ (circPowR ‖F‖ (m'+1)) η' · ‖F (η - η')‖.
      exact hbound

/-! ## `kEnvOf` and `circPowR` are the same k-fold circular self-power. -/

/-- The k-fold circular self-convolution `kEnvOf e k` (from `KModEnvSingleDominated`)
coincides with the real circular self-power `circPowR e k` (from
`PeriodicBaseKfoldPeriodisation`): they obey the same recurrence. -/
theorem kEnvOf_eq_circPowR (e : ℝ → ℝ) :
    ∀ k, kEnvOf e k = circPowR e k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    match k with
    | 0 => rfl
    | (k + 1) =>
      rw [kEnvOf_succ_succ, circPowR_succ_succ, ih]

/-! ## The k-fold circular-modulus bound by `circPowR` of a common periodic envelope. -/

/-- **The bridge LHS is bounded by the k-fold circular self-power of any common
periodic envelope `G`.**

If `G : ℝ → ℝ` is non-negative, continuous, and pointwise dominates every per-factor
Fourier modulus `‖FT (fun r => (factor n (ℓ j) r : ℂ)) η‖` (for `j < k`), then for
every `k ≥ 1` and `ξ`,

  `‖∑' r, (∏ j, factor n (ℓ j) r) · e^{-iξr}‖ ≤ circPowR G k ξ`.

This is the periodic-base analogue of the (broken, compact-support-based)
`T4_modulus_le_kModEnv`+`kModEnv_le_kEnvOf` chain — staying with the PERIODIC `G`
throughout.  It composes:
* `KwayLHSToKModEnv.T4_modulus_le_kModEnv` : `LHS ≤ kModEnv (fseq n k ℓ) k ξ`;
* `KModEnvSingleDominated.kModEnv_le_kEnvOf` : `kModEnv (fseq …) k ξ ≤ kEnvOf G k ξ`;
* `kEnvOf_eq_circPowR` : `kEnvOf G k = circPowR G k`.

The per-factor domination hypothesis is exactly what the common periodic envelope
`Genv` supplies (`FT_factor_norm_le_Genv` below); the modulus is `ℓj`-free, so a
single `G` dominates every factor. -/
theorem T4_modulus_le_circPowR_of_dom (n k : ℕ) (ℓ : Fin k → ℕ) (hk : 1 ≤ k)
    (G : ℝ → ℝ) (hG_nn : ∀ x, 0 ≤ G x) (hG_cont : Continuous G)
    (hdom : ∀ j : ℕ, ∀ η, ‖FT (fseq n k ℓ j) η‖ ≤ G η)
    (ξ : ℝ) :
    ‖∑' r : ℤ, (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
      ≤ circPowR G k ξ := by
  -- Step 1: LHS ≤ kModEnv (fseq n k ℓ) k ξ.
  have h1 := KwayLHSToKModEnv.T4_modulus_le_kModEnv n k ℓ hk ξ
  -- Step 2: kModEnv (fseq n k ℓ) k ξ ≤ kEnvOf G k ξ.
  have h2 := kModEnv_le_kEnvOf (fseq n k ℓ) G
    (fun j => KwayLHSToKModEnv.FT_fseq_continuous n k ℓ j)
    (fun j x => KwayLHSToKModEnv.FT_fseq_periodic n k ℓ j x)
    hG_nn hG_cont hdom k hk ξ
  -- Step 3: kEnvOf G k = circPowR G k.
  rw [kEnvOf_eq_circPowR] at h2
  exact le_trans h1 h2

/-! ## The common periodic per-factor envelope `Genv` and the per-factor bound. -/

/-- **The common periodic per-factor Fourier-modulus envelope.**

`Genv n η := ∑' b, α^(b+1) · circPowR (Bbase n) (b+1) η`,

the circular-geometric series of the real circular self-powers of the `ℓj`-free base
modulus `Bbase n = ‖FT (pBinC n)‖`.  This is the TRUE periodic per-factor envelope
(NOT the clean `α·|cos|^n`, which F43 disproved dominates the factor): it is the
modulus-triangle bound of the per-factor circular-geometric series
`FactorFTSeries.factor_FT_circPow_series`. -/
noncomputable def Genv (n : ℕ) (η : ℝ) : ℝ :=
  ∑' b : ℕ, alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η

/-- **Per-factor modulus bound by the common periodic envelope `Genv`.**

Taking moduli of the per-factor circular-geometric series
(`FactorFTSeries.factor_FT_circPow_series`) and bounding each circular power via the
iterated modulus-triangle (`circPow_norm_le_circPowR`, using the `ℓj`-independence
`FT_binAtom_norm_eq_Bbase`) gives, for every `η`,

  `‖FT (fun r => (factor n ℓj r : ℂ)) η‖ ≤ Genv n η`.

The two summability side-conditions (of the norm series and of the `Genv` series at
`η`) are taken as hypotheses; they are the geometric-decay facts of the
circular-geometric envelope, discharged from `α · binAtom ≤ 1/2` and the
sup-norm bound `Bbase ≤ 1`. -/
theorem FT_factor_norm_le_Genv (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ)
    (hsum_norm : Summable (fun b : ℕ =>
      ‖(alphaC n : ℂ) ^ (b + 1)
        * circPow (FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ))) (b + 1) η‖))
    (hsum_Genv : Summable (fun b : ℕ =>
      alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η)) :
    ‖FT (fun r => ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)) η‖ ≤ Genv n η := by
  rw [factor_FT_circPow_series n hn ℓj η]
  -- ‖∑' b, T b‖ ≤ ∑' b, ‖T b‖.
  refine le_trans (norm_tsum_le_tsum_norm hsum_norm) ?_
  -- termwise: ‖α^(b+1) · circPow (FT binAtom) (b+1) η‖ ≤ α^(b+1) · circPowR (Bbase n) (b+1) η.
  apply Summable.tsum_le_tsum _ hsum_norm hsum_Genv
  intro b
  -- LHS = |α|^(b+1) · ‖circPow (FT binAtom) (b+1) η‖
  rw [norm_mul]
  have hα : ‖(alphaC n : ℂ) ^ (b + 1)‖ = alphaC n ^ (b + 1) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (alphaC_nonneg n)]
  rw [hα]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (alphaC_nonneg n) _)
  -- ‖circPow (FT binAtom) (b+1) η‖ ≤ circPowR (Bbase n) (b+1) η
  have hF_cont : Continuous (fun η : ℝ => FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η) :=
    FT_continuous_of_finite_support _
      (Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                  ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))))
      (binAtomC_support n ℓj)
  have hF_per : ∀ x, FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) (x + 2 * Real.pi)
      = FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) x :=
    fun x => FT_periodic _ x
  have htri := circPow_norm_le_circPowR
    (fun η => FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η) hF_cont hF_per (b + 1) (by omega) η
  -- circPowR (‖FT binAtom ·‖) (b+1) η = circPowR (Bbase n) (b+1) η, by ℓj-independence.
  have hbase : (fun x => ‖FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) x‖) = Bbase n := by
    funext x
    exact FT_binAtom_norm_eq_Bbase n ℓj x
  rw [hbase] at htri
  exact htri

/-- `Genv n` is non-negative (the series has non-negative terms). -/
theorem Genv_nonneg (n : ℕ) (η : ℝ) : 0 ≤ Genv n η := by
  unfold Genv
  apply tsum_nonneg
  intro b
  exact mul_nonneg (pow_nonneg (alphaC_nonneg n) _)
    (circPowR_nonneg (Bbase n) (Bbase_nonneg n) (b + 1) (by omega) η)

/-- **The bridge LHS is bounded by the k-fold circular self-power of the common
periodic envelope `Genv` (Lemma 7, G4 main bound).**

For `n, k ≥ 1`, given:
* `hGenv_cont` : `Genv n` is continuous (the geometric series of circular powers
  converges uniformly — the regularity side of the open analytic content);
* per-factor norm/`Genv`-series summability at every needed frequency
  (`hsum_norm`, `hsum_Genv`);

then for every `ξ`,

  `‖∑' r, (∏ j, factor n (ℓ j) r) · e^{-iξr}‖ ≤ circPowR (Genv n) k ξ`.

This is the precise periodic-base k-fold circular-modulus bound the downstream
`periodise_kfold` consumes (it then yields `circPowR (Genv n) k ξ ≤ ∑_s linPow G0 k
(ξ+2πs)`, leaving only the multinomial-collapse to the final agent).  The proof
chains `FT_factor_norm_le_Genv` (per-factor bound) into `T4_modulus_le_circPowR_of_dom`
(the full k-fold composition), using the `ℓj`-freeness of `Genv` to dominate every
factor `fseq n k ℓ j`. -/
theorem T4_modulus_le_circPowR (n k : ℕ) (ℓ : Fin k → ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hGenv_cont : Continuous (Genv n))
    (hsum_norm : ∀ (ℓj : ℕ) (η : ℝ), Summable (fun b : ℕ =>
      ‖(alphaC n : ℂ) ^ (b + 1)
        * circPow (FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ))) (b + 1) η‖))
    (hsum_Genv : ∀ (η : ℝ), Summable (fun b : ℕ =>
      alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η))
    (ξ : ℝ) :
    ‖∑' r : ℤ, (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
      ≤ circPowR (Genv n) k ξ := by
  apply T4_modulus_le_circPowR_of_dom n k ℓ hk (Genv n) (Genv_nonneg n) hGenv_cont _ ξ
  -- per-factor domination, uniformly in j (Genv is ℓj-free).
  intro j η
  by_cases hj : j < k
  · -- fseq n k ℓ j = (factor n (ℓ ⟨j, hj⟩) ·: ℂ) for j < k.
    have hfun : fseq n k ℓ j
        = (fun r => ((KwayFactorSummable.factor n (ℓ ⟨j, hj⟩) r : ℝ) : ℂ)) := by
      funext r
      simp only [fseq, KwayFactorSummable.fcx, dif_pos hj]
    rw [hfun]
    exact FT_factor_norm_le_Genv n hn (ℓ ⟨j, hj⟩) η
      (hsum_norm (ℓ ⟨j, hj⟩) η) (hsum_Genv η)
  · -- fseq n k ℓ j = 0 for j ≥ k, so ‖FT 0‖ = 0 ≤ Genv.
    have hfun : fseq n k ℓ j = (fun _ : ℤ => (0 : ℂ)) := by
      funext r
      simp only [fseq, KwayFactorSummable.fcx, dif_neg hj]
    rw [hfun]
    have hFT0 : FT (fun _ : ℤ => (0 : ℂ)) η = 0 := by
      unfold FT; simp
    rw [hFT0, norm_zero]
    exact Genv_nonneg n η

end T4ToCircPowRPeriodic
