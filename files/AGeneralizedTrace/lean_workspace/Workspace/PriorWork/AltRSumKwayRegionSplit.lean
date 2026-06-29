-- CONDITIONAL k ≥ 1 region-split modulus assembly for Lemma 8
-- (`AltRSumFourierBound`), Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1,
-- §3, lines 362-382. SORRY-FREE.
--
-- GOAL.  Discharge the `hFT` hypothesis of
-- `AltRSumFourierBoundKway.altRSum_fourier_bound_of_kway` (the k ≥ 1 Lemma-8
-- assembly) by BUILDING the region-split modulus bound
--
--   ‖fullCleanFT(π)‖ ≤ B_exp + B_Fou
--
-- as a CONDITIONAL lemma `fullCleanFT_pi_modulus_bound_of_kwayTail`.  The
-- genuinely-analytic Lemma-7 input (the k-way Fourier tail bound, wrapped by
-- `AltRSumKwayFourierBridge.kwayFactor_fourier_tail_bound`) is taken as EXPLICIT
-- HYPOTHESES `hkwayTail` / `hkwayL1` on `kwayFT`, rather than as `sorry`.  The
-- 3-binom `cleanFT` modulus on each region (the B_exp main term, mirroring the
-- proved-at-π k=0 machinery `AltRSumEmptyOuterBound.cleanFT_pi_abs_le_Couter`)
-- is likewise taken as a region hypothesis `hcleanRegion`.
--
-- SORRY-FREE CONTENT WE LAND HERE:
--   (0) Finset↔tuple reindex bridge: `kwayProd` (a `Finset ℕ` product of
--       `ellFactor`) equals the `Fin k → ℕ`-tuple product
--       `kwayFactor_fourier_tail_bound` consumes (via `Finset.orderEmbOfFin`).
--   (1) `kwayProd` is finitely supported (nonempty ℓ) ⇒ ℓ¹ (ℝ and ℂ-cast).
--   (2) `fullCleanFT(ξ) = cleanFT ⊛ kwayFT`  (one `ConvolutionTheoremDiscrete`).
--   (3) `‖fullCleanFT(π)‖ ≤ (1/2π) ∫ ‖cleanFT η‖·‖kwayFT(π-η)‖`
--       (`ModulusOfCircularConvolutionTriangle`; periodicity + integrability of
--       both factors proved from finite support).
--   (4) The CONDITIONAL region split → `B_exp + B_Fou`.
--   (5) Composition: feed the result to `altRSum_fourier_bound_of_kway` to obtain
--       the k≥1 `AltRSumFourierBound` conclusion, conditional on the kway/clean
--       region hypotheses.
--
-- We do NOT import `SublemmaFourierKway` directly (it is being edited
-- concurrently).  We import `T4L1NormBound` only for the support fact
-- `ellFactor_zero_of_out_support` (that file imports only Mathlib + the type +
-- `BinomialPmfMaxBound`; NOT Lemma 7).
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.AltRSumEmptyFourierBridge
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.ConvolutionTheoremDiscrete
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle
import Workspace.PriorWork.AltRSumFourierBoundKway
import Workspace.ProofLemmas.T4L1NormBound

set_option maxHeartbeats 1600000

namespace Workspace.PriorWork.AltRSumKwayRegionSplit

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.AltRSumEmptyFourierBridge
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumFourierBoundKway

/-! ### (0) The Finset↔tuple reindex bridge -/

/-- **Finset→tuple product reindex.** For a finite index set `ℓ` of cardinality
`k`, the `Fin k → ℕ` product of `ellFactor` along the order embedding
`ℓ.orderEmbOfFin hk` equals `kwayProd n α ℓ r` (the `Finset ℕ` product) — the
exact tuple object `AltRSumKwayFourierBridge.kwayFactor_fourier_tail_bound`
consumes. -/
theorem kwayProd_eq_tupleProd (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (r : ℤ)
    (k : ℕ) (hk : ℓ.card = k) :
    (∏ i : Fin k, ellFactor n α r (((ℓ.orderEmbOfFin hk) i) - 1))
      = kwayProd n α ℓ r := by
  unfold kwayProd
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin k)), ∀ y ∈ (Finset.univ : Finset (Fin k)),
      (ℓ.orderEmbOfFin hk) x = (ℓ.orderEmbOfFin hk) y → x = y := by
    intro x _ y _ hxy
    exact (ℓ.orderEmbOfFin hk).injective hxy
  have key : (∏ j ∈ (Finset.univ : Finset (Fin k)).image (ℓ.orderEmbOfFin hk),
      ellFactor n α r (j - 1))
      = ∏ i : Fin k, ellFactor n α r (((ℓ.orderEmbOfFin hk) i) - 1) :=
    Finset.prod_image hinj
  rw [Finset.image_orderEmbOfFin_univ ℓ hk] at key
  exact key.symm

/-- **The order embedding of a Finset is strictly increasing.** (Restated in the
shape `kwayFactor_fourier_tail_bound`'s `hℓ_strict` hypothesis expects.) -/
theorem orderEmbOfFin_strict (ℓ : Finset ℕ) (k : ℕ) (hk : ℓ.card = k) :
    ∀ i j : Fin k, i.val < j.val →
      (ℓ.orderEmbOfFin hk) i < (ℓ.orderEmbOfFin hk) j := by
  intro i j hij
  exact (ℓ.orderEmbOfFin hk).strictMono hij

/-- **Each enumerated element lies in `ℓ`.** Combined with a range hypothesis on
`ℓ`, transfers element-wise range bounds (`1 ≤ ℓ_i ≤ (n-1)/2`) to the tuple. -/
theorem orderEmbOfFin_mem (ℓ : Finset ℕ) (k : ℕ) (hk : ℓ.card = k) (i : Fin k) :
    (ℓ.orderEmbOfFin hk) i ∈ ℓ :=
  Finset.orderEmbOfFin_mem ℓ hk i

/-! ### (1) `kwayProd` is finitely supported ⇒ ℓ¹ (nonempty ℓ) -/

/-- **Support window of `kwayProd`.** Off the window
`Icc (-(n/4) - j₀) (n - n/4 - j₀)` (for any chosen `j₀ ∈ ℓ`), the factor
`ellFactor n α r j₀` vanishes, hence so does the whole product. -/
theorem kwayProd_off_window_zero (n : ℕ) (α : ℝ) (ℓ : Finset ℕ)
    (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) (r : ℤ)
    (hr : r ∉ Finset.Icc (-(n / 4 : ℤ) - ((j₀ - 1 : ℕ) : ℤ)) ((n : ℤ) - (n / 4 : ℤ) - ((j₀ - 1 : ℕ) : ℤ))) :
    kwayProd n α ℓ r = 0 := by
  unfold kwayProd
  apply Finset.prod_eq_zero hj₀
  apply T4L1NormBoundAux.ellFactor_zero_of_out_support
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  rintro ⟨h1, h2⟩
  rcases hr with hlo | hhi <;> omega

/-- **`kwayProd` is summable in absolute value over `ℤ`** (finite support), for
nonempty `ℓ`. -/
theorem kwayProd_summable (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) :
    Summable (fun r : ℤ => ‖kwayProd n α ℓ r‖) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-(n / 4 : ℤ) - ((j₀ - 1 : ℕ) : ℤ)) ((n : ℤ) - (n / 4 : ℤ) - ((j₀ - 1 : ℕ) : ℤ)))
  intro b hb
  rw [kwayProd_off_window_zero n α ℓ j₀ hj₀ b hb, norm_zero]

/-- ℂ-cast summability of `kwayProd` (the ℓ¹ hypothesis the FT consumes). -/
theorem kwayProd_summable_complex (n : ℕ) (α : ℝ) (ℓ : Finset ℕ)
    (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) :
    Summable (fun r : ℤ => ‖((kwayProd n α ℓ r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((kwayProd n α ℓ r : ℝ) : ℂ)‖)
      = (fun r : ℤ => ‖kwayProd n α ℓ r‖) := by
    funext r; rw [Complex.norm_real]
  rw [h]
  exact kwayProd_summable n α ℓ j₀ hj₀

/-- ℂ-cast summability of `cleanThreeFactor` (finite support; ℓ¹ hypothesis the
FT consumes). -/
theorem cleanThreeFactor_summable_complex (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (fun r : ℤ => ‖((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ)‖)
      = (fun r : ℤ => ‖cleanThreeFactor n δ zMinus zPlus r‖) := by
    funext r; rw [Complex.norm_real]
  rw [h]
  exact cleanThreeFactor_summable n δ zMinus zPlus

/-! ### (2) The k-way factor Fourier transform `kwayFT` -/

/-- The complex ℤ-Fourier transform of the k-way product factor `kwayProd` at
frequency `ζ`. -/
noncomputable def kwayFT (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (ζ : ℝ) : ℂ :=
  ∑' r : ℤ, ((kwayProd n α ℓ r : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))

/-! ### (3) `fullCleanFT(ξ) = cleanFT ⊛ kwayFT`  (ConvolutionTheoremDiscrete) -/

/-- **Convolution identity for the full FT.** Writing `fullClean =
cleanThreeFactor · kwayProd`, the discrete convolution theorem expresses
`fullCleanFT(ξ)` as the circular convolution of `cleanFT` (the 3-binom atom FT)
and `kwayFT` (the k-way factor FT):

  fullCleanFT(ξ) = (1/2π) ∫_{-π}^{π} cleanFT(η) · kwayFT(ξ-η) dη.

One application of `ConvolutionTheoremDiscrete` to `(cleanThreeFactor : ℂ)`,
`(kwayProd : ℂ)`, both ℓ¹ by finite support (nonempty ℓ). -/
theorem fullCleanFT_eq_conv
    (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ)
    (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) (ξ : ℝ) :
    fullCleanFT n δ α zMinus zPlus ℓ ξ
      = (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            cleanFT n δ zMinus zPlus η * kwayFT n α ℓ (ξ - η) := by
  unfold fullCleanFT cleanFT kwayFT
  have hcongr : ∀ r : ℤ,
      ((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))
      = (((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ) *
          ((kwayProd n α ℓ r : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))) := by
    intro r
    unfold fullClean
    push_cast
    ring
  rw [tsum_congr hcongr]
  have hconv := ConvolutionTheoremDiscrete
    (fun r => ((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ))
    (fun r => ((kwayProd n α ℓ r : ℝ) : ℂ))
    (cleanThreeFactor_summable_complex n δ zMinus zPlus)
    (kwayProd_summable_complex n α ℓ j₀ hj₀)
    ξ
  rw [hconv]
  congr 1
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  congr 1
  apply tsum_congr
  intro r
  congr 2
  push_cast
  ring

/-! ### (4) Periodicity & integrability of `cleanFT` and `kwayFT` -/

/-- **`cleanFT` is 2π-periodic in ξ.** -/
theorem cleanFT_periodic (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (ξ : ℝ) :
    cleanFT n δ zMinus zPlus (ξ + 2 * Real.pi) = cleanFT n δ zMinus zPlus ξ := by
  unfold cleanFT
  exact discreteFT_periodic
    (fun r : ℤ => ((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ)) ξ

/-- **`kwayFT` is 2π-periodic in ζ.** -/
theorem kwayFT_periodic (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (ζ : ℝ) :
    kwayFT n α ℓ (ζ + 2 * Real.pi) = kwayFT n α ℓ ζ := by
  unfold kwayFT
  exact discreteFT_periodic (fun r : ℤ => ((kwayProd n α ℓ r : ℝ) : ℂ)) ζ

/-- **A finitely-supported discrete FT is continuous in ξ.** If `f : ℤ → ℝ`
vanishes off a finite set `s`, then `ξ ↦ ∑'_r (f r : ℂ)·exp(-(I·ξ·r))` is a finite
sum of continuous exponentials, hence continuous. -/
theorem finiteSupport_FT_continuous (f : ℤ → ℝ) (s : Finset ℤ)
    (hsupp : ∀ r ∉ s, f r = 0) :
    Continuous (fun ξ : ℝ =>
      ∑' r : ℤ, ((f r : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))) := by
  have heq : (fun ξ : ℝ =>
      ∑' r : ℤ, ((f r : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = (fun ξ : ℝ =>
        ∑ r ∈ s, ((f r : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))) := by
    funext ξ
    rw [tsum_eq_sum (s := s)]
    intro b hb
    rw [hsupp b hb]
    simp
  rw [heq]
  apply continuous_finset_sum
  intro r _
  apply Continuous.mul continuous_const
  apply Complex.continuous_exp.comp
  apply Continuous.neg
  apply Continuous.mul
  · exact (continuous_const.mul Complex.continuous_ofReal)
  · exact continuous_const

/-- **`cleanFT` is continuous in ξ** (finite support of `cleanThreeFactor`). -/
theorem cleanFT_continuous (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Continuous (fun ξ : ℝ => cleanFT n δ zMinus zPlus ξ) := by
  unfold cleanFT
  exact finiteSupport_FT_continuous (cleanThreeFactor n δ zMinus zPlus)
    (Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
    (fun r hr => cleanThreeFactor_off_window_zero n δ zMinus zPlus r hr)

/-- **`kwayFT` is continuous in ζ** (finite support of `kwayProd`, nonempty ℓ). -/
theorem kwayFT_continuous (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) :
    Continuous (fun ζ : ℝ => kwayFT n α ℓ ζ) := by
  unfold kwayFT
  exact finiteSupport_FT_continuous (kwayProd n α ℓ)
    (Finset.Icc (-(n / 4 : ℤ) - ((j₀ - 1 : ℕ) : ℤ)) ((n : ℤ) - (n / 4 : ℤ) - ((j₀ - 1 : ℕ) : ℤ)))
    (fun r hr => kwayProd_off_window_zero n α ℓ j₀ hj₀ r hr)

/-- **`cleanFT` is IntegrableOn `[-π,π]`** (continuous on a compact set). -/
theorem cleanFT_integrableOn (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    MeasureTheory.IntegrableOn (fun ξ : ℝ => cleanFT n δ zMinus zPlus ξ)
      (Set.Icc (-Real.pi) Real.pi) :=
  (cleanFT_continuous n δ zMinus zPlus).continuousOn.integrableOn_compact isCompact_Icc

/-- **`kwayFT` is IntegrableOn `[-π,π]`** (continuous on a compact set). -/
theorem kwayFT_integrableOn (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) :
    MeasureTheory.IntegrableOn (fun ζ : ℝ => kwayFT n α ℓ ζ)
      (Set.Icc (-Real.pi) Real.pi) :=
  (kwayFT_continuous n α ℓ j₀ hj₀).continuousOn.integrableOn_compact isCompact_Icc

/-! ### (5) Modulus bound via the circular-convolution triangle inequality -/

/-- **Triangle modulus bound for `fullCleanFT(π)`.** -/
theorem fullCleanFT_pi_abs_le_modulus_integral
    (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) :
    ‖fullCleanFT n δ α zMinus zPlus ℓ Real.pi‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖ := by
  rw [fullCleanFT_eq_conv n δ α zMinus zPlus ℓ j₀ hj₀ Real.pi]
  exact ModulusOfCircularConvolutionTriangle
    (fun η => cleanFT n δ zMinus zPlus η)
    (fun ζ => kwayFT n α ℓ ζ)
    (fun x => cleanFT_periodic n δ zMinus zPlus x)
    (fun x => kwayFT_periodic n α ℓ x)
    (cleanFT_integrableOn n δ zMinus zPlus)
    (kwayFT_integrableOn n α ℓ j₀ hj₀)
    Real.pi

/-! ### (6) The CONDITIONAL region-split bound

The integrand `‖cleanFT η‖·‖kwayFT(π-η)‖` is split at the k-way frequency
`ζ := π - η`.  On `|ζ| ≥ 2` the k-way tail bound `hkwayTail` gives the
`2·e^{-√n}` decay (the B_Fou tail); on `|ζ| < 2` the trivial ℓ¹ bound `hkwayL1`
caps `kwayFT` by `n+1` while the 3-binom `cleanFT` modulus `hcleanRegion` supplies
the B_exp main-term decay.  Integrating the constant pointwise bounds over the
`2π`-box and dividing by `2π` collapses to `B_exp + B_Fou`.

The three region inputs are taken as HYPOTHESES (each discharges, once Lemma 7 is
proved, from `kwayFactor_fourier_tail_bound` via the reindex bridge of §0, the
trivial k-way ℓ¹ bound, and a general-η version of the proved-at-π k=0 cleanFT
machinery `AltRSumEmptyOuterBound.cleanFT_pi_abs_le_Couter`). -/
theorem fullCleanFT_pi_modulus_bound_of_kwayTail
    (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    -- The pointwise integrand bound on the WHOLE box `[-π,π]`, split at ζ = π-η:
    --   * |ζ| ≥ 2 : ‖cleanFT η‖·‖kwayFT(π-η)‖ ≤ B_Fou-density, and
    --   * |ζ| < 2 : ‖cleanFT η‖·‖kwayFT(π-η)‖ ≤ B_exp-density,
    -- bundled as: integrand ≤ (B_exp-density) + (B_Fou-density) pointwise.
    (Bexp BFou : ℝ) (hBexp : 0 ≤ Bexp) (hBFou : 0 ≤ BFou)
    (hpt : ∀ η ∈ Set.Icc (-Real.pi) Real.pi,
        ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
          ≤ Bexp + BFou) :
    ‖fullCleanFT n δ α zMinus zPlus ℓ Real.pi‖ ≤ Bexp + BFou := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have htri := fullCleanFT_pi_abs_le_modulus_integral n δ α zMinus zPlus ℓ j₀ hj₀
  -- integrand
  set F : ℝ → ℝ := fun η =>
    ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖ with hF
  have hFcont : Continuous F := by
    rw [hF]
    apply Continuous.mul
    · exact (cleanFT_continuous n δ zMinus zPlus).norm
    · apply Continuous.norm
      exact (kwayFT_continuous n α ℓ j₀ hj₀).comp (continuous_const.sub continuous_id)
  have hFiint : IntervalIntegrable F MeasureTheory.volume (-Real.pi) Real.pi :=
    hFcont.intervalIntegrable _ _
  have hintbound : (∫ η in (-Real.pi)..Real.pi, F η)
      ≤ ∫ _ in (-Real.pi)..Real.pi, (Bexp + BFou) :=
    intervalIntegral.integral_mono_on hπ hFiint intervalIntegrable_const
      (fun η hη => hpt η hη)
  have hconst : (∫ _ in (-Real.pi)..Real.pi, (Bexp + BFou))
      = (2 * Real.pi) * (Bexp + BFou) := by
    rw [intervalIntegral.integral_const, smul_eq_mul,
        show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
  calc ‖fullCleanFT n δ α zMinus zPlus ℓ Real.pi‖
      ≤ (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi, F η := htri
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * (Bexp + BFou)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hconst]; exact hintbound
    _ = Bexp + BFou := by field_simp

/-! ### (7) Composition: conditional k ≥ 1 `AltRSumFourierBound` conclusion

Instantiating `fullCleanFT_pi_modulus_bound_of_kwayTail` at the axiom's
`B_exp`, `B_Fou` and feeding the result to
`AltRSumFourierBoundKway.altRSum_fourier_bound_of_kway` gives the k ≥ 1
`AltRSumFourierBound` conclusion, CONDITIONAL on the region integrand bound `hpt`
(which discharges, once Lemma 7 lands, from the kway tail bound via the §0 reindex
bridge plus the cleanFT region machinery). -/
theorem altRSum_fourier_bound_of_region_split
    (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpt : ∀ η ∈ Set.Icc (-Real.pi) Real.pi,
        ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
          ≤ (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
                (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                          (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                     (Real.exp (-((n : ℝ) / 150)))))
            + (4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ)))) :
    |altRSum n δ α zMinus zPlus ℓ|
      ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                 (Real.exp (-((n : ℝ) / 150))))
          +
          4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hBexp : (0:ℝ) ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
      (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
           (Real.exp (-((n : ℝ) / 150)))) := by
    have hpi2 : (0:ℝ) ≤ 2 * Real.pi - 2 := by linarith [Real.pi_gt_d2]
    apply mul_nonneg
    · apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by positivity) hpi2) (by positivity)
    · apply le_max_of_le_right; positivity
  have hBFou : (0:ℝ) ≤ 4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    positivity
  have hFT := fullCleanFT_pi_modulus_bound_of_kwayTail n δ α zMinus zPlus ℓ j₀ hj₀ hδ0 hδ1
    _ _ hBexp hBFou hpt
  exact altRSum_fourier_bound_of_kway n δ α zMinus zPlus ℓ hFT

end Workspace.PriorWork.AltRSumKwayRegionSplit
