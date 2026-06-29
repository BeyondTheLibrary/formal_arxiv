import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.AltRSumEnvelopeRouteTypicalZ

namespace Workspace.ProofLemmas

set_option maxHeartbeats 8000000

open Workspace.Types.AlternatingSumExpression

/-- Typical-z envelope per-summand bound (HONEST envelope-route form, F88 de-axiomatization).
For typical `z₋, z₊ ∈ Ico (n/16) (n/2+1)` the L¹-summed inner alternating r-sum is bounded by
the central-binomial factor `√(2/(π·n))` times the envelope weight `envelopeW(ℓ)`:

  ∑_{z₋ ∈ Ico (n/16) (n_h+1)} ∑_{z₊ ∈ Ico (n/16) (n_h+1)} |altRSum n δ α z₋ z₊ ℓ|
    ≤ √(2/(π·n)) · envelopeW(ℓ),

with `envelopeW(ℓ) = ∑_{r ∈ Icc(-(n/4), n/4)} ∏_{j∈ℓ} ellFactor n α r (j-1)`. There is NO `e^{-√n}`
factor and NO polynomial prefactor here — this is the faithful triangle/factor bound proved
sorry-free in `AltRSumEnvelopeRouteTypicalZProof.altRSum_envelope_route_typicalZ`. The decay for
the rare (light) realizations is supplied DOWNSTREAM by `LightEnvelopeBound`
(`∑_{ℓ∈P_L} envelopeW(ℓ) ≤ n · e^{-√n/32}`). -/
theorem SublemmaPerSummandBoundEnvelope :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∀ (δ : ℝ), (320 : ℝ) / Real.sqrt n ≤ δ → δ ≤ 1 / 2 →
      let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let n_h : ℕ := n / 2
      let envelopeW : Finset ℕ → ℝ := fun ℓ =>
        ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ,
            Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1)
      ∀ (ℓ : Finset ℕ), ℓ ⊆ Finset.Icc 1 n_h →
      Workspace.Types.AlternatingSumExpression.sameParity ℓ →
        (∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
          ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α
              zMinus zPlus ℓ|)
          ≤ Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) * envelopeW ℓ := by
  intro n hn hmod δ hδ_lb hδ_ub c' α n_h envelopeW ℓ hℓ_sub hℓ_par
  have h := AltRSumEnvelopeRouteTypicalZProof.altRSum_envelope_route_typicalZ
              n hn hmod δ hδ_lb hδ_ub ℓ hℓ_sub hℓ_par
  simpa only [] using h

end Workspace.ProofLemmas
