import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.PerSummandBoundEmptyEll
import Workspace.ProofLemmas.AltRSumFourierBoundProved

set_option maxHeartbeats 16000000

open Real

theorem SublemmaPerSummandBound :
    ∀ (n : ℕ), (10 : ℕ) ^ 12 ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1/2 →
    ∀ (ℓ : Finset ℕ), ℓ ⊆ Finset.Icc 1 (n / 2) →
      Workspace.Types.AlternatingSumExpression.sameParity ℓ →
    ∀ (zMinus zPlus : ℕ),
      zMinus ∈ Finset.range (n / 2 + 1) →
      zPlus ∈ Finset.range (n / 2 + 1) →
      let cPrime : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let B_exp : ℕ → ℝ → ℕ → ℕ → ℝ := fun n' δ' zM zP =>
        ((n' : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ') ^ 2 *
          max (max (Real.exp (-(δ' * (zM : ℝ) / 20)) / (1 - δ'))
                   (Real.exp (-(δ' * (zP : ℝ) / 20)) / (1 - δ')))
              (Real.exp (-((n' : ℝ) / 150)))
      let B_Fou : ℕ → ℝ → ℝ := fun n' δ' =>
        4 * (2 * Real.pi) ^ 2 / (1 - δ') ^ 2 * Real.exp (-Real.sqrt (n' : ℝ))
      |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
        ≤ B_exp n δ zMinus zPlus + B_Fou n δ := by
  intro n hn hnmod δ hδpos hδhalf ℓ hℓsub hℓpar zMinus zPlus hzm hzp
  -- Case split on whether ℓ is empty.
  by_cases h_empty : ℓ = ∅
  · -- k = 0 case: apply PerSummandBoundEmptyEll.
    subst h_empty
    have h_em := PerSummandBoundEmptyEll n hn hnmod δ hδpos hδhalf zMinus zPlus hzm hzp
    simpa using h_em
  · -- k ≥ 1 case: apply the AltRSumFourierBound prior_work axiom.
    have hne : ℓ.Nonempty := Finset.nonempty_of_ne_empty h_empty
    have hzm' : zMinus < n / 2 + 1 := Finset.mem_range.mp hzm
    have hzp' : zPlus < n / 2 + 1 := Finset.mem_range.mp hzp
    have h_fb := Workspace.ProofLemmas.AltRSumFourierBoundProved.AltRSumFourierBoundProved
      n hn hnmod δ hδpos hδhalf zMinus zPlus hzm' hzp'
      ℓ hℓsub hℓpar hne
    simpa using h_fb
