import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.AltRSumFourierBoundEmpty

set_option maxHeartbeats 8000000

open Real

theorem PerSummandBoundEmptyEll :
    ∀ (n : ℕ), (10 : ℕ) ^ 12 ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1/2 →
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
      |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus
          (∅ : Finset ℕ)|
        ≤ B_exp n δ zMinus zPlus + B_Fou n δ := by
  intro n hn hmod δ hδpos hδhalf zMinus zPlus hzM hzP
  simp only
  have hzM' : zMinus < n / 2 + 1 := Finset.mem_range.mp hzM
  have hzP' : zPlus < n / 2 + 1 := Finset.mem_range.mp hzP
  exact AltRSumFourierBoundEmpty n hn hmod δ hδpos hδhalf zMinus zPlus hzM' hzP'
