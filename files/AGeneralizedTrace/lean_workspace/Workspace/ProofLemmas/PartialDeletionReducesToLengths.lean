import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.WitnessPrefixSuffixTail
import Workspace.ProofLemmas.TVPartialBoundedByLengthsPlusBad

open Workspace.Types.BinVec
open Workspace.Types.Trace

theorem PartialDeletionReducesToLengths :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∀ (Se So : Workspace.Types.ProbVec.ProbVec n),
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (∀ i : Fin n, So.p i =
          (if (i.val) % 2 = 1
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        ∀ (δ : Workspace.Types.DelProb.DelProb),
          (320 : ℝ) / Real.sqrt n ≤ δ.val → δ.val ≤ 1 / 2 →
          ∀ (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
            (partO : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n So δ)
            (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
            (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
            ((1 / 2) : ℝ) *
                ∑' s : (BinVec (n / 2) × Trace n × Trace n),
                  |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|
              ≤ ((1 / 2) : ℝ) *
                  ∑' s : (BinVec (n / 2) × ℕ × ℕ),
                    |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|
                + Real.exp (-((1 : ℝ) / 2 * Real.sqrt n)) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub partE partO lenE lenO
  -- Get cfdE, cfdO from the existence lemma
  obtain ⟨cfdE⟩ := CoinFlipDistExists Se
  obtain ⟨cfdO⟩ := CoinFlipDistExists So
  -- Apply structural decomposition: TV(part) ≤ TV(len) + bad_E + bad_O
  have h_decomp := TVPartialBoundedByLengthsPlusBad cfdE cfdO partE partO lenE lenO
  -- Apply tail bound: bad_E ≤ (1/4) exp(-√n/2) and bad_O ≤ (1/4) exp(-√n/2)
  have h_tail := WitnessPrefixSuffixTail n hn hmod Se So hSe hSo cfdE cfdO
  -- Note that exp(-√n/2) = exp(-(1/2 * √n))
  have h_neg_eq : -(Real.sqrt n / 2) = -((1 : ℝ) / 2 * Real.sqrt n) := by ring
  -- Combine: bad_E + bad_O ≤ (1/2) exp(-√n/2) ≤ exp(-√n/2)
  rw [h_neg_eq] at h_tail
  -- Reconcile the suffix-window boundary: 3*(n/4) = n/4 + n/2 when n % 8 = 1.
  have hbnd : ((3 * (n / 4 : ℕ) : ℤ)) = ((n / 4 + n / 2 : ℕ) : ℤ) := by
    have : 3 * (n / 4) = n / 4 + n / 2 := by omega
    exact_mod_cast this
  simp only [hbnd] at h_tail
  linarith [h_decomp, h_tail.1, h_tail.2, Real.exp_pos (-((1 : ℝ) / 2 * Real.sqrt n))]
