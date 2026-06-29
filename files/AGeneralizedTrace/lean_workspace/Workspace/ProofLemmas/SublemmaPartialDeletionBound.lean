import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.TraceDist
import Workspace.Types.TVDistance
import Workspace.Types.PartialDeletionAxioms
import Workspace.ProofLemmas.LengthsOnlyExists
import Workspace.ProofLemmas.PartialDeletionExists
import Workspace.ProofLemmas.SublemmaLemma6
import Workspace.ProofLemmas.AlternatingSumWitnessBound

theorem SublemmaPartialDeletionBound :
    ∃ (cOmega : ℝ), 0 < cOmega ∧
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
            ∀ (td₁ : Workspace.Types.TraceDist.TraceDist n Se δ)
              (td₂ : Workspace.Types.TraceDist.TraceDist n So δ),
              Workspace.Types.TVDistance.TVDistance td₁.toPMF td₂.toPMF
                ≤ Real.exp (-((1 : ℝ) / 64 * Real.sqrt n)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub td₁ td₂
  obtain ⟨partE⟩ := partial_exists Se δ
  obtain ⟨partO⟩ := partial_exists So δ
  obtain ⟨lenE⟩ := lengthsOnly_exists Se δ
  obtain ⟨lenO⟩ := lengthsOnly_exists So δ
  have h1 := SublemmaLemma6 n hn hmod Se So hSe hSo δ hδ_lb hδ_ub td₁ td₂
              partE partO lenE lenO
  have h2 := AlternatingSumWitnessBound n hn hmod δ.val hδ_lb hδ_ub
  linarith
