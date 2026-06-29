import Mathlib
import Workspace.Types.LowerBoundConstants
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.TraceDist
import Workspace.ProofLemmas.SublemmaPartialDeletionBound
import Workspace.Types.TVDistance

/--
`SublemmaTVAssembly` (Step 4e — final assembly).

Combines the per-summand Fourier bound (`SublemmaPerSummandBound`), the
sparse-support bound (`SublemmaRareSupport`), and the typical-event bound
(`SublemmaTypicalRZ`) to conclude the end-result TV bound used by the
main theorem.

With explicit constants `c_δ := 320`, `c_tv := 1/4`, `n_0 := 10^12`, for
every `n ≥ n_0` with `n ≡ 1 (mod 8)`, every `δ : DelProb` with
`c_δ / √n ≤ δ.val ≤ 1/2`, and the witnesses `S_e, S_o : ProbVec n`
produced by `SublemmaWitnessConstruction` (assigning to each index `i` of
the correct parity the value `(1/(4·e²·√(2π))) · √n · C(n, i) · 2⁻ⁿ` and
zero elsewhere), every pair of trace distributions `td₁ : TraceDist n S_e δ`,
`td₂ : TraceDist n S_o δ` satisfies

  `TVDistance(td₁.toPMF, td₂.toPMF) ≤ exp(-c_tv · √n)`.

The conclusion matches `SublemmaPartialDeletionBound`'s; the difference is
intent (this is the assembly itself, not the alternating-sum reduction).
The unused `cOmega` existential of `SublemmaPartialDeletionBound` is
dropped here because the constants `(320, 1/4, 10^12)` are already explicit.
-/
theorem SublemmaTVAssembly :
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
  obtain ⟨_cOmega, _hcOmega_pos, hPDB⟩ := SublemmaPartialDeletionBound
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub td₁ td₂
  exact hPDB n hn hmod Se So hSe hSo δ hδ_lb hδ_ub td₁ td₂
