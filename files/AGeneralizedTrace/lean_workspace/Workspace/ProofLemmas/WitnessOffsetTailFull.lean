import Mathlib
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CentralBinomialLowerTailWide
import Workspace.ProofLemmas.CentralBinomialUpperTailWide
import Workspace.ProofLemmas.WitnessOffsetTail

/-!
# WitnessOffsetTailFull — the full (two-sided) offset-weight tail bound

Combines `WitnessOffsetTail.offset_lower_tail` with its mirror image (the
upper tail, via `binPMF_half_symm`) to bound the total offset mass with
`|r| > n/8`.

All lemmas are sorry-free.
-/

open Workspace.Types.PartialDeletionProcess
open Workspace.Types.AlternatingSumExpression

namespace WitnessOffsetTailFull

/-- The upper binomial tail mirrors the lower tail: the `m`-binomial mass at the
top `K` coordinates `Ico (m - K + 1) (m + 1)` equals the bottom-`K` mass
`range K`, by binomial symmetry. -/
theorem binPMF_upper_eq_lower (m K : ℕ) (hK : K ≤ m) :
    (∑ k ∈ Finset.Ico (m - K + 1) (m + 1), binPMF m (1 / 2 : ℝ) k)
      = ∑ k ∈ Finset.range K, binPMF m (1 / 2 : ℝ) k := by
  apply Finset.sum_nbij' (fun k => m - k) (fun j => m - j)
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]; omega
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ico]; omega
  · intro k hk
    rw [Finset.mem_Ico] at hk; omega
  · intro j hj
    rw [Finset.mem_range] at hj; omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [CentralBinomialUpperTailWideProof.binPMF_half_symm m k (by omega)]

/-- The upper offset tail: the `n/2`-binomial mass at the top `n/8` coordinates
is `≤ exp(-n/256)`. -/
theorem offset_upper_tail (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ k ∈ Finset.Ico (n / 2 - (n / 8) + 1) (n / 2 + 1),
        binPMF (n / 2) (1 / 2 : ℝ) k)
      ≤ Real.exp (-((n : ℝ) / 256)) := by
  rw [binPMF_upper_eq_lower (n / 2) (n / 8) (by omega)]
  exact WitnessOffsetTail.offset_lower_tail n hn

end WitnessOffsetTailFull
