import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.Proposition7ZeroCount
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.Prop7GeneralFromDistinct

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianPDF
open Workspace.Types.ZeroCount

/--
Proposition 7 of Moitra–Valiant (general form, applied to a signed Gaussian
combination `S`): if `S` has at least one nonzero coefficient and its density is
not identically zero, then `S.density` has at most `2·(length − 1)` distinct
real zeros — with NO assumption that the variances are pairwise distinct.

Proof structure:

* **Case A (pairwise-distinct variances).**  The `Nodup` variance list lets us
  invoke `Proposition7ZeroCount` directly — this is the genuine distinct-variance
  Proposition 7 whose proof goes through the Hurwitz/IFT induction
  (`GaussianZeroCountInductiveStep`).

* **Case B (some variances coincide).**  Here `Proposition7ZeroCount` does NOT
  apply.  The general (non-distinct) Proposition 7 is supplied by the
  assembly-proven `Workspace.ProofLemmas.Prop7GeneralFromDistinct`, which routes
  the coincident-variance case through the §6.1 first reduction (an
  infinitesimal coefficient perturbation makes all zeros simple without
  decreasing the multiplicity-free zero count) and then applies the
  distinct-variance Proposition 7 to a variance-perturbed combination.
-/
theorem ZeroCountAfterPerturbation
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (h_nonzero_coeffs : ∀ p ∈ S.components, p.fst ≠ 0)
    (h_density_nonzero : ∃ x, S.density x ≠ 0)
    (hm : 1 ≤ S.components.length) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      S.density (2 * (S.components.length - 1)) := by
  classical
  -- A nonzero coefficient exists (the component list is nonempty since length ≥ 1).
  have hne : S.components ≠ [] := by
    intro hc; rw [hc] at hm; simp at hm
  obtain ⟨p₀, hp₀_mem⟩ := List.exists_mem_of_ne_nil _ hne
  have h_exists_nonzero : ∃ p ∈ S.components, p.fst ≠ 0 :=
    ⟨p₀, hp₀_mem, h_nonzero_coeffs p₀ hp₀_mem⟩
  by_cases hnodup : (S.components.map (fun p => p.snd.varSq)).Nodup
  · -- Case A: pairwise-distinct variances — the genuine distinct-variance Prop 7.
    exact Proposition7ZeroCount S hm hnodup h_exists_nonzero
  · -- Case B: coincident variances — the general Proposition 7 (corrected axiom).
    exact Workspace.ProofLemmas.Prop7GeneralFromDistinct S h_exists_nonzero
      h_density_nonzero hm

end Workspace.ProofLemmas
