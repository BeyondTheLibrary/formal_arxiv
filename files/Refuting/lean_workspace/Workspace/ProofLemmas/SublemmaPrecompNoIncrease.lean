import Mathlib
import Workspace.Types.Protocol
import Workspace.Types.CommComplexity
import Workspace.UpperBound

open Workspace.Types.CommComplexity

namespace Workspace.ProofLemmas

theorem SublemmaPrecompNoIncrease {A B A' B' Z : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (g : A → B → Z) (α : A' → A) (β : B' → B) :
    D (fun u v => g (α u) (β v)) ≤ D g := by
  -- It suffices to show AchievableCosts g ⊆ AchievableCosts (g ∘ (α,β)),
  -- then sInf is monotone.
  have hsub : AchievableCosts g ⊆ AchievableCosts (fun u v => g (α u) (β v)) := by
    rintro c ⟨P, hcost, hcomp⟩
    refine ⟨Workspace.UpperBound.Protocol.comap α β P, ?_, ?_⟩
    · rw [Workspace.UpperBound.Protocol.comap_cost]; exact hcost
    · intro u v
      rw [Workspace.UpperBound.Protocol.comap_eval]
      exact hcomp (α u) (β v)
  rcases Set.eq_empty_or_nonempty (AchievableCosts g) with hempty | hne
  · -- No protocol computes g; then no protocol computes g' either, so both sInf are 0.
    have hempty' : AchievableCosts (fun u v => g (α u) (β v)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro c ⟨P, _, _⟩
      -- A protocol for g' yields a value in Z, hence a (trivial) protocol for g,
      -- contradicting emptiness of AchievableCosts g.
      have hZ : Nonempty Z := Workspace.UpperBound.Protocol.nonempty_codomain P
      haveI := hZ
      have hne := Workspace.UpperBound.AchievableCosts_nonempty g
      rw [hempty] at hne
      exact absurd hne (by simp)
    rw [D, D, hempty, hempty']
  · -- AchievableCosts g is nonempty: use monotonicity of sInf over a subset.
    exact csInf_le_csInf' hne hsub

end Workspace.ProofLemmas
