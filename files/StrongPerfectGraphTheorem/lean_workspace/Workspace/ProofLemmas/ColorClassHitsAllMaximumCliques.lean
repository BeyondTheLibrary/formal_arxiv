import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- In a finite graph whose chromatic number equals its clique number, the
color class of any specified vertex is an independent set meeting every
maximum clique. -/
theorem ColorClassHitsAllMaximumCliques {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (x : W)
    (hχ : K.chromaticNumber = (K.cliqueNum : ℕ∞)) :
    ∃ S : Set W, x ∈ S ∧ K.IsIndepSet S ∧
      ∀ Q : Finset W, K.IsClique (↑Q : Set W) → Q.card = K.cliqueNum →
        ∃ q : W, q ∈ Q ∧ q ∈ S := by
  classical
  have hcolor : K.Colorable K.cliqueNum := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable, hχ]
  obtain ⟨C⟩ := hcolor
  refine ⟨C.colorClass (C x), ?_, C.isIndepSet_colorClass (C x), ?_⟩
  · simp [SimpleGraph.Coloring.colorClass]
  · intro Q hQ hcard
    have hsurj : Set.SurjOn (⇑C) (↑Q : Set W) Set.univ :=
      C.surjOn_of_card_le_isClique hQ (by
        simpa only [Fintype.card_fin] using Nat.le_of_eq hcard.symm)
    obtain ⟨q, hq, hqx⟩ := hsurj (Set.mem_univ (C x))
    exact ⟨q, hq, hqx⟩

end Workspace.ProofLemmas
