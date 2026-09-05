import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- A `k`-coloring together with a clique of cardinality `k` pins down the
chromatic and clique numbers of a finite simple graph. -/
theorem ColoringCliqueSandwich
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (k : ℕ)
    (hcolor : K.Colorable k)
    (hclique : ∃ Q : Finset W,
      K.IsClique (↑Q : Set W) ∧ Q.card = k) :
    K.chromaticNumber = (K.cliqueNum : ℕ∞) := by
  obtain ⟨Q, hQclique, hQcard⟩ := hclique
  apply le_antisymm
  · calc
      K.chromaticNumber ≤ (k : ℕ∞) :=
        SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcolor
      _ = (Q.card : ℕ∞) := by exact_mod_cast hQcard.symm
      _ ≤ (K.cliqueNum : ℕ∞) := by exact_mod_cast hQclique.card_le_cliqueNum
  · exact K.cliqueNum_le_chromaticNumber

end Workspace.ProofLemmas
