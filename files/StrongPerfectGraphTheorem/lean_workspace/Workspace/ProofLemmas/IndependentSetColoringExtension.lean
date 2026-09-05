import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- Extends a coloring across an independent set by reserving one fresh color. -/
theorem IndependentSetColoringExtension
    {W : Type*} (K : SimpleGraph W) (Y R : Set W) (S : Set Y) {m : Nat}
    (hS : (K.induce Y).IsIndepSet S) (cR : (K.induce R).Coloring (Fin m))
    (lift : ∀ y : Y, y ∉ S → R)
    (hliftAdj : ∀ {a b : Y} (ha : a ∉ S) (hb : b ∉ S),
      (K.induce Y).Adj a b → (K.induce R).Adj (lift a ha) (lift b hb)) :
    (K.induce Y).Colorable (m + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk
    (fun y : Y =>
      if hy : y ∈ S then Fin.last m
      else Fin.castSucc (cR (lift y hy))) ?_⟩
  intro a b hab
  dsimp only
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · exact ((hS ha hb hab.ne) hab).elim
    · rw [dif_pos ha, dif_neg hb]
      exact (Fin.castSucc_ne_last _).symm
  · by_cases hb : b ∈ S
    · rw [dif_neg ha, dif_pos hb]
      exact Fin.castSucc_ne_last _
    · rw [dif_neg ha, dif_neg hb]
      intro heq
      apply cR.valid (hliftAdj ha hb hab)
      exact Fin.castSucc_injective _ heq

end Workspace.ProofLemmas
