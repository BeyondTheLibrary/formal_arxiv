import Mathlib

/-!
# Joining a colouring of `C` and a colouring of `D` over a partition

The pure-Mathlib plumbing lemma of the proof of 1.5, used once, at the end of §6:

> *"so they are `s`-colourable and `(t − s)`-colourable, respectively.  But then `G`
> is `t`-colourable"*

Colour `C` from the first block of `Fin (p + q)` and `D` from the second: an edge
inside `C` is handled by the first colouring, an edge inside `D` by the second, and
an edge between `C` and `D` has its endpoints in different blocks.

Mathlib has `SimpleGraph.Colorable` and `SimpleGraph.chromaticNumber_le_iff_colorable`
but no join-over-a-partition lemma, so this has to be built by hand from a
`SimpleGraph.Coloring` into `Fin p ⊕ Fin q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.ColorableSplitJoin

/-- If `C` and `D` partition the vertex set, `G|C` is `p`-colourable and `G|D` is
`q`-colourable, then `G` is `(p + q)`-colourable. -/
theorem colorable_add_of_partition {V : Type*} (G : SimpleGraph V) {C D : Set V}
    (hcov : C ∪ D = Set.univ) (hdisj : Disjoint C D) {p q : ℕ}
    (hC : (G.induce C).Colorable p) (hD : (G.induce D).Colorable q) :
    G.Colorable (p + q) := by
  classical
  obtain ⟨cC⟩ := hC
  obtain ⟨cD⟩ := hD
  have hmem : ∀ v : V, v ∉ C → v ∈ D := by
    intro v hv
    rcases (hcov ▸ Set.mem_univ v : v ∈ C ∪ D) with h | h
    · exact absurd h hv
    · exact h
  -- colours `0 … p-1` on `C`, colours `p … p+q-1` on `D`
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if h : v ∈ C then Fin.castAdd q (cC ⟨v, h⟩) else Fin.natAdd p (cD ⟨v, hmem v h⟩))
    ?_⟩
  intro u v hadj
  dsimp only
  by_cases hu : u ∈ C
  · by_cases hv : v ∈ C
    · -- an edge inside `C`
      rw [dif_pos hu, dif_pos hv]
      exact fun h => cC.valid (show (G.induce C).Adj ⟨u, hu⟩ ⟨v, hv⟩ from hadj)
        (Fin.castAdd_injective _ _ h)
    · -- an edge between `C` and `D`: the two colours lie in different blocks
      rw [dif_pos hu, dif_neg hv]
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
      have := (cC ⟨u, hu⟩).isLt
      omega
  · by_cases hv : v ∈ C
    · rw [dif_neg hu, dif_pos hv]
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
      have := (cC ⟨v, hv⟩).isLt
      omega
    · -- an edge inside `D`
      rw [dif_neg hu, dif_neg hv]
      intro h
      refine cD.valid
        (show (G.induce D).Adj ⟨u, hmem u hu⟩ ⟨v, hmem v hv⟩ from hadj) ?_
      have h' := congrArg Fin.val h
      simp only [Fin.val_natAdd] at h'
      exact Fin.ext (by omega)

end Workspace.ProofLemmas.ColorableSplitJoin
