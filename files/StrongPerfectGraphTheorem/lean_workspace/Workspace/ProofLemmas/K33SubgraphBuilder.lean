import Mathlib

/-!
# Exhibiting a `K₃,₃` subgraph from six vertices

The cross-track branch of Step 2 of 5.3 ends with

> *"and so `m = 3`, and similarly `n = 3`.  **Hence there is a subgraph `J` of `H` isomorphic to
> `K₃,₃`.**"*

At that point the configuration is completely explicit: `P = p₁-p₂-p₃`, `Q = q₁-q₂-q₃`, the four
cross edges `p₁q₁, p₁q₃, p₃q₁, p₃q₃`, and the track `R = p₂-q₂`.  The bipartition is
`{p₁, p₃, q₂}` against `{q₁, q₃, p₂}` — note that it is *not* `V(P)` against `V(Q)`: the middle
vertices swap sides.

This module turns that data into the required `J : H.Subgraph` with `J.coe ≃g K₃,₃`.

The construction avoids all case-bashing on the isomorphism.  Rather than building an
`Equiv` between a six-element vertex set and `Fin 3 ⊕ Fin 3` by hand, take

```
J.verts = Set.range w        J.Adj x y = ∃ s t, K₃,₃.Adj s t ∧ x = w s ∧ y = w t
```

for the injection `w : Fin 3 ⊕ Fin 3 → W` naming the six vertices.  Then `Equiv.ofInjective w`
*is* the underlying equivalence of the isomorphism, the coercion `↑(Equiv.ofInjective w hinj s)`
is `w s` by `rfl`, and `map_rel_iff'` is two lines.  Only `adj_sub` needs the nine adjacencies,
and only injectivity needs the fifteen disequalities — and both of those are the caller's.
-/

set_option autoImplicit false
-- `fin_cases` already reduces the `![…]` applications, so the `Matrix.cons_val_*` lemmas passed
-- to the case bashes below are redundant in most branches; they are kept because dropping them
-- makes the `simp only` fail outright in the branches where they *are* what closes the goal.
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.K33SubgraphBuilder

variable {W : Type*}

/-- The subgraph spanned by six vertices arranged as a `K₃,₃`. -/
private def k33Subgraph (H : SimpleGraph W) (w : Fin 3 ⊕ Fin 3 → W)
    (hw : ∀ s t, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj s t → H.Adj (w s) (w t)) :
    H.Subgraph where
  verts := Set.range w
  Adj := fun x y =>
    ∃ s t, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj s t ∧ x = w s ∧ y = w t
  adj_sub := by rintro x y ⟨s, t, hst, rfl, rfl⟩; exact hw s t hst
  edge_vert := by rintro x y ⟨s, t, hst, rfl, rfl⟩; exact ⟨s, rfl⟩
  symm := by rintro x y ⟨s, t, hst, rfl, rfl⟩; exact ⟨t, s, hst.symm, rfl, rfl⟩

/-- **Six vertices in `K₃,₃` position span a `K₃,₃` subgraph.**

`w` names the six vertices, with `Sum.inl` indexing one side of the bipartition and `Sum.inr`
the other; `hw` says every cross pair is an edge of `H`. -/
theorem exists_k33_subgraph {H : SimpleGraph W} (w : Fin 3 ⊕ Fin 3 → W)
    (hinj : Function.Injective w)
    (hw : ∀ s t, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj s t → H.Adj (w s) (w t)) :
    ∃ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  refine ⟨k33Subgraph H w hw, ⟨SimpleGraph.Iso.symm ?_⟩⟩
  refine ⟨Equiv.ofInjective w hinj, ?_⟩
  intro s t
  constructor
  · rintro ⟨s', t', hst', h1, h2⟩
    rw [hinj h1, hinj h2]
    exact hst'
  · intro h
    exact ⟨s, t, h, rfl, rfl⟩

/-- **The configuration 5.3 actually reaches.**

`P = p₁-p₂-p₃` and `Q = q₁-q₂-q₃` with the four cross edges `p₁q₁, p₁q₃, p₃q₁, p₃q₃` and the
track `R = p₂-q₂` span a `K₃,₃`.  The bipartition is `{p₁, p₃, q₂}` against `{q₁, q₃, p₂}` — the
middle vertices of `P` and `Q` swap sides, which is why the nine edges are the four cross edges,
the two edges of `P`, the two edges of `Q`, and `R`. -/
theorem exists_k33_subgraph_of_six {H : SimpleGraph W} (p₁ p₂ p₃ q₁ q₂ q₃ : W)
    (hnd : [p₁, p₂, p₃, q₁, q₂, q₃].Nodup)
    (e11 : H.Adj p₁ q₁) (e13 : H.Adj p₁ q₃) (e1p : H.Adj p₁ p₂)
    (e31 : H.Adj p₃ q₁) (e33 : H.Adj p₃ q₃) (e3p : H.Adj p₃ p₂)
    (e21 : H.Adj q₂ q₁) (e23 : H.Adj q₂ q₃) (e2p : H.Adj q₂ p₂) :
    ∃ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have a12 : p₁ ≠ p₂ := by rintro rfl; simp at hnd
  have a13 : p₁ ≠ p₃ := by rintro rfl; simp at hnd
  have a1q1 : p₁ ≠ q₁ := by rintro rfl; simp at hnd
  have a1q2 : p₁ ≠ q₂ := by rintro rfl; simp at hnd
  have a1q3 : p₁ ≠ q₃ := by rintro rfl; simp at hnd
  have a23 : p₂ ≠ p₃ := by rintro rfl; simp at hnd
  have a2q1 : p₂ ≠ q₁ := by rintro rfl; simp at hnd
  have a2q2 : p₂ ≠ q₂ := by rintro rfl; simp at hnd
  have a2q3 : p₂ ≠ q₃ := by rintro rfl; simp at hnd
  have a3q1 : p₃ ≠ q₁ := by rintro rfl; simp at hnd
  have a3q2 : p₃ ≠ q₂ := by rintro rfl; simp at hnd
  have a3q3 : p₃ ≠ q₃ := by rintro rfl; simp at hnd
  have aq12 : q₁ ≠ q₂ := by rintro rfl; simp at hnd
  have aq13 : q₁ ≠ q₃ := by rintro rfl; simp at hnd
  have aq23 : q₂ ≠ q₃ := by rintro rfl; simp at hnd
  clear hnd
  refine exists_k33_subgraph (Sum.elim ![p₁, p₃, q₂] ![q₁, q₃, p₂]) ?_ ?_
  · rintro (i | i) (j | j) h <;> fin_cases i <;> fin_cases j <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h <;> simp_all
  · have key : ∀ i j : Fin 3, H.Adj (![p₁, p₃, q₂] i) (![q₁, q₃, p₂] j) := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] <;> assumption
    rintro (i | i) (j | j) hst
    · exact absurd hst (by simp [_root_.completeBipartiteGraph_adj])
    · exact key i j
    · exact (key j i).symm
    · exact absurd hst (by simp [_root_.completeBipartiteGraph_adj])

end Workspace.ProofLemmas.K33SubgraphBuilder
