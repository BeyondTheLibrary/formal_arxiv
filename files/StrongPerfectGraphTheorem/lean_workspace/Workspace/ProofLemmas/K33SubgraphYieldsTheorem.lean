import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.K33SubgraphSpanning
import Workspace.ProofLemmas.Thm53Assembly

/-!
# Step 3 of 5.3: the closing paragraph

The printed text (`paper/proofs/5_3.md`, published page 19) is:

> *"It is helpful now to change the notation.  Let `J` have vertex set
> `{a₁,a₂,a₃,b₁,b₂,b₃}`, where `a₁,a₂,a₃` are adjacent to `b₁,b₂,b₃`.  **Suppose that there is a
> component `F` of `H \ V(J)`.**  Since `H` is cyclically 3-connected, at least two vertices of
> `J` are attachments of `F`.  If say `a₁, b₁` are attachments, choose a track `P` between
> `a₁, b₁` with interior in `F`; then the union of `P` and `J \ {a₁b₁, a₂b₂}` satisfies the
> theorem.  If say `a₁, a₂` are attachments of `F`, choose a track `P` between `a₁, a₂` with
> interior in `F`; then the union of `P` and `J \ {a₁b₁, a₂b₃}` satisfies the theorem.  **So we
> may assume there is no such `F`.**  Since `H` is bipartite, it follows that `H = J = K₃,₃`,
> and so the theorem holds."*

So the paragraph is a dichotomy on whether `H` has a vertex outside `V(J)`:

* **no such vertex** — `J` spans, and `Workspace.ProofLemmas.K33SubgraphSpanning.iso_k33_of_spanning`
  is exactly the last sentence.  Proved.
* **some such vertex** — take the component `F` of `H \ V(J)` containing it and run the paper's
  two constructions.  That is `ComponentYieldsNondegenerate` below, still open.

This module proves the dichotomy itself (`k33SubgraphYieldsTheorem_of_component`), so that
`Thm53Assembly.K33SubgraphYieldsTheorem` closes with a single `exact` once the construction
lands, and supplies the bipartite ingredient that the construction's *nondegeneracy* obligation
turns on (`colour_split_of_four_cycle`).

## Why `colour_split_of_four_cycle` is the crux of nondegeneracy

`DegenerateK4Appearance D` asks for a four-cycle of `D` whose vertex set contains every
branch-vertex of `D`.  Both of the paper's constructions produce a `K₄`-subdivision inside the
*bipartite* `H`, so the four-cycle would live in a bipartite graph, and there its two colour
classes each have exactly two of the four vertices.  That is what kills both cases:

* attachments `a₁, a₂` on the **same** side — the four branch-vertices are `a₁, a₂, a₃, b₂`,
  which split `3`–`1` across the bipartition, so no four-cycle can contain them all;
* attachments `a₁, b₁` on **opposite** sides — the four branch-vertices are `a₁, a₃, b₁, b₃`,
  splitting `2`–`2`, and the cycle is then forced to use all four of `a₁b₁, a₁b₃, a₃b₁, a₃b₃`;
  but `a₁b₁` is one of the two deleted edges, so it is not an edge of the constructed subgraph.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.K33SubgraphYieldsTheorem

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {W : Type*}

/-! ### The bipartite ingredient of nondegeneracy -/

/-- **In a two-colourable graph the two "diagonals" of a four-cycle are monochromatic.**

For a four-cycle `a-b-c-d-a`, adjacency forces the colours to alternate, and with only two
colours available that means `a`, `c` share a colour and `b`, `d` share the other.  Hence the
vertex set of a four-cycle always splits `2`–`2` across the bipartition — never `3`–`1`. -/
theorem colour_split_of_four_cycle {D : SimpleGraph W} (col : D.Coloring (Fin 2)) {a b c d : W}
    (hab : D.Adj a b) (hbc : D.Adj b c) (hcd : D.Adj c d) (hda : D.Adj d a) :
    col a = col c ∧ col b = col d := by
  have v1 := (col a).isLt
  have v2 := (col b).isLt
  have v3 := (col c).isLt
  have v4 := (col d).isLt
  have n1 : ((col a : ℕ)) ≠ ((col b : ℕ)) := fun h => col.valid hab (Fin.val_injective h)
  have n2 : ((col b : ℕ)) ≠ ((col c : ℕ)) := fun h => col.valid hbc (Fin.val_injective h)
  have n3 : ((col c : ℕ)) ≠ ((col d : ℕ)) := fun h => col.valid hcd (Fin.val_injective h)
  have n4 : ((col d : ℕ)) ≠ ((col a : ℕ)) := fun h => col.valid hda (Fin.val_injective h)
  exact ⟨Fin.val_injective (by omega), Fin.val_injective (by omega)⟩

/-- The `3`–`1` corollary: the vertex set of a four-cycle of a two-colourable graph never
contains three distinct vertices of the same colour.

This is the whole nondegeneracy argument in the *same-side* case of 5.3's closing paragraph,
where the four branch-vertices are `a₁, a₂, a₃, b₂` and the first three share a colour. -/
theorem no_three_same_colour_on_four_cycle {D : SimpleGraph W} (col : D.Coloring (Fin 2))
    {a b c d : W} (hab : D.Adj a b) (hbc : D.Adj b c) (hcd : D.Adj c d) (hda : D.Adj d a)
    {x y z : W} (hx : x = a ∨ x = b ∨ x = c ∨ x = d) (hy : y = a ∨ y = b ∨ y = c ∨ y = d)
    (hz : z = a ∨ z = b ∨ z = c ∨ z = d) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : col x = col y) (h2 : col y = col z) : False := by
  obtain ⟨hac, hbd⟩ := colour_split_of_four_cycle col hab hbc hcd hda
  have hne : col a ≠ col b := col.valid hab
  -- only two colours are available, so every vertex has the colour of `a` or that of `b`
  have two : ∀ w : W, col w = col a ∨ col w = col b := by
    intro w
    have v0 := (col w).isLt
    have va := (col a).isLt
    have vb := (col b).isLt
    have hv : ((col a : ℕ)) ≠ ((col b : ℕ)) := fun h => hne (Fin.val_injective h)
    have hcase : ((col w : ℕ)) = ((col a : ℕ)) ∨ ((col w : ℕ)) = ((col b : ℕ)) := by omega
    rcases hcase with h' | h'
    · exact Or.inl (Fin.val_injective h')
    · exact Or.inr (Fin.val_injective h')
  -- each colour class of `{a,b,c,d}` is `{a,c}` or `{b,d}`, of size at most two
  have key : ∀ w : W, (w = a ∨ w = b ∨ w = c ∨ w = d) → col w = col a → w = a ∨ w = c := by
    intro w hw hcolw
    rcases hw with h | h | h | h
    · exact Or.inl h
    · rw [h] at hcolw; exact absurd hcolw.symm hne
    · exact Or.inr h
    · rw [h] at hcolw; exact absurd (hbd.trans hcolw).symm hne
  have key' : ∀ w : W, (w = a ∨ w = b ∨ w = c ∨ w = d) → col w = col b → w = b ∨ w = d := by
    intro w hw hcolw
    rcases hw with h | h | h | h
    · rw [h] at hcolw; exact absurd hcolw hne
    · exact Or.inl h
    · rw [h] at hcolw; exact absurd (hac.trans hcolw) hne
    · exact Or.inr h
  -- three distinct vertices cannot all lie in a two-element set
  have pigeon : ∀ u v w p q : W, (u = p ∨ u = q) → (v = p ∨ v = q) → (w = p ∨ w = q) →
      u ≠ v → u ≠ w → v ≠ w → False := by
    intro u v w p q hu hv hw huv huw hvw
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact huv (hu.trans hv.symm)
    · exact huv (hu.trans hv.symm)
    · exact huw (hu.trans hw.symm)
    · exact hvw (hv.trans hw.symm)
    · exact hvw (hv.trans hw.symm)
    · exact huw (hu.trans hw.symm)
    · exact huv (hu.trans hv.symm)
    · exact huv (hu.trans hv.symm)
  rcases two x with hx2 | hx2
  · have hy2 : col y = col a := h1.symm.trans hx2
    have hz2 : col z = col a := h2.symm.trans hy2
    exact pigeon x y z a c (key x hx hx2) (key y hy hy2) (key z hz hz2) hxy hxz hyz
  · have hy2 : col y = col b := h1.symm.trans hx2
    have hz2 : col z = col b := h2.symm.trans hy2
    exact pigeon x y z b d (key' x hx hx2) (key' y hy hy2) (key' z hz hz2) hxy hxz hyz

/-! ### The dichotomy of the closing paragraph -/

/-- **The open half of 5.3's closing paragraph.**  If the `K₃,₃` subgraph `J` does not span `H`,
pick a component `F` of `H \ V(J)`; cyclic 3-connectivity gives `F` at least two attachments in
`V(J)`, and a track `P` through `F` between two of them turns `J` into a nondegenerate
`K₄`-subdivision — `P ∪ (J \ {a₁b₁, a₂b₂})` when the attachments are on opposite sides,
`P ∪ (J \ {a₁b₁, a₂b₃})` when they are on the same side. -/
def ComponentYieldsNondegenerate (H : SimpleGraph W) : Prop :=
  H.IsBipartite → CyclicallyThreeConnected H →
  ∀ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    (∃ v : W, v ∉ J.verts) →
    ∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe

/-- **Step 3 of 5.3**, reduced to its one open half.

The paragraph is a dichotomy on whether `V(J) = V(H)`.  If it is, `J` spans and
`K33SubgraphSpanning.iso_k33_of_spanning` gives `H ≅ K₃,₃` — the paper's *"Since `H` is
bipartite, it follows that `H = J = K₃,₃`"*.  If it is not, there is a vertex outside `V(J)`,
hence a component `F` of `H \ V(J)`, and `ComponentYieldsNondegenerate` runs the paper's two
constructions. -/
theorem k33SubgraphYieldsTheorem_of_component (H : SimpleGraph W)
    (hcomp : ComponentYieldsNondegenerate H) : Thm53Assembly.K33SubgraphYieldsTheorem H := by
  intro hbip hc3 J hJ
  by_cases hspan : J.verts = Set.univ
  · exact Or.inl (K33SubgraphSpanning.iso_k33_of_spanning hbip J hJ hspan)
  · refine Or.inr (hcomp hbip hc3 J hJ ?_)
    by_contra hcon
    push Not at hcon
    exact hspan (Set.eq_univ_of_forall hcon)

end Workspace.ProofLemmas.K33SubgraphYieldsTheorem
