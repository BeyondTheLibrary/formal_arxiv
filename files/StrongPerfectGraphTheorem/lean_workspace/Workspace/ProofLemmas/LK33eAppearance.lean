import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Classes
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# `L(K₃,₃ \ e)` is forbidden in `F₃`

The printed proof of **15.1** ends

> *"There are two possible pairings; in one case the subgraph induced on these eight vertices
> is a double diamond, and in the other it is `L(K₃,₃ \ e)`.  In both cases this contradicts
> that `G ∈ F₆`."*

The first pairing is disposed of by the double-diamond clause of `InF6`.  This module supplies
the second one: **eight vertices of `G` inducing `L(K₃,₃ \ e)` contradict `G ∈ F₃`** (hence a
fortiori `G ∈ F₆`).

Nothing here corresponds to a numbered result of the paper; it is the routine verification the
paper leaves implicit, namely that `K₃,₃ \ e` *is* a bipartite subdivision of `K₄`, so that the
`F₃` clause

> *"for every bipartite subdivision `H` of `K₄`, no induced subgraph of `G` or of `Ḡ` is
> isomorphic to `L(H)`"*

applies to it.

## Why `K₃,₃ \ e` is a bipartite subdivision of `K₄`

Draw `K₃,₃` on `Fin 6` with `0, 1, 2 = x₀, x₁, x₂` and `3, 4, 5 = y₀, y₁, y₂`, and delete the
edge `x₂y₂`.  The four vertices `x₀, x₁, y₀, y₁` (i.e. `0, 1, 3, 4`) carry a `K₄`:

* the four edges `x₀y₀`, `x₀y₁`, `x₁y₀`, `x₁y₁` are present as edges;
* the fifth edge `x₀x₁` is subdivided once, by `y₂`  — the track `0 - 5 - 1`;
* the sixth edge `y₀y₁` is subdivided once, by `x₂` — the track `3 - 2 - 4`.

That accounts for all `8 = 4 + 2 + 2` edges and all `6 = 4 + 1 + 1` vertices, and the graph is
bipartite (`x`'s against `y`'s).  So `K₃,₃ \ e` is `K₄` with two *opposite* edges subdivided
once each.

## Contents

* `K33e` — the graph `K₃,₃ \ e` on `Fin 6`, with `DecidableRel K33e.Adj`;
* `K33e_bipartite`, `K33e_isSubdivision`, `K33e_isBipartiteSubdivision` — the three facts of
  the previous paragraph, in the vocabulary of `Workspace.Types.Tracks`;
* `LK33e` — the abstract eight-vertex graph `L(K₃,₃ \ e)` on `Fin 8`, and `lkIsoLine :
  LK33e ≃g K33e.lineGraph`;
* `lk33e_iso_induce` — eight vertices of `G` with the `L(K₃,₃ \ e)` adjacency pattern induce a
  subgraph isomorphic to `K33e.lineGraph`;
* `not_inF3_of_LK33e` — hence `G ∉ F₃`.  Variants `not_inF3_of_iso` /
  `not_inF3_of_iso_compl` take the isomorphism directly, in `G` resp. `Ḡ`.

## Technique

Everything about the concrete graphs is discharged by `decide`.  The only clause of
`IsSubdivision` that is not decidable as stated is the edge-set identity `E(H) = ⋃ trackEdges`,
because `trackEdges` quantifies over an unbounded `ℕ`; it is handled by
`trackEdges_subset_edgeSet` in one direction and eight explicit witnesses in the other.  The
adjacency clause of `IsTrackList` is likewise not decidable as stated, but it is exactly
`List.isChain_iff_getElem`, and `List.IsChain` *is* decidable — so the whole of clause 2 of
`IsSubdivision` is one `decide` too.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.LK33eAppearance

open Workspace.Types.Tracks.SPGT

/-! ### Generic facts about short tracks -/

/-- A two-vertex track has exactly one edge. -/
theorem trackEdges_pair {W : Type*} (a b : W) : trackEdges [a, b] = {s(a, b)} := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hlen : ([a, b] : List W).length = 2 := rfl
    have hi0 : i = 0 := by omega
    subst hi0
    rfl
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

/-- A three-vertex track has exactly two edges. -/
theorem trackEdges_triple {W : Type*} (a b c : W) :
    trackEdges [a, b, c] = {s(a, b), s(b, c)} := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hlen : ([a, b, c] : List W).length = 3 := rfl
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩

/-- Every edge of a track is an edge of the host graph.  Stated with `List.IsChain`, which is
decidable, rather than with `IsTrackList`, whose adjacency clause is not. -/
theorem trackEdges_subset_edgeSet {W : Type*} {D : SimpleGraph W} {q : List W}
    (h : q.IsChain D.Adj) : trackEdges q ⊆ D.edgeSet := by
  rintro e ⟨i, hi, rfl⟩
  exact List.isChain_iff_getElem.mp h i hi

/-! ### `K₃,₃ \ e` on `Fin 6`

`0, 1, 2 = x₀, x₁, x₂` and `3, 4, 5 = y₀, y₁, y₂`; the deleted edge is `x₂y₂ = s(2,5)`. -/

/-- Raw (asymmetric) edge relation of `K₃,₃` minus the edge `x₂y₂`. -/
def k33eRel (x y : Fin 6) : Bool :=
  ((x == 0 || x == 1) && (y == 3 || y == 4 || y == 5)) ||
  (x == 2 && (y == 3 || y == 4))

/-- Its symmetrisation. -/
def k33eAdj (x y : Fin 6) : Prop := k33eRel x y = true ∨ k33eRel y x = true

instance : DecidableRel k33eAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- **`K₃,₃ \ e`**: the complete bipartite graph `K₃,₃` with one edge deleted. -/
def K33e : SimpleGraph (Fin 6) where
  Adj := k33eAdj
  symm := fun _ _ h => h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel K33e.Adj := inferInstanceAs (DecidableRel k33eAdj)

/-- `K₃,₃ \ e` is bipartite: the `x`'s get colour `0`, the `y`'s colour `1`. -/
theorem K33e_bipartite : K33e.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk ![0, 0, 0, 1, 1, 1] ?_⟩
  intro u v h
  revert h
  revert u v
  decide

/-- The eight edges of `K₃,₃ \ e`. -/
def E8 : Set (Sym2 (Fin 6)) :=
  {s(0, 3), s(0, 4), s(0, 5), s(1, 3), s(1, 4), s(1, 5), s(2, 3), s(2, 4)}

theorem K33e_edgeSet : K33e.edgeSet = E8 := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeSet, E8, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a b
    decide

/-! ### `K₃,₃ \ e` as a subdivision of `K₄`

The branch vertices are `x₀, x₁, y₀, y₁`; the edges `x₀x₁` and `y₀y₁` of the `K₄` they carry
are subdivided by `y₂` and `x₂` respectively. -/

/-- The branch-vertex injection `V(K₄) → V(K₃,₃ \ e)`. -/
def k33eIota : Fin 4 → Fin 6 := ![0, 1, 3, 4]

/-- The six tracks of the subdivision, in both orientations.  Four of them are single edges;
the two tracks for the opposite pair `{0,1}`, `{2,3}` of `K₄`-edges pass through `y₂ = 5` and
`x₂ = 2`. -/
def k33eTrack : Fin 4 → Fin 4 → List (Fin 6)
  | 0, 1 => [0, 5, 1]
  | 1, 0 => [1, 5, 0]
  | 0, 2 => [0, 3]
  | 2, 0 => [3, 0]
  | 0, 3 => [0, 4]
  | 3, 0 => [4, 0]
  | 1, 2 => [1, 3]
  | 2, 1 => [3, 1]
  | 1, 3 => [1, 4]
  | 3, 1 => [4, 1]
  | 2, 3 => [3, 2, 4]
  | 3, 2 => [4, 2, 3]
  | _, _ => []

/-- **`K₃,₃ \ e` is a subdivision of `K₄`.** -/
theorem K33e_isSubdivision : IsSubdivision (⊤ : SimpleGraph (Fin 4)) K33e := by
  have h2 : ∀ u v : Fin 4, u ≠ v →
      (k33eTrack u v ≠ [] ∧ (k33eTrack u v).Nodup ∧ (k33eTrack u v).IsChain K33e.Adj ∧
       (k33eTrack u v).head? = some (k33eIota u) ∧
       (k33eTrack u v).getLast? = some (k33eIota v)) := by decide
  refine ⟨k33eIota, k33eTrack, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- each `T u v` is a track from `ι u` to `ι v`
    intro u v huv
    rw [SimpleGraph.top_adj] at huv
    obtain ⟨q1, q2, q3, q4, q5⟩ := h2 u v huv
    exact ⟨⟨q1, q2, fun i hi => List.isChain_iff_getElem.mp q3 i hi⟩, q4, q5⟩
  · -- each track has at least one edge
    intro u v huv
    rw [SimpleGraph.top_adj] at huv
    revert huv; revert u v; decide
  · -- reversing the edge reverses the track
    intro u v huv
    rw [SimpleGraph.top_adj] at huv
    revert huv; revert u v; decide
  · -- distinct tracks meet only in their ends
    intro u v u' v' huv huv' hs
    rw [SimpleGraph.top_adj] at huv huv'
    revert hs; revert huv'; revert huv; revert u v u' v'; decide
  · -- no internal vertex of a track is a branch vertex
    intro u v huv
    rw [SimpleGraph.top_adj] at huv
    revert huv; revert u v; decide
  · -- every vertex is a branch vertex or internal to a track
    intro w
    have : (∃ u, w = k33eIota u) ∨
        ∃ u v : Fin 4, u ≠ v ∧ w ∈ trackInterior (k33eTrack u v) := by revert w; decide
    rcases this with h | ⟨u, v, huv, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, v, by rw [SimpleGraph.top_adj]; exact huv, hw⟩
  · -- the tracks carry exactly the edges of `K₃,₃ \ e`
    apply Set.Subset.antisymm
    · rw [K33e_edgeSet]
      intro e he
      simp only [E8, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      simp only [Set.mem_iUnion]
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, 2, by decide, 0, by decide, rfl⟩
      · exact ⟨0, 3, by decide, 0, by decide, rfl⟩
      · exact ⟨0, 1, by decide, 0, by decide, rfl⟩
      · exact ⟨1, 2, by decide, 0, by decide, rfl⟩
      · exact ⟨1, 3, by decide, 0, by decide, rfl⟩
      · exact ⟨1, 0, by decide, 0, by decide, rfl⟩
      · exact ⟨3, 2, by decide, 1, by decide, rfl⟩
      · exact ⟨2, 3, by decide, 1, by decide, rfl⟩
    · intro e he
      simp only [Set.mem_iUnion] at he
      obtain ⟨u, v, huv, he⟩ := he
      rw [SimpleGraph.top_adj] at huv
      exact trackEdges_subset_edgeSet (h2 u v huv).2.2.1 he

/-- **`K₃,₃ \ e` is a *bipartite* subdivision of `K₄`** — so the `F₃` clause applies to it. -/
theorem K33e_isBipartiteSubdivision :
    IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) K33e :=
  ⟨K33e_isSubdivision, K33e_bipartite⟩

/-! ### `L(K₃,₃ \ e)` on `Fin 8`

Its eight vertices are the eight edges `xᵢyⱼ` of `K₃,₃ \ e` (all `(i, j)` except `(2,2)`), two
being adjacent exactly when the corresponding edges share an end, i.e. when `i = i'` or
`j = j'`. -/

/-- The eight edges of `K₃,₃ \ e`, as pairs `(i, j)` standing for `xᵢyⱼ`. -/
def lkIdx : Fin 8 → Fin 3 × Fin 3 :=
  ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)]

/-- The same eight edges, as elements of `Sym2 (Fin 6)`: `(i, j) ↦ s(i, 3 + j)`. -/
def lkPsi : Fin 8 → Sym2 (Fin 6) :=
  ![s(0, 3), s(0, 4), s(0, 5), s(1, 3), s(1, 4), s(1, 5), s(2, 3), s(2, 4)]

theorem lkPsi_mem (k : Fin 8) : lkPsi k ∈ K33e.edgeSet := by revert k; decide

/-- The eight vertices of `L(K₃,₃ \ e)`. -/
def lkPsiE (k : Fin 8) : K33e.edgeSet := ⟨lkPsi k, lkPsi_mem k⟩

theorem lkPsiE_inj : Function.Injective lkPsiE := by decide

theorem lkPsiE_bij : Function.Bijective lkPsiE :=
  (Fintype.bijective_iff_injective_and_card lkPsiE).mpr ⟨lkPsiE_inj, by decide⟩

/-- Adjacency of `L(K₃,₃ \ e)`: two distinct edges of `K₃,₃` share an end iff they have the
same `x`-index or the same `y`-index. -/
def lkAdj (k l : Fin 8) : Prop :=
  k ≠ l ∧ ((lkIdx k).1 = (lkIdx l).1 ∨ (lkIdx k).2 = (lkIdx l).2)

instance : DecidableRel lkAdj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- **`L(K₃,₃ \ e)`** as an abstract graph on eight vertices. -/
def LK33e : SimpleGraph (Fin 8) where
  Adj := lkAdj
  symm := by
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩
  loopless := ⟨by decide⟩

instance : DecidableRel LK33e.Adj := inferInstanceAs (DecidableRel lkAdj)

/-- **`LK33e` really is the line graph of `K₃,₃ \ e`.** -/
noncomputable def lkIsoLine : LK33e ≃g K33e.lineGraph where
  toEquiv := Equiv.ofBijective lkPsiE lkPsiE_bij
  map_rel_iff' := by
    intro p q
    show K33e.lineGraph.Adj (lkPsiE p) (lkPsiE q) ↔ _
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    revert p q
    decide

theorem lkIdx_ne (k : Fin 8) : lkIdx k ≠ (2, 2) := by revert k; decide

theorem lkIdx_inj : Function.Injective lkIdx := by decide

theorem lkIdx_surj : ∀ p : Fin 3 × Fin 3, p ≠ (2, 2) → ∃ k : Fin 8, lkIdx k = p := by decide

/-! ### An appearance of `L(K₃,₃ \ e)` in a graph -/

/-- **Eight vertices of `G` indexed by the edges of `K₃,₃ \ e`, adjacent exactly when the
corresponding edges share an end, induce a copy of `L(K₃,₃ \ e)`.**

`w p` is the vertex of `G` standing for the `K₃,₃`-edge `x_{p.1} y_{p.2}`; the value `w (2,2)`
is irrelevant (the edge `x₂y₂` is the deleted one), so a caller may put anything there. -/
theorem lk33e_iso_induce {V : Type*} {G : SimpleGraph V}
    (w : Fin 3 × Fin 3 → V)
    (hne : ∀ p q, p ≠ (2, 2) → q ≠ (2, 2) → p ≠ q → w p ≠ w q)
    (hadj : ∀ p q, p ≠ (2, 2) → q ≠ (2, 2) → p ≠ q →
      (G.Adj (w p) (w q) ↔ (p.1 = q.1 ∨ p.2 = q.2))) :
    Nonempty (G.induce (w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)}) ≃g K33e.lineGraph) := by
  have hf : ∀ k : Fin 8, w (lkIdx k) ∈ w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)} :=
    fun k => ⟨lkIdx k, lkIdx_ne k, rfl⟩
  set F : Fin 8 → (w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)} : Set V) :=
    fun k => ⟨w (lkIdx k), hf k⟩ with hF
  have hinj : Function.Injective F := by
    intro k l hkl
    by_contra hc
    have hidx : lkIdx k ≠ lkIdx l := fun h => hc (lkIdx_inj h)
    exact hne _ _ (lkIdx_ne k) (lkIdx_ne l) hidx (congrArg Subtype.val hkl)
  have hsurj : Function.Surjective F := by
    rintro ⟨v, p, hp, rfl⟩
    obtain ⟨k, hk⟩ := lkIdx_surj p hp
    exact ⟨k, Subtype.ext (by rw [hF]; simp only [hk])⟩
  have hrel : ∀ k l : Fin 8,
      (G.induce (w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)})).Adj (F k) (F l) ↔ LK33e.Adj k l := by
    intro k l
    show G.Adj (w (lkIdx k)) (w (lkIdx l)) ↔ LK33e.Adj k l
    by_cases hkl : k = l
    · subst hkl
      constructor
      · intro h; exact absurd h (G.irrefl)
      · intro h; exact absurd rfl (show lkAdj k k from h).1
    · have hidx : lkIdx k ≠ lkIdx l := fun h => hkl (lkIdx_inj h)
      rw [hadj _ _ (lkIdx_ne k) (lkIdx_ne l) hidx]
      constructor
      · intro h; exact ⟨hkl, h⟩
      · intro h; exact (show lkAdj k l from h).2
  exact ⟨(⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun {k l} => hrel k l⟩ :
    LK33e ≃g G.induce (w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)})).symm.trans lkIsoLine⟩

open Workspace.Types.Classes.SPGT in
/-- **If some induced subgraph of `G` is isomorphic to `L(K₃,₃ \ e)`, then `G ∉ F₃`.** -/
theorem not_inF3_of_iso {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {K : Set V} (e : Nonempty (G.induce K ≃g LK33e)) : ¬ InF3 G := by
  intro hF
  obtain ⟨e⟩ := e
  exact (hF.2 6 K33e K33e_isBipartiteSubdivision).1 ⟨K, ⟨e.trans lkIsoLine⟩⟩

open Workspace.Types.Classes.SPGT in
/-- **If some induced subgraph of `Ḡ` is isomorphic to `L(K₃,₃ \ e)`, then `G ∉ F₃`.** -/
theorem not_inF3_of_iso_compl {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {K : Set V} (e : Nonempty (Gᶜ.induce K ≃g LK33e)) : ¬ InF3 G := by
  intro hF
  obtain ⟨e⟩ := e
  exact (hF.2 6 K33e K33e_isBipartiteSubdivision).2 ⟨K, ⟨e.trans lkIsoLine⟩⟩

open Workspace.Types.Classes.SPGT in
/-- **The form 15.1 needs.**  If eight vertices of `G`, indexed by the edges of `K₃,₃ \ e`, are
pairwise distinct and adjacent exactly when the corresponding edges of `K₃,₃` share an end,
then `G ∉ F₃`.

`w p` stands for the `K₃,₃`-edge `x_{p.1} y_{p.2}`; the deleted edge is `x₂y₂`, so `w (2,2)`
is never looked at and may be given any value. -/
theorem not_inF3_of_LK33e {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (w : Fin 3 × Fin 3 → V)
    (hne : ∀ p q, p ≠ (2, 2) → q ≠ (2, 2) → p ≠ q → w p ≠ w q)
    (hadj : ∀ p q, p ≠ (2, 2) → q ≠ (2, 2) → p ≠ q →
      (G.Adj (w p) (w q) ↔ (p.1 = q.1 ∨ p.2 = q.2))) :
    ¬ InF3 G := by
  intro hF
  exact (hF.2 6 K33e K33e_isBipartiteSubdivision).1
    ⟨w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)}, lk33e_iso_induce w hne hadj⟩

open Workspace.Types.Classes.SPGT in
/-- The `Ḡ` twin of `not_inF3_of_LK33e`. -/
theorem not_inF3_of_LK33e_compl {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (w : Fin 3 × Fin 3 → V)
    (hne : ∀ p q, p ≠ (2, 2) → q ≠ (2, 2) → p ≠ q → w p ≠ w q)
    (hadj : ∀ p q, p ≠ (2, 2) → q ≠ (2, 2) → p ≠ q →
      (Gᶜ.Adj (w p) (w q) ↔ (p.1 = q.1 ∨ p.2 = q.2))) :
    ¬ InF3 G := by
  intro hF
  exact (hF.2 6 K33e K33e_isBipartiteSubdivision).2
    ⟨w '' {p : Fin 3 × Fin 3 | p ≠ (2, 2)}, lk33e_iso_induce w hne hadj⟩

end Workspace.ProofLemmas.LK33eAppearance
