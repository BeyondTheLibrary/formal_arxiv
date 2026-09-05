import Mathlib

/-!
# The basic classes of perfect graphs (Section 1 of the published paper, pp. 1–2)

Three definitions from the introduction of *The Strong Perfect Graph Theorem*
(Chudnovsky, Robertson, Seymour, Thomas; `perfect.pdf`, printed pages 1–2):

* `SPGT.IsLineGraphOfBipartite` — `G` is (isomorphic to) the line graph of a bipartite graph;
* `SPGT.IsDoubleSplitGraph` — `G` is a *double split graph*;
* `SPGT.IsBasic` — `G` is *basic*.
-/

namespace Workspace.Types.BasicClasses

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Line graph of a bipartite graph** (published paper, p. 2).

> "The *line graph* `L(G)` of a graph `G` has vertex set the set `E(G)` of edges of `G`, and
> `e,f ∈ E(G)` are adjacent in `L(G)` if they share an end in `G`."

and, from the definition of *basic*,

> "either `G` or `Ḡ` is bipartite or is the line graph of a bipartite graph".

`L(H)` is Mathlib's `SimpleGraph.lineGraph` (for `H : SimpleGraph W` it is a
`SimpleGraph H.edgeSet`, exactly the paper's vertex set `E(H)`, with two edges adjacent iff
they are distinct and meet), and "bipartite" is Mathlib's `SimpleGraph.IsBipartite`
(an abbreviation for `Colorable 2`).

All graphs in the paper are finite, so the bipartite graph `H` is quantified as a graph on
`Fin n` for some `n : ℕ`: every finite simple graph is isomorphic to such an `H`, and this
avoids universe polymorphism in the existential. "`G` is the line graph of `H`" is read, as
always in the paper, up to isomorphism. -/
def IsLineGraphOfBipartite (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n)), H.IsBipartite ∧ Nonempty (G ≃g H.lineGraph)

/-- **Double split graph** (published paper, pp. 1–2).

> "We say that `G` is a *double split graph* if `V(G)` can be partitioned into four sets
> `{a₁,…,a_m}`, `{b₁,…,b_m}`, `{c₁,…,c_n}`, `{d₁,…,d_n}` for some `m,n ≥ 2`, such that:
>
> * `aᵢ` is adjacent to `bᵢ` for `1 ≤ i ≤ m`, and `c_j` is nonadjacent to `d_j` for `1 ≤ j ≤ n`
> * there are no edges between `{aᵢ,bᵢ}` and `{a_{i'},b_{i'}}` for `1 ≤ i < i' ≤ m`, and all four
>   edges between `{c_j,d_j}` and `{c_{j'},d_{j'}}` for `1 ≤ j < j' ≤ n`
> * there are exactly two edges between `{aᵢ,bᵢ}` and `{c_j,d_j}` for `1 ≤ i ≤ m` and
>   `1 ≤ j ≤ n`, and these two edges have no common end."
>
> "(The name is because such a graph can be obtained from what is called a 'split graph' by
> doubling each vertex)."

(The printed text spells "partioned"; that is a typo for "partitioned".)

Encoding notes.

* "`V(G)` can be **partitioned** into four sets `{a₁,…,a_m}`, `{b₁,…,b_m}`, `{c₁,…,c_n}`,
  `{d₁,…,d_n}`" is rendered by requiring the combined indexing map
  `Sum.elim (Sum.elim a b) (Sum.elim c d) : (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n) → V`
  to be a **bijection**. Injectivity says the `2m + 2n` listed vertices are pairwise distinct
  (so the four sets are pairwise disjoint and each has no repetitions, i.e. `|{a₁,…,a_m}| = m`
  and so on); surjectivity says they cover `V(G)`.
* The paper's index conditions are `1 ≤ i < i' ≤ m` (resp. `1 ≤ j < j' ≤ n`); quantifying over
  `i ≠ i'` in `Fin m` (resp. `j ≠ j'` in `Fin n`) is equivalent, because each of the two blocks
  of four conditions is, as a block, invariant under swapping `i, i'` (resp. `j, j'`), adjacency
  in a simple graph being symmetric.
* "there are **exactly two** edges between `{aᵢ,bᵢ}` and `{c_j,d_j}` … and these two edges have
  no common end": the only candidate edges are the four pairs `aᵢc_j, aᵢd_j, bᵢc_j, bᵢd_j`, and
  the only two-element sets of candidates with no common end are `{aᵢc_j, bᵢd_j}` and
  `{aᵢd_j, bᵢc_j}`. Hence the condition is exactly the printed two-case disjunction below; the
  negative conjuncts are what makes it "exactly two" rather than "at least two". -/
def IsDoubleSplitGraph (G : SimpleGraph V) : Prop :=
  ∃ (m n : ℕ) (a b : Fin m → V) (c d : Fin n → V),
    2 ≤ m ∧ 2 ≤ n ∧
    Function.Bijective (Sum.elim (Sum.elim a b) (Sum.elim c d)) ∧
    (∀ i : Fin m, G.Adj (a i) (b i)) ∧
    (∀ j : Fin n, ¬ G.Adj (c j) (d j)) ∧
    (∀ i i' : Fin m, i ≠ i' →
      ¬ G.Adj (a i) (a i') ∧ ¬ G.Adj (a i) (b i') ∧
      ¬ G.Adj (b i) (a i') ∧ ¬ G.Adj (b i) (b i')) ∧
    (∀ j j' : Fin n, j ≠ j' →
      G.Adj (c j) (c j') ∧ G.Adj (c j) (d j') ∧
      G.Adj (d j) (c j') ∧ G.Adj (d j) (d j')) ∧
    (∀ (i : Fin m) (j : Fin n),
      (G.Adj (a i) (c j) ∧ G.Adj (b i) (d j) ∧ ¬ G.Adj (a i) (d j) ∧ ¬ G.Adj (b i) (c j)) ∨
      (¬ G.Adj (a i) (c j) ∧ ¬ G.Adj (b i) (d j) ∧ G.Adj (a i) (d j) ∧ G.Adj (b i) (c j)))

/-- **Basic graph** (published paper, p. 2).

> "Let us say a graph `G` is *basic* if either `G` or `Ḡ` is bipartite or is the line graph of a
> bipartite graph, or is a double split graph. (Note that if `G` is a double split graph then so
> is `Ḡ`.)"

The paper's `Ḡ` is Mathlib's `Gᶜ`. The parenthetical remark is flagged by the authors as a
consequence, not as part of the definition, so it is not a conjunct here. -/
def IsBasic (G : SimpleGraph V) : Prop :=
  (G.IsBipartite ∨ IsLineGraphOfBipartite G ∨ IsDoubleSplitGraph G) ∨
  (Gᶜ.IsBipartite ∨ IsLineGraphOfBipartite Gᶜ ∨ IsDoubleSplitGraph Gᶜ)

end SPGT

end Workspace.Types.BasicClasses
