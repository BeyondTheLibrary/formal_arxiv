import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.Prisms

/-!
# A shared constructor for the five *"can be linked onto the triangle"* steps of 10.1

PAPER (proof of 10.1, printed pp. 56–58).  Five times the argument builds three explicit paths
inside the prism and appeals to 2.4:

1. *"`c₁` can be linked onto the triangle `A`, via the paths `c₁-C₁-a₁`, `c₁-f₁-c₂-C₂-a₂`, and
   `c₁-D₁-b₁-b₃-R₃-a₃`, contrary to 2.4, since `f` has at most one neighbour in `A`"*
   (claim (1), the case `c₁ = d₁`);
2. *"it can be linked onto `A`, via `f₁-c₁-C₁-a₁`, `f₁-c₂-C₂-a₂` and `f₁-d₁-D₁-b₁-b₃-R₃-a₃`,
   contrary to 2.4"* (claim (1), the case `c₁` nonadjacent to `d₁`);
3. *"Since `f₁` is not major, we may assume that it has at most one neighbour in `A` … and
   therefore cannot be linked onto `A`"* (claim (1), the case where `X` meets all three paths —
   the three paths there are `C₁, C₂, C₃`);
4. *"`a₂` can be linked onto the triangle `B`, via `a₂-fₙ-fₙ₋₁-⋯-f₁-d₁-D₁-b₁`, `a₂-R₂-b₂`,
   `a₂-a₃-R₃-b₃`, contrary to 2.4"* (claim (2));
5. *"`c₁` can be linked onto `A`, via `c₁-C₁-a₁`, `c₁-f₁-⋯-fₙ-c₂-C₂-a₂`, `c₁-D₁-b₁-b₃-R₃-a₃`"*
   and *"`f₁` can be linked onto `A` via `f₁-c₁-C₁-a₁`, `f₁-⋯-fₙ-c₂-C₂-a₂`,
   `f₁-d₁-D₁-b₁-b₃-R₃-a₃`"* (the closing paragraph).

Every one of them has to discharge the same two clauses of
`Workspace.Types.RousselRubio.SPGT.VertexLinkedOntoTriangle` (`Types/RousselRubio.lean:100`):

* *"the three paths `P₁, P₂, P₃` are mutually vertex-disjoint"* — three list-level clauses
  `∀ x ∈ p₁, x ∉ p₂` etc.;
* *"for `1 ≤ i < j ≤ 3`, `aᵢaⱼ` is the unique edge of `G` between `V(Pᵢ)` and `V(Pⱼ)`"* — three
  list-level *iff*s.

## What this module factors out, and why in this shape

`linkedOntoTriangle_of_sectors` below reduces those six list-level clauses to **one** uniform
set-level clause.  The caller chooses, for each `i`, a *sector* `S i : Set V` containing its
`i`-th path, and proves once and for all

```
∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, G.Adj x y → x = c i ∧ y = c j
```

together with pairwise disjointness of the sectors.  The `←` halves of the three *iff*s need
only `G.Adj (c i) (c j)`, which is supplied once by `htri`.

Why *sectors* rather than the three paths themselves?  Because at each of the five call sites
the paths are built by concatenation (`c₁-D₁-b₁-b₃-R₃-a₃` runs along `R₁`, crosses the edge
`b₁b₃` and comes back along `R₃`; `c₁-f₁-⋯-fₙ-c₂-C₂-a₂` runs through `F` and then along `R₂`),
and it is much easier to name the *vertex set* the concatenation lives in than to reason about
membership in the concatenated list.  The five sector triples are, in the order above:

| # | `S 0` | `S 1` | `S 2` | triangle |
|---|---|---|---|---|
| 1 | `V(C₁)` | `F ∪ V(C₂)` | `V(D₁) ∪ V(R₃)` | `A` |
| 2 | `V(C₁)` | `V(C₂)` | `V(D₁) ∪ V(R₃)` | `A` |
| 3 | `V(C₁)` | `V(C₂)` | `V(C₃)` | `A` |
| 4 | `F ∪ V(D₁)` | `V(R₂) \ {a₂}` | `V(R₃)` | `B` |
| 5 | `V(C₁)` | `F ∪ V(C₂)` | `V(D₁) ∪ V(R₃)` | `A` |

and in each case the cross-edge clause comes from two ingredients only: the prism's own
*"the only edges between `V(Rᵢ)` and `V(Rⱼ)` are `aᵢaⱼ` and `bᵢbⱼ`"*
(`PrismSymmetry.formPrism_family`, whose cross clause is already stated as `∀ i j, i ≠ j → …`,
so it plugs straight in), and the description of the edges between `F` and `V(K)` that the
surrounding case of 10.1 has already established.

`canBeLinkedOntoTriangle_of_sectors` is the existentially-quantified form, which is the shape
2.4 (`Workspace.Statements.S02.SPGT.thm_2_4`) actually consumes.

`canBeLinkedOntoTriangle_of_prism_segments` is the degenerate instance in which each sector is
just the path itself and each path lies on the corresponding `Rᵢ` avoiding `bᵢ`; it is exactly
application 3 above (the paths `C₁, C₂, C₃`), and is stated separately because there the
cross-edge clause is discharged from `FormPrism` alone.

**Call site**: the proofs of `Workspace.ProofLemmas.Thm101ClaimOne.claim_one`,
`Workspace.ProofLemmas.Thm101ClaimTwo.claim_two` and
`Workspace.ProofLemmas.Thm101Endgame.endgame`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101LinkOntoTriangle

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem prism_path (G : SimpleGraph V) {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (i : Fin 3) :
    IsPathFrom G (R i) (a i) (b i) := by
  fin_cases i
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1

private theorem path_two_le (G : SimpleGraph V) {p : List V} {x y : V}
    (hp : IsPathFrom G p x y) (hxy : x ≠ y) : 2 ≤ p.length := by
  cases p with
  | nil =>
    exact False.elim (hp.1.1 rfl)
  | cons z zs =>
    cases zs with
    | nil =>
      exfalso
      apply hxy
      have hx : z = x := by simpa using hp.2.1
      have hy : z = y := by simpa using hp.2.2
      exact hx.symm.trans hy
    | cons z' zs =>
      simp

private theorem path_has_neighbor (G : SimpleGraph V) {p : List V}
    (hp : IsPathList G p) (h2 : 2 ≤ p.length) {u : V} (hu : u ∈ p) :
    ∃ w ∈ p, G.Adj u w := by
  obtain ⟨k, hk, hku⟩ := List.getElem_of_mem hu
  by_cases hk1 : k + 1 < p.length
  · refine ⟨p[k + 1]'hk1, List.getElem_mem _, ?_⟩
    rw [← hku]
    exact (hp.2.2 k (k + 1) hk hk1).mpr (Or.inl rfl)
  · have hk0 : 1 ≤ k := by omega
    refine ⟨p[k - 1]'(by omega), List.getElem_mem _, ?_⟩
    rw [← hku, SimpleGraph.adj_comm]
    exact (hp.2.2 (k - 1) k (by omega) hk).mpr (Or.inl (by omega))

private theorem flip_cross (G : SimpleGraph V) {P Q : List V} {a₁ a₂ b₁ b₂ : V}
    (hc : ∀ u ∈ P, ∀ w ∈ Q,
      (G.Adj u w ↔ (u = a₁ ∧ w = a₂) ∨ (u = b₁ ∧ w = b₂))) :
    ∀ u ∈ Q, ∀ w ∈ P,
      (G.Adj u w ↔ (u = a₂ ∧ w = a₁) ∨ (u = b₂ ∧ w = b₁)) := by
  intro u hu w hw
  rw [SimpleGraph.adj_comm, hc w hw u hu]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩

private theorem prism_cross (G : SimpleGraph V) {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    ∀ u ∈ R i, ∀ w ∈ R j,
      (G.Adj u w ↔ (u = a i ∧ w = a j) ∨ (u = b i ∧ w = b j)) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact flip_cross G h.2.2.2.2.2.2.1
  · exact (hij rfl).elim
  · exact h.2.2.2.2.2.2.2.2
  · exact flip_cross G h.2.2.2.2.2.2.2.1
  · exact flip_cross G h.2.2.2.2.2.2.2.2
  · exact (hij rfl).elim

private theorem prism_disjoint (G : SimpleGraph V) {a b : Fin 3 → V}
    {R : Fin 3 → List V} (h : FormPrism G a b (R 0) (R 1) (R 2))
    {i j : Fin 3} (hij : i ≠ j) : ∀ u ∈ R i, u ∉ R j := by
  intro u hu huj
  obtain ⟨w, hw, hadjw⟩ :=
    path_has_neighbor G (prism_path G h j).1
      (path_two_le G (prism_path G h j) (h.2.2.1 j j)) huj
  obtain ⟨w', hw', hadjw'⟩ :=
    path_has_neighbor G (prism_path G h i).1
      (path_two_le G (prism_path G h i) (h.2.2.1 i i)) hu
  have h1 := (prism_cross G h hij u hu w hw).mp hadjw
  have h2 := (prism_cross G h hij.symm u huj w' hw').mp hadjw'
  rcases h1 with ⟨e1, -⟩ | ⟨e1, -⟩ <;>
    rcases h2 with ⟨e2, -⟩ | ⟨e2, -⟩
  · exact (h.1 i j hij).ne (e1.symm.trans e2)
  · exact h.2.2.1 i j (e1.symm.trans e2)
  · exact h.2.2.1 j i (e2.symm.trans e1)
  · exact (h.2.1 i j hij).ne (e1.symm.trans e2)

/-- **The three paths of a linkage, presented by sectors.**

PAPER (printed p. 9): *"We say a vertex `v` can be linked onto a triangle `{a₁,a₂,a₃}` (via
paths `P₁,P₂,P₃`) if: the three paths `P₁,P₂,P₃` are mutually vertex-disjoint; for `i = 1,2,3`
`aᵢ` is an end of `Pᵢ`; for `1 ≤ i < j ≤ 3`, `aᵢaⱼ` is the unique edge of `G` between `V(Pᵢ)`
and `V(Pⱼ)`; `v` has a neighbour in each of `P₁,P₂` and `P₃`."*

`p i` is the `i`-th path and `S i` a set of vertices containing it.  Disjointness of the paths
and the uniqueness of the cross edges are inherited from the sectors, so the caller states them
once, at the level of sets. -/
theorem linkedOntoTriangle_of_sectors (G : SimpleGraph V) (v : V)
    (c : Fin 3 → V) (p : Fin 3 → List V) (S : Fin 3 → Set V)
    (htri : ∀ i j : Fin 3, i ≠ j → G.Adj (c i) (c j))
    (hpath : ∀ i : Fin 3, IsPathList G (p i))
    (hend : ∀ i : Fin 3, (p i).head? = some (c i) ∨ (p i).getLast? = some (c i))
    (hsub : ∀ i : Fin 3, ∀ x ∈ p i, x ∈ S i)
    (hdisj : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ S i, x ∉ S j)
    (hcross : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, G.Adj x y → x = c i ∧ y = c j)
    (hnbr : ∀ i : Fin 3, ∃ x ∈ p i, G.Adj v x) :
    VertexLinkedOntoTriangle G v (c 0) (c 1) (c 2) (p 0) (p 1) (p 2) := by
  refine ⟨⟨hpath 0, hpath 1, hpath 2⟩, ?_, ⟨hend 0, hend 1, hend 2⟩, ?_,
    ⟨hnbr 0, hnbr 1, hnbr 2⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx0 hx1
      exact hdisj 0 1 (by decide) x (hsub 0 x hx0) (hsub 1 x hx1)
    · intro x hx0 hx2
      exact hdisj 0 2 (by decide) x (hsub 0 x hx0) (hsub 2 x hx2)
    · intro x hx1 hx2
      exact hdisj 1 2 (by decide) x (hsub 1 x hx1) (hsub 2 x hx2)
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      constructor
      · exact hcross 0 1 (by decide) x (hsub 0 x hx) y (hsub 1 y hy)
      · rintro ⟨rfl, rfl⟩
        exact htri 0 1 (by decide)
    · intro x hx y hy
      constructor
      · exact hcross 0 2 (by decide) x (hsub 0 x hx) y (hsub 2 y hy)
      · rintro ⟨rfl, rfl⟩
        exact htri 0 2 (by decide)
    · intro x hx y hy
      constructor
      · exact hcross 1 2 (by decide) x (hsub 1 x hx) y (hsub 2 y hy)
      · rintro ⟨rfl, rfl⟩
        exact htri 1 2 (by decide)

/-- The *"can be linked"* form of `linkedOntoTriangle_of_sectors`: this is the shape that
`Workspace.Statements.S02.SPGT.thm_2_4` consumes. -/
theorem canBeLinkedOntoTriangle_of_sectors (G : SimpleGraph V) (v : V)
    (c : Fin 3 → V) (p : Fin 3 → List V) (S : Fin 3 → Set V)
    (htri : ∀ i j : Fin 3, i ≠ j → G.Adj (c i) (c j))
    (hpath : ∀ i : Fin 3, IsPathList G (p i))
    (hend : ∀ i : Fin 3, (p i).head? = some (c i) ∨ (p i).getLast? = some (c i))
    (hsub : ∀ i : Fin 3, ∀ x ∈ p i, x ∈ S i)
    (hdisj : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ S i, x ∉ S j)
    (hcross : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, G.Adj x y → x = c i ∧ y = c j)
    (hnbr : ∀ i : Fin 3, ∃ x ∈ p i, G.Adj v x) :
    VertexCanBeLinkedOntoTriangle G v (c 0) (c 1) (c 2) := by
  exact ⟨p 0, p 1, p 2,
    linkedOntoTriangle_of_sectors G v c p S htri hpath hend hsub hdisj hcross hnbr⟩

/-- The instance in which the three paths are the `aᵢ`-side subpaths `C₁, C₂, C₃` of the three
paths of the prism — the third of the five applications of 2.4 in the proof of 10.1
(*"Since `f₁` is not major, we may assume that it has at most one neighbour in `A` … and
therefore cannot be linked onto `A`"*).  Here each sector is the path itself, and the
cross-edge clause is discharged from `FormPrism` alone: `p i` lies on `R i` and avoids `b i`,
so the only surviving cross edges are the `aᵢaⱼ`. -/
theorem canBeLinkedOntoTriangle_of_prism_segments (G : SimpleGraph V)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (v : V) (p : Fin 3 → List V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hpath : ∀ i : Fin 3, IsPathList G (p i))
    (hsub : ∀ i : Fin 3, ∀ x ∈ p i, x ∈ R i)
    (hend : ∀ i : Fin 3, (p i).head? = some (a i) ∨ (p i).getLast? = some (a i))
    (hb : ∀ i : Fin 3, b i ∉ p i)
    (hnbr : ∀ i : Fin 3, ∃ x ∈ p i, G.Adj v x) :
    VertexCanBeLinkedOntoTriangle G v (a 0) (a 1) (a 2) := by
  apply canBeLinkedOntoTriangle_of_sectors G v a p (fun i => {x | x ∈ p i})
  · exact hprism.1
  · exact hpath
  · exact hend
  · intro i x hx
    exact hx
  · intro i j hij x hx hxj
    exact prism_disjoint G hprism hij x (hsub i x hx) (hsub j x hxj)
  · intro i j hij x hx y hy hxy
    rcases (prism_cross G hprism hij x (hsub i x hx) y (hsub j y hy)).mp hxy with ha | hbxy
    · exact ha
    · exact False.elim (hb i (hbxy.1 ▸ hx))
  · exact hnbr

end Workspace.ProofLemmas.Thm101LinkOntoTriangle
