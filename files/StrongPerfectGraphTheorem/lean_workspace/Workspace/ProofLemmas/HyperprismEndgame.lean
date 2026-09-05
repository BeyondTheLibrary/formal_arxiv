import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismNineVertices

/-!
# 10.6, the closing paragraph (P8)

This module is the last paragraph of the printed proof of **10.6** (published version,
printed p. 63):

> *"From (2) it follows that for every component of `V(G) \ V(H)`, all its attachments in `H`
> are a subset of one of `S₁, S₂, S₃`.  Let `X` be the union of `S₁` and all components of
> `V(G) \ V(H)` whose attachment set is a subset of `S₁`, and let `Y = V(G) \ X`.  Then
> `|Y| ≥ 4`, and so either `(X,Y)` is a proper 2-join in `G`, or both `A₁, B₁` have one
> element and `X` is the vertex set of a path between these two vertices.  We may assume the
> latter, and the same for `S₂` and `S₃`; and so `G` is an even prism.  Then either it admits
> a proper 2-join, or `|V(G)| = 9`.  This proves 10.6."*

`thm_10_6_endgame` is that paragraph.  Its last two sentences are already available as
`HyperprismNineVertices.thm_10_6_all_degenerate` (P9), so what is added here is the
construction of `X` and the trichotomy.

## How the printed sentences map onto the Lean proof

* *"Let `X` be the union of `S₁` and all components of `V(G) \ V(H)` whose attachment set is
  a subset of `S₁`"* is `sideSet G A B C i`, written for a general index `i` because the
  paper immediately says *"and the same for `S₂` and `S₃`"*.  `Y = V(G) \ X` is then
  `sideSet G A B C j ∪ sideSet G A B C k` for the other two indices — that this really is the
  complement of `X` is `sideSet_cover` (they exhaust `V(G)`) plus `notMem_sideSet` (they are
  pairwise disjoint).

* **The standing assumption `hne`.**  The sentence immediately before this paragraph reads
  *"So we may assume there is no such `F`"*, where *such an `F`* is a component of
  `V(G) \ V(H)` all of whose attachments lie in `A` (and, by the following clause, in `B`).
  A component with **no** attachments at all is in particular such an `F`, so under that
  standing assumption every nonempty component of `V(G) \ V(H)` has a nonempty attachment
  set.  That is exactly `hne`, and it is what makes the paper's `X` well defined: the index
  `i` with *"attachment set a subset of `Sᵢ`"* is then unique, because `S₁, S₂, S₃` are
  pairwise disjoint.  (Without it the three `X`'s overlap and the construction degenerates —
  a component floating free of `H` would have to be put into all three at once.)

* *"either `(X,Y)` is a proper 2-join in `G`, or both `A₁, B₁` have one element and `X` is the
  vertex set of a path between these two vertices"* is `admitsProper2Join_of_not_degenerate`:
  the second alternative is precisely the antecedent of the fourth bullet of
  `IsProper2Join` on the `X` side, so when it fails that bullet holds vacuously, and the
  other bullets are verified unconditionally.
  - Bullets 1–2 (*"which edges run between `X` and `Y`"*) are `sideSet_cross`: an edge
    leaving `Xᵢ` can only be an edge of `H`, because a vertex of a component `F ⊆ Xᵢ` has all
    its `V(H)`-neighbours inside `Sᵢ` and no neighbour in another component.
  - Bullet 3 (*"every component of `G|Xᵢ` meets both `Aᵢ` and `Bᵢ`"*) is `component_meets`:
    a component of `G|X` containing a vertex of a hanging component `F` also contains an
    attachment of `F`, hence a vertex of `Sᵢ`, hence — since every vertex of `Sᵢ` lies on an
    `i`-rung, and rungs are connected subsets of `Sᵢ` — a whole `i`-rung, whose two ends are
    in `Aᵢ` and `Bᵢ`.
  - The fourth bullet on the **`Y`** side is where the paper's *"Then `|Y| ≥ 4`"* is used.
    We use instead that `|A₂ ∪ A₃| ≥ 2` (the two sets are nonempty and disjoint), which makes
    that bullet's antecedent `A_Y = {a}` unsatisfiable.  This is the same fact in a sharper
    form: `|Y| ≥ 4` on its own rules out only the *"length `≥ 3`"* half of the bullet, not the
    *"odd"* half, whereas `A_Y` not being a singleton rules out the bullet outright.

* *"We may assume the latter, and the same for `S₂` and `S₃`; and so `G` is an even prism.
  Then either it admits a proper 2-join, or `|V(G)| = 9`."* is the `hall` branch: all three
  `Xᵢ` degenerate to paths, and `HyperprismNineVertices.thm_10_6_all_degenerate` (P9) finishes.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C : Fin 3 → Set V}

private theorem dl {X Y : Set V} (h : Disjoint X Y) {x : V} (hx : x ∈ X) : x ∉ Y :=
  Set.disjoint_left.mp h hx

/-- Three pairwise distinct indices exhaust `Fin 3`. -/
private theorem fin3_triple : ∀ i j k l : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    (l = i ∨ l = j ∨ l = k) := by decide

/-- Every index has two distinct companions. -/
private theorem fin3_other : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide

/-! ### The paper's `X` -/

/-- PAPER (printed p. 63): *"Let `X` be the union of `S₁` and all components of
`V(G) \ V(H)` whose attachment set is a subset of `S₁`"*, written for a general index `i`
because the next sentence is *"and the same for `S₂` and `S₃`"*. -/
def sideSet (G : SimpleGraph V) (A B C : Fin 3 → Set V) (i : Fin 3) : Set V :=
  (A i ∪ B i ∪ C i) ∪
    {v : V | ∃ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F ∧ v ∈ F ∧
      attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i}

theorem mem_sideSet_iff {i : Fin 3} {v : V} :
    v ∈ sideSet G A B C i ↔ v ∈ A i ∪ B i ∪ C i ∨
      ∃ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F ∧ v ∈ F ∧
        attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i := Iff.rfl

theorem S_subset_sideSet (i : Fin 3) : A i ∪ B i ∪ C i ⊆ sideSet G A B C i :=
  fun _ hx => Or.inl hx

theorem comp_subset_sideSet {i : Fin 3} {F : Set V}
    (hF : IsComponent G (hyperVerts A B C)ᶜ F)
    (hsub : attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i) :
    F ⊆ sideSet G A B C i :=
  fun _ hv => Or.inr ⟨F, hF, hv, hsub⟩

theorem sideSet_nonempty (hH : IsHyperprism G A B C) (i : Fin 3) :
    (sideSet G A B C i).Nonempty := by
  obtain ⟨x, hx⟩ := (hH.1 i).1
  exact ⟨x, S_subset_sideSet i (Or.inl (Or.inl hx))⟩

/-- *"From (2) it follows that for every component of `V(G) \ V(H)`, all its attachments in
`H` are a subset of one of `S₁, S₂, S₃`"* — hence every vertex of `G` lies in some `Xᵢ`. -/
theorem exists_mem_sideSet
    (hloc : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F →
      ∃ i : Fin 3, attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i)
    (v : V) : ∃ i : Fin 3, v ∈ sideSet G A B C i := by
  by_cases hv : v ∈ hyperVerts A B C
  · obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hv
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨F, hF, hvF⟩ :=
      ComponentsOfSetBasics.exists_isComponent_mem G (hyperVerts A B C)ᶜ hv
    obtain ⟨i, hi⟩ := hloc F hF
    exact ⟨i, Or.inr ⟨F, hF, hvF, hi⟩⟩

/-- The three `Xᵢ` exhaust `V(G)`; this is what makes `Y = V(G) \ X` the union of the other
two. -/
theorem sideSet_cover
    (hloc : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F →
      ∃ i : Fin 3, attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i) :
    sideSet G A B C 0 ∪ sideSet G A B C 1 ∪ sideSet G A B C 2 = Set.univ := by
  ext v
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  obtain ⟨i, hi⟩ := exists_mem_sideSet hloc v
  rcases fin3_cases i with rfl | rfl | rfl
  exacts [Or.inl (Or.inl hi), Or.inl (Or.inr hi), Or.inr hi]

/-- The three `Xᵢ` are pairwise disjoint.  This is where the standing assumption `hne` — no
component of `V(G) \ V(H)` is attachment-free — is needed: a component with no attachments
would qualify for all three `Xᵢ` at once. -/
theorem notMem_sideSet (hH : IsHyperprism G A B C)
    (hne : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F → F.Nonempty →
      (attachments G F (hyperVerts A B C)).Nonempty)
    {i j : Fin 3} (hij : i ≠ j) {v : V} (hv : v ∈ sideSet G A B C i) :
    v ∉ sideSet G A B C j := by
  intro hvj
  rcases mem_sideSet_iff.mp hv with hvi | ⟨F, hF, hvF, hsub⟩
  · rcases mem_sideSet_iff.mp hvj with hvj' | ⟨F', hF', hvF', -⟩
    · exact notMem_S hH hij hvi hvj'
    · exact hF'.1 hvF' (subset_hyperVerts i hvi)
  · rcases mem_sideSet_iff.mp hvj with hvj' | ⟨F', hF', hvF', hsub'⟩
    · exact hF.1 hvF (subset_hyperVerts j hvj')
    · have hFF : F = F' := by
        by_contra hFF
        exact (Set.disjoint_left.mp
          (ComponentsOfSetBasics.disjoint_of_isComponent G hF hF' hFF)) hvF hvF'
      subst hFF
      obtain ⟨w, hw⟩ := hne F hF ⟨v, hvF⟩
      exact notMem_S hH hij (hsub hw) (hsub' hw)

/-- **Bullets 1 and 2 of the 2-join**: the only edges between `Xᵢ` and `Xⱼ` are the edges of
`H` between `Aᵢ` and `Aⱼ` and between `Bᵢ` and `Bⱼ`.

A vertex of a component `F` hanging on `Xᵢ` has all its `V(H)`-neighbours inside the
attachment set of `F`, which is inside `Sᵢ`; and distinct components of `V(G) \ V(H)` are
anticomplete to one another. -/
theorem sideSet_cross (hH : IsHyperprism G A B C)
    (hne : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F → F.Nonempty →
      (attachments G F (hyperVerts A B C)).Nonempty)
    {i j : Fin 3} (hij : i ≠ j) {u v : V}
    (hu : u ∈ sideSet G A B C i) (hv : v ∈ sideSet G A B C j) (hadj : G.Adj u v) :
    (u ∈ A i ∧ v ∈ A j) ∨ (u ∈ B i ∧ v ∈ B j) := by
  rcases mem_sideSet_iff.mp hu with hui | ⟨F, hF, huF, hsub⟩
  · rcases mem_sideSet_iff.mp hv with hvj | ⟨F', hF', hvF', hsub'⟩
    · exact cross hH hij hui hvj hadj
    · exfalso
      have hatt : u ∈ attachments G F' (hyperVerts A B C) :=
        ⟨subset_hyperVerts i hui, v, hvF', hadj⟩
      exact notMem_S hH hij hui (hsub' hatt)
  · rcases mem_sideSet_iff.mp hv with hvj | ⟨F', hF', hvF', hsub'⟩
    · exfalso
      have hatt : v ∈ attachments G F (hyperVerts A B C) :=
        ⟨subset_hyperVerts j hvj, u, huF, hadj.symm⟩
      exact notMem_S hH hij (hsub hatt) hvj
    · exfalso
      by_cases hFF : F = F'
      · subst hFF
        obtain ⟨w, hw⟩ := hne F hF ⟨u, huF⟩
        exact notMem_S hH hij (hsub hw) (hsub' hw)
      · exact ComponentsOfSetBasics.anticomplete_of_isComponent G hF hF' hFF u huF v hvF' hadj

/-- **Bullet 3 of the 2-join.**  Let `D` be a component of a set `W` containing `Xₗ`, and let
`D` contain a vertex of `Xₗ`.  Then `D` meets both `Aₗ` and `Bₗ`.

The vertex is either already in `Sₗ`, or lies in a hanging component `F`; in the latter case
`F` together with any one of its attachments is a connected subset of `W` meeting `D`, so
maximality of `D` swallows it and puts that attachment — a vertex of `Sₗ` — into `D`.  Every
vertex of `Sₗ` lies on an `l`-rung, and an `l`-rung is a connected subset of `Sₗ ⊆ W`, so
maximality swallows the whole rung, whose two ends are in `Aₗ` and `Bₗ`. -/
theorem component_meets (hH : IsHyperprism G A B C)
    (hne : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F → F.Nonempty →
      (attachments G F (hyperVerts A B C)).Nonempty)
    {W D : Set V} (hD : IsComponent G W D) {l : Fin 3}
    (hWl : sideSet G A B C l ⊆ W) {v : V} (hvD : v ∈ D) (hvl : v ∈ sideSet G A B C l) :
    (D ∩ A l).Nonempty ∧ (D ∩ B l).Nonempty := by
  -- maximality of `D`: any connected subset of `W` meeting `D` is contained in `D`
  have key : ∀ {Z : Set V}, ConnectedSet G Z → Z ⊆ W → (D ∩ Z).Nonempty → Z ⊆ D := by
    intro Z hZ hZW hmeet
    obtain ⟨x, hxD, hxZ⟩ := hmeet
    have hcon : ConnectedSet G (D ∪ Z) :=
      ConnectedSetUnionAttach.connectedSet_union hD.2.1 hZ (Or.inl ⟨x, hxD, hxZ⟩)
    have heq : D ∪ Z = D :=
      hD.2.2 (D ∪ Z) Set.subset_union_left (Set.union_subset hD.1 hZW) hcon
    intro z hz
    rw [← heq]
    exact Or.inr hz
  -- Step 1: `D` meets `Sₗ`
  have hstep1 : ∃ w, w ∈ D ∧ w ∈ A l ∪ B l ∪ C l := by
    rcases mem_sideSet_iff.mp hvl with hvS | ⟨F, hF, hvF, hsub⟩
    · exact ⟨v, hvD, hvS⟩
    · obtain ⟨w, hw⟩ := hne F hF ⟨v, hvF⟩
      obtain ⟨hwH, f, hfF, hadj⟩ := hw
      have hwS : w ∈ A l ∪ B l ∪ C l := hsub ⟨hwH, f, hfF, hadj⟩
      have hZ : ConnectedSet G (F ∪ {w}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨f, hfF, hadj⟩
      have hZW : F ∪ {w} ⊆ W := by
        rintro z (hz | hz)
        · exact hWl (comp_subset_sideSet hF hsub hz)
        · rw [show z = w from hz]
          exact hWl (S_subset_sideSet l hwS)
      exact ⟨w, key hZ hZW ⟨v, hvD, Or.inl hvF⟩ (Or.inr rfl), hwS⟩
  obtain ⟨w, hwD, hwS⟩ := hstep1
  -- Step 2: the whole `l`-rung through `w` lies in `D`
  obtain ⟨p, x, y, hp, hwp⟩ := exists_rung_through hH l hwS
  have hpD : {z : V | z ∈ p} ⊆ D := by
    refine key (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp.2.2.1.1) ?_
      ⟨w, hwD, hwp⟩
    intro z hz
    exact hWl (S_subset_sideSet l (rung_mem_S hp z hz))
  exact ⟨⟨x, hpD (PathBasics.head_mem hp.2.2.1.2.1), hp.1⟩,
    ⟨y, hpD (PathBasics.getLast_mem hp.2.2.1.2.2), hp.2.1⟩⟩

/-! ### The trichotomy -/

/-- **PAPER** (printed p. 63): *"Then `|Y| ≥ 4`, and so either `(X,Y)` is a proper 2-join in
`G`, or both `A₁, B₁` have one element and `X` is the vertex set of a path between these two
vertices."*

`hnd` is the failure of the second alternative, and the conclusion is the first. -/
theorem admitsProper2Join_of_not_degenerate (hH : IsHyperprism G A B C)
    (hne : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F → F.Nonempty →
      (attachments G F (hyperVerts A B C)).Nonempty)
    (hloc : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F →
      ∃ i : Fin 3, attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hnd : ¬ ∃ (x y : V) (p : List V), A i = {x} ∧ B i = {y} ∧
      IsPathFrom G p x y ∧ {z : V | z ∈ p} = sideSet G A B C i) :
    AdmitsProper2Join G := by
  ------------------------------------------------------------------
  -- `(X, Y)` is a partition of `V(G)`.
  ------------------------------------------------------------------
  have hcover : sideSet G A B C i ∪ (sideSet G A B C j ∪ sideSet G A B C k) = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    obtain ⟨l, hl⟩ := exists_mem_sideSet hloc v
    rcases fin3_triple i j k l hij hik hjk with rfl | rfl | rfl
    exacts [Or.inl hl, Or.inr (Or.inl hl), Or.inr (Or.inr hl)]
  have hdisj : Disjoint (sideSet G A B C i) (sideSet G A B C j ∪ sideSet G A B C k) := by
    refine Set.disjoint_left.mpr ?_
    rintro v hv (h | h)
    · exact notMem_sideSet hH hne hij hv h
    · exact notMem_sideSet hH hne hik hv h
  ------------------------------------------------------------------
  -- The edges between `X` and `Y`.
  ------------------------------------------------------------------
  have hcross : ∀ u ∈ sideSet G A B C i, ∀ v ∈ sideSet G A B C j ∪ sideSet G A B C k,
      (G.Adj u v ↔ ((u ∈ A i ∧ v ∈ A j ∪ A k) ∨ (u ∈ B i ∧ v ∈ B j ∪ B k))) := by
    intro u hu v hv
    constructor
    · intro hadj
      rcases hv with hvj | hvk
      · rcases sideSet_cross hH hne hij hu hvj hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, Or.inl h2⟩
        · exact Or.inr ⟨h1, Or.inl h2⟩
      · rcases sideSet_cross hH hne hik hu hvk hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr ⟨h1, Or.inr h2⟩
    · rintro (⟨h1, (h2 | h2)⟩ | ⟨h1, (h2 | h2)⟩)
      · exact complete_A hH hij _ h1 _ h2
      · exact complete_A hH hik _ h1 _ h2
      · exact complete_B hH hij _ h1 _ h2
      · exact complete_B hH hik _ h1 _ h2
  ------------------------------------------------------------------
  -- Assembling `IsProper2Join`.
  ------------------------------------------------------------------
  obtain ⟨aj, hajA⟩ := (hH.1 j).1
  obtain ⟨ak, hakA⟩ := (hH.1 k).1
  refine ⟨sideSet G A B C i, sideSet G A B C j ∪ sideSet G A B C k, hcover, hdisj,
    A i, B i, A j ∪ A k, B j ∪ B k,
    fun z hz => S_subset_sideSet i (Or.inl (Or.inl hz)),
    fun z hz => S_subset_sideSet i (Or.inl (Or.inr hz)), ?_, ?_,
    (hH.1 i).1, (hH.1 i).2.1, ⟨aj, Or.inl hajA⟩, ?_, hH.2.1 i i, ?_, hcross, ?_, ?_, ?_, ?_⟩
  · -- `A₂ ⊆ X₂`
    rintro z (hz | hz)
    · exact Or.inl (S_subset_sideSet j (Or.inl (Or.inl hz)))
    · exact Or.inr (S_subset_sideSet k (Or.inl (Or.inl hz)))
  · -- `B₂ ⊆ X₂`
    rintro z (hz | hz)
    · exact Or.inl (S_subset_sideSet j (Or.inl (Or.inr hz)))
    · exact Or.inr (S_subset_sideSet k (Or.inl (Or.inr hz)))
  · -- `B₂` nonempty
    obtain ⟨bj, hbjB⟩ := (hH.1 j).2.1
    exact ⟨bj, Or.inl hbjB⟩
  · -- `Disjoint A₂ B₂`
    refine Set.disjoint_left.mpr ?_
    rintro z (hz | hz) (hz' | hz') <;> exact dl (hH.2.1 _ _) hz hz'
  · -- every component of `G|X` meets `A₁` and `B₁`
    intro D hD
    obtain ⟨v, hvD⟩ :=
      ComponentsOfSetBasics.nonempty_of_isComponent G (sideSet_nonempty hH i) hD
    exact component_meets hH hne hD (subset_refl _) hvD (hD.1 hvD)
  · -- every component of `G|Y` meets `A₂` and `B₂`
    intro D hD
    obtain ⟨v, hvD⟩ := ComponentsOfSetBasics.nonempty_of_isComponent G
      ⟨(sideSet_nonempty hH j).choose, Or.inl (sideSet_nonempty hH j).choose_spec⟩ hD
    rcases hD.1 hvD with hvj | hvk
    · obtain ⟨⟨x, hxD, hxA⟩, ⟨y, hyD, hyB⟩⟩ :=
        component_meets hH hne hD Set.subset_union_left hvD hvj
      exact ⟨⟨x, hxD, Or.inl hxA⟩, ⟨y, hyD, Or.inl hyB⟩⟩
    · obtain ⟨⟨x, hxD, hxA⟩, ⟨y, hyD, hyB⟩⟩ :=
        component_meets hH hne hD Set.subset_union_right hvD hvk
      exact ⟨⟨x, hxD, Or.inr hxA⟩, ⟨y, hyD, Or.inr hyB⟩⟩
  · -- fourth bullet on the `X` side: its antecedent is the excluded alternative
    intro x y hx hy p hp hpset
    exact absurd ⟨x, y, p, hx, hy, hp, hpset⟩ hnd
  · -- fourth bullet on the `Y` side: `A₂` has at least two elements, so it is not a singleton
    intro x y hx _ p _ _
    exfalso
    have h1 : aj = x := by
      have hm : aj ∈ A j ∪ A k := Or.inl hajA
      rw [hx] at hm; exact hm
    have h2 : ak = x := by
      have hm : ak ∈ A j ∪ A k := Or.inr hakA
      rw [hx] at hm; exact hm
    exact dl (hH.2.2.2.2.1 j k hjk) hajA (by rw [h1, ← h2]; exact hakA)

/-! ### The closing paragraph -/

/-- **The closing paragraph of the printed proof of 10.6** (printed p. 63).

PAPER: *"From (2) it follows that for every component of `V(G) \ V(H)`, all its attachments in
`H` are a subset of one of `S₁, S₂, S₃`.  Let `X` be the union of `S₁` and all components of
`V(G) \ V(H)` whose attachment set is a subset of `S₁`, and let `Y = V(G) \ X`.  Then
`|Y| ≥ 4`, and so either `(X,Y)` is a proper 2-join in `G`, or both `A₁, B₁` have one element
and `X` is the vertex set of a path between these two vertices.  We may assume the latter, and
the same for `S₂` and `S₃`; and so `G` is an even prism.  Then either it admits a proper
2-join, or `|V(G)| = 9`.  This proves 10.6."*

`hloc` is the sentence *"From (2) it follows …"*, and `hne` is the standing assumption carried
over from the previous paragraph (*"So we may assume there is no such `F`"* — a component of
`V(G) \ V(H)` with no attachments at all has all of them in `A`). -/
theorem thm_10_6_endgame (hG : Berge G) (hH : IsHyperprism G A B C)
    (hne : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F → F.Nonempty →
      (attachments G F (hyperVerts A B C)).Nonempty)
    (hloc : ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F →
      ∃ i : Fin 3, attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i) :
    ((∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃ ∧
        {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} = Set.univ) ∧
      Fintype.card V = 9) ∨
    AdmitsProper2Join G ∨ AdmitsBalancedSkewPartition G := by
  by_cases hall : ∀ l : Fin 3, ∃ (x y : V) (p : List V), A l = {x} ∧ B l = {y} ∧
      IsPathFrom G p x y ∧ {z : V | z ∈ p} = sideSet G A B C l
  · -- *"We may assume the latter, and the same for `S₂` and `S₃`; and so `G` is an even prism."*
    choose a b P hA hB hP hX using hall
    have hSP : ∀ l : Fin 3, A l ∪ B l ∪ C l ⊆ {v : V | v ∈ P l} := by
      intro l
      rw [hX l]
      exact S_subset_sideSet l
    have hout : ∀ l m : Fin 3, l ≠ m → ∀ u ∈ P l, ∀ v ∈ P m, G.Adj u v →
        u ∈ A l ∪ B l ∪ C l ∧ v ∈ A m ∪ B m ∪ C m := by
      intro l m hlm u hu v hv hadj
      have hu' : u ∈ sideSet G A B C l := by rw [← hX l]; exact hu
      have hv' : v ∈ sideSet G A B C m := by rw [← hX m]; exact hv
      rcases sideSet_cross hH hne hlm hu' hv' hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Or.inl (Or.inl h1), Or.inl (Or.inl h2)⟩
      · exact ⟨Or.inl (Or.inr h1), Or.inl (Or.inr h2)⟩
    have hcov : {v : V | v ∈ P 0} ∪ {v : V | v ∈ P 1} ∪ {v : V | v ∈ P 2} = Set.univ := by
      rw [hX 0, hX 1, hX 2]
      exact sideSet_cover hloc
    rcases HyperprismNineVertices.thm_10_6_all_degenerate hG hH a b hA hB P hP hSP hout hcov with
      h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · -- *"either `(X,Y)` is a proper 2-join in `G`, or …"* — take an index where the second
    -- alternative fails.
    obtain ⟨i, hi⟩ := not_forall.mp hall
    obtain ⟨j, k, hij, hik, hjk⟩ := fin3_other i
    exact Or.inr (Or.inl
      (admitsProper2Join_of_not_degenerate hH hne hloc hij hik hjk hi))

end Workspace.ProofLemmas.HyperprismEndgame
