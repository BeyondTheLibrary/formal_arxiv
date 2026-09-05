import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.ProofLemmas.PathBasics

/-!
# A striation whose strips and antistrips all have two vertices makes `G` a double split graph

PAPER (9.6, printed p. 55, the endgame of claim (3)):

> *"So we may assume that each `Sᵢ` has only two vertices.  In particular, every `Sᵢ`-rung has
> length 1, so by taking complements the same argument shows that we may assume every `V(Tⱼ)`
> has only two vertices.  **But then `G` is a double split graph** and the theorem holds.  This
> proves (3)."*

This module states the emphasised step.  It is the last missing ingredient of the `sorry` in
`Workspace.ProofLemmas.Thm96Body.claim3`; the other one (the appeal to 9.1 that starts claim
(3)) is already available as `Workspace.ProofLemmas.KnotFromTwist.exists_knot_of_twist`.

## Why the hypotheses are exactly these

Claim (3) is the case `M = N = ∅` of 9.6, and `Thm96Body.Setup` records
`M ∪ N = (striationVertices S T)ᶜ`; so `M = N = ∅` says precisely that
`striationVertices S T = V(G)`, which is the hypothesis `hcover` below.  That is where the
**bijection** demanded by `IsDoubleSplitGraph` comes from: the `2m + 2n` vertices of the strips
and antistrips are pairwise distinct (the strips and antistrips of a striation are pairwise
disjoint, and inside `V(Sᵢ) = Aᵢ ∪ Bᵢ ∪ Cᵢ` the three sets are disjoint) and by `hcover` they
exhaust `V(G)`.

With that in hand the striation axioms map clause for clause onto `IsDoubleSplitGraph`:

| `IsStriation` | `IsDoubleSplitGraph` |
|---|---|
| `2 ≤ m`, `2 ≤ n` | `2 ≤ m`, `2 ≤ n` |
| every `Sᵢ`-rung is a path from `Aᵢ` to `Bᵢ` with interior in `Cᵢ`; `|V(Sᵢ)| = 2` forces `Cᵢ = ∅`, `Aᵢ = {aᵢ}`, `Bᵢ = {bᵢ}` and the rung `[aᵢ, bᵢ]` | `aᵢ` is adjacent to `bᵢ` |
| the same in `Ḡ` for `Tⱼ = (Xⱼ, Zⱼ, Yⱼ)`, giving `Xⱼ = {cⱼ}`, `Yⱼ = {dⱼ}`, `Zⱼ = ∅` | `cⱼ` is nonadjacent to `dⱼ` |
| `Sᵢ` anticomplete to `Sᵢ'` for `i ≠ i'` | no edges between `{aᵢ,bᵢ}` and `{aᵢ',bᵢ'}` |
| `Tⱼ` complete to `Tⱼ'` for `j ≠ j'` | all four edges between `{cⱼ,dⱼ}` and `{cⱼ',dⱼ'}` |
| `Sᵢ, Tⱼ` **parallel** — `Aᵢ` complete to `Xⱼ ∪ Zⱼ`, `Bᵢ` complete to `Yⱼ ∪ Zⱼ`, `Xⱼ` anticomplete to `Bᵢ ∪ Cᵢ`, `Yⱼ` anticomplete to `Aᵢ ∪ Cᵢ` | first disjunct: `aᵢcⱼ`, `bᵢdⱼ` edges, `aᵢdⱼ`, `bᵢcⱼ` nonedges |
| `Sᵢ, Tⱼ` **co-parallel** | second disjunct: `aᵢdⱼ`, `bᵢcⱼ` edges, `aᵢcⱼ`, `bᵢdⱼ` nonedges |

so the two vertices of `V(Sᵢ)` are the paper's `aᵢ, bᵢ` and the two vertices of `V(Tⱼ)` are its
`cⱼ, dⱼ`, and *"exactly two edges between `{aᵢ,bᵢ}` and `{cⱼ,dⱼ}`, with no common end"* is
exactly the striation's *"`Sᵢ` and `Tⱼ` are either parallel or co-parallel"*.

The two size hypotheses are stated as `Set.ncard (stripVertices …) = 2`, which is the printed
*"has only two vertices"*; `A`, `B` nonempty and `A`, `B`, `C` pairwise disjoint (both part of
`IsStrip`) then force `|A| = |B| = 1` and `C = ∅`.

## The one lemma the proof factors through

`strip_two` is the printed *"each `Sᵢ` has only two vertices.  In particular, every `Sᵢ`-rung
has length 1"*: a strip with two vertices all of whose rungs have odd length is
`({x}, ∅, {y})` with `xy` an edge.  Applying it to `Gᶜ` and `T j` — an antistrip *is* a strip of
`Gᶜ`, and an antirung *is* a `Gᶜ`-rung — is the printed *"by taking complements the same
argument shows …"*.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.DegenerateStriationIsDoubleSplit

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.6, claim (3)):** *"each `Sᵢ` has only two vertices.  In particular, every
`Sᵢ`-rung has length 1"*.

A strip whose vertex set has exactly two elements is `({x}, ∅, {y})`, and `xy` is an edge: the
two elements are one end in `A` and one end in `B`, so `C` is empty, so every rung has empty
interior, so — being of odd length — every rung is the single edge `xy`. -/
private theorem strip_two {G : SimpleGraph V} {Sv : Set V × Set V × Set V}
    (hstrip : IsStrip G Sv) (hcard : (stripVertices Sv).ncard = 2)
    (hodd : ∀ p : List V, IsSRung G Sv p → Odd (pathLength p)) :
    ∃ x y : V, G.Adj x y ∧ Sv = ({x}, (∅ : Set V), {y}) := by
  obtain ⟨A, C, B⟩ := Sv
  obtain ⟨hAB, hAC, hBC, ⟨x, hx⟩, ⟨y, hy⟩, hcov⟩ := hstrip
  have hxy : x ≠ y := by
    intro h; subst h; exact (Set.disjoint_left.mp hAB hx) hy
  have hsub : ({x, y} : Set V) ⊆ A ∪ B ∪ C := by
    intro z hz
    rcases hz with h | h
    · exact Or.inl (Or.inl (by rw [h]; exact hx))
    · exact Or.inl (Or.inr (by rw [show z = y from h]; exact hy))
  have hcard' : (A ∪ B ∪ C).ncard = 2 := hcard
  have heq : A ∪ B ∪ C = ({x, y} : Set V) :=
    (Set.eq_of_subset_of_ncard_le hsub
      (le_of_eq (by rw [hcard', Set.ncard_pair hxy])) (Set.toFinite _)).symm
  -- `A = {x}`, `B = {y}`, `C = ∅`
  have hAeq : A = ({x} : Set V) := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.mpr hx)
    have hzm : z ∈ ({x, y} : Set V) := by rw [← heq]; exact Or.inl (Or.inl hz)
    rcases hzm with h | h
    · exact h
    · exfalso
      rw [show z = y from h] at hz
      exact (Set.disjoint_left.mp hAB hz) hy
  have hBeq : B = ({y} : Set V) := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.mpr hy)
    have hzm : z ∈ ({x, y} : Set V) := by rw [← heq]; exact Or.inl (Or.inr hz)
    rcases hzm with h | h
    · exfalso
      rw [h] at hz
      exact (Set.disjoint_left.mp hAB hx) hz
    · exact h
  have hCeq : C = (∅ : Set V) := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun z hz => ?_)
    have hzm : z ∈ ({x, y} : Set V) := by rw [← heq]; exact Or.inr hz
    rcases hzm with h | h
    · rw [h] at hz; exact (Set.disjoint_left.mp hAC hx) hz
    · rw [show z = y from h] at hz; exact (Set.disjoint_left.mp hBC hy) hz
  -- a rung through `x`; its interior lies in `C = ∅`, so it is the single edge `xy`
  obtain ⟨p, hp, -⟩ := hcov x (Or.inl (Or.inl hx))
  have hoddp := hodd p hp
  obtain ⟨a', b', hpf, ha', hb', -, -, hint⟩ := hp
  have ha'x : a' = x := by rw [hAeq] at ha'; exact ha'
  have hb'y : b' = y := by rw [hBeq] at hb'; exact hb'
  have hnil : (Workspace.Types.Core.SPGT.interior p).length = 0 := by
    rcases hq : Workspace.Types.Core.SPGT.interior p with _ | ⟨w, ws⟩
    · simp
    · exfalso
      have hw : w ∈ Workspace.Types.Core.SPGT.interior p := by rw [hq]; simp
      have hwC := hint w hw
      rw [hCeq] at hwC
      exact hwC
  have hone : pathLength p = 1 := by
    rw [Workspace.ProofLemmas.PathBasics.interior_length] at hnil
    have hplen := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hpf.1
    rw [Nat.odd_iff] at hoddp
    omega
  have hadj : G.Adj x y := by
    have := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hpf hone
    rwa [ha'x, hb'y] at this
  exact ⟨x, y, hadj, by rw [hAeq, hBeq, hCeq]⟩

/-- **PAPER (9.6, printed p. 55, claim (3)):** *"So we may assume that each `Sᵢ` has only two
vertices. … we may assume every `V(Tⱼ)` has only two vertices.  But then `G` is a double split
graph and the theorem holds."*

`hcover` is the claim-(3) hypothesis `M = N = ∅` read through `Thm96Body.Setup`'s
`M ∪ N = (striationVertices S T)ᶜ`: the strips and antistrips cover `V(G)`.  See the module
doc-comment for the clause-by-clause correspondence with `IsDoubleSplitGraph`. -/
theorem isDoubleSplitGraph_of_striation_two_vertices
    {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T)
    (hcover : striationVertices S T = (Set.univ : Set V))
    (hS : ∀ i : Fin m, (stripVertices (S i)).ncard = 2)
    (hT : ∀ j : Fin n, (stripVertices (T j)).ncard = 2) :
    IsDoubleSplitGraph G := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7, hLm, hLn, hL10, hL11, hL12, -, -⟩ := hL
  -- every strip is `({aᵢ}, ∅, {bᵢ})` with `aᵢbᵢ` an edge
  have hSsplit : ∀ i : Fin m, ∃ x y : V, G.Adj x y ∧ S i = ({x}, (∅ : Set V), {y}) :=
    fun i => strip_two (hL1 i) (hS i) (fun p hp => hL6 i p hp)
  choose a b hab hSeq using hSsplit
  -- and, in `Gᶜ`, every antistrip is `({cⱼ}, ∅, {dⱼ})` with `cⱼdⱼ` a nonedge of `G`
  have hTsplit : ∀ j : Fin n, ∃ x y : V, Gᶜ.Adj x y ∧ T j = ({x}, (∅ : Set V), {y}) :=
    fun j => strip_two (G := Gᶜ) (hL2 j) (hT j) (fun p hp => hL7 j p hp)
  choose c d hcd hTeq using hTsplit
  have hSV : ∀ i : Fin m, stripVertices (S i) = ({a i, b i} : Set V) := by
    intro i
    rw [hSeq i]
    show ({a i} : Set V) ∪ {b i} ∪ ∅ = _
    rw [Set.union_empty, Set.singleton_union]
  have hTV : ∀ j : Fin n, stripVertices (T j) = ({c j, d j} : Set V) := by
    intro j
    rw [hTeq j]
    show ({c j} : Set V) ∪ {d j} ∪ ∅ = _
    rw [Set.union_empty, Set.singleton_union]
  have haS : ∀ i : Fin m, a i ∈ stripVertices (S i) := by intro i; rw [hSV i]; simp
  have hbS : ∀ i : Fin m, b i ∈ stripVertices (S i) := by intro i; rw [hSV i]; simp
  have hcT : ∀ j : Fin n, c j ∈ stripVertices (T j) := by intro j; rw [hTV j]; simp
  have hdT : ∀ j : Fin n, d j ∈ stripVertices (T j) := by intro j; rw [hTV j]; simp
  -- pairwise disjointness of the strips and antistrips, in "distinct vertices" form
  have hSne : ∀ i i' : Fin m, i ≠ i' → ∀ z ∈ stripVertices (S i),
      ∀ w ∈ stripVertices (S i'), z ≠ w := by
    intro i i' hne z hz w hw h
    exact Set.disjoint_left.mp (hL3 i i' hne) hz (by rw [h]; exact hw)
  have hTne : ∀ j j' : Fin n, j ≠ j' → ∀ z ∈ stripVertices (T j),
      ∀ w ∈ stripVertices (T j'), z ≠ w := by
    intro j j' hne z hz w hw h
    exact Set.disjoint_left.mp (hL4 j j' hne) hz (by rw [h]; exact hw)
  have hSTne : ∀ (i : Fin m) (j : Fin n), ∀ z ∈ stripVertices (S i),
      ∀ w ∈ stripVertices (T j), z ≠ w := by
    intro i j z hz w hw h
    exact Set.disjoint_left.mp (hL5 i j) hz (by rw [h]; exact hw)
  -- the `2m + 2n` listed vertices are pairwise distinct
  have hinj : Function.Injective (Sum.elim (Sum.elim a b) (Sum.elim c d)) := by
    rintro ((i | i) | (j | j)) ((i' | i') | (j' | j')) h <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at h
    · by_cases hne : i = i'
      · rw [hne]
      · exact absurd h (hSne i i' hne (a i) (haS i) (a i') (haS i'))
    · exfalso
      by_cases hne : i = i'
      · subst hne; exact (hab i).ne h
      · exact hSne i i' hne (a i) (haS i) (b i') (hbS i') h
    · exact absurd h (hSTne i j' (a i) (haS i) (c j') (hcT j'))
    · exact absurd h (hSTne i j' (a i) (haS i) (d j') (hdT j'))
    · exfalso
      by_cases hne : i = i'
      · subst hne; exact (hab i).ne h.symm
      · exact hSne i i' hne (b i) (hbS i) (a i') (haS i') h
    · by_cases hne : i = i'
      · rw [hne]
      · exact absurd h (hSne i i' hne (b i) (hbS i) (b i') (hbS i'))
    · exact absurd h (hSTne i j' (b i) (hbS i) (c j') (hcT j'))
    · exact absurd h (hSTne i j' (b i) (hbS i) (d j') (hdT j'))
    · exact absurd h (Ne.symm (hSTne i' j (a i') (haS i') (c j) (hcT j)))
    · exact absurd h (Ne.symm (hSTne i' j (b i') (hbS i') (c j) (hcT j)))
    · by_cases hne : j = j'
      · rw [hne]
      · exact absurd h (hTne j j' hne (c j) (hcT j) (c j') (hcT j'))
    · exfalso
      by_cases hne : j = j'
      · subst hne; exact (hcd j).ne h
      · exact hTne j j' hne (c j) (hcT j) (d j') (hdT j') h
    · exact absurd h (Ne.symm (hSTne i' j (a i') (haS i') (d j) (hdT j)))
    · exact absurd h (Ne.symm (hSTne i' j (b i') (hbS i') (d j) (hdT j)))
    · exfalso
      by_cases hne : j = j'
      · subst hne; exact (hcd j).ne h.symm
      · exact hTne j j' hne (d j) (hdT j) (c j') (hcT j') h
    · by_cases hne : j = j'
      · rw [hne]
      · exact absurd h (hTne j j' hne (d j) (hdT j) (d j') (hdT j'))
  -- and they exhaust `V(G)`, because `V(L) = V(G)`
  have hsurj : Function.Surjective (Sum.elim (Sum.elim a b) (Sum.elim c d)) := by
    intro v
    have hv : v ∈ striationVertices S T := by rw [hcover]; exact Set.mem_univ v
    simp only [striationVertices, Set.mem_union, Set.mem_iUnion] at hv
    rcases hv with ⟨i, hvi⟩ | ⟨j, hvj⟩
    · rw [hSV i] at hvi
      rcases hvi with h | h
      · exact ⟨Sum.inl (Sum.inl i), h.symm⟩
      · exact ⟨Sum.inl (Sum.inr i), (show v = b i from h).symm⟩
    · rw [hTV j] at hvj
      rcases hvj with h | h
      · exact ⟨Sum.inr (Sum.inl j), h.symm⟩
      · exact ⟨Sum.inr (Sum.inr j), (show v = d j from h).symm⟩
  refine ⟨m, n, a, b, c, d, hLm, hLn, ⟨hinj, hsurj⟩, hab, ?_, ?_, ?_, ?_⟩
  · -- `cⱼ` is nonadjacent to `dⱼ`
    exact fun j => ((SimpleGraph.compl_adj G _ _).mp (hcd j)).2
  · -- distinct strips are anticomplete
    intro i i' hne
    have hz : ∀ z ∈ ({a i, b i} : Set V), ∀ w ∈ ({a i', b i'} : Set V), ¬ G.Adj z w := by
      intro z hz w hw
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hL10 i i' hlt z (by rw [hSV i]; exact hz) w (by rw [hSV i']; exact hw)
      · exact fun hadj =>
          hL10 i' i hlt w (by rw [hSV i']; exact hw) z (by rw [hSV i]; exact hz) hadj.symm
    exact ⟨hz _ (Or.inl rfl) _ (Or.inl rfl), hz _ (Or.inl rfl) _ (Or.inr rfl),
      hz _ (Or.inr rfl) _ (Or.inl rfl), hz _ (Or.inr rfl) _ (Or.inr rfl)⟩
  · -- distinct antistrips are complete
    intro j j' hne
    have hz : ∀ z ∈ ({c j, d j} : Set V), ∀ w ∈ ({c j', d j'} : Set V), G.Adj z w := by
      intro z hz w hw
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hL11 j j' hlt z (by rw [hTV j]; exact hz) w (by rw [hTV j']; exact hw)
      · exact (hL11 j' j hlt w (by rw [hTV j']; exact hw) z (by rw [hTV j]; exact hz)).symm
    exact ⟨hz _ (Or.inl rfl) _ (Or.inl rfl), hz _ (Or.inl rfl) _ (Or.inr rfl),
      hz _ (Or.inr rfl) _ (Or.inl rfl), hz _ (Or.inr rfl) _ (Or.inr rfl)⟩
  · -- parallel or co-parallel: exactly the two-edge condition
    intro i j
    rcases hL12 i j with hpar | hcop
    · rw [hSeq i, hTeq j] at hpar
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hpar
      refine Or.inl ⟨h1 (a i) rfl (c j) (Or.inl rfl), h2 (b i) rfl (d j) (Or.inl rfl), ?_, ?_⟩
      · exact fun hadj => h4 (d j) rfl (a i) (Or.inl rfl) hadj.symm
      · exact fun hadj => h3 (c j) rfl (b i) (Or.inl rfl) hadj.symm
    · rw [hSeq i, hTeq j] at hcop
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcop
      refine Or.inr ⟨?_, ?_, h1 (a i) rfl (d j) (Or.inl rfl), h2 (b i) rfl (c j) (Or.inl rfl)⟩
      · exact fun hadj => h4 (c j) rfl (a i) (Or.inl rfl) hadj.symm
      · exact fun hadj => h3 (d j) rfl (b i) (Or.inl rfl) hadj.symm

end Workspace.ProofLemmas.DegenerateStriationIsDoubleSplit
