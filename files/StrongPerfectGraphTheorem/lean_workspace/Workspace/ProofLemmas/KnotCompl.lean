import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics

/-!
# Passing a knot to the complement

Section 9 of *The Strong Perfect Graph Theorem* uses, over and over, the fact that a knot in
`G` is again a knot in `Ḡ` with the paths and the antipaths exchanged.  The paper never states
this as a numbered result; it simply writes things like (printed p. 49, proof of 9.3)

> *"Therefore, in `Ḡ`, the set of neighbours of `f` in `K̄` is not local with respect to the
> knot `(Q̄₁, Q̄₂, P̄₁, P̄₂)`"*

and

> *"`V(K) \ X` is not local with respect to the knot `(P₁,P₂,Q₁,Q₂)` in `G`, and hence `X` does
> not resolve the knot `(Q̄₁, Q̄₂, P̄₁, P̄₂)` in `Ḡ`."*

Both moves are formalised here.

## What the exchange does to the eight end labels

`Knots.IsKnot` pins the ends of each list down as its head and its last entry, so "*with a
suitable relabelling of the ends*" is not free: the two paths have to be **reversed**.  Writing
`a₁,b₁,a₂,b₂,x₁,y₁,x₂,y₂` for the labels of the knot `(P₁,P₂,Q₁,Q₂)` in `G`, the knot
`(Q₁, Q₂, P₁ᴿ, P₂ᴿ)` in `Ḡ` carries the labels

| in `Ḡ` | `a₁'` | `b₁'` | `a₂'` | `b₂'` | `x₁'` | `y₁'` | `x₂'` | `y₂'` |
|---|---|---|---|---|---|---|---|---|
| is | `x₁` | `y₁` | `x₂` | `y₂` | `b₁` | `a₁` | `b₂` | `a₂` |

which is exactly the antipodal 8-cycle symmetry described in the doc-comment of 9.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.KnotCompl

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

/-- Adjacency in the complement, spelled out. -/
private theorem compl_adj_iff {G : SimpleGraph V} {u w : V} :
    Gᶜ.Adj u w ↔ (u ≠ w ∧ ¬ G.Adj u w) := Iff.rfl

/-- **A knot in `G` is a knot in `Ḡ` with the paths and antipaths exchanged.**

PAPER (printed p. 49, inside the proof of 9.3): *"the knot `(Q̄₁, Q̄₂, P̄₁, P̄₂)` in `Ḡ`"*.

The two paths must be reversed, because `IsKnot` fixes the end labels as the head and the last
entry of each list; see the table in the module doc-comment. -/
theorem isKnot_compl {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    (h : IsKnot G P₁ P₂ Q₁ Q₂) : IsKnot Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse := by
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hP1, hP2, hQ1, hQ2,
    d12, d1q1, d1q2, d2q1, d2q2, dq12,
    lP1, lP2, lQ1, lQ2, hanti, hcomp, hE11, hE12, hE21, hE22, hN11, hN12, hN31, hN42⟩ := h
  -- Membership in a reversed list.
  have memrev : ∀ (l : List V) (v : V), v ∈ l.reverse ↔ v ∈ l := by
    intro l v; exact List.mem_reverse
  refine ⟨x₁, y₁, x₂, y₂, b₁, a₁, b₂, a₂, hQ1, hQ2, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `P₁ᴿ` is an antipath of `Ḡ` from `b₁` to `a₁`
  · show IsPathFrom Gᶜᶜ P₁.reverse b₁ a₁
    rw [compl_compl]
    exact PathBasics.isPathFrom_reverse hP1
  · show IsPathFrom Gᶜᶜ P₂.reverse b₂ a₂
    rw [compl_compl]
    exact PathBasics.isPathFrom_reverse hP2
  -- disjointness
  · exact fun v hv hv2 => dq12 v hv hv2
  · exact fun v hv hv2 => d1q1 v ((memrev P₁ v).mp hv2) hv
  · exact fun v hv hv2 => d2q1 v ((memrev P₂ v).mp hv2) hv
  · exact fun v hv hv2 => d1q2 v ((memrev P₁ v).mp hv2) hv
  · exact fun v hv hv2 => d2q2 v ((memrev P₂ v).mp hv2) hv
  · intro v hv hv2
    exact d12 v ((memrev P₁ v).mp hv) ((memrev P₂ v).mp hv2)
  -- lengths
  · exact lQ1
  · exact lQ2
  · rw [PathBasics.pathLength_reverse]; exact lP1
  · rw [PathBasics.pathLength_reverse]; exact lP2
  -- `V(Q₁)` anticomplete to `V(Q₂)` in `Ḡ`, since it is complete in `G`
  · intro u hu w hw
    exact fun hadj => hadj.2 (hcomp u hu w hw)
  -- `V(P₁ᴿ)` complete to `V(P₂ᴿ)` in `Ḡ`, since it is anticomplete in `G`
  · intro u hu w hw
    have hu' : u ∈ P₁ := (memrev P₁ u).mp hu
    have hw' : w ∈ P₂ := (memrev P₂ w).mp hw
    exact ⟨fun heq => d12 u hu' (heq ▸ hw'), hanti u hu' w hw'⟩
  -- the four "edges" clauses, from the four "nonedges" clauses of the knot in `G`
  · intro u hu w hw
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d1q1 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP1).2) (by rw [← heq]; exact hu)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d1q1 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP1).1) (by rw [← heq]; exact hu)
    have hw' : w ∈ ({a₁, b₁} : Set V) := by
      rcases hw with rfl | hw
      · exact Or.inr rfl
      · simp only [Set.mem_singleton_iff] at hw; subst hw; exact Or.inl rfl
    rw [compl_adj_iff, hN11 u hu w hw']
    constructor
    · rintro ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
  · intro u hu w hw
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d2q1 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP2).2) (by rw [← heq]; exact hu)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d2q1 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP2).1) (by rw [← heq]; exact hu)
    have hw' : w ∈ ({a₂, b₂} : Set V) := by
      rcases hw with rfl | hw
      · exact Or.inr rfl
      · simp only [Set.mem_singleton_iff] at hw; subst hw; exact Or.inl rfl
    rw [compl_adj_iff, hN31 u hu w hw']
    constructor
    · rintro ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
  · intro u hu w hw
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d1q2 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP1).2) (by rw [← heq]; exact hu)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d1q2 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP1).1) (by rw [← heq]; exact hu)
    have hw' : w ∈ ({a₁, b₁} : Set V) := by
      rcases hw with rfl | hw
      · exact Or.inr rfl
      · simp only [Set.mem_singleton_iff] at hw; subst hw; exact Or.inl rfl
    rw [compl_adj_iff, hN12 u hu w hw']
    constructor
    · rintro ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
  · intro u hu w hw
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d2q2 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP2).2) (by rw [← heq]; exact hu)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d2q2 w (heq ▸ (PathBasics.isPathFrom_ends_mem hP2).1) (by rw [← heq]; exact hu)
    have hw' : w ∈ ({a₂, b₂} : Set V) := by
      rcases hw with rfl | hw
      · exact Or.inr rfl
      · simp only [Set.mem_singleton_iff] at hw; subst hw; exact Or.inl rfl
    rw [compl_adj_iff, hN42 u hu w hw']
    constructor
    · rintro ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
  -- the four "nonedges" clauses, from the four "edges" clauses of the knot in `G`
  · intro u hu w hw
    have hu' : u ∈ P₁ := (memrev P₁ u).mp hu
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d1q1 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ1).1)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d1q1 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ1).2)
    have hw' : w ∈ ({x₁, y₁} : Set V) := hw
    rw [compl_adj_iff, not_and_or, not_not, not_not, hE11 u hu' w hw']
    constructor
    · rintro (heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact absurd heq hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro u hu w hw
    have hu' : u ∈ P₂ := (memrev P₂ u).mp hu
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d2q1 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ1).1)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d2q1 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ1).2)
    have hw' : w ∈ ({x₁, y₁} : Set V) := hw
    rw [compl_adj_iff, not_and_or, not_not, not_not, hE21 u hu' w hw']
    constructor
    · rintro (heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact absurd heq hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro u hu w hw
    have hu' : u ∈ P₁ := (memrev P₁ u).mp hu
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d1q2 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ2).1)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d1q2 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ2).2)
    have hw' : w ∈ ({x₂, y₂} : Set V) := hw
    rw [compl_adj_iff, not_and_or, not_not, not_not, hE12 u hu' w hw']
    constructor
    · rintro (heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact absurd heq hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro u hu w hw
    have hu' : u ∈ P₂ := (memrev P₂ u).mp hu
    have hne : u ≠ w := by
      rcases hw with rfl | hw
      · exact fun heq => d2q2 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ2).1)
      · simp only [Set.mem_singleton_iff] at hw
        subst hw
        exact fun heq => d2q2 u hu' (heq ▸ (PathBasics.isPathFrom_ends_mem hQ2).2)
    have hw' : w ∈ ({x₂, y₂} : Set V) := hw
    rw [compl_adj_iff, not_and_or, not_not, not_not, hE22 u hu' w hw']
    constructor
    · rintro (heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact absurd heq hne
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The vertex set induced by a knot does not change when the paths and antipaths are
exchanged and the paths reversed. -/
theorem knotInduces_compl {P₁ P₂ Q₁ Q₂ : List V} {K : Set V}
    (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) :
    KnotInduces Q₁ Q₂ P₁.reverse P₂.reverse K := by
  unfold KnotInduces at hK ⊢
  subst hK
  ext v
  simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
  tauto

/-- **"`X` resolves the knot" is the first form of the definition, not just the second.**

PAPER (printed pp. 47–48, definition of *resolves*): *"We say `X` resolves the knot if
`V(K) \ X` is local with respect to the knot `(Q₁,Q₂,P₁,P₂)` in `Ḡ`; that is, if `X` includes
one of `V(Q₁), V(Q₂)`, and `X` meets both `P₁` and `P₂`, and `X` contains at least one end of
every edge between `V(P₁) ∪ V(P₂)` and `V(Q₁) ∪ V(Q₂)`."*

`Knots.ResolvesKnot` transcribes the second ("*that is*") form; this lemma proves the paper's
first form equivalent to it.  It is the step the proof of 9.3 makes when it says (printed
p. 49): *"`V(K) \ X` is not local with respect to the knot `(P₁,P₂,Q₁,Q₂)` in `G`, and hence
`X` does not resolve the knot `(Q̄₁,Q̄₂,P̄₁,P̄₂)` in `Ḡ`."* -/
theorem resolvesKnot_iff_localForKnot_compl {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂) {K : Set V} (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) {X : Set V} :
    ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔
      LocalForKnot Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse (K \ X) := by
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hP1, hP2, hQ1, hQ2,
    d12, d1q1, d1q2, d2q1, d2q2, dq12, -⟩ := hknot
  subst hK
  -- every vertex of one of the four lists lies in `V(K)`
  have hinK : ∀ v : V, (v ∈ P₁ ∨ v ∈ P₂ ∨ v ∈ Q₁ ∨ v ∈ Q₂) →
      v ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} :
        Set V) := by
    intro v hv
    simp only [Set.mem_union, Set.mem_setOf_eq]
    tauto
  -- a vertex of a `Q` and a vertex of a `P` are distinct
  have hPQne : ∀ u w : V, (u ∈ P₁ ∨ u ∈ P₂) → (w ∈ Q₁ ∨ w ∈ Q₂) → w ≠ u := by
    rintro u w (hu | hu) (hw | hw) rfl
    · exact d1q1 w hu hw
    · exact d1q2 w hu hw
    · exact d2q1 w hu hw
    · exact d2q2 w hu hw
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases h1 with h | h
      · exact Or.inl (Set.disjoint_left.mpr fun v hv hvQ => hv.2 (h hvQ))
      · exact Or.inr (Set.disjoint_left.mpr fun v hv hvQ => hv.2 (h hvQ))
    · intro hsub
      obtain ⟨v, hvX, hvP⟩ := h2
      exact (hsub (show v ∈ P₁.reverse from List.mem_reverse.mpr hvP)).2 hvX
    · intro hsub
      obtain ⟨v, hvX, hvP⟩ := h3
      exact (hsub (show v ∈ P₂.reverse from List.mem_reverse.mpr hvP)).2 hvX
    · rintro w ⟨⟨-, hwX⟩, hwQ⟩ u ⟨⟨-, huX⟩, huP⟩
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_reverse] at hwQ huP
      refine ⟨hPQne u w huP hwQ, fun hadj => ?_⟩
      rcases h4 u (by simp only [Set.mem_union, Set.mem_setOf_eq]; tauto) w
        (by simp only [Set.mem_union, Set.mem_setOf_eq]; tauto) hadj.symm with h | h
      · exact huX h
      · exact hwX h
  · rintro ⟨r1, r2, r3, r4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases r1 with h | h
      · refine Or.inl fun v hv => ?_
        by_contra hvX
        exact (Set.disjoint_left.mp h ⟨hinK v (by tauto), hvX⟩) hv
      · refine Or.inr fun v hv => ?_
        by_contra hvX
        exact (Set.disjoint_left.mp h ⟨hinK v (by tauto), hvX⟩) hv
    · obtain ⟨v, hvP, hvY⟩ := Set.not_subset.mp r2
      have hvP' : v ∈ P₁ := List.mem_reverse.mp hvP
      refine ⟨v, ?_, hvP'⟩
      by_contra hvX
      exact hvY ⟨hinK v (by tauto), hvX⟩
    · obtain ⟨v, hvP, hvY⟩ := Set.not_subset.mp r3
      have hvP' : v ∈ P₂ := List.mem_reverse.mp hvP
      refine ⟨v, ?_, hvP'⟩
      by_contra hvX
      exact hvY ⟨hinK v (by tauto), hvX⟩
    · intro u hu w hw hadj
      simp only [Set.mem_union, Set.mem_setOf_eq] at hu hw
      by_contra hcon
      obtain ⟨huX, hwX⟩ := not_or.mp hcon
      refine (r4 w ⟨⟨hinK w (by tauto), hwX⟩, ?_⟩ u ⟨⟨hinK u (by tauto), huX⟩, ?_⟩).2 hadj.symm
      · simpa only [Set.mem_union, Set.mem_setOf_eq] using hw
      · simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
        exact hu

end Workspace.ProofLemmas.KnotCompl
