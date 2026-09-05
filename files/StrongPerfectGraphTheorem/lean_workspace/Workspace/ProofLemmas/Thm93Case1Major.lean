import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.CyclicPathConcatenationIsHole

/-!
# 9.3, case (1): a vertex of `F` whose neighbour set saturates `L(H)`

PAPER (proof of 9.3, printed p. 48, inside claim (1) *"If `Q₁, Q₂` have length 1 then the
  theorem holds"*):

> *"Suppose that the neighbour set of some `f ∈ F` saturates `L(H)`.  If `f` has a neighbour
> in both `V(P₁)` and `V(P₂)` then statement 1 of the theorem holds, so we assume it has no
> neighbour in `V(P₁)`.  But then `f` is adjacent to all four of `x₁, x₂, y₁, y₂`, since it
> has two neighbours in every triangle of `K`, and then `f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole,
> a contradiction."*

Both halves are proved here.  When `Q₁, Q₂` have length `1` the knot `(P₁,P₂,Q₁,Q₂)` induces a
*degenerate* appearance of `K₄` (`Workspace.ProofLemmas.AppearanceFromKnot`), whose four
branch-vertices carry the four triangles

```
N c₁ = {x₁, x₂, a₁}      N c₂ = {x₁, y₂, a₂}
N c₃ = {y₁, y₂, b₁}      N c₄ = {y₁, x₂, b₂}
```

so *"the neighbour set of `f` saturates `L(H)`"* is, read back in `G`, exactly the statement
that each of those four triangles contains at most one non-neighbour of `f` — the paper's own
gloss *"it has two neighbours in every triangle of `K`"*.  The two lemmas below therefore take
that condition in its triangle form, which keeps them free of the `H`/`φ` bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93Case1Major

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

/-- *"It has two neighbours in every triangle of `K`"*: from a triangle with at most one
non-neighbour of `f`, any two distinct members give a neighbour. -/
theorem mem_or_mem_of_subsingleton {N S : Set V} (h : (S \ N).Subsingleton) {p r : V}
    (hp : p ∈ S) (hr : r ∈ S) (hpr : p ≠ r) : p ∈ N ∨ r ∈ N := by
  by_contra hc
  push_neg at hc
  exact hpr (h ⟨hp, hc.1⟩ ⟨hr, hc.2⟩)

/-- **The positive half.**

PAPER: *"If `f` has a neighbour in both `V(P₁)` and `V(P₂)` then statement 1 of the theorem
holds."* -/
theorem resolvesKnot_of_saturating [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ1len : pathLength Q₁ = 1) (hQ2len : pathLength Q₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (f : V)
    (hT₁ : (({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton)
    (hT₂ : (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton)
    (hT₃ : (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton)
    (hT₄ : (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton)
    (hf₁ : ∃ v ∈ P₁, G.Adj f v) (hf₂ : ∃ v ∈ P₂, G.Adj f v) :
    ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K) := by
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq12, -, -, -, -, -, -,
    hE11, hE12, hE21, hE22, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  -- the two antipaths are the two-element lists of their ends
  have hQ₁eq : Q₁ = [x₁, y₁] := KnotLabels.anti_eq_pair_of_length_one hQ₁ hQ1len
  have hQ₂eq : Q₂ = [x₂, y₂] := KnotLabels.anti_eq_pair_of_length_one hQ₂ hQ2len
  -- membership facts
  have ha₁ : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb₁ : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).2
  have ha₂ : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).1
  have hb₂ : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).2
  have hx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hx₂ : x₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have hy₂ : y₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  -- the ends of the two antipaths are distinct from one another
  have hx₁x₂ : x₁ ≠ x₂ := fun h => dq12 x₁ hx₁ (h ▸ hx₂)
  have hx₁y₂ : x₁ ≠ y₂ := fun h => dq12 x₁ hx₁ (h ▸ hy₂)
  have hy₁x₂ : y₁ ≠ x₂ := fun h => dq12 y₁ hy₁ (h ▸ hx₂)
  have hy₁y₂ : y₁ ≠ y₂ := fun h => dq12 y₁ hy₁ (h ▸ hy₂)
  have ha₁x₁ : a₁ ≠ x₁ := fun h => d1q1 a₁ ha₁ (h ▸ hx₁)
  have ha₁x₂ : a₁ ≠ x₂ := fun h => d1q2 a₁ ha₁ (h ▸ hx₂)
  have hb₁y₁ : b₁ ≠ y₁ := fun h => d1q1 b₁ hb₁ (h ▸ hy₁)
  have hb₁y₂ : b₁ ≠ y₂ := fun h => d1q2 b₁ hb₁ (h ▸ hy₂)
  have ha₂x₁ : a₂ ≠ x₁ := fun h => d2q1 a₂ ha₂ (h ▸ hx₁)
  have ha₂y₂ : a₂ ≠ y₂ := fun h => d2q2 a₂ ha₂ (h ▸ hy₂)
  have hb₂y₁ : b₂ ≠ y₁ := fun h => d2q1 b₂ hb₂ (h ▸ hy₁)
  have hb₂x₂ : b₂ ≠ x₂ := fun h => d2q2 b₂ hb₂ (h ▸ hx₂)
  have hx₁y₁ : x₁ ≠ y₁ := by
    have := PathBasics.antipath_nodup hQ₁.1
    rw [hQ₁eq] at this; simpa using this
  have hx₂y₂ : x₂ ≠ y₂ := by
    have := PathBasics.antipath_nodup hQ₂.1
    rw [hQ₂eq] at this; simpa using this
  -- everything of the four lists lies in `K`
  have hmemK : ∀ v : V, (v ∈ P₁ ∨ v ∈ P₂ ∨ v ∈ Q₁ ∨ v ∈ Q₂) → v ∈ K := by
    intro v hv; rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]; tauto
  have kP₁ : ∀ v ∈ P₁, v ∈ K := fun v hv => hmemK v (Or.inl hv)
  have kP₂ : ∀ v ∈ P₂, v ∈ K := fun v hv => hmemK v (Or.inr (Or.inl hv))
  have kQ₁ : ∀ v ∈ Q₁, v ∈ K := fun v hv => hmemK v (Or.inr (Or.inr (Or.inl hv)))
  have kQ₂ : ∀ v ∈ Q₂, v ∈ K := fun v hv => hmemK v (Or.inr (Or.inr (Or.inr hv)))
  -- the four saturation facts, in the paper's *"two neighbours in every triangle"* form
  have s₁ : x₁ ∈ G.neighborSet f ∨ x₂ ∈ G.neighborSet f :=
    mem_or_mem_of_subsingleton hT₁ (by simp) (by simp) hx₁x₂
  have s₂ : x₁ ∈ G.neighborSet f ∨ y₂ ∈ G.neighborSet f :=
    mem_or_mem_of_subsingleton hT₂ (by simp) (by simp) hx₁y₂
  have s₃ : y₁ ∈ G.neighborSet f ∨ y₂ ∈ G.neighborSet f :=
    mem_or_mem_of_subsingleton hT₃ (by simp) (by simp) hy₁y₂
  have s₄ : y₁ ∈ G.neighborSet f ∨ x₂ ∈ G.neighborSet f :=
    mem_or_mem_of_subsingleton hT₄ (by simp) (by simp) hy₁x₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- *"`X` includes one of `V(Q₁), V(Q₂)`"*
    have key : (x₁ ∈ G.neighborSet f ∧ y₁ ∈ G.neighborSet f) ∨
        (x₂ ∈ G.neighborSet f ∧ y₂ ∈ G.neighborSet f) := by tauto
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ?_
      intro v hv
      rw [hQ₁eq] at hv
      rcases List.mem_cons.mp hv with he | hv
      · exact ⟨he ▸ h1, kQ₁ v (he ▸ hx₁)⟩
      · have he : v = y₁ := by simpa using hv
        exact ⟨he ▸ h2, kQ₁ v (he ▸ hy₁)⟩
    · refine Or.inr ?_
      intro v hv
      rw [hQ₂eq] at hv
      rcases List.mem_cons.mp hv with he | hv
      · exact ⟨he ▸ h1, kQ₂ v (he ▸ hx₂)⟩
      · have he : v = y₂ := by simpa using hv
        exact ⟨he ▸ h2, kQ₂ v (he ▸ hy₂)⟩
  · obtain ⟨v, hv, hadj⟩ := hf₁
    exact ⟨v, ⟨hadj, kP₁ v hv⟩, hv⟩
  · obtain ⟨v, hv, hadj⟩ := hf₂
    exact ⟨v, ⟨hadj, kP₂ v hv⟩, hv⟩
  · -- *"`X` contains at least one end of every edge between `V(P₁) ∪ V(P₂)` and
    -- `V(Q₁) ∪ V(Q₂)`"* — there are exactly eight such edges, and each lies inside one of
    -- the four triangles.
    intro u hu w hw hadj
    simp only [Set.mem_union, Set.mem_setOf_eq] at hu hw
    have hfin : ∀ S : Set V, (S \ G.neighborSet f).Subsingleton → ∀ p r : V,
        p ∈ S → r ∈ S → p ≠ r → p ∈ K → r ∈ K →
        (p ∈ G.neighborSet f ∩ K ∨ r ∈ G.neighborSet f ∩ K) := by
      intro S hS p r hp hr hpr hpK hrK
      rcases mem_or_mem_of_subsingleton hS hp hr hpr with h | h
      · exact Or.inl ⟨h, hpK⟩
      · exact Or.inr ⟨h, hrK⟩
    rw [hQ₁eq] at hw
    rw [hQ₂eq] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hu with hu | hu
    · rcases hw with (hwe | hwe) | (hwe | hwe)
      · -- `u ∈ P₁`, `w = x₁`: the edge is `a₁x₁`
        have hua : u = a₁ := by
          rw [hwe] at hadj
          rcases (hE11 u hu x₁ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
          · exact h
          · exact absurd h hx₁y₁
        rw [hwe, hua]
        exact hfin ({x₁, x₂, a₁} : Set V) hT₁ a₁ x₁ (by simp) (by simp) ha₁x₁
          (kP₁ a₁ ha₁) (kQ₁ x₁ hx₁)
      · -- `u ∈ P₁`, `w = y₁`: the edge is `b₁y₁`
        have hua : u = b₁ := by
          rw [hwe] at hadj
          rcases (hE11 u hu y₁ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd h.symm hx₁y₁
          · exact h
        rw [hwe, hua]
        exact hfin ({y₁, y₂, b₁} : Set V) hT₃ b₁ y₁ (by simp) (by simp) hb₁y₁
          (kP₁ b₁ hb₁) (kQ₁ y₁ hy₁)
      · -- `u ∈ P₁`, `w = x₂`: the edge is `a₁x₂`
        have hua : u = a₁ := by
          rw [hwe] at hadj
          rcases (hE12 u hu x₂ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
          · exact h
          · exact absurd h hx₂y₂
        rw [hwe, hua]
        exact hfin ({x₁, x₂, a₁} : Set V) hT₁ a₁ x₂ (by simp) (by simp) ha₁x₂
          (kP₁ a₁ ha₁) (kQ₂ x₂ hx₂)
      · -- `u ∈ P₁`, `w = y₂`: the edge is `b₁y₂`
        have hua : u = b₁ := by
          rw [hwe] at hadj
          rcases (hE12 u hu y₂ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd h.symm hx₂y₂
          · exact h
        rw [hwe, hua]
        exact hfin ({y₁, y₂, b₁} : Set V) hT₃ b₁ y₂ (by simp) (by simp) hb₁y₂
          (kP₁ b₁ hb₁) (kQ₂ y₂ hy₂)
    · rcases hw with (hwe | hwe) | (hwe | hwe)
      · -- `u ∈ P₂`, `w = x₁`: the edge is `a₂x₁`
        have hua : u = a₂ := by
          rw [hwe] at hadj
          rcases (hE21 u hu x₁ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
          · exact h
          · exact absurd h hx₁y₁
        rw [hwe, hua]
        exact hfin ({x₁, y₂, a₂} : Set V) hT₂ a₂ x₁ (by simp) (by simp) ha₂x₁
          (kP₂ a₂ ha₂) (kQ₁ x₁ hx₁)
      · -- `u ∈ P₂`, `w = y₁`: the edge is `b₂y₁`
        have hua : u = b₂ := by
          rw [hwe] at hadj
          rcases (hE21 u hu y₁ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd h.symm hx₁y₁
          · exact h
        rw [hwe, hua]
        exact hfin ({y₁, x₂, b₂} : Set V) hT₄ b₂ y₁ (by simp) (by simp) hb₂y₁
          (kP₂ b₂ hb₂) (kQ₁ y₁ hy₁)
      · -- `u ∈ P₂`, `w = x₂`: the edge is `b₂x₂`
        have hua : u = b₂ := by
          rw [hwe] at hadj
          rcases (hE22 u hu x₂ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd h hx₂y₂
          · exact h
        rw [hwe, hua]
        exact hfin ({y₁, x₂, b₂} : Set V) hT₄ b₂ x₂ (by simp) (by simp) hb₂x₂
          (kP₂ b₂ hb₂) (kQ₂ x₂ hx₂)
      · -- `u ∈ P₂`, `w = y₂`: the edge is `a₂y₂`
        have hua : u = a₂ := by
          rw [hwe] at hadj
          rcases (hE22 u hu y₂ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
          · exact h
          · exact absurd h hx₂y₂.symm
        rw [hwe, hua]
        exact hfin ({x₁, y₂, a₂} : Set V) hT₂ a₂ y₂ (by simp) (by simp) ha₂y₂
          (kP₂ a₂ ha₂) (kQ₂ y₂ hy₂)

/-- **Closing `P₁` into a hole through `y₁`, `f`, `x₁`.**

PAPER: *"and then `f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole"*.  The cycle is written here as the
cyclic concatenation of the four blocks `P₁`, `[y₁]`, `[f]`, `[x₁]`, which is the form
`CyclicPathConcatenationIsHole.isHoleList_flatMap_of_cyclic` takes. -/
theorem closing_hole {G : SimpleGraph V} {P₁ : List V} {a₁ b₁ x₁ y₁ f : V}
    (hP₁ : IsPathFrom G P₁ a₁ b₁)
    (hx₁P₁ : x₁ ∉ P₁) (hy₁P₁ : y₁ ∉ P₁) (hfP₁ : f ∉ P₁)
    (hx₁y₁ : x₁ ≠ y₁) (hfx₁ne : f ≠ x₁) (hfy₁ne : f ≠ y₁)
    (hadjx₁ : ∀ u ∈ P₁, (G.Adj u x₁ ↔ u = a₁))
    (hadjy₁ : ∀ u ∈ P₁, (G.Adj u y₁ ↔ u = b₁))
    (hnadj : ¬ G.Adj x₁ y₁)
    (hfx : G.Adj f x₁) (hfy : G.Adj f y₁)
    (hfanti : ∀ v ∈ P₁, ¬ G.Adj f v)
    (h2 : 2 ≤ P₁.length) :
    IsHoleList G (([P₁, [y₁], [f], [x₁]] : List (List V)).flatMap id) ∧
      holeLength (([P₁, [y₁], [f], [x₁]] : List (List V)).flatMap id) = P₁.length + 3 := by
  have hnadj' : ¬ G.Adj y₁ x₁ := fun h => hnadj h.symm
  have hfanti' : ∀ v ∈ P₁, ¬ G.Adj v f := fun v hv h => hfanti v hv h.symm
  refine ⟨?_, by simp [holeLength]⟩
  refine CyclicPathConcatenationIsHole.isHoleList_flatMap_of_cyclic G
    ([P₁, [y₁], [f], [x₁]] : List (List V))
    (fun i => if i = 0 then a₁ else if i = 1 then y₁ else if i = 2 then f else x₁)
    (fun i => if i = 0 then b₁ else if i = 1 then y₁ else if i = 2 then f else x₁)
    (by norm_num) ?_ ?_ ?_ ?_ (by simp; omega)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> norm_num
    · exact hP₁
    · exact ⟨PathBasics.isPathList_singleton G y₁, rfl, rfl⟩
    · exact ⟨PathBasics.isPathList_singleton G f, rfl, rfl⟩
    · exact ⟨PathBasics.isPathList_singleton G x₁, rfl, rfl⟩
  · intro i j hi hj hij
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      first
        | exact absurd rfl hij
        | (intro z hz hz2
           simp only [List.getElem_cons_zero, List.getElem_cons_succ,
             List.mem_cons, List.not_mem_nil, or_false] at hz hz2
           simp_all)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceMod, Nat.reduceAdd] <;>
      intro z hz w hw <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hw <;> norm_num
    · subst hw; simp [hadjy₁ z hz]
    · subst hz; subst hw; exact iff_of_true hfy.symm ⟨rfl, rfl⟩
    · subst hz; subst hw; exact iff_of_true hfx ⟨rfl, rfl⟩
    · subst hz
      simp only [eq_self_iff_true, true_and]
      rw [SimpleGraph.adj_comm]
      exact hadjx₁ w hw
  · intro i j hi hj hij h1 h2'
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      first
        | omega
        | (intro z hz w hw
           simp only [List.getElem_cons_zero, List.getElem_cons_succ,
             List.mem_cons, List.not_mem_nil, or_false] at hz hw
           simp_all)

/-- **The negative half.**

PAPER: *"so we assume it has no neighbour in `V(P₁)`.  But then `f` is adjacent to all four of
`x₁, x₂, y₁, y₂`, since it has two neighbours in every triangle of `K`, and then
`f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole, a contradiction."*

Only the two triangles `N c₁ = {x₁, x₂, a₁}` and `N c₃ = {y₁, y₂, b₁}` are needed, since the
hole uses only `x₁` and `y₁`.  `Odd (pathLength P₁)` is the first half of **9.1**. -/
theorem false_of_saturating_anticomplete_to_P₁ [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ1len : pathLength Q₁ = 1) (hQ2len : pathLength Q₂ = 1)
    (hoddP₁ : Odd (pathLength P₁))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (f : V) (hf : f ∉ K)
    (hT₁ : (({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton)
    (hT₃ : (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton)
    (hfP₁ : ∀ v ∈ P₁, ¬ G.Adj f v) : False := by
  obtain ⟨-, d1q1, -, -, -, -, hlP₁, -, -, -, -, -, hE11, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hQ₁eq : Q₁ = [x₁, y₁] := KnotLabels.anti_eq_pair_of_length_one hQ₁ hQ1len
  have ha₁ : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb₁ : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).2
  have hx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hx₁P₁ : x₁ ∉ P₁ := fun h => d1q1 x₁ h hx₁
  have hy₁P₁ : y₁ ∉ P₁ := fun h => d1q1 y₁ h hy₁
  have ha₁x₁ : a₁ ≠ x₁ := fun h => d1q1 a₁ ha₁ (h ▸ hx₁)
  have hb₁y₁ : b₁ ≠ y₁ := fun h => d1q1 b₁ hb₁ (h ▸ hy₁)
  -- `x₁ y₁` is a nonedge of `G`: `Q₁` is an antipath of length `1`
  have hx₁y₁c : Gᶜ.Adj x₁ y₁ := PathBasics.isPathFrom_ends_adj_of_length_one hQ₁ hQ1len
  have hx₁y₁ : x₁ ≠ y₁ := hx₁y₁c.ne
  have hnadj : ¬ G.Adj x₁ y₁ := ((SimpleGraph.compl_adj G x₁ y₁).mp hx₁y₁c).2
  -- *"`f` is adjacent to all four of `x₁, x₂, y₁, y₂`, since it has two neighbours in every
  -- triangle of `K`"* — only `x₁` and `y₁` are used below.
  have hfx₁ : G.Adj f x₁ := by
    rcases mem_or_mem_of_subsingleton hT₁ (show x₁ ∈ ({x₁, x₂, a₁} : Set V) by simp)
      (show a₁ ∈ ({x₁, x₂, a₁} : Set V) by simp) (Ne.symm ha₁x₁) with h | h
    · exact h
    · exact absurd h (hfP₁ a₁ ha₁)
  have hfy₁ : G.Adj f y₁ := by
    rcases mem_or_mem_of_subsingleton hT₃ (show y₁ ∈ ({y₁, y₂, b₁} : Set V) by simp)
      (show b₁ ∈ ({y₁, y₂, b₁} : Set V) by simp) (Ne.symm hb₁y₁) with h | h
    · exact h
    · exact absurd h (hfP₁ b₁ hb₁)
  -- the only edges between `P₁` and `{x₁, y₁}` are `a₁x₁` and `b₁y₁`
  have hadjx₁ : ∀ u ∈ P₁, (G.Adj u x₁ ↔ u = a₁) := by
    intro u hu
    rw [hE11 u hu x₁ (by simp)]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩); · exact h
      · exact absurd h hx₁y₁
    · intro h; exact Or.inl ⟨h, rfl⟩
  have hadjy₁ : ∀ u ∈ P₁, (G.Adj u y₁ ↔ u = b₁) := by
    intro u hu
    rw [hE11 u hu y₁ (by simp)]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩); · exact absurd h.symm hx₁y₁
      · exact h
    · intro h; exact Or.inr ⟨h, rfl⟩
  have hfP₁' : f ∉ P₁ := by
    intro h
    refine hf ?_
    rw [hK]
    exact Or.inl (Or.inl (Or.inl h))
  have hfx₁ne : f ≠ x₁ := hfx₁.ne
  have hfy₁ne : f ≠ y₁ := hfy₁.ne
  -- *"`f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole"*
  have hP₁len : 2 ≤ P₁.length := by
    have := PathBasics.length_eq_pathLength_add_one hP₁.1
    omega
  obtain ⟨hhole, hlen⟩ :=
    closing_hole hP₁ hx₁P₁ hy₁P₁ hfP₁' hx₁y₁ hfx₁ne hfy₁ne hadjx₁ hadjy₁ hnadj
      hfx₁ hfy₁ hfP₁ hP₁len
  have heven := hG.1 _ hhole
  rw [hlen] at heven
  obtain ⟨k, hk⟩ := hoddP₁
  obtain ⟨m, hm⟩ := heven
  unfold pathLength at hk
  omega

/-- **The negative half, with `P₁` and `P₂` exchanged.**

PAPER: *"so we assume it has no neighbour in `V(P₁)`"* — the paper reaches that normalisation
*"up to symmetry"*, i.e. by exchanging `P₁, P₂` (and renaming the ends accordingly).  Carrying
out the exchange gives the hole `f-x₁-a₂-P₂-b₂-y₁-f`: the only edges between `V(P₂)` and
`{x₁, y₁}` are `a₂x₁` and `b₂y₁`, so the same argument applies verbatim, now using the
triangles `N c₂ = {x₁, y₂, a₂}` and `N c₄ = {y₁, x₂, b₂}`. -/
theorem false_of_saturating_anticomplete_to_P₂ [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ1len : pathLength Q₁ = 1) (hQ2len : pathLength Q₂ = 1)
    (hoddP₂ : Odd (pathLength P₂))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (f : V) (hf : f ∉ K)
    (hT₂ : (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton)
    (hT₄ : (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton)
    (hfP₂ : ∀ v ∈ P₂, ¬ G.Adj f v) : False := by
  obtain ⟨-, -, -, d2q1, -, -, -, -, -, -, -, -, -, -, hE21, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hQ₁eq : Q₁ = [x₁, y₁] := KnotLabels.anti_eq_pair_of_length_one hQ₁ hQ1len
  have ha₂ : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).1
  have hb₂ : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).2
  have hx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hx₁P₂ : x₁ ∉ P₂ := fun h => d2q1 x₁ h hx₁
  have hy₁P₂ : y₁ ∉ P₂ := fun h => d2q1 y₁ h hy₁
  have ha₂x₁ : a₂ ≠ x₁ := fun h => d2q1 a₂ ha₂ (h ▸ hx₁)
  have hb₂y₁ : b₂ ≠ y₁ := fun h => d2q1 b₂ hb₂ (h ▸ hy₁)
  have hx₁y₁c : Gᶜ.Adj x₁ y₁ := PathBasics.isPathFrom_ends_adj_of_length_one hQ₁ hQ1len
  have hx₁y₁ : x₁ ≠ y₁ := hx₁y₁c.ne
  have hnadj : ¬ G.Adj x₁ y₁ := ((SimpleGraph.compl_adj G x₁ y₁).mp hx₁y₁c).2
  have hfx₁ : G.Adj f x₁ := by
    rcases mem_or_mem_of_subsingleton hT₂ (show x₁ ∈ ({x₁, y₂, a₂} : Set V) by simp)
      (show a₂ ∈ ({x₁, y₂, a₂} : Set V) by simp) (Ne.symm ha₂x₁) with h | h
    · exact h
    · exact absurd h (hfP₂ a₂ ha₂)
  have hfy₁ : G.Adj f y₁ := by
    rcases mem_or_mem_of_subsingleton hT₄ (show y₁ ∈ ({y₁, x₂, b₂} : Set V) by simp)
      (show b₂ ∈ ({y₁, x₂, b₂} : Set V) by simp) (Ne.symm hb₂y₁) with h | h
    · exact h
    · exact absurd h (hfP₂ b₂ hb₂)
  have hadjx₁ : ∀ u ∈ P₂, (G.Adj u x₁ ↔ u = a₂) := by
    intro u hu
    rw [hE21 u hu x₁ (by simp)]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact h
      · exact absurd h hx₁y₁
    · intro h; exact Or.inl ⟨h, rfl⟩
  have hadjy₁ : ∀ u ∈ P₂, (G.Adj u y₁ ↔ u = b₂) := by
    intro u hu
    rw [hE21 u hu y₁ (by simp)]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h.symm hx₁y₁
      · exact h
    · intro h; exact Or.inr ⟨h, rfl⟩
  have hfP₂' : f ∉ P₂ := by
    intro h
    exact hf (by rw [hK]; exact Or.inl (Or.inl (Or.inr h)))
  have hP₂len : 2 ≤ P₂.length := by
    have := PathBasics.length_eq_pathLength_add_one hP₂.1
    obtain ⟨k, hk⟩ := hoddP₂
    omega
  obtain ⟨hhole, hlen⟩ :=
    closing_hole hP₂ hx₁P₂ hy₁P₂ hfP₂' hx₁y₁ hfx₁.ne hfy₁.ne hadjx₁ hadjy₁ hnadj
      hfx₁ hfy₁ hfP₂ hP₂len
  have heven := hG.1 _ hhole
  rw [hlen] at heven
  obtain ⟨k, hk⟩ := hoddP₂
  obtain ⟨m, hm⟩ := heven
  unfold pathLength at hk
  omega

/-- **Claim (1) of the proof of 9.3, first two sentences.**

PAPER: *"Suppose that the neighbour set of some `f ∈ F` saturates `L(H)`.  If `f` has a
neighbour in both `V(P₁)` and `V(P₂)` then statement 1 of the theorem holds, so we assume it
has no neighbour in `V(P₁)`.  But then … a contradiction.  So we assume there is no such
`f` …"*

Read through the dictionary of `Workspace.ProofLemmas.AppearanceFromKnot`, *"the neighbour set
of `f` saturates `L(H)`"* is the conjunction of the four triangle conditions below.  The
conclusion is therefore the dichotomy the paper reaches: either outcome 9.3.1 holds, or no
`f ∈ F` is major, which is the hypothesis under which 5.8 is applied. -/
theorem case1_saturating_dichotomy [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ1len : pathLength Q₁ = 1) (hQ2len : pathLength Q₂ = 1)
    (hoddP₁ : Odd (pathLength P₁)) (hoddP₂ : Odd (pathLength P₂))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (F : Set V) (hFsub : F ⊆ Kᶜ) :
    (∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)) ∨
    (∀ f ∈ F, ¬ ((({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton)) := by
  by_cases hex : ∃ f ∈ F, (({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton
  · obtain ⟨f, hfF, hT₁, hT₂, hT₃, hT₄⟩ := hex
    have hfK : f ∉ K := hFsub hfF
    refine Or.inl ⟨f, hfF, ?_⟩
    by_cases h₁ : ∃ v ∈ P₁, G.Adj f v
    · by_cases h₂ : ∃ v ∈ P₂, G.Adj f v
      · exact resolvesKnot_of_saturating G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
          hknot hP₁ hP₂ hQ₁ hQ₂ hQ1len hQ2len K hK f hT₁ hT₂ hT₃ hT₄ h₁ h₂
      · push_neg at h₂
        exact absurd (false_of_saturating_anticomplete_to_P₂ G hG P₁ P₂ Q₁ Q₂
          a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hQ1len hQ2len hoddP₂ K hK f hfK
          hT₂ hT₄ h₂) (by simp)
    · push_neg at h₁
      exact absurd (false_of_saturating_anticomplete_to_P₁ G hG P₁ P₂ Q₁ Q₂
        a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hQ1len hQ2len hoddP₁ K hK f hfK
        hT₁ hT₃ h₁) (by simp)
  · exact Or.inr fun f hfF hsat => hex ⟨f, hfF, hsat⟩

end Workspace.ProofLemmas.Thm93Case1Major
