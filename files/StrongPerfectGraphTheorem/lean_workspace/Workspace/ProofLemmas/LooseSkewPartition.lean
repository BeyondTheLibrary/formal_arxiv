import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.LeapPrism
import Workspace.Statements.S02.Thm_2_1

/-!
# Anticomponents of a skew partition, and the length bound a non-loose one forces

The vocabulary of Section 4 (`IsLooseSkewPartition`) meets the vocabulary of Section 2
(`thm_2_1`) in the proof of 15.1 (printed p. 92), and the meeting produces one reusable fact:

> *"Now the ends of `P` are `B₂`-complete, and its internal vertices are not, since the skew
> partition is not loose; suppose that `P` has length at least `5`.  Then by 2.1, `B₂` contains
> a leap `x, y` for `P`, and then the subgraph induced on `V(P) ∪ {x,y}` is a long prism, a
> contradiction since `G ∈ F₆`.  So no such path has length `≥ 5`; and similarly no odd
> antipath with ends in `A` and interior in `B` has length `≥ 5`."*

`no_long_odd_path` is the first sentence and `no_long_odd_antipath` the second; the second is
literally the first applied to `Ḡ` with the two sides of the skew partition interchanged, which
needs `isLooseSkewPartition_of_compl` (the *loose* analogue of
`ClassLemmas.isSkewPartition_compl`, which `ClassLemmas` does not carry).

The supporting anticomponent lemmas are stated separately because the same three moves --
*"let `B₁` be the anticomponent containing `b₁, b₁'`"*, *"let `B₂` be a second anticomponent"*,
*"`b₁` is `B₂`-complete"* -- recur throughout Sections 4, 13 and 15.  Note that two vertices of
`B` that are **nonadjacent in `G`** are `Ḡ`-adjacent and therefore automatically lie in the same
anticomponent, so no connectivity argument is ever needed for the first of them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.LooseSkewPartition

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Anticomponents of the `B` side -/

/-- The empty set is anticonnected, so a skew partition has both sides nonempty. -/
theorem nonempty_of_not_anticonnected {G : SimpleGraph V} {B : Set V}
    (h : ¬ AnticonnectedSet G B) : B.Nonempty := by
  rcases Set.eq_empty_or_nonempty B with rfl | hne
  · exact absurd (fun p _ => absurd p.2 (Set.notMem_empty _)) h
  · exact hne

/-- Two vertices of `B` that are nonadjacent in `G` lie in the same anticomponent of `B`. -/
theorem same_anticomponent {G : SimpleGraph V} {B B₁ B₂ : Set V}
    (h₁ : IsAnticomponent G B B₁) (h₂ : IsAnticomponent G B B₂)
    {u v : V} (hu : u ∈ B₁) (hv : v ∈ B₂) (hne : u ≠ v) (hadj : ¬ G.Adj u v) :
    B₁ = B₂ := by
  by_contra hB
  exact (ComponentsOfSetBasics.anticomplete_of_isComponent Gᶜ h₁ h₂ hB) u hu v hv ⟨hne, hadj⟩

/-- A vertex of `B` outside an anticomponent `B₂` of `B` is `B₂`-complete. -/
theorem vertexComplete_of_notMem_anticomponent {G : SimpleGraph V} {B B₂ : Set V}
    (h₂ : IsAnticomponent G B B₂) {u : V} (hu : u ∈ B) (hnu : u ∉ B₂) :
    VertexComplete G u B₂ := by
  obtain ⟨B₁, h₁, hu₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hu
  have hne : B₁ ≠ B₂ := fun h => hnu (h ▸ hu₁)
  intro y hy
  have := (ComponentsOfSetBasics.anticomplete_of_isComponent Gᶜ h₁ h₂ hne) u hu₁ y hy
  by_contra hg
  exact this ⟨fun he => hnu (he ▸ hy), hg⟩

/-- The `B` side of a skew partition has an anticomponent missing any two of its vertices that
are nonadjacent in `G`. -/
theorem exists_far_anticomponent {G : SimpleGraph V} {A B : Set V}
    (hAB : IsSkewPartition G A B) {u v : V} (hu : u ∈ B) (hv : v ∈ B)
    (hne : u ≠ v) (hadj : ¬ G.Adj u v) :
    ∃ B₂ : Set V, IsAnticomponent G B B₂ ∧ u ∉ B₂ ∧ v ∉ B₂ := by
  have hBne : B.Nonempty := nonempty_of_not_anticonnected hAB.2.2.2
  obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
    ComponentsOfSetBasics.exists_two_isComponent Gᶜ hBne hAB.2.2.2
  obtain ⟨B₁, h₁, hu₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hu
  obtain ⟨B₁', h₁', hv₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hv
  have hsame : B₁ = B₁' := same_anticomponent h₁ h₁' hu₁ hv₁ hne hadj
  subst hsame
  by_cases hPB : P = B₁
  · refine ⟨Q, hQ, ?_, ?_⟩
    · exact fun h => (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ h₁ hQ
        (fun he => hPQ (hPB.trans he))).le_bot ⟨hu₁, h⟩
    · exact fun h => (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ h₁ hQ
        (fun he => hPQ (hPB.trans he))).le_bot ⟨hv₁, h⟩
  · refine ⟨P, hP, ?_, ?_⟩
    · exact fun h => (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ h₁ hP
        (fun he => hPB he.symm)).le_bot ⟨hu₁, h⟩
    · exact fun h => (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ h₁ hP
        (fun he => hPB he.symm)).le_bot ⟨hv₁, h⟩

/-! ## *"So no such path has length ≥ 5"* -/

/-- PAPER (15.1): *"Now the ends of `P` are `B₂`-complete, and its internal vertices are not,
since the skew partition is not loose; suppose that `P` has length at least `5`.  Then by 2.1,
`B₂` contains a leap `x, y` for `P`, and then the subgraph induced on `V(P) ∪ {x,y}` is a long
prism, a contradiction since `G ∈ F₆`.  So no such path has length `≥ 5`."* -/
theorem no_long_odd_path {G : SimpleGraph V} (hG : InF6 G) {A B : Set V}
    (hAB : IsSkewPartition G A B) (hnl : ¬ IsLooseSkewPartition G A B)
    {P : List V} {u v : V} (hu : u ∈ B) (hv : v ∈ B) (huv : ¬ G.Adj u v)
    (hP : IsPathFrom G P u v) (hint : ∀ x ∈ SPGT.interior P, x ∈ A)
    (hodd : Odd (pathLength P)) : pathLength P < 5 := by
  by_contra hge
  push Not at hge
  have hberge : Berge G := hG.1.1.1
  have hne : u ≠ v := by
    rintro rfl
    obtain ⟨t, ht⟩ := hodd
    have hlen : P.length = 1 := by
      by_contra hc
      have h2 : 2 ≤ P.length := by
        have := PathBasics.path_length_pos hP.1
        omega
      exact PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)
        ((PathBasics.getElem_zero_of_head? hP.2.1 (by omega)).trans
          (PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)).symm)
    have : pathLength P = 0 := by simp only [pathLength, hlen]
    omega
  obtain ⟨B₂, hB₂, hnu, hnv⟩ := exists_far_anticomponent hAB hu hv hne huv
  have hcu : VertexComplete G u B₂ := vertexComplete_of_notMem_anticomponent hB₂ hu hnu
  have hcv : VertexComplete G v B₂ := vertexComplete_of_notMem_anticomponent hB₂ hv hnv
  have hB₂anti : AnticonnectedSet G B₂ := hB₂.2.1
  have hAB' : ∀ x ∈ A, x ∉ B := by
    intro x hx hxB
    exact (Set.disjoint_left.mp hAB.2.1) hx hxB
  -- no vertex of `P` lies in `B₂`
  have hPB₂ : ∀ w ∈ P, w ∉ B₂ := by
    intro w hw hwB₂
    by_cases hint' : w ∈ SPGT.interior P
    · exact hAB' w (hint w hint') (hB₂.1 hwB₂)
    · have hnot := (PathBasics.mem_interior_iff_of_pathFrom hP).not.mp hint'
      push Not at hnot
      by_cases hwu : w = u
      · exact hnu (hwu ▸ hwB₂)
      · exact hnv ((hnot hw hwu) ▸ hwB₂)
  -- no internal vertex of `P` is `B₂`-complete, since `(A,B)` is not loose
  have hnotcomp : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w B₂ := by
    intro w hw hcw
    exact hnl ⟨hAB, Or.inr ⟨w, hint w hw, B₂, hB₂, hcw⟩⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_1 G hberge B₂ hB₂anti P u v hP hPB₂
      hodd hcu hcv with hedge | ⟨-, a, ha, b, hb, hleap⟩ | ⟨h3, -⟩
  · -- an `B₂`-complete edge of `P` would join two `B₂`-complete vertices of `P`,
    -- and the only ones are the two (nonadjacent) ends
    obtain ⟨x, hx, y, hy, hxy, hcx, hcy⟩ := hedge
    have honly : ∀ w ∈ P, VertexComplete G w B₂ → w = u ∨ w = v := by
      intro w hw hcw
      by_contra hc
      push Not at hc
      exact hnotcomp w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, hc.1, hc.2⟩) hcw
    rcases honly x hx hcx with rfl | rfl <;> rcases honly y hy hcy with rfl | rfl
    · exact G.irrefl hxy
    · exact huv hxy
    · exact huv hxy.symm
    · exact G.irrefl hxy
  · exact hG.1.2.1 (LeapPrism.longPrism_of_leap hleap (by omega))
  · omega


/-! ## *"and similarly no odd antipath with ends in `A` and interior in `B` has length ≥ 5"* -/

/-- A loose skew partition of `Ḡ`, sides swapped, is a loose skew partition of `G`.
(The two bullets of *loose* swap, exactly as the two clauses of *balanced* do.) -/
theorem isLooseSkewPartition_of_compl {G : SimpleGraph V} {A B : Set V}
    (h : IsLooseSkewPartition Gᶜ B A) : IsLooseSkewPartition G A B := by
  obtain ⟨hskew, hcase⟩ := h
  have hAB : IsSkewPartition G A B := ClassLemmas.isSkewPartition_compl.mp hskew
  have hdisj : ∀ x ∈ A, x ∉ B := fun x hx hxB => (Set.disjoint_left.mp hAB.2.1) hx hxB
  refine ⟨hAB, ?_⟩
  rcases hcase with ⟨a, ha, B', hB', hanti⟩ | ⟨b, hb, A', hA', hcomp⟩
  · -- `a ∈ A` has no `Ḡ`-neighbour in the `Ḡ`-component `B'` of `B`, i.e. `a` is
    -- `B'`-complete in `G` and `B'` is an anticomponent of `B`
    refine Or.inr ⟨a, ha, B', hB', ?_⟩
    intro y hy
    have hne : a ≠ y := fun he => hdisj a ha (he ▸ hB'.1 hy)
    by_contra hg
    exact hanti y hy ⟨hne, hg⟩
  · -- dually
    refine Or.inl ⟨b, hb, A', by rwa [IsAnticomponent, compl_compl] at hA', ?_⟩
    intro y hy
    have hA'sub : A' ⊆ A := by
      have : IsComponent G A A' := by rwa [IsAnticomponent, compl_compl] at hA'
      exact this.1
    exact (hcomp y hy).2

/-- PAPER (15.1): *"and similarly no odd antipath with ends in `A` and interior in `B` has
length `≥ 5`"* — the same statement in `Ḡ`, with the two sides of the skew partition
interchanged. -/
theorem no_long_odd_antipath {G : SimpleGraph V} (hG : InF6 G) {A B : Set V}
    (hAB : IsSkewPartition G A B) (hnl : ¬ IsLooseSkewPartition G A B)
    {Q : List V} {u v : V} (hu : u ∈ A) (hv : v ∈ A) (huv : G.Adj u v)
    (hQ : IsAntipathFrom G Q u v) (hint : ∀ x ∈ SPGT.interior Q, x ∈ B)
    (hodd : Odd (pathLength Q)) : pathLength Q < 5 :=
  no_long_odd_path (ClassLemmas.inF6_compl.mpr hG)
    (ClassLemmas.isSkewPartition_compl.mpr hAB)
    (fun h => hnl (isLooseSkewPartition_of_compl h))
    hu hv (fun h => h.2 huv) hQ hint hodd

end Workspace.ProofLemmas.LooseSkewPartition
