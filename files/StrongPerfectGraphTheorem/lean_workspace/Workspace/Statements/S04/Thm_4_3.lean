/-  Proof attempt 1 for statement 4.3.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.Statements.S04.Thm_4_2

/-!
# Section 4 — Skew partitions

The six numbered statements 4.1 – 4.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 14–18).
Every definition used here is imported, never restated:

* `Workspace.Types.Core` — `Berge`, `IsPathFrom`, `IsAntipathFrom`, `pathLength`,
  `SPGT.interior`, `IsComponent`, `IsAnticomponent`, `VertexComplete`,
  `VertexAnticomplete`, `Complete`, `Anticomplete`, `SPGT.Balanced`
* `Workspace.Types.Decompositions` — `IsSkewPartition`, `IsBalancedSkewPartition`,
  `AdmitsBalancedSkewPartition`
* `Workspace.Types.SkewTools` — `IsLooseSkewPartition`, `AdmitsLooseSkewPartition`,
  `IsPathPair`, `IsAntipathPair`, `IsKernel`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S04

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

namespace SPGT

/-! ### Infrastructure for 4.3

None of this is in the paper.  It is the bookkeeping behind the printed phrases
*"Since `P₁ ∪ P₂` is not a hole, it follows that `P₂` also has interior in `A₁`"* and
*"If `u,v` are joined by a path with interior in `A₂`, then its union with one of `P₁`, `P₂`
would be an odd hole"*. -/

namespace Helpers43

open Workspace.ProofLemmas

variable {V : Type*}

/-- Two entries of a list at equal indices are equal. -/
theorem getElem_eq_of_eq {l : List V} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- A path whose two ends are distinct has at least two vertices. -/
theorem two_le_length {G : SimpleGraph V} {q : List V} {u v : V}
    (hq : IsPathFrom G q u v) (hne : u ≠ v) : 2 ≤ q.length := by
  have hpos := PathBasics.path_length_pos hq.1
  have h0 : q[0]'hpos = u := PathBasics.getElem_zero_of_head? hq.2.1 hpos
  have hl : q[q.length - 1]'(by omega) = v := PathBasics.getElem_last_of_getLast? hq.2.2 hpos
  by_contra hc
  push_neg at hc
  exact hne (h0.symm.trans ((getElem_eq_of_eq hpos (by omega) (by omega)).trans hl))

/-- A path with at least two vertices has distinct ends. -/
theorem ends_ne {G : SimpleGraph V} {q : List V} {u v : V}
    (hq : IsPathFrom G q u v) (h2 : 2 ≤ q.length) : u ≠ v := by
  intro h
  have hpos : 0 < q.length := by omega
  have h0 : q[0]'hpos = u := PathBasics.getElem_zero_of_head? hq.2.1 hpos
  have hl : q[q.length - 1]'(by omega) = v := PathBasics.getElem_last_of_getLast? hq.2.2 hpos
  exact PathBasics.path_ne_of_ne_index hq.1 hpos (by omega) (by omega)
    (h0.trans (h.trans hl.symm))

/-- A path between two distinct, nonadjacent vertices has at least three vertices. -/
theorem three_le_length {G : SimpleGraph V} {q : List V} {u v : V}
    (hq : IsPathFrom G q u v) (hne : u ≠ v) (hadj : ¬ G.Adj u v) : 3 ≤ q.length := by
  have h2 := two_le_length hq hne
  have hpos : 0 < q.length := by omega
  have h0 : q[0]'hpos = u := PathBasics.getElem_zero_of_head? hq.2.1 hpos
  have hl : q[q.length - 1]'(by omega) = v := PathBasics.getElem_last_of_getLast? hq.2.2 hpos
  by_contra hc
  push_neg at hc
  have hadj2 : G.Adj (q[0]'hpos) (q[1]'(by omega)) := PathBasics.path_adj_succ hq.1 (by omega)
  have hone : q[1]'(show 1 < q.length by omega) = v :=
    (getElem_eq_of_eq (by omega) (by omega) (by omega)).trans hl
  rw [h0, hone] at hadj2
  exact hadj hadj2

/-- **The union of two paths with the same ends, whose interiors are disjoint and
anticomplete, is a hole** — the paper's `P₁ ∪ P₂`.  Its length is the sum of the lengths of
the two paths. -/
theorem odd_hole_of_two_paths {G : SimpleGraph V} {p p' : List V} {u v : V}
    (hp : IsPathFrom G p u v) (hp' : IsPathFrom G p' u v)
    (h3 : 3 ≤ p.length) (h3' : 3 ≤ p'.length)
    (hdisj : ∀ x ∈ SPGT.interior p, x ∉ SPGT.interior p')
    (hanti : ∀ x ∈ SPGT.interior p, ∀ y ∈ SPGT.interior p', ¬ G.Adj x y) :
    IsHoleList G (p ++ (SPGT.interior p').reverse) ∧
      holeLength (p ++ (SPGT.interior p').reverse) = pathLength p + pathLength p' := by
  have hIlen : (SPGT.interior p').length = p'.length - 2 := PathBasics.interior_length p'
  have hint' : IsPathFrom G (SPGT.interior p')
      (p'[1]'(by omega)) (p'[p'.length - 2]'(by omega)) :=
    PathGlue.isPathFrom_interior hp'.1 h3'
  have hR : IsPathFrom G (SPGT.interior p').reverse
      (p'[p'.length - 2]'(by omega)) (p'[1]'(by omega)) :=
    PathBasics.isPathFrom_reverse hint'
  have hu0 : p'[0]'(show 0 < p'.length by omega) = u :=
    PathBasics.getElem_zero_of_head? hp'.2.1 (by omega)
  have hvn : p'[p'.length - 1]'(show p'.length - 1 < p'.length by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp'.2.2 (by omega)
  have hmemR : ∀ y : V, y ∈ (SPGT.interior p').reverse ↔ y ∈ SPGT.interior p' :=
    fun y => List.mem_reverse
  have hdisjP : ∀ x ∈ p, x ∉ (SPGT.interior p').reverse := by
    intro x hx hxR
    rw [hmemR] at hxR
    have hx' := (PathBasics.mem_interior_iff_of_pathFrom hp').mp hxR
    by_cases hxi : x ∈ SPGT.interior p
    · exact hdisj x hxi hxR
    · have hcases := (PathBasics.mem_interior_iff_of_pathFrom hp).not.mp hxi
      push_neg at hcases
      rcases eq_or_ne x u with rfl | hxu
      · exact hx'.2.1 rfl
      · exact hx'.2.2 (hcases hx hxu)
  have hcross : ∀ x ∈ p, ∀ y ∈ (SPGT.interior p').reverse,
      (G.Adj x y ↔ (x = v ∧ y = p'[p'.length - 2]'(by omega)) ∨
        (x = u ∧ y = p'[1]'(by omega))) := by
    intro x hx y hyR
    rw [hmemR] at hyR
    obtain ⟨k, hk, hk1, hk2, hky⟩ := PathBasics.exists_getElem_of_mem_interior hp'.1 hyR
    constructor
    · intro hadj
      by_cases hxi : x ∈ SPGT.interior p
      · exact absurd hadj (hanti x hxi y hyR)
      · have hcases := (PathBasics.mem_interior_iff_of_pathFrom hp).not.mp hxi
        push_neg at hcases
        rcases eq_or_ne x u with hxu | hxu
        · right
          refine ⟨hxu, ?_⟩
          have hadj0 : G.Adj (p'[0]'(show 0 < p'.length by omega)) (p'[k]'hk) := by
            rw [hu0, hky, ← hxu]; exact hadj
          have hkk := (PathBasics.path_adj_iff hp'.1 (show 0 < p'.length by omega) hk).mp hadj0
          have hk1' : k = 1 := by omega
          subst hk1'
          exact hky.symm
        · have hxv : x = v := hcases hx hxu
          left
          refine ⟨hxv, ?_⟩
          have hadjn : G.Adj (p'[p'.length - 1]'(show p'.length - 1 < p'.length by omega))
              (p'[k]'hk) := by
            rw [hvn, hky, ← hxv]; exact hadj
          have hkk := (PathBasics.path_adj_iff hp'.1
            (show p'.length - 1 < p'.length by omega) hk).mp hadjn
          have hk2' : k = p'.length - 2 := by omega
          subst hk2'
          exact hky.symm
    · rintro (⟨hxv, hyw⟩ | ⟨hxu, hyw⟩)
      · rw [hxv, hyw, ← hvn]
        exact (PathBasics.path_adj_iff hp'.1 (by omega) (by omega)).mpr (Or.inr (by omega))
      · rw [hxu, hyw, ← hu0]
        exact (PathBasics.path_adj_iff hp'.1 (by omega) (by omega)).mpr (Or.inl (by omega))
  have hlen : 4 ≤ p.length + (SPGT.interior p').reverse.length := by
    rw [List.length_reverse, hIlen]; omega
  refine ⟨PathGlue.glue_hole hp hR hdisjP hcross hlen, ?_⟩
  simp only [holeLength, List.length_append, List.length_reverse, hIlen, pathLength]
  omega

/-- PAPER (4.3): *"Since `P₁ ∪ P₂` is not a hole, it follows that `P₂` also has interior in
`A₁`."*  If the two paths have the same ends and the sum of their lengths is odd, then in a
Berge graph their interiors must meet or be joined by an edge — otherwise their union is an
odd hole. -/
theorem interiors_linked {G : SimpleGraph V} (hG : Berge G) {p p' : List V} {u v : V}
    (hp : IsPathFrom G p u v) (hp' : IsPathFrom G p' u v)
    (h3 : 3 ≤ p.length) (h3' : 3 ≤ p'.length)
    (hpar : ¬ Even (pathLength p + pathLength p')) :
    (∃ x, x ∈ SPGT.interior p ∧ x ∈ SPGT.interior p') ∨
      (∃ x ∈ SPGT.interior p, ∃ y ∈ SPGT.interior p', G.Adj x y) := by
  by_cases hd : ∃ x, x ∈ SPGT.interior p ∧ x ∈ SPGT.interior p'
  · exact Or.inl hd
  by_cases ha : ∃ x ∈ SPGT.interior p, ∃ y ∈ SPGT.interior p', G.Adj x y
  · exact Or.inr ha
  exfalso
  push_neg at hd ha
  obtain ⟨hhole, hlen⟩ := odd_hole_of_two_paths hp hp' h3 h3' hd ha
  have heven := hG.1 _ hhole
  rw [hlen] at heven
  exact hpar heven

/-- **The first alternative of 4.3.**

PAPER: *"There is an even path `P₁` and an odd path `P₂` joining `u,v`, both with interior in
`A`.  Let `A₁` be the component of `A` including the interior of `P₁`.  Since `P₁ ∪ P₂` is not
a hole, it follows that `P₂` also has interior in `A₁`.  Let `A₂` be another component of `A`.
If `u,v` are joined by a path with interior in `A₂`, then its union with one of `P₁`, `P₂`
would be an odd hole, a contradiction; so there is no such path.  Hence one of `u,v` has no
neighbours in `A₂`, and hence `(A,B)` is loose."* -/
theorem case_one [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : Berge G) {A B : Set V}
    (hAB : IsSkewPartition G A B) {u v : V} {p p' : List V} (hu : u ∈ B) (hv : v ∈ B)
    (hp : IsPathFrom G p u v) (hpint : ∀ x ∈ SPGT.interior p, x ∈ A)
    (hpodd : Odd (pathLength p))
    (hp' : IsPathFrom G p' u v) (hp'int : ∀ x ∈ SPGT.interior p', x ∈ A)
    (hp'even : Even (pathLength p')) :
    IsLooseSkewPartition G A B := by
  classical
  -- the two ends are distinct and nonadjacent
  have h2p : 2 ≤ p.length := by
    have hpos := PathBasics.path_length_pos hp.1
    obtain ⟨t, ht⟩ := hpodd
    simp only [pathLength] at ht
    omega
  have hne : u ≠ v := ends_ne hp h2p
  have h2p' : 2 ≤ p'.length := two_le_length hp' hne
  have h3p' : 3 ≤ p'.length := by
    obtain ⟨t, ht⟩ := hp'even
    simp only [pathLength] at ht
    omega
  have hu0' : p'[0]'(show 0 < p'.length by omega) = u :=
    PathBasics.getElem_zero_of_head? hp'.2.1 (by omega)
  have hvn' : p'[p'.length - 1]'(show p'.length - 1 < p'.length by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp'.2.2 (by omega)
  have hnadj : ¬ G.Adj u v := by
    have hends := PathBasics.path_ends_not_adj hp'.1 h3p'
    rwa [hu0', hvn'] at hends
  have h3p : 3 ≤ p.length := three_le_length hp hne hnadj
  -- the sum of the two lengths is odd
  have hpar : ¬ Even (pathLength p + pathLength p') := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hpodd
    obtain ⟨t, ht⟩ := hp'even
    omega
  -- *"Let `A₁` be the component of `A` including the interior of `P₁`."*
  have hconp : ConnectedSet G {z : V | z ∈ SPGT.interior p} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathGlue.isPathFrom_interior hp.1 h3p).1
  have hconp' : ConnectedSet G {z : V | z ∈ SPGT.interior p'} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathGlue.isPathFrom_interior hp'.1 h3p').1
  have hx₀ : (p'[1]'(show 1 < p'.length by omega)) ∈ SPGT.interior p' :=
    PathBasics.getElem_mem_interior hp'.1 (by omega) le_rfl (by omega)
  have hx₀A : (p'[1]'(show 1 < p'.length by omega)) ∈ A := hp'int _ hx₀
  obtain ⟨A₁, hA₁, hx₀A₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A hx₀A
  -- *"Since `P₁ ∪ P₂` is not a hole, it follows that `P₂` also has interior in `A₁`."*
  have hlink := interiors_linked hG hp hp' h3p h3p' hpar
  have hconU : ConnectedSet G
      ({z : V | z ∈ SPGT.interior p} ∪ {z : V | z ∈ SPGT.interior p'}) :=
    ConnectedSetUnionAttach.connectedSet_union hconp hconp' (by
      rcases hlink with ⟨x, hx1, hx2⟩ | ⟨x, hx1, y, hy1, hadj⟩
      · exact Or.inl ⟨x, hx1, hx2⟩
      · exact Or.inr ⟨x, hx1, y, hy1, hadj⟩)
  have hUA : ({z : V | z ∈ SPGT.interior p} ∪ {z : V | z ∈ SPGT.interior p'}) ⊆ A := by
    rintro z (hz | hz)
    · exact hpint z hz
    · exact hp'int z hz
  have hUsub : ({z : V | z ∈ SPGT.interior p} ∪ {z : V | z ∈ SPGT.interior p'}) ⊆ A₁ :=
    Helpers42.subset_component hconU hUA hA₁ (Or.inr hx₀) hx₀A₁
  have hpsub : ∀ z ∈ SPGT.interior p, z ∈ A₁ := fun z hz => hUsub (Or.inl hz)
  have hp'sub : ∀ z ∈ SPGT.interior p', z ∈ A₁ := fun z hz => hUsub (Or.inr hz)
  -- *"Let `A₂` be another component of `A`."*
  have hAne : A.Nonempty := ⟨_, hx₀A⟩
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQne⟩ :=
    ComponentsOfSetBasics.exists_two_isComponent G hAne hAB.2.2.1
  obtain ⟨A₂, hA₂, hA₂ne⟩ : ∃ A₂ : Set V, IsComponent G A A₂ ∧ A₂ ≠ A₁ := by
    by_cases hq : Q₁ = A₁
    · exact ⟨Q₂, hQ₂, fun he => hQne (hq.trans he.symm)⟩
    · exact ⟨Q₁, hQ₁, hq⟩
  have hdisj12 : Disjoint A₁ A₂ :=
    ComponentsOfSetBasics.disjoint_of_isComponent G hA₁ hA₂ (Ne.symm hA₂ne)
  have hanti12 : Anticomplete G A₁ A₂ :=
    ComponentsOfSetBasics.anticomplete_of_isComponent G hA₁ hA₂ (Ne.symm hA₂ne)
  have hABd : ∀ x ∈ A, x ∉ B := fun x hx hxB => (Set.disjoint_left.mp hAB.2.1) hx hxB
  have huA₂ : u ∉ A₂ := fun h => hABd u (hA₂.1 h) hu
  have hvA₂ : v ∉ A₂ := fun h => hABd v (hA₂.1 h) hv
  -- *"If `u,v` are joined by a path with interior in `A₂`, then its union with one of
  --   `P₁`, `P₂` would be an odd hole, a contradiction; so there is no such path."*
  have hkey : (¬ ∃ x ∈ A₂, G.Adj u x) ∨ (¬ ∃ x ∈ A₂, G.Adj v x) := by
    by_contra hc
    push_neg at hc
    obtain ⟨hcu, hcv⟩ := hc
    obtain ⟨q, hq, hqint⟩ :=
      PathInteriorIn.exists_path_interior_in hA₂.2.1 huA₂ hvA₂ hcu hcv
    have h3q : 3 ≤ q.length := three_le_length hq hne hnadj
    rcases Nat.even_or_odd (pathLength q) with hqe | hqo
    · -- pair the even path `q` with the odd path `P₂`
      have hpar' : ¬ Even (pathLength q + pathLength p) := by
        rintro ⟨r, hr⟩
        obtain ⟨s, hs⟩ := hpodd
        obtain ⟨t, ht⟩ := hqe
        omega
      rcases interiors_linked hG hq hp h3q h3p hpar' with
        ⟨x, hx1, hx2⟩ | ⟨x, hx1, y, hy1, hadj⟩
      · exact Set.disjoint_left.mp hdisj12 (hpsub x hx2) (hqint x hx1)
      · exact hanti12 y (hpsub y hy1) x (hqint x hx1) hadj.symm
    · -- pair the odd path `q` with the even path `P₁`
      have hpar' : ¬ Even (pathLength q + pathLength p') := by
        rintro ⟨r, hr⟩
        obtain ⟨s, hs⟩ := hqo
        obtain ⟨t, ht⟩ := hp'even
        omega
      rcases interiors_linked hG hq hp' h3q h3p' hpar' with
        ⟨x, hx1, hx2⟩ | ⟨x, hx1, y, hy1, hadj⟩
      · exact Set.disjoint_left.mp hdisj12 (hp'sub x hx2) (hqint x hx1)
      · exact hanti12 y (hp'sub y hy1) x (hqint x hx1) hadj.symm
  -- *"Hence one of `u,v` has no neighbours in `A₂`, and hence `(A,B)` is loose."*
  rcases hkey with hk | hk
  · push_neg at hk
    exact ⟨hAB, Or.inl ⟨u, hu, A₂, hA₂, hk⟩⟩
  · push_neg at hk
    exact ⟨hAB, Or.inl ⟨v, hv, A₂, hA₂, hk⟩⟩

end Helpers43

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **4.3** (printed p. 15)

PAPER: *"Let `(A,B)` be a skew partition of a Berge graph `G`.  If either:*

*• there exist `u,v ∈ B` joined by an odd path with interior in `A`, and joined by an even
path with interior in `A`, or*

*• there exist `u,v ∈ A` joined by an odd antipath with interior in `B`, and joined by an even
antipath with interior in `B`,*

*then `(A,B)` is loose and therefore `G` admits a balanced skew partition."*

Transcription notes.

* In each alternative the *same* pair `u,v` carries both the odd and the even path (resp.
  antipath), so the two paths `p` (odd) and `p'` (even) are bound together with `u,v`.
* The paper does **not** require `u,v` to be nonadjacent (in the first alternative) or
  adjacent (in the second), nor `u ≠ v`, so no such conjunct is added.
* The conclusion is the conjunction of both asserted facts: `(A,B)` is loose, *and* `G`
  admits a balanced skew partition. -/
theorem thm_4_3 (G : SimpleGraph V) (hG : Berge G) (A B : Set V)
    (hAB : IsSkewPartition G A B)
    (h : (∃ (u v : V) (p p' : List V), u ∈ B ∧ v ∈ B ∧
            IsPathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ A) ∧ Odd (pathLength p) ∧
            IsPathFrom G p' u v ∧ (∀ x ∈ SPGT.interior p', x ∈ A) ∧ Even (pathLength p')) ∨
         (∃ (u v : V) (p p' : List V), u ∈ A ∧ v ∈ A ∧
            IsAntipathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ B) ∧ Odd (pathLength p) ∧
            IsAntipathFrom G p' u v ∧ (∀ x ∈ SPGT.interior p', x ∈ B) ∧
              Even (pathLength p'))) :
    IsLooseSkewPartition G A B ∧ AdmitsBalancedSkewPartition G := by
  -- *"By taking complements we may assume that the first case of the theorem applies."*
  have hloose : IsLooseSkewPartition G A B := by
    rcases h with ⟨u, v, p, p', hu, hv, hp, hpint, hpodd, hp', hp'int, hp'even⟩ |
      ⟨u, v, p, p', hu, hv, hp, hpint, hpodd, hp', hp'int, hp'even⟩
    · exact Helpers43.case_one hG hAB hu hv hp hpint hpodd hp' hp'int hp'even
    · refine Workspace.ProofLemmas.LooseSkewPartition.isLooseSkewPartition_of_compl ?_
      exact Helpers43.case_one
        (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG)
        (Workspace.ProofLemmas.ClassLemmas.isSkewPartition_compl.mpr hAB)
        hu hv hp hpint hpodd hp' hp'int hp'even
  exact ⟨hloose, thm_4_2 G hG ⟨A, B, hloose⟩⟩


end SPGT

end Workspace.Statements.S04
