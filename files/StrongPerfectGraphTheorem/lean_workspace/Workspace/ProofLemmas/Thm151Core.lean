import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm151Pairing

/-!
# The body of the printed proof of 15.1

PAPER (printed p. 92): *"Let `(A,B)` be a skew partition in `G`, which by 4.2 we may assume is
not loose.  We may assume that there is an odd path `P` of length `≥ 3` with ends in `B` and
with interior in `A`.  Let `P` have ends `b₁, b₁'`, and let their neighbours in `P` be `a₁, a₁'`
respectively.  Let `A₁` be the component of `A` including the interior of `P`, and let `B₁` be
the anticomponent of `B` containing `b₁, b₁'`.  Let `A₂` be a second component of `A`, and `B₂`
a second anticomponent of `B`.  Now the ends of `P` are `B₂`-complete, and its internal vertices
are not, since the skew partition is not loose; suppose that `P` has length at least `5`.  Then
by 2.1, `B₂` contains a leap `x, y` for `P`, and then the subgraph induced on `V(P) ∪ {x,y}` is
a long prism, a contradiction since `G ∈ F₆`.  So no such path has length `≥ 5`; and similarly
no odd antipath with ends in `A` and interior in `B` has length `≥ 5`.  Hence `P` has vertices
`b₁-a₁-a₁'-b₁'` in order.

Now `a₁, a₁'` both have non-neighbours in `B₂`, and hence are joined by an antipath with
interior in `B₂`; this antipath is odd, since its union with `b₁, b₁'` induces an antihole, and
since all such antipaths have length `3` it follows that there exist nonadjacent `b₂, b₂' ∈ B₂`
such that `b₂-a₁-a₁'-b₂'` is a path.  Now `b₁, b₁'` both have neighbours in `A₂`, since the skew
partition is not loose, and hence are joined by a path with interior in `A₂`, and it is odd as
usual, and hence has length `3`; so there exist adjacent `a₂, a₂' ∈ A₂` such that `b₁-a₂-a₂'-b₁'`
is a path.  Since `b₂-b₁-a₂-a₂'-b₁'-b₂` is not an odd hole, `b₂` is adjacent to one of `a₂, a₂'`,
and similarly so is `b₂'`.  But `b₂, b₂'` have no common neighbour in `A₂`, for if `v ∈ A₂` were
adjacent to them both then `v-b₂-a₁-a₁'-b₂'-v` would be an odd hole.  So there are exactly two
edges between `{a₂, a₂'}` and `{b₂, b₂'}`, forming a 2-edge matching.  There are two possible
pairings; in one case the subgraph induced on these eight vertices is a double diamond, and in
the other it is `L(K₃,₃ \ e)`.  In both cases this contradicts that `G ∈ F₆`."*

Everything from *"We may assume that there is an odd path `P` …"* to the end is a
**contradiction**, so `no_odd_path_of_not_loose` below concludes `False`.  The first two
sentences (the appeal to 4.2, and the reduction of the *antipath* alternative to the *path*
alternative by complementation) live in the caller.

The two length bounds are `LooseSkewPartition.no_long_odd_path` / `no_long_odd_antipath`; the
final case split is `Thm151Pairing.doubleDiamond_of_pairing_one` / `not_inF3_of_pairing_two`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm151Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Two small utilities -/

/-- An induced path of length `3` from `u` to `v` is literally the list `[u, x, y, v]`. -/
theorem path_three {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (h3 : pathLength p = 3) :
    ∃ x y : V, p = [u, x, y, v] := by
  have hlen : p.length = 4 := by
    have := PathBasics.length_eq_pathLength_add_one hp.1
    omega
  obtain ⟨a, b, c, d, rfl⟩ := PathGlue.length_eq_four hlen
  refine ⟨b, c, ?_⟩
  have ha : a = u := by simpa using hp.2.1
  have hd : d = v := by simpa using hp.2.2
  rw [ha, hd]

/-- *"its union with `b₁, b₁'` induces an antihole"* / *"`b₁-R-b₁'-a₁'-a₁-b₁` is a hole"*.

Closing an induced path `Q` (from `u` to `v`) through **two** further adjacent vertices `s, t`,
where `s` sees only `v` on `Q` and `t` sees only `u`.  The resulting hole is `Q ++ [s, t]`, of
length `Q.length + 2 = pathLength Q + 3`. -/
theorem hole_of_path_add_edge {G : SimpleGraph V} {Q : List V} {u v s t : V}
    (hQ : IsPathFrom G Q u v) (h2 : 2 ≤ Q.length)
    (hst : G.Adj s t) (hsv : G.Adj v s) (htu : G.Adj u t)
    (hsu : ¬ G.Adj u s) (htv : ¬ G.Adj v t)
    (hsQ : s ∉ Q) (htQ : t ∉ Q)
    (hint : ∀ x ∈ Q, x ≠ u → x ≠ v → ¬ G.Adj x s ∧ ¬ G.Adj x t) :
    IsHoleList G (Q ++ [s, t]) := by
  have hstne : s ≠ t := G.ne_of_adj hst
  have huv : u ≠ v := by
    rintro rfl
    exact hsu hsv
  have hst2 : IsPathFrom G [s, t] s t := ⟨PathBasics.isPathList_pair hst, rfl, by simp⟩
  refine PathGlue.glue_hole hQ hst2 ?_ ?_ ?_
  · intro x hx hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact hsQ hx
    · have hxt : x = t := by simpa using hmem'
      exact htQ (hxt ▸ hx)
  · intro x hx y hy
    by_cases hxu : x = u
    · subst hxu
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact iff_of_false hsu (by simp [huv, hstne])
      · have hyt : y = t := by simpa using hy'
        subst hyt
        exact iff_of_true htu (by simp)
    · by_cases hxv : x = v
      · subst hxv
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact iff_of_true hsv (by simp)
        · have hyt : y = t := by simpa using hy'
          subst hyt
          exact iff_of_false htv (by simp [Ne.symm hstne, Ne.symm huv])
      · obtain ⟨hns, hnt⟩ := hint x hx hxu hxv
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact iff_of_false hns (by simp [hxv, hxu])
        · have hyt : y = t := by simpa using hy'
          subst hyt
          exact iff_of_false hnt (by simp [hxv, hxu])
  · simp only [List.length_cons, List.length_nil]
    omega

/-- Length bookkeeping for `hole_of_path_add_edge`. -/
theorem holeLength_add_edge {Q : List V} (s t : V) (h : 0 < Q.length) :
    holeLength (Q ++ [s, t]) = pathLength Q + 3 := by
  simp only [holeLength, pathLength, List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## The body of the proof -/

/-- PAPER (15.1, everything after *"We may assume that there is an odd path `P` …"*).

There is no odd path with ends nonadjacent vertices of `B` and interior in `A`, when `(A,B)` is
a non-loose skew partition of a graph in `F₆`. -/
theorem no_odd_path_of_not_loose {G : SimpleGraph V} (hG : InF6 G) {A B : Set V}
    (hAB : IsSkewPartition G A B) (hnl : ¬ IsLooseSkewPartition G A B)
    {P : List V} {b₁ b₁' : V} (hb₁ : b₁ ∈ B) (hb₁' : b₁' ∈ B) (hnadj : ¬ G.Adj b₁ b₁')
    (hP : IsPathFrom G P b₁ b₁') (hintP : ∀ x ∈ SPGT.interior P, x ∈ A)
    (hodd : Odd (pathLength P)) : False := by
  classical
  have hberge : Berge G := hG.1.1.1
  have hdisjAB : ∀ x ∈ A, x ∉ B := fun x hx hxB => (Set.disjoint_left.mp hAB.2.1) hx hxB
  have hdisjBA : ∀ x ∈ B, x ∉ A := fun x hx hxA => (Set.disjoint_left.mp hAB.2.1) hxA hx
  -- ==========================================================================
  -- *"Hence `P` has vertices `b₁-a₁-a₁'-b₁'` in order."*
  -- ==========================================================================
  have hlt5 := LooseSkewPartition.no_long_odd_path hG hAB hnl hb₁ hb₁' hnadj hP hintP hodd
  have hpos : 1 ≤ pathLength P := by obtain ⟨k, hk⟩ := hodd; omega
  have hne : b₁ ≠ b₁' := PathBasics.isPathFrom_ends_ne hP hpos
  have h3 : pathLength P = 3 := by
    obtain ⟨k, hk⟩ := hodd
    rcases (show pathLength P = 1 ∨ pathLength P = 3 by omega) with h1 | h3
    · exact absurd (PathBasics.isPathFrom_ends_adj_of_length_one hP h1) hnadj
    · exact h3
  obtain ⟨a₁, a₁', rfl⟩ := path_three hP h3
  have hPl : IsPathList G [b₁, a₁, a₁', b₁'] := hP.1
  have hb₁a₁ : G.Adj b₁ a₁ :=
    (PathBasics.path_adj_iff hPl (i := 0) (j := 1) (by simp) (by simp)).mpr (Or.inl rfl)
  have ha₁a₁' : G.Adj a₁ a₁' :=
    (PathBasics.path_adj_iff hPl (i := 1) (j := 2) (by simp) (by simp)).mpr (Or.inl rfl)
  have ha₁'b₁' : G.Adj a₁' b₁' :=
    (PathBasics.path_adj_iff hPl (i := 2) (j := 3) (by simp) (by simp)).mpr (Or.inl rfl)
  have hnb₁a₁' : ¬ G.Adj b₁ a₁' := by
    intro h
    have := (PathBasics.path_adj_iff hPl (i := 0) (j := 2) (by simp) (by simp)).mp h
    omega
  have hna₁b₁' : ¬ G.Adj a₁ b₁' := by
    intro h
    have := (PathBasics.path_adj_iff hPl (i := 1) (j := 3) (by simp) (by simp)).mp h
    omega
  have hintPeq : SPGT.interior [b₁, a₁, a₁', b₁'] = [a₁, a₁'] := rfl
  have ha₁A : a₁ ∈ A := hintP a₁ (by rw [hintPeq]; simp)
  have ha₁'A : a₁' ∈ A := hintP a₁' (by rw [hintPeq]; simp)
  have hnea : a₁ ≠ a₁' := G.ne_of_adj ha₁a₁'
  -- ==========================================================================
  -- *"let `B₂` [be] a second anticomponent of `B`"*
  -- ==========================================================================
  obtain ⟨B₂, hB₂, hb₁B₂, hb₁'B₂⟩ :=
    LooseSkewPartition.exists_far_anticomponent hAB hb₁ hb₁' hne hnadj
  have hB₂sub : B₂ ⊆ B := hB₂.1
  have hB₂anti : AnticonnectedSet G B₂ := hB₂.2.1
  have hb₁c : VertexComplete G b₁ B₂ :=
    LooseSkewPartition.vertexComplete_of_notMem_anticomponent hB₂ hb₁ hb₁B₂
  have hb₁'c : VertexComplete G b₁' B₂ :=
    LooseSkewPartition.vertexComplete_of_notMem_anticomponent hB₂ hb₁' hb₁'B₂
  -- ==========================================================================
  -- *"Let `A₂` be a second component of `A`"* (and `A₁` the one containing `P*`)
  -- ==========================================================================
  have hABc : IsSkewPartition Gᶜ B A := ClassLemmas.isSkewPartition_compl.mpr hAB
  have hnadjc : ¬ Gᶜ.Adj a₁ a₁' := fun h => h.2 ha₁a₁'
  obtain ⟨A₂, hA₂c, ha₁A₂, ha₁'A₂⟩ :=
    LooseSkewPartition.exists_far_anticomponent hABc ha₁A ha₁'A hnea hnadjc
  have hA₂ : IsComponent G A A₂ := by
    rw [IsAnticomponent, compl_compl] at hA₂c
    exact hA₂c
  obtain ⟨A₁, hA₁, ha₁A₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A ha₁A
  have ha₁'A₁ : a₁' ∈ A₁ := by
    obtain ⟨A₁', hA₁', ha₁'A₁'⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A ha₁'A
    have heq : A₁ = A₁' := by
      by_contra hc
      exact (ComponentsOfSetBasics.anticomplete_of_isComponent G hA₁ hA₁' hc)
        a₁ ha₁A₁ a₁' ha₁'A₁' ha₁a₁'
    rw [heq]; exact ha₁'A₁'
  have hA₁A₂ : A₁ ≠ A₂ := fun h => ha₁A₂ (h ▸ ha₁A₁)
  have hanti12 : Anticomplete G A₁ A₂ :=
    ComponentsOfSetBasics.anticomplete_of_isComponent G hA₁ hA₂ hA₁A₂
  have hA₂sub : A₂ ⊆ A := hA₂.1
  -- ==========================================================================
  -- *"`a₁, a₁'` … are joined by an antipath `Q` with interior in `B₂`"*
  -- ==========================================================================
  have ha₁nB₂ : a₁ ∉ B₂ := fun h => hdisjAB a₁ ha₁A (hB₂sub h)
  have ha₁'nB₂ : a₁' ∉ B₂ := fun h => hdisjAB a₁' ha₁'A (hB₂sub h)
  have ha₁nn : ∃ x ∈ B₂, ¬ G.Adj a₁ x := by
    by_contra hc
    push Not at hc
    exact hnl ⟨hAB, Or.inr ⟨a₁, ha₁A, B₂, hB₂, hc⟩⟩
  have ha₁'nn : ∃ x ∈ B₂, ¬ G.Adj a₁' x := by
    by_contra hc
    push Not at hc
    exact hnl ⟨hAB, Or.inr ⟨a₁', ha₁'A, B₂, hB₂, hc⟩⟩
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hB₂anti ha₁nB₂ ha₁'nB₂ ha₁nn ha₁'nn
  have hQF : IsPathFrom Gᶜ Q a₁ a₁' := hQ
  have hQlen : 2 ≤ Q.length := by
    by_contra hc
    have h1 : 0 < Q.length := PathBasics.path_length_pos hQF.1
    have : Q.length = 1 := by omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp this
    have e1 : z = a₁ := by simpa using hQF.2.1
    have e2 : z = a₁' := by simpa using hQF.2.2
    exact hnea (e1 ▸ e2 ▸ rfl)
  -- *"since its union with `b₁, b₁'` induces an antihole"*: `Q ++ [b₁, b₁']` is a hole of `Ḡ`
  have hb₁nQ : b₁ ∉ Q := by
    intro h
    exact hb₁B₂ (hQint b₁ ((PathBasics.mem_interior_iff_of_pathFrom hQF).mpr
      ⟨h, fun hc => hdisjBA b₁ hb₁ (hc ▸ ha₁A), fun hc => hdisjBA b₁ hb₁ (hc ▸ ha₁'A)⟩))
  have hb₁'nQ : b₁' ∉ Q := by
    intro h
    exact hb₁'B₂ (hQint b₁' ((PathBasics.mem_interior_iff_of_pathFrom hQF).mpr
      ⟨h, fun hc => hdisjBA b₁' hb₁' (hc ▸ ha₁A), fun hc => hdisjBA b₁' hb₁' (hc ▸ ha₁'A)⟩))
  have hholeQ : IsHoleList Gᶜ (Q ++ [b₁, b₁']) := by
    refine hole_of_path_add_edge hQF hQlen ?_ ?_ ?_ ?_ ?_ hb₁nQ hb₁'nQ ?_
    · exact (SimpleGraph.compl_adj G b₁ b₁').mpr ⟨hne, hnadj⟩
    · exact (SimpleGraph.compl_adj G a₁' b₁).mpr
        ⟨fun hc => hdisjAB a₁' ha₁'A (hc ▸ hb₁), fun hc => hnb₁a₁' hc.symm⟩
    · exact (SimpleGraph.compl_adj G a₁ b₁').mpr
        ⟨fun hc => hdisjAB a₁ ha₁A (hc ▸ hb₁'), hna₁b₁'⟩
    · exact fun h => h.2 hb₁a₁.symm
    · exact fun h => h.2 ha₁'b₁'
    · intro x hx hxu hxv
      have hxB₂ : x ∈ B₂ :=
        hQint x ((PathBasics.mem_interior_iff_of_pathFrom hQF).mpr ⟨hx, hxu, hxv⟩)
      exact ⟨fun h => h.2 (hb₁c x hxB₂).symm, fun h => h.2 (hb₁'c x hxB₂).symm⟩
  have hQodd : Odd (pathLength Q) := by
    have hev := hberge.2 _ hholeQ
    rw [holeLength_add_edge b₁ b₁' (by omega)] at hev
    rw [Nat.even_iff] at hev
    rw [Nat.odd_iff]
    omega
  -- *"and since all such antipaths have length 3"*
  have hQintB : ∀ x ∈ SPGT.interior Q, x ∈ B := fun x hx => hB₂sub (hQint x hx)
  have hQlt5 :=
    LooseSkewPartition.no_long_odd_antipath hG hAB hnl ha₁A ha₁'A ha₁a₁' hQ hQintB hQodd
  have hQ3 : pathLength Q = 3 := by
    obtain ⟨k, hk⟩ := hQodd
    rcases (show pathLength Q = 1 ∨ pathLength Q = 3 by omega) with h1 | h3
    · exact absurd (PathBasics.isPathFrom_ends_adj_of_length_one hQF h1) hnadjc
    · exact h3
  obtain ⟨b₂', b₂, hQeq⟩ := path_three hQF hQ3
  have hQl : IsPathList Gᶜ [a₁, b₂', b₂, a₁'] := hQeq ▸ hQF.1
  have hQinteq : SPGT.interior ([a₁, b₂', b₂, a₁'] : List V) = [b₂', b₂] := rfl
  have hb₂'B₂ : b₂' ∈ B₂ := hQint b₂' (by rw [hQeq, hQinteq]; simp)
  have hb₂B₂ : b₂ ∈ B₂ := hQint b₂ (by rw [hQeq, hQinteq]; simp)
  -- read off the `G`-adjacencies among `a₁, a₁', b₂, b₂'`
  have hcna₁b₂' : ¬ G.Adj a₁ b₂' :=
    ((PathBasics.path_adj_iff hQl (i := 0) (j := 1) (by simp) (by simp)).mpr (Or.inl rfl)).2
  have hcnb₂b₂' : ¬ G.Adj b₂ b₂' := fun h =>
    ((PathBasics.path_adj_iff hQl (i := 1) (j := 2) (by simp) (by simp)).mpr (Or.inl rfl)).2 h.symm
  have hcnb₂a₁' : ¬ G.Adj b₂ a₁' :=
    ((PathBasics.path_adj_iff hQl (i := 2) (j := 3) (by simp) (by simp)).mpr (Or.inl rfl)).2
  have hb₂a₁ : G.Adj b₂ a₁ := by
    by_contra hc
    have hna : ¬ Gᶜ.Adj a₁ b₂ := by
      intro h
      have := (PathBasics.path_adj_iff hQl (i := 0) (j := 2) (by simp) (by simp)).mp h
      omega
    exact hna ((SimpleGraph.compl_adj G a₁ b₂).mpr
      ⟨fun he => hdisjAB a₁ ha₁A (he ▸ hB₂sub hb₂B₂), fun h => hc h.symm⟩)
  have ha₁'b₂' : G.Adj a₁' b₂' := by
    by_contra hc
    have hna : ¬ Gᶜ.Adj b₂' a₁' := by
      intro h
      have := (PathBasics.path_adj_iff hQl (i := 1) (j := 3) (by simp) (by simp)).mp h
      omega
    exact hna ((SimpleGraph.compl_adj G b₂' a₁').mpr
      ⟨fun he => hdisjAB a₁' ha₁'A (he ▸ hB₂sub hb₂'B₂), fun h => hc h.symm⟩)
  -- ==========================================================================
  -- *"`b₁, b₁'` … are joined by a path `R` with interior in `A₂`"*
  -- ==========================================================================
  have hA₂conn : ConnectedSet G A₂ := hA₂.2.1
  have hb₁nA₂ : b₁ ∉ A₂ := fun h => hdisjBA b₁ hb₁ (hA₂sub h)
  have hb₁'nA₂ : b₁' ∉ A₂ := fun h => hdisjBA b₁' hb₁' (hA₂sub h)
  have hb₁nbr : ∃ f ∈ A₂, G.Adj b₁ f := by
    by_contra hc
    push Not at hc
    exact hnl ⟨hAB, Or.inl ⟨b₁, hb₁, A₂, hA₂, hc⟩⟩
  have hb₁'nbr : ∃ f ∈ A₂, G.Adj b₁' f := by
    by_contra hc
    push Not at hc
    exact hnl ⟨hAB, Or.inl ⟨b₁', hb₁', A₂, hA₂, hc⟩⟩
  obtain ⟨R, hR, hRint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hA₂conn hb₁nA₂ hb₁'nA₂ hb₁nbr hb₁'nbr
  have hRlen : 2 ≤ R.length := by
    by_contra hc
    have h1 : 0 < R.length := PathBasics.path_length_pos hR.1
    have : R.length = 1 := by omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp this
    have e1 : z = b₁ := by simpa using hR.2.1
    have e2 : z = b₁' := by simpa using hR.2.2
    exact hne (e1 ▸ e2 ▸ rfl)
  have ha₁nR : a₁ ∉ R := by
    intro h
    exact ha₁A₂ (hRint a₁ ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr
      ⟨h, fun hc => hdisjAB a₁ ha₁A (hc ▸ hb₁), fun hc => hdisjAB a₁ ha₁A (hc ▸ hb₁')⟩))
  have ha₁'nR : a₁' ∉ R := by
    intro h
    exact ha₁'A₂ (hRint a₁' ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr
      ⟨h, fun hc => hdisjAB a₁' ha₁'A (hc ▸ hb₁), fun hc => hdisjAB a₁' ha₁'A (hc ▸ hb₁')⟩))
  have hholeR : IsHoleList G (R ++ [a₁', a₁]) := by
    refine hole_of_path_add_edge hR hRlen ha₁a₁'.symm ha₁'b₁'.symm hb₁a₁ ?_ ?_ ha₁'nR ha₁nR ?_
    · exact hnb₁a₁'
    · exact fun h => hna₁b₁' h.symm
    · intro x hx hxu hxv
      have hxA₂ : x ∈ A₂ :=
        hRint x ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hx, hxu, hxv⟩)
      exact ⟨fun h => hanti12 a₁' ha₁'A₁ x hxA₂ h.symm,
        fun h => hanti12 a₁ ha₁A₁ x hxA₂ h.symm⟩
  have hRodd : Odd (pathLength R) := by
    have hev := hberge.1 _ hholeR
    rw [holeLength_add_edge a₁' a₁ (by omega)] at hev
    rw [Nat.even_iff] at hev
    rw [Nat.odd_iff]
    omega
  have hRintA : ∀ x ∈ SPGT.interior R, x ∈ A := fun x hx => hA₂sub (hRint x hx)
  have hRlt5 :=
    LooseSkewPartition.no_long_odd_path hG hAB hnl hb₁ hb₁' hnadj hR hRintA hRodd
  have hR3 : pathLength R = 3 := by
    obtain ⟨k, hk⟩ := hRodd
    rcases (show pathLength R = 1 ∨ pathLength R = 3 by omega) with h1 | h3
    · exact absurd (PathBasics.isPathFrom_ends_adj_of_length_one hR h1) hnadj
    · exact h3
  obtain ⟨a₂, a₂', hReq⟩ := path_three hR hR3
  have hRl : IsPathList G [b₁, a₂, a₂', b₁'] := hReq ▸ hR.1
  have hRinteq : SPGT.interior ([b₁, a₂, a₂', b₁'] : List V) = [a₂, a₂'] := rfl
  have ha₂A₂ : a₂ ∈ A₂ := hRint a₂ (by rw [hReq, hRinteq]; simp)
  have ha₂'A₂ : a₂' ∈ A₂ := hRint a₂' (by rw [hReq, hRinteq]; simp)
  have hb₁a₂ : G.Adj b₁ a₂ :=
    (PathBasics.path_adj_iff hRl (i := 0) (j := 1) (by simp) (by simp)).mpr (Or.inl rfl)
  have ha₂a₂' : G.Adj a₂ a₂' :=
    (PathBasics.path_adj_iff hRl (i := 1) (j := 2) (by simp) (by simp)).mpr (Or.inl rfl)
  have ha₂'b₁' : G.Adj a₂' b₁' :=
    (PathBasics.path_adj_iff hRl (i := 2) (j := 3) (by simp) (by simp)).mpr (Or.inl rfl)
  have hnb₁a₂' : ¬ G.Adj b₁ a₂' := by
    intro h
    have := (PathBasics.path_adj_iff hRl (i := 0) (j := 2) (by simp) (by simp)).mp h
    omega
  have hna₂b₁' : ¬ G.Adj a₂ b₁' := by
    intro h
    have := (PathBasics.path_adj_iff hRl (i := 1) (j := 3) (by simp) (by simp)).mp h
    omega
  -- ==========================================================================
  -- the eight-vertex configuration
  -- ==========================================================================
  have hcfg : Thm151Pairing.Config G b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂' :=
    { a₁a₁' := ha₁a₁'
      a₂a₂' := ha₂a₂'
      nb₁b₁' := hnadj
      nb₂b₂' := hcnb₂b₂'
      b₁b₂ := hb₁c b₂ hb₂B₂
      b₁b₂' := hb₁c b₂' hb₂'B₂
      b₁'b₂ := hb₁'c b₂ hb₂B₂
      b₁'b₂' := hb₁'c b₂' hb₂'B₂
      b₁a₁ := hb₁a₁
      a₁'b₁' := ha₁'b₁'
      nb₁a₁' := hnb₁a₁'
      na₁b₁' := hna₁b₁'
      b₁a₂ := hb₁a₂
      a₂'b₁' := ha₂'b₁'
      nb₁a₂' := hnb₁a₂'
      na₂b₁' := hna₂b₁'
      b₂a₁ := hb₂a₁
      a₁'b₂' := ha₁'b₂'
      nb₂a₁' := hcnb₂a₁'
      na₁b₂' := hcna₁b₂'
      na₁a₂ := hanti12 a₁ ha₁A₁ a₂ ha₂A₂
      na₁a₂' := hanti12 a₁ ha₁A₁ a₂' ha₂'A₂
      na₁'a₂ := hanti12 a₁' ha₁'A₁ a₂ ha₂A₂
      na₁'a₂' := hanti12 a₁' ha₁'A₁ a₂' ha₂'A₂ }
  -- ==========================================================================
  -- *"Since `b₂-b₁-a₂-a₂'-b₁'-b₂` is not an odd hole, `b₂` is adjacent to one of `a₂, a₂'`"*
  -- ==========================================================================
  have step6 : ∀ w : V, w ∈ B₂ → (G.Adj a₂ w ∨ G.Adj a₂' w) := by
    intro w hw
    by_contra hc
    push Not at hc
    have hwR : w ∉ R := by
      rw [hReq]
      intro hmem
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
      rcases hmem with he | he | he | he
      · exact hb₁B₂ (he ▸ hw)
      · exact hdisjAB a₂ (hA₂sub ha₂A₂) (hB₂sub (he ▸ hw))
      · exact hdisjAB a₂' (hA₂sub ha₂'A₂) (hB₂sub (he ▸ hw))
      · exact hb₁'B₂ (he ▸ hw)
    have hhole : IsHoleList G (w :: R) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hR (by omega)
        ((hb₁c w hw).symm) ((hb₁'c w hw).symm) hwR ?_
      intro x hx
      rw [hReq, hRinteq] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact fun h => hc.1 h.symm
      · exact fun h => hc.2 h.symm
    have hev := hberge.1 _ hhole
    rw [PrismBasics.holeLength_cons w (PathBasics.path_ne_nil hR.1)] at hev
    rw [hR3, Nat.even_iff] at hev
    omega
  -- ==========================================================================
  -- *"But `b₂, b₂'` have no common neighbour in `A₂`"*
  -- ==========================================================================
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24, d25, d26, d27, d28⟩ := Thm151Pairing.config_ne hcfg
  have hSpath : IsPathFrom G [b₂, a₁, a₁', b₂'] b₂ b₂' := by
    refine ⟨PathGlue.isPathList_four ?_ hb₂a₁ ha₁a₁' ha₁'b₂' hcnb₂a₁' hcnb₂b₂' hcna₁b₂',
      rfl, by simp⟩
    simp [d8, d10, d12, d15, d17, d24.symm]
  have step7 : ∀ v : V, v ∈ A₂ → ¬ (G.Adj v b₂ ∧ G.Adj v b₂') := by
    rintro v hv ⟨hv2, hv2'⟩
    have hvR : v ∉ [b₂, a₁, a₁', b₂'] := by
      intro hmem
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact hdisjAB v (hA₂sub hv) (hB₂sub hb₂B₂)
      · exact ha₁A₂ hv
      · exact ha₁'A₂ hv
      · exact hdisjAB v (hA₂sub hv) (hB₂sub hb₂'B₂)
    have hhole : IsHoleList G (v :: [b₂, a₁, a₁', b₂']) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hSpath (by simp [pathLength])
        hv2 hv2' hvR ?_
      intro x hx
      have hxeq : SPGT.interior ([b₂, a₁, a₁', b₂'] : List V) = [a₁, a₁'] := rfl
      rw [hxeq] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact fun h => hanti12 x ha₁A₁ v hv h.symm
      · exact fun h => hanti12 x ha₁'A₁ v hv h.symm
    have hev := hberge.1 _ hhole
    simp only [holeLength, List.length_cons, List.length_nil] at hev
    rw [Nat.even_iff] at hev
    omega
  -- ==========================================================================
  -- *"So there are exactly two edges … There are two possible pairings"*
  -- ==========================================================================
  have h6b₂ := step6 b₂ hb₂B₂
  have h6b₂' := step6 b₂' hb₂'B₂
  have h7a₂ := step7 a₂ ha₂A₂
  have h7a₂' := step7 a₂' ha₂'A₂
  by_cases hp1 : G.Adj a₂ b₂
  · have hnp3 : ¬ G.Adj a₂ b₂' := fun h => h7a₂ ⟨hp1, h⟩
    have hp4 : G.Adj a₂' b₂' := by
      rcases h6b₂' with h | h
      · exact absurd h hnp3
      · exact h
    have hnp2 : ¬ G.Adj a₂' b₂ := fun h => h7a₂' ⟨h, hp4⟩
    exact hG.2 (Thm151Pairing.doubleDiamond_of_pairing_one hcfg hp1 hp4 hnp3 hnp2)
  · have hp2 : G.Adj a₂' b₂ := by
      rcases h6b₂ with h | h
      · exact absurd h hp1
      · exact h
    have hnp4 : ¬ G.Adj a₂' b₂' := fun h => h7a₂' ⟨hp2, h⟩
    have hp3 : G.Adj a₂ b₂' := by
      rcases h6b₂' with h | h
      · exact h
      · exact absurd h hnp4
    exact Thm151Pairing.not_inF3_of_pairing_two hcfg hp3 hp2 hp1 hnp4 hG.1.1

end Workspace.ProofLemmas.Thm151Core
