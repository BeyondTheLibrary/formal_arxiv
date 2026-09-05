import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleBasics

/-!
# The union of two paths with the same ends is a hole

The paper's most frequently used hole-construction is *"`P₁ ∪ P₂` is a hole"*: two induced
paths with the **same two ends**, each on at least three vertices, whose interiors are
disjoint and anticomplete, close up into a hole whose length is the sum of the two path
lengths.  Printed instances include

* 4.3: *"Since `P₁ ∪ P₂` is not a hole, it follows that `P₂` also has interior in `A₁`"*, and
  *"If `u,v` are joined by a path with interior in `A₂`, then its union with one of `P₁`,
  `P₂` would be an odd hole, a contradiction"*;
* 22.4, claim (5): *"its union with the antipath with interior in `Y` is an antihole"*
  (instantiate at `Gᶜ`);
* §13/§15, wherever two paths joining the same pair of `Y`-complete vertices are compared.

This is the missing companion to `PrismBasics.isHoleList_of_path_add_vertex` and
`PrismBasics.isHoleList_of_path_add_two_vertices`, which close a *single* path into a hole
through one or two **extra vertices** rather than through a second path.

Encoding: the hole is `p ++ (interior p').reverse` — the first path in full, then the second
path's interior traversed backwards, so that the two connecting edges of the cycle are
`v–p'[|p'|-2]` and `p'[1]–u`.  See `paper/spec/CONVENTIONS.md` for the list encoding.

Everything is stated for an arbitrary `G`, so instantiating at `Gᶜ` gives the
antipath/antihole mirror that §22 uses.

No counterpart in the paper; this is infrastructure.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.TwoPathsHole

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- Two entries of a list at equal indices are equal. -/
private theorem getElem_eq_of_eq {l : List V} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- **The union of two paths with the same ends, whose interiors are disjoint and
anticomplete, is a hole** — the paper's `P₁ ∪ P₂`.  Its length is the sum of the lengths of
the two paths.

The hypotheses `3 ≤ p.length`, `3 ≤ p'.length` say that each path has length `≥ 2`, i.e. has
a nonempty interior; without them the "union" is not a cycle at all (two paths of length `1`
between the same ends coincide, and a path of length `1` together with a longer one gives a
chorded cycle).  This is exactly what the paper supplies at every call site, where both paths
have interior inside a prescribed set.

Call sites: 4.3 (*"Since `P₁ ∪ P₂` is not a hole …"*, *"its union with one of `P₁`, `P₂`
would be an odd hole"*), and — at `Gᶜ` — 22.4 claim (5) (*"its union with the antipath with
interior in `Y` is an antihole"*). -/
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

/-- **The Berge-wrapped form**, which is what the printed proofs actually invoke:
two paths with the same ends, each on at least three vertices, whose lengths have **opposite
parity**, must have interiors that meet or are joined by an edge — otherwise
`odd_hole_of_two_paths` would produce an odd hole.

The parity hypothesis is stated as `¬ Even (pathLength p + pathLength p')`, which is the form
`odd_hole_of_two_paths` feeds straight into `Berge`; a call site holding
`Even (pathLength p)` and `Odd (pathLength p')` converts in one step.

Call sites: 4.3 (*"Since `P₁ ∪ P₂` is not a hole, it follows that `P₂` also has interior in
`A₁`"*, and the `A₂` paragraph), and — at `Gᶜ` — 22.4 claim (5). -/
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

end Workspace.ProofLemmas.TwoPathsHole
