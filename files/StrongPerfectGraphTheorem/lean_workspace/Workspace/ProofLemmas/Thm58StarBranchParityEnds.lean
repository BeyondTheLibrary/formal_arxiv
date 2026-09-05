import Workspace.ProofLemmas.PathBasics

/-!
# The ends of an induced path are determined by its vertex set

The rung of a branch is an induced path of `G`, and 5.8 (2) hands us *some* induced path `R`
with the same vertex set.  To identify the far end of `R` with the far end of the rung we use
the elementary fact that in an induced path the ends are exactly the vertices with at most one
neighbour on the path, a property of the vertex set alone.

Also here: a slice `p_i-⋯-p_j` of an induced path is a path when `i = j` as well as when
`i < j` (`PathBasics.isPathList_slice` demands `i < j`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarBranchParityEnds

open Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V} {p : List V}

/-- A slice `p_i-⋯-p_j` of an induced path is a path also when `i = j`. -/
theorem isPathList_slice' (h : IsPathList G p) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    IsPathList G ((p.drop i).take (j - i + 1)) :=
  PathBasics.isPathList_take (PathBasics.isPathList_drop h (by omega)) (by omega)

theorem isPathFrom_slice' (h : IsPathList G p) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'(by omega)) (p[j]'hj) :=
  ⟨isPathList_slice' h hij hj, PathBasics.head?_slice p hij hj,
    PathBasics.getLast?_slice p hij hj⟩

/-- An end of an induced path has at most one neighbour on the path. -/
theorem eq_of_adj_end (hp : IsPathList G p) (hlen : 0 < p.length) {x y z : V}
    (hx : x = p[0]'hlen ∨ x = p[p.length - 1]'(by omega))
    (hy : y ∈ p) (hz : z ∈ p) (hxy : G.Adj x y) (hxz : G.Adj x z) : y = z := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  rcases hx with rfl | rfl
  · have h1 := (PathBasics.path_adj_iff hp hlen hi).mp hxy
    have h2 := (PathBasics.path_adj_iff hp hlen hj).mp hxz
    have : i = j := by omega
    subst this; rfl
  · have h1 := (PathBasics.path_adj_iff hp (by omega) hi).mp hxy
    have h2 := (PathBasics.path_adj_iff hp (by omega) hj).mp hxz
    have : i = j := by omega
    subst this; rfl

/-- A vertex of an induced path which is not an end has two distinct neighbours on it. -/
theorem exists_two_adj (hp : IsPathList G p) (hlen : 0 < p.length) {x : V} (hx : x ∈ p)
    (h0 : x ≠ p[0]'hlen) (h1 : x ≠ p[p.length - 1]'(by omega)) :
    ∃ y ∈ p, ∃ z ∈ p, y ≠ z ∧ G.Adj x y ∧ G.Adj x z := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi0 : i ≠ 0 := by rintro rfl; exact h0 rfl
  have hil : i ≠ p.length - 1 := by rintro rfl; exact h1 rfl
  refine ⟨p[i - 1]'(by omega), List.getElem_mem _, p[i + 1]'(by omega),
    List.getElem_mem _, ?_, ?_, ?_⟩
  · intro hc
    have := hp.2.1.getElem_inj_iff.mp hc
    omega
  · exact (PathBasics.path_adj_iff hp hi (by omega)).mpr (by omega)
  · exact (PathBasics.path_adj_iff hp hi (by omega)).mpr (by omega)

/-- Two induced paths with the same vertex set have the same pair of ends. -/
theorem end_mem_ends {p p' : List V} (hp : IsPathList G p) (hp' : IsPathList G p')
    (hlen : 0 < p.length) (hlen' : 0 < p'.length) (hset : ∀ x : V, x ∈ p ↔ x ∈ p')
    {x : V} (hx : x = p[0]'hlen ∨ x = p[p.length - 1]'(by omega)) :
    x = p'[0]'hlen' ∨ x = p'[p'.length - 1]'(by omega) := by
  by_contra hcon
  push_neg at hcon
  have hxp : x ∈ p := by
    rcases hx with rfl | rfl <;> exact List.getElem_mem _
  obtain ⟨y, hy, z, hz, hyz, hxy, hxz⟩ :=
    exists_two_adj hp' hlen' ((hset x).mp hxp) hcon.1 hcon.2
  exact hyz (eq_of_adj_end hp hlen hx ((hset y).mpr hy) ((hset z).mpr hz) hxy hxz)


/-- The tail of a list is the stretch from position `1` to the end. -/
theorem tail_eq_slice (l : List V) :
    l.tail = (l.drop 1).take (l.length - 1 - 1 + 1) := by
  rw [List.drop_one, List.take_of_length_le]
  simp only [List.length_tail]
  omega

/-- Dropping the first vertex of an induced path leaves an induced path. -/
theorem isPathFrom_tail {l : List V} {u v : V} (hl : IsPathFrom G l u v) (h2 : 2 ≤ l.length) :
    IsPathFrom G l.tail (l[1]'(by omega)) v := by
  have hs := isPathFrom_slice' hl.1 (show 1 ≤ l.length - 1 by omega)
    (show l.length - 1 < l.length by omega)
  rw [← tail_eq_slice l] at hs
  have hv : l[l.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hl.2.2 (by omega)
  rwa [hv] at hs

end Workspace.ProofLemmas.Thm58StarBranchParityEnds
