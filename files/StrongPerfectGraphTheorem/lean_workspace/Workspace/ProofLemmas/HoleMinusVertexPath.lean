import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics

/-!
# Deleting one vertex from a hole leaves a path

§3.1 step 5 of the proof of 1.5 reads *"so `C \ z` is an odd path of `G`, with ends
in `B₁` and with interior in `A`"*, and §3.2 step 3 makes the same move inside
`(G')ᶜ`.  This module records what "`C \ z`" is, mechanically.

The hole is a list `c` with `IsHoleList K c`; the deleted vertex is put at position
`0` by the caller (with `HoleBasics.isHoleList_rotate`, `holeLength_rotate` and
`mem_rotate_iff`), so that "`c` with `v` deleted" is literally `c.tail` and no
`rotate` appears in any statement below.  Writing `v := c[0]`, `x := c[1]` and
`y := c[k-1]` with `k = holeLength c = c.length`, the tail is a path of `K` from
`x` to `y` of length `k - 2`, whose interior consists of the vertices of `c` other
than `v`, `x` and `y`.

Everything is stated for an **arbitrary** graph `K`, so that §3.2 may apply it to
`(G')ᶜ` (the antihole case) with no extra work.

The hypothesis is `5 ≤ c.length`, not `4 ≤ c.length`: both call sites supply
oddness of the hole length together with `HoleBasics.hole_length_ge_four`, so
`k = 4` never occurs there, while `k ≥ 5` is what makes the last two clauses
meaningful.  Note `holeLength c` is by definition `c.length`.

All membership statements are **list** membership, because that is what
`SPGT.interior : List V` and the two clauses of `SPGT.Balanced` consume.

NOTE ON SYNTAX.  `Mathlib.GroupTheory.Perm.Cycle.Concrete` declares `c[` as a
notation atom, so `c[i]'hi` does not parse when the list is literally named `c`;
its entries must be written `((c)[i]'hi)`.

None of these lemmas has a counterpart in the paper; they are bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.HoleMinusVertexPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {W : Type*} {K : SimpleGraph W} {c : List W}

/-- The cyclic successor `(i + 1) % n` of an index `i < n`, with the `%` eliminated
so that `omega` can finish the index bookkeeping. -/
private theorem succ_mod {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- Rewriting the index of a `getElem`. -/
private theorem getElem_congr_idx (l : List W) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by
  subst h; rfl

/-- **(a), first half** The two neighbours `x = c[1]`, `y = c[k-1]` of `v = c[0]` on
the hole are distinct. -/
theorem ends_ne (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    ((c)[1]'(by omega)) ≠ ((c)[c.length - 1]'(by omega)) := by
  exact HoleBasics.hole_ne_of_ne_index hc (by omega) (by omega) (by omega)

/-- **(a), second half** The two neighbours `x = c[1]`, `y = c[k-1]` of `v = c[0]`
on the hole are nonadjacent (this is where `5 ≤ k` is used: for `k = 4` they would
be adjacent). -/
theorem ends_not_adj (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    ¬ K.Adj ((c)[1]'(by omega)) ((c)[c.length - 1]'(by omega)) := by
  refine HoleBasics.hole_not_adj_of_gap' hc (by omega) (by omega) ?_ ?_
  · rw [succ_mod (show (1 : ℕ) < c.length by omega)]
    split_ifs <;> omega
  · rw [succ_mod (show c.length - 1 < c.length by omega)]
    split_ifs <;> omega

/-- **(b)** `c[1]` and `c[k-1]` are *exactly* the neighbours of `c[0]` on the
hole. -/
theorem adj_head_iff (hc : IsHoleList K c) (hlen : 5 ≤ c.length)
    {i : ℕ} (hi : i < c.length) :
    K.Adj ((c)[0]'(by omega)) ((c)[i]'hi) ↔ (i = 1 ∨ i = c.length - 1) := by
  rw [HoleBasics.hole_adj_iff hc (show 0 < c.length by omega) hi,
    succ_mod (show (0 : ℕ) < c.length by omega), succ_mod hi]
  split_ifs <;> simp_all <;> omega

/-- **(c), first part** The hole with its first vertex deleted is a path from
`c[1]` to `c[k-1]`. -/
theorem isPathFrom_tail (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    IsPathFrom K c.tail ((c)[1]'(by omega)) ((c)[c.length - 1]'(by omega)) := by
  have htl : c.tail.length = c.length - 1 := by simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h
    have h0 : c.tail.length = 0 := by rw [h]; rfl
    omega
  · exact List.Nodup.sublist (List.tail_sublist c) (HoleBasics.hole_nodup hc)
  · intro i j hi hj
    have hi' : i + 1 < c.length := by omega
    have hj' : j + 1 < c.length := by omega
    simp only [List.getElem_tail]
    rw [HoleBasics.hole_adj_iff hc hi' hj', succ_mod hi', succ_mod hj']
    split_ifs <;> simp_all <;> omega
  · rw [← List.drop_one, List.head?_drop,
      List.getElem?_eq_getElem (show (1 : ℕ) < c.length by omega)]
  · rw [← List.drop_one, List.getLast?_drop, if_neg (by omega),
      List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show c.length - 1 < c.length by omega)]

/-- **(c), second part** The deleted hole has `k - 1` vertices. -/
theorem length_tail (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    c.tail.length = c.length - 1 := by
  simp

/-- **(c), third part** The deleted hole is a path of length `k - 2`. -/
theorem pathLength_tail (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    pathLength c.tail = c.length - 2 := by
  simp only [pathLength, List.length_tail]
  omega

/-- **(d)** The vertices of the deleted hole are the vertices of the hole other than
the deleted one. -/
theorem mem_tail_iff (hc : IsHoleList K c) (hlen : 5 ≤ c.length) (u : W) :
    u ∈ c.tail ↔ (u ∈ c ∧ u ≠ ((c)[0]'(by omega))) := by
  have htl : c.tail.length = c.length - 1 := by simp
  constructor
  · intro hu
    refine ⟨List.mem_of_mem_tail hu, ?_⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hu
    rw [← hget, List.getElem_tail]
    exact HoleBasics.hole_ne_of_ne_index hc (by omega) (by omega) (by omega)
  · rintro ⟨hu, hne⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hu
    have hi0 : i ≠ 0 := by rintro rfl; exact hne hget.symm
    have hmem : (c.tail[i - 1]'(by omega)) = u :=
      (List.getElem_tail _).trans ((getElem_congr_idx c _ hi (by omega)).trans hget)
    exact hmem ▸ List.getElem_mem _

/-- **(e)** The interior of the deleted hole consists of the vertices of the hole
other than `v = c[0]` and its two neighbours `x = c[1]`, `y = c[k-1]`. -/
theorem mem_interior_tail_iff (hc : IsHoleList K c) (hlen : 5 ≤ c.length) (u : W) :
    u ∈ SPGT.interior c.tail ↔
      (u ∈ c ∧ u ≠ ((c)[0]'(by omega)) ∧ u ≠ ((c)[1]'(by omega)) ∧
        u ≠ ((c)[c.length - 1]'(by omega))) := by
  rw [PathBasics.mem_interior_iff_of_pathFrom (isPathFrom_tail hc hlen),
    mem_tail_iff hc hlen u, and_assoc]

/-- **(f), first half** The entry next to the first end of the deleted hole is an
interior vertex.  (`5 ≤ c.length` gives `4 ≤ c.tail.length`, which is the form in
which this clause is used at §3.2 step 5.) -/
theorem getElem_one_mem_interior_tail (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    (c.tail[1]'(by simp only [List.length_tail]; omega)) ∈ SPGT.interior c.tail := by
  have htl : c.tail.length = c.length - 1 := by simp
  exact PathBasics.getElem_mem_interior (isPathFrom_tail hc hlen).1 _ (by omega) (by omega)

/-- **(f), second half** The entry next to the second end of the deleted hole is an
interior vertex. -/
theorem getElem_sub_two_mem_interior_tail (hc : IsHoleList K c) (hlen : 5 ≤ c.length) :
    (c.tail[c.tail.length - 2]'(by simp only [List.length_tail]; omega)) ∈
      SPGT.interior c.tail := by
  have htl : c.tail.length = c.length - 1 := by simp
  exact PathBasics.getElem_mem_interior (isPathFrom_tail hc hlen).1 _ (by omega) (by omega)

end Workspace.ProofLemmas.HoleMinusVertexPath
