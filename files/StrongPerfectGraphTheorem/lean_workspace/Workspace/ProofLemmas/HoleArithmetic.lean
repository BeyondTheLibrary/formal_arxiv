import Mathlib
import Workspace.ProofLemmas.PathGlue

/-!
# Cyclic index arithmetic for holes

Four facts that every "long hole" step of the paper reduces to, and that had been written out
more than once each in `ProofAttempts/`:

* `hole_no_short_chord` — the generic *"which is impossible since `n ≥ 6`"*: on a cycle of
  length `≥ 6`, a neighbour of `s` other than `t` and a neighbour of `t` other than `s` sit at
  cyclic distance `3`, hence are not cyclically consecutive.  §§16–23 make this step constantly.
* `two_common_nbrs` — *"since every vertex in `X` is adjacent to both `p₁` and `pₙ` it follows
  that at most one vertex of `X` is in `D`"* (2.10): two **distinct** common neighbours of two
  distinct non-consecutive cycle vertices force the cycle to have length `4`.
* `rot_last` / `rot_head_last` — cutting a hole at a named edge.  If `b` is the cyclic successor
  of `a`, then `L.rotate b` runs from `L[b]` round to `L[a]`; this is the rotation that
  `Workspace.Types.RousselRubio.SPGT.IsLeapForHole` and `IsHatForHole` are stated in terms of.
* `exists_rotate_head` — rotate a named member of a list into position `0`, the standard opening
  move before `HoleMinusVertexPath`.

`getElem_congr_idx` is exported too: rewriting an index inside a `getElem` with `rw` is a motive
error, and this is the lemma to use instead.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
-- `List.length_rotate` is kept in the `simp only` sets on purpose: without it, `rw`ing the
-- length after `getElem_rotate` is a motive error (see `lean_knowledge.md`).
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.HoleArithmetic

open Workspace.ProofLemmas

/-- Rewriting the index of a `getElem`.  **Use this instead of `rw`**: rewriting an index
equation inside `l[i]'h` gives "motive is not type correct". -/
theorem getElem_congr_idx {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by
  subst h; rfl

/-! ## Two distance facts on a cycle -/

/-- **The generic "impossible since the hole is long".**  On a cycle of length `≥ 6` with `ab` a
cyclically consecutive pair, a cyclic neighbour `e` of `a` other than `b` and a cyclic neighbour
`f` of `b` other than `a` are at cyclic distance `3`, hence not cyclically consecutive. -/
theorem hole_no_short_chord {n a b e f : ℕ} (hn6 : 6 ≤ n) (ha : a < n) (hb : b < n)
    (he : e < n) (hf : f < n)
    (hst : b = (a + 1) % n ∨ a = (b + 1) % n)
    (hsz : e = (a + 1) % n ∨ a = (e + 1) % n) (heb : e ≠ b)
    (htz : f = (b + 1) % n ∨ b = (f + 1) % n) (hfa : f ≠ a) :
    ¬ (f = (e + 1) % n ∨ e = (f + 1) % n) := by
  simp only [PathGlue.succ_mod_eq ha, PathGlue.succ_mod_eq hb, PathGlue.succ_mod_eq he,
    PathGlue.succ_mod_eq hf] at hst hsz htz ⊢
  split_ifs at hst hsz htz ⊢ <;> omega

/-- **At most one common neighbour.**  On a cycle of length `≥ 5`, two distinct vertices cannot
have two distinct common cyclic neighbours: that would make the cycle a `4`-cycle. -/
theorem two_common_nbrs {m a b e f : ℕ} (h5 : 5 ≤ m) (ha : a < m) (hb : b < m)
    (he : e < m) (hf : f < m) (hab : a ≠ b) (hef : e ≠ f)
    (h1 : e = (a + 1) % m ∨ a = (e + 1) % m) (h2 : e = (b + 1) % m ∨ b = (e + 1) % m)
    (h3 : f = (a + 1) % m ∨ a = (f + 1) % m) (h4 : f = (b + 1) % m ∨ b = (f + 1) % m) :
    False := by
  simp only [PathGlue.succ_mod_eq ha, PathGlue.succ_mod_eq hb, PathGlue.succ_mod_eq he,
    PathGlue.succ_mod_eq hf] at h1 h2 h3 h4
  split_ifs at h1 h2 h3 h4 <;> omega

/-! ## Cutting a cycle at a named edge -/

/-- `(m - 1 + b) % m = a` when `b` is the cyclic successor of `a`. -/
theorem rot_last {m a b : ℕ} (ha : a < m) (h : b = (a + 1) % m) : (m - 1 + b) % m = a := by
  rcases (by omega : a + 1 < m ∨ a + 1 = m) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    rw [show m - 1 + (a + 1) = m + a by omega, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
  · rw [h1, Nat.mod_self] at h
    subst h
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Cutting a cycle at a named edge.**  If `b` is the cyclic successor of `a` in `L`, then the
rotation `L.rotate b` runs from `L[b]` round to `L[a]`.  This is the rotation in terms of which
`IsLeapForHole` (and the paper's `C \ e`) is stated. -/
theorem rot_head_last {α : Type*} (L : List α) {a b : ℕ} (ha : a < L.length)
    (hb : b < L.length) (h : b = (a + 1) % L.length) :
    (L.rotate b).head? = some ((L)[b]'hb) ∧ (L.rotate b).getLast? = some ((L)[a]'ha) := by
  have hlen : (L.rotate b).length = L.length := List.length_rotate ..
  have hpos : 0 < (L.rotate b).length := by omega
  constructor
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    congr 1
    have hlt : (0 + b) % L.length < L.length := Nat.mod_lt _ (by omega)
    have hg : ((L.rotate b)[0]'hpos) = ((L)[(0 + b) % L.length]'hlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hg]
    exact getElem_congr_idx L hlt hb (by rw [Nat.zero_add, Nat.mod_eq_of_lt hb])
  · rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show (L.rotate b).length - 1 < (L.rotate b).length by omega)]
    congr 1
    have hlt : (L.length - 1 + b) % L.length < L.length := Nat.mod_lt _ (by omega)
    have hg : ((L.rotate b)[(L.rotate b).length - 1]'(by omega))
        = ((L)[(L.length - 1 + b) % L.length]'hlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hg]
    exact getElem_congr_idx L hlt ha (rot_last ha h)

/-- **Rotate a named member into position `0`.**  The standard opening move before applying
`Workspace.ProofLemmas.HoleMinusVertexPath` to a hole through a distinguished vertex.  Length and
membership come from `List.length_rotate` and `List.mem_rotate`. -/
theorem exists_rotate_head {α : Type*} {L : List α} {z : α} (hz : z ∈ L) :
    ∃ r : ℕ, ∀ (h : 0 < (L.rotate r).length), ((L.rotate r)[0]'h) = z := by
  obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem hz
  refine ⟨j, ?_⟩
  intro h
  have hjlt : (0 + j) % L.length < L.length := Nat.mod_lt _ (by omega)
  have hg : ((L.rotate j)[0]'h) = ((L)[(0 + j) % L.length]'hjlt) := by
    simp only [List.getElem_rotate, List.length_rotate]
  rw [hg]
  exact (getElem_congr_idx L hjlt hj (by rw [Nat.zero_add, Nat.mod_eq_of_lt hj])).trans hjz

end Workspace.ProofLemmas.HoleArithmetic
