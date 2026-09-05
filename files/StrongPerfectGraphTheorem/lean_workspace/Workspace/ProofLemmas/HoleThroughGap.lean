import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics

/-!
# A hole through a gap of a path

The paper says, over and over, *"let `C` be a hole containing `x, pᵢ, pᵢ₊₁` and with
`C \ x ⊆ P`"* (18.4, printed p. 111; and the same move in §§16–18 and §23).  The construction
behind that sentence is always the same: `x` is nonadjacent to two consecutive vertices `pᵢ`,
`pᵢ₊₁` of the induced path `P`, but has neighbours on `P` on both sides of them; take the last
neighbour before `pᵢ` and the first neighbour after `pᵢ₊₁`, and the stretch of `P` between
them, closed up through `x`, is a hole.

`exists_hole_through_gap` is that construction.  The two bracketing indices `a < i` and
`b > i + 1` are returned, together with the fact that `x` has **no** neighbour strictly
between them — which is what a caller needs in order to identify the hole's vertices, and to
know that `pᵢ₋₁` and `pᵢ₊₂` lie on the hole.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.HoleThroughGap

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem getElem_index {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- Greatest index below `n` satisfying `Q`. -/
private theorem exists_greatest {Q : ℕ → Prop} : ∀ n : ℕ, (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-- **The paper's `C`.**  Let `P` be an induced path, `x` a vertex off `P` nonadjacent to the
two consecutive vertices `P[i]`, `P[i+1]` but with *some* neighbour on `P` before position `i`
and *some* neighbour after position `i+1`.  Then there are bracketing positions `a < i` and
`b > i + 1` such that `x` is adjacent to `P[a]` and `P[b]` and to nothing strictly between,
and the stretch `P[a] … P[b]` closed through `x` is a hole of length `(b - a) + 2`. -/
theorem exists_hole_through_gap
    {P : List V} (hP : IsPathList G P) {x : V} (hxP : x ∉ P)
    {i : ℕ} (hi : i + 1 < P.length)
    (hxi : ¬ G.Adj x (P[i]'(by omega))) (hxi1 : ¬ G.Adj x (P[i + 1]'hi))
    {a₀ : ℕ} (ha₀ : a₀ < i) (hxa₀ : G.Adj x (P[a₀]'(by omega)))
    {b₀ : ℕ} (hb₀ : i + 1 < b₀) (hb₀len : b₀ < P.length)
    (hxb₀ : G.Adj x (P[b₀]'hb₀len)) :
    ∃ (a b : ℕ) (ha : a < i) (hb : i + 1 < b) (hblen : b < P.length),
      G.Adj x (P[a]'(by omega)) ∧ G.Adj x (P[b]'hblen) ∧
      (∀ (k : ℕ) (hk : k < P.length), a < k → k < b → ¬ G.Adj x (P[k]'hk)) ∧
      IsHoleList G (x :: (P.drop a).take (b - a + 1)) ∧
      holeLength (x :: (P.drop a).take (b - a + 1)) = (b - a) + 2 := by
  classical
  -- `a` — the last neighbour of `x` on `P` before position `i`
  obtain ⟨a, ha, hxa', hamax⟩ :=
    exists_greatest (Q := fun k => ∃ hk : k < P.length, G.Adj x (P[k]'hk)) i
      ⟨a₀, ha₀, ⟨by omega, hxa₀⟩⟩
  obtain ⟨hka, hxa⟩ := hxa'
  -- `b` — the first neighbour of `x` on `P` after position `a`
  have hex : ∃ t : ℕ, ∃ hk : a + 1 + t < P.length, G.Adj x (P[a + 1 + t]'hk) := by
    refine ⟨b₀ - (a + 1), by omega, ?_⟩
    rw [getElem_index P (show a + 1 + (b₀ - (a + 1)) = b₀ from by omega) (by omega) hb₀len]
    exact hxb₀
  obtain ⟨hblen, hxb⟩ := Nat.find_spec hex
  have hbmin : ∀ t : ℕ, t < Nat.find hex → ¬ ∃ hk : a + 1 + t < P.length,
      G.Adj x (P[a + 1 + t]'hk) := fun t ht => Nat.find_min hex ht
  -- the bracketing positions really do bracket the gap
  have hnone : ∀ (k : ℕ) (hk : k < P.length), a < k → k < a + 1 + Nat.find hex →
      ¬ G.Adj x (P[k]'hk) := by
    intro k hk h1 h2 hadj
    refine hbmin (k - (a + 1)) (by omega) ⟨by omega, ?_⟩
    rw [getElem_index P (show a + 1 + (k - (a + 1)) = k from by omega) (by omega) hk]
    exact hadj
  have hbgap : i + 1 < a + 1 + Nat.find hex := by
    by_contra hcon
    rcases (by omega : a + 1 + Nat.find hex < i ∨ a + 1 + Nat.find hex = i ∨
      a + 1 + Nat.find hex = i + 1) with h | h | h
    · have := hamax (a + 1 + Nat.find hex) h ⟨hblen, hxb⟩
      omega
    · refine hxi ?_
      rw [← getElem_index P h hblen (by omega)]
      exact hxb
    · refine hxi1 ?_
      rw [← getElem_index P h hblen hi]
      exact hxb
  have hsne : (P.drop a).take (a + 1 + Nat.find hex - a + 1) ≠ [] := by
    intro hnil
    have hl := PathBasics.length_slice P (show a ≤ a + 1 + Nat.find hex by omega) hblen
    rw [hnil] at hl
    simp only [List.length_nil] at hl
    omega
  refine ⟨a, a + 1 + Nat.find hex, ha, hbgap, hblen, hxa, hxb, hnone, ?_, ?_⟩
  · refine PrismBasics.isHoleList_of_path_add_vertex
      (PathBasics.isPathFrom_slice hP (by omega) hblen) ?_ hxa hxb ?_ ?_
    · rw [PathBasics.pathLength_eq, PathBasics.length_slice P (by omega) hblen]
      omega
    · intro hmem
      obtain ⟨k, hk, -, -, hkx⟩ := (PathBasics.mem_slice_iff P (by omega) hblen).mp hmem
      exact hxP (hkx ▸ List.getElem_mem hk)
    · intro y hy
      obtain ⟨k, hk, h1, h2, rfl⟩ :=
        (PathBasics.mem_interior_slice_iff hP (by omega) hblen).mp hy
      exact hnone k hk h1 h2
  · rw [PrismBasics.holeLength_cons x hsne, PathBasics.pathLength_eq,
      PathBasics.length_slice P (show a ≤ a + 1 + Nat.find hex by omega) hblen]
    omega

end Workspace.ProofLemmas.HoleThroughGap
