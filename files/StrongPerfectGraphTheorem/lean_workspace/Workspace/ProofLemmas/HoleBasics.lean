import Mathlib
import Workspace.Types.Core

/-!
# Basic facts about the list encoding of holes

Infrastructure for the proofs in this development.  A hole of `G` is encoded as
the list `c` of its vertices in cyclic order (`IsHoleList`), and this module
records the projections out of that definition, the two symmetries of a cyclic
order (reversal and rotation), and the interaction of `Berge` with complementation
and with passing to an induced subgraph.

None of these lemmas has a counterpart in the paper; they are bookkeeping for the
chosen encoding.

NOTE ON SYNTAX.  `Mathlib.GroupTheory.Perm.Cycle.Concrete` declares `c[` as a
notation atom (for cycle permutations), so `c[i]'hi` does not parse.  Whenever the
hole is called `c`, its entries must be written `((c)[i]'hi)`.  `Workspace.Types.Core`
does the same.
-/

namespace Workspace.ProofLemmas.HoleBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-! ### Arithmetic helpers

The cyclic successor `(i + 1) % n` of an index `i < n` is `i + 1` unless `i` is the
last index, in which case it wraps to `0`.  Rewriting with `succ_mod_eq` turns the
index side-conditions below into goals `omega` can finish. -/

private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- Adding a constant to both sides of a congruence mod `n` is reversible. -/
private theorem add_mod_cancel_right {n a b k : ℕ} :
    (a + k) % n = (b + k) % n ↔ a % n = b % n :=
  ⟨fun h => Nat.ModEq.add_right_cancel' k h, fun h => Nat.ModEq.add_right k h⟩

/-! ### Projections out of `IsHoleList` -/

theorem hole_length_ge_four {G : SimpleGraph V} {c : List V} (h : IsHoleList G c) :
    4 ≤ c.length := h.1

theorem hole_nodup {G : SimpleGraph V} {c : List V} (h : IsHoleList G c) :
    c.Nodup := h.2.1

/-- Two vertices of a hole are adjacent exactly when their indices are cyclically
consecutive. -/
theorem hole_adj_iff {G : SimpleGraph V} {c : List V} (h : IsHoleList G c)
    {i j : ℕ} (hi : i < c.length) (hj : j < c.length) :
    G.Adj ((c)[i]'hi) ((c)[j]'hj) ↔ (j = (i + 1) % c.length ∨ i = (j + 1) % c.length) :=
  h.2.2 i j hi hj

/-- Consecutive vertices of a hole are adjacent. -/
theorem hole_adj_succ {G : SimpleGraph V} {c : List V} (h : IsHoleList G c)
    {i : ℕ} (hi : i + 1 < c.length) :
    G.Adj ((c)[i]'(Nat.lt_of_succ_lt hi)) ((c)[i + 1]'hi) := by
  refine (hole_adj_iff h (Nat.lt_of_succ_lt hi) hi).mpr (Or.inl ?_)
  rw [Nat.mod_eq_of_lt hi]

/-- The last and the first vertex of a hole are adjacent. -/
theorem hole_adj_wrap {G : SimpleGraph V} {c : List V} (h : IsHoleList G c) :
    G.Adj ((c)[c.length - 1]'(by have := h.1; omega)) ((c)[0]'(by have := h.1; omega)) := by
  have h4 := h.1
  refine (h.2.2 (c.length - 1) 0 (by omega) (by omega)).mpr (Or.inl ?_)
  have he : c.length - 1 + 1 = c.length := by omega
  rw [he, Nat.mod_self]

set_option linter.unusedVariables false in
/-- Two vertices of a hole whose indices are not cyclically consecutive are
non-adjacent.  (The hypothesis `hij : i ≠ j` is not needed — see
`hole_not_adj_of_gap'` — but is kept here because it is how the fact is used.) -/
theorem hole_not_adj_of_gap {G : SimpleGraph V} {c : List V} (h : IsHoleList G c)
    {i j : ℕ} (hi : i < c.length) (hj : j < c.length) (hij : i ≠ j)
    (h1 : j ≠ (i + 1) % c.length) (h2 : i ≠ (j + 1) % c.length) :
    ¬ G.Adj ((c)[i]'hi) ((c)[j]'hj) := by
  intro hadj
  rcases (hole_adj_iff h hi hj).mp hadj with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- `hole_not_adj_of_gap` without the redundant `i ≠ j` hypothesis. -/
theorem hole_not_adj_of_gap' {G : SimpleGraph V} {c : List V} (h : IsHoleList G c)
    {i j : ℕ} (hi : i < c.length) (hj : j < c.length)
    (h1 : j ≠ (i + 1) % c.length) (h2 : i ≠ (j + 1) % c.length) :
    ¬ G.Adj ((c)[i]'hi) ((c)[j]'hj) := by
  intro hadj
  rcases (hole_adj_iff h hi hj).mp hadj with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- Distinct indices of a hole give distinct vertices. -/
theorem hole_ne_of_ne_index {G : SimpleGraph V} {c : List V} (h : IsHoleList G c)
    {i j : ℕ} (hi : i < c.length) (hj : j < c.length) (hij : i ≠ j) :
    ((c)[i]'hi) ≠ ((c)[j]'hj) := fun he =>
  hij ((List.Nodup.getElem_inj_iff (hole_nodup h)).mp he)

/-! ### The two symmetries of a cyclic order -/

/-- Reversing the vertex list of a hole gives a hole. -/
theorem isHoleList_reverse {G : SimpleGraph V} {c : List V} (h : IsHoleList G c) :
    IsHoleList G c.reverse := by
  obtain ⟨h4, hnd, hadj⟩ := h
  refine ⟨by simpa using h4, List.nodup_reverse.mpr hnd, ?_⟩
  intro i j hi hj
  have hi' : i < c.length := by simpa using hi
  have hj' : j < c.length := by simpa using hj
  simp only [List.getElem_reverse, List.length_reverse]
  rw [hadj _ _ (show c.length - 1 - i < c.length by omega)
        (show c.length - 1 - j < c.length by omega),
    succ_mod_eq (show c.length - 1 - i < c.length by omega),
    succ_mod_eq (show c.length - 1 - j < c.length by omega),
    succ_mod_eq hi', succ_mod_eq hj']
  split_ifs <;> omega

/-- Rotating the vertex list of a hole gives a hole.  This is what licenses the
paper's habit of starting the numbering of a hole wherever it likes. -/
theorem isHoleList_rotate {G : SimpleGraph V} {c : List V} (h : IsHoleList G c) (k : ℕ) :
    IsHoleList G (c.rotate k) := by
  obtain ⟨h4, hnd, hadj⟩ := h
  refine ⟨by simpa using h4, List.nodup_rotate.mpr hnd, ?_⟩
  intro i j hi hj
  have hi' : i < c.length := by simpa using hi
  have hj' : j < c.length := by simpa using hj
  have hpos : 0 < c.length := by omega
  have hA : ((j + k) % c.length = (i + k + 1) % c.length) ↔ (j = (i + 1) % c.length) := by
    rw [show i + k + 1 = (i + 1) + k by ring, add_mod_cancel_right, Nat.mod_eq_of_lt hj']
  have hB : ((i + k) % c.length = (j + k + 1) % c.length) ↔ (i = (j + 1) % c.length) := by
    rw [show j + k + 1 = (j + 1) + k by ring, add_mod_cancel_right, Nat.mod_eq_of_lt hi']
  simp only [List.getElem_rotate, List.length_rotate]
  rw [hadj _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)]
  simp only [Nat.mod_add_mod]
  rw [hA, hB]

/-! ### Length and vertex set are invariant -/

theorem holeLength_reverse (c : List V) : holeLength c.reverse = holeLength c := by
  simp [holeLength]

theorem holeLength_rotate (c : List V) (k : ℕ) : holeLength (c.rotate k) = holeLength c := by
  simp [holeLength]

theorem mem_reverse_iff {c : List V} {v : V} : v ∈ c.reverse ↔ v ∈ c := List.mem_reverse

theorem mem_rotate_iff {c : List V} {v : V} {k : ℕ} : v ∈ c.rotate k ↔ v ∈ c := List.mem_rotate

/-- Reversal does not change `V(C)`. -/
theorem setOf_mem_reverse (c : List V) : {v : V | v ∈ c.reverse} = {v : V | v ∈ c} := by
  ext v; exact mem_reverse_iff

/-- Rotation does not change `V(C)`. -/
theorem setOf_mem_rotate (c : List V) (k : ℕ) :
    {v : V | v ∈ c.rotate k} = {v : V | v ∈ c} := by
  ext v; exact mem_rotate_iff

/-! ### Antiholes, complementation, induced subgraphs -/

theorem isAntiholeList_iff {G : SimpleGraph V} {c : List V} :
    IsAntiholeList G c ↔ IsHoleList Gᶜ c := Iff.rfl

/-- `Berge` is invariant under complementation: the paper's "and the same holds in
`Ḡ`". -/
theorem berge_compl {G : SimpleGraph V} : Berge Gᶜ ↔ Berge G := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun c hc => h2 c (by rwa [compl_compl]), h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun c hc => h1 c (by rwa [compl_compl] at hc)⟩

/-- Complementation commutes with passing to an induced subgraph. -/
theorem induce_compl {G : SimpleGraph V} (X : Set V) :
    (G.induce X)ᶜ = (Gᶜ).induce X := by
  ext u v
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- A hole of an induced subgraph, read through `Subtype.val`, is a hole of the
ambient graph, of the same length. -/
theorem isHoleList_map_val {G : SimpleGraph V} {X : Set V} {c : List X}
    (h : IsHoleList (G.induce X) c) : IsHoleList G (c.map Subtype.val) := by
  obtain ⟨h4, hnd, hadj⟩ := h
  refine ⟨by simpa using h4, hnd.map Subtype.val_injective, ?_⟩
  intro i j hi hj
  have hi' : i < c.length := by simpa using hi
  have hj' : j < c.length := by simpa using hj
  simpa using hadj i j hi' hj'

/-- Berge-ness is hereditary. -/
theorem berge_induce {G : SimpleGraph V} (h : Berge G) (X : Set V) :
    Berge (G.induce X) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · simpa [holeLength] using h.1 (c.map Subtype.val) (isHoleList_map_val hc)
  · rw [induce_compl] at hc
    simpa [holeLength] using h.2 (c.map Subtype.val) (isHoleList_map_val hc)

end Workspace.ProofLemmas.HoleBasics
