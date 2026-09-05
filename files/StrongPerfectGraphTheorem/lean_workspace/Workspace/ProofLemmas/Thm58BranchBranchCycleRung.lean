import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Types.Tracks

/-!
# A cycle of `H` gives a hole of `G` through the appearance

PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the branch
between `u₁` and `v₁`, and using `u₂` and not `v₂`.  There correspond two paths
in `L(H)` …"*

Two edges of a cycle share an end exactly when they are consecutive on the
cycle, so the edges of a cycle of `H`, listed in cyclic order, form an induced
cycle of `L(H)` of the same length.  Through an appearance isomorphism this is a
hole of `G`.  `Workspace/Types` has no cycle predicate (its tracks are paths and
its holes are induced), so `IsCycleList` is defined here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranchCycleRung

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT

variable {V W : Type*}

/-- The position after `i` on a cycle with `cy.length` vertices. -/
def nxt (cy : List W) (i : ℕ) : ℕ := (i + 1) % cy.length

theorem nxt_lt {cy : List W} {i : ℕ} (hi : i < cy.length) : nxt cy i < cy.length :=
  Nat.mod_lt _ (by omega)

/-- A cycle of `H`, given by the list of its vertices in cyclic order: at least
three vertices, no repetition, and each vertex adjacent to the next one
cyclically. -/
def IsCycleList (H : SimpleGraph W) (cy : List W) : Prop :=
  3 ≤ cy.length ∧ cy.Nodup ∧
    ∀ (i : ℕ) (hi : i < cy.length) (h2 : nxt cy i < cy.length), H.Adj cy[i] cy[nxt cy i]

/-- The `i`-th edge of a cycle. -/
def cycleEdge (cy : List W) (i : ℕ) (hi : i < cy.length) : Sym2 W :=
  have h2 : nxt cy i < cy.length := nxt_lt hi
  s(cy[i], cy[nxt cy i])

theorem cycleEdge_eq (cy : List W) (i : ℕ) (hi : i < cy.length) (h2 : nxt cy i < cy.length) :
    cycleEdge cy i hi = s(cy[i], cy[nxt cy i]) := rfl

theorem cycleEdge_mem {H : SimpleGraph W} {cy : List W} (hc : IsCycleList H cy)
    (i : ℕ) (hi : i < cy.length) : cycleEdge cy i hi ∈ H.edgeSet := hc.2.2 i hi (nxt_lt hi)

/-- Two edges of a cycle are equal only if their indices are. -/
theorem cycleEdge_inj {H : SimpleGraph W} {cy : List W} (hc : IsCycleList H cy)
    {i j : ℕ} (hi : i < cy.length) (hj : j < cy.length)
    (h : cycleEdge cy i hi = cycleEdge cy j hj) : i = j := by
  obtain ⟨h3, hnd, -⟩ := hc
  have hi' : nxt cy i < cy.length := nxt_lt hi
  have hj' : nxt cy j < cy.length := nxt_lt hj
  rw [cycleEdge_eq cy i hi hi', cycleEdge_eq cy j hj hj'] at h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hnd.getElem_inj_iff.mp h1
  · have e1 : i = nxt cy j := hnd.getElem_inj_iff.mp h1
    have e2 : nxt cy i = j := hnd.getElem_inj_iff.mp h2
    rw [nxt, PathGlue.succ_mod_eq hi] at e2
    rw [nxt, PathGlue.succ_mod_eq hj] at e1
    split_ifs at e1 e2 <;> omega

/-- Two edges of a cycle share a vertex exactly when their indices are
cyclically consecutive.  This is what makes the line graph of a cycle an
*induced* cycle. -/
theorem cycleEdge_meet_iff {H : SimpleGraph W} {cy : List W} (hc : IsCycleList H cy)
    {i j : ℕ} (hi : i < cy.length) (hj : j < cy.length) (hij : i ≠ j) :
    (∃ v : W, v ∈ cycleEdge cy i hi ∧ v ∈ cycleEdge cy j hj) ↔
      (j = nxt cy i ∨ i = nxt cy j) := by
  obtain ⟨h3, hnd, -⟩ := hc
  have hi' : nxt cy i < cy.length := nxt_lt hi
  have hj' : nxt cy j < cy.length := nxt_lt hj
  rw [cycleEdge_eq cy i hi hi', cycleEdge_eq cy j hj hj']
  constructor
  · rintro ⟨v, hvi, hvj⟩
    rcases Sym2.mem_iff.mp hvi with rfl | rfl <;> rcases Sym2.mem_iff.mp hvj with h2 | h2
    · exact absurd (hnd.getElem_inj_iff.mp h2) hij
    · exact Or.inr (hnd.getElem_inj_iff.mp h2)
    · exact Or.inl (hnd.getElem_inj_iff.mp h2).symm
    · have hh := hnd.getElem_inj_iff.mp h2
      rw [nxt, PathGlue.succ_mod_eq hi, nxt, PathGlue.succ_mod_eq hj] at hh
      split_ifs at hh <;> omega
  · rintro (h | h)
    · subst h
      exact ⟨cy[nxt cy i], Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    · subst h
      exact ⟨cy[nxt cy j], Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩

/-- The hole of `G` carried by a cycle of `H`: its edges, in cyclic order, read
through the appearance isomorphism. -/
def cycleRung {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {cy : List W} (hc : IsCycleList H cy) : List V :=
  List.ofFn (fun i : Fin cy.length =>
    (↑(φ ⟨cycleEdge cy i.1 i.2, cycleEdge_mem hc i.1 i.2⟩) : V))

theorem cycleRung_length {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {cy : List W} (hc : IsCycleList H cy) :
    (cycleRung φ hc).length = cy.length := by
  simp [cycleRung]

theorem cycleRung_getElem {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {cy : List W} (hc : IsCycleList H cy)
    (i : ℕ) (hi : i < (cycleRung φ hc).length) (hi' : i < cy.length) :
    (cycleRung φ hc)[i]'hi =
      (↑(φ ⟨cycleEdge cy i hi', cycleEdge_mem hc i hi'⟩) : V) := by
  simp [cycleRung]

theorem cycleRung_subset_K {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {cy : List W} (hc : IsCycleList H cy) :
    ∀ x ∈ cycleRung φ hc, x ∈ K := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < cy.length := by rw [cycleRung_length] at hi; exact hi
  rw [cycleRung_getElem φ hc i hi hi']
  exact (φ _).2

/-- **The edges of a cycle of `H` form a hole of `G`.** -/
theorem isHoleList_cycleRung {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {cy : List W} (hc : IsCycleList H cy)
    (h4 : 4 ≤ cy.length) : IsHoleList G (cycleRung φ hc) := by
  have hlen := cycleRung_length φ hc
  refine ⟨by omega, ?_, ?_⟩
  · rw [cycleRung, List.nodup_ofFn]
    intro a b hab
    have hedge : cycleEdge cy a.1 a.2 = cycleEdge cy b.1 b.2 :=
      congrArg (fun e : H.edgeSet => e.1) (φ.injective (Subtype.ext hab))
    exact Fin.ext (cycleEdge_inj hc a.2 b.2 hedge)
  · intro i j hi hj
    have hi' : i < cy.length := by omega
    have hj' : j < cy.length := by omega
    rw [cycleRung_getElem φ hc i hi hi', cycleRung_getElem φ hc j hj hj', hlen]
    by_cases hij : i = j
    · subst hij
      constructor
      · intro hadj; exact absurd rfl (G.ne_of_adj hadj)
      · intro hh
        rw [PathGlue.succ_mod_eq hi'] at hh
        split_ifs at hh <;> omega
    · have hmap : G.Adj (↑(φ ⟨cycleEdge cy i hi', cycleEdge_mem hc i hi'⟩) : V)
          (↑(φ ⟨cycleEdge cy j hj', cycleEdge_mem hc j hj'⟩) : V) ↔
          H.lineGraph.Adj ⟨cycleEdge cy i hi', cycleEdge_mem hc i hi'⟩
            ⟨cycleEdge cy j hj', cycleEdge_mem hc j hj'⟩ := φ.map_rel_iff
      rw [hmap, SimpleGraph.lineGraph_adj_iff_exists]
      constructor
      · rintro ⟨-, v, hv1, hv2⟩
        exact (cycleEdge_meet_iff hc hi' hj' hij).mp ⟨v, hv1, hv2⟩
      · intro hh
        refine ⟨fun hcon => hij (cycleEdge_inj hc hi' hj'
          (congrArg (fun e : H.edgeSet => e.1) hcon)), ?_⟩
        exact (cycleEdge_meet_iff hc hi' hj' hij).mpr hh

end Workspace.ProofLemmas.Thm58BranchBranchCycleRung
