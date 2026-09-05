import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleYEdgeParity

/-!
# Counting the `Y`-complete edges of a path by index

The final paragraph of 18.3 (`paper/proofs/18_3.md`, published page 110) counts

> *"`y`, … the number of `Y`-complete edges in `P`"*

and compares it with *"the number of elements of `{p₁, pₙ}` that are `Y`-complete"*.  In the
frozen Lean statement both are `Set.ncard`s — one of a set of `Sym2 V`, one of a set of
vertices.  The counting argument itself, however, is an argument about **indices** along the
path.  This module is the bridge between the two.

Because `P` is an **induced** path, two of its vertices are adjacent exactly when their
positions differ by one, so the `Y`-complete edges of `P` are in bijection with the indices `k`
such that `pₖ` and `pₖ₊₁` are both `Y`-complete.  That is `yEdges_ncard_eq_index_ncard`.

`ends_YComplete_ncard` is the (entirely routine) evaluation of the other side.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm183EdgeCount

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- The set of indices `k` such that the `k`-th and `(k+1)`-st vertices of `p` both exist and
are `Y`-complete.  This is the paper's *"`Y`-complete edge of `P`"*, read off positionally. -/
def YEdgeIdx (G : SimpleGraph V) (Y : Set V) (p : List V) : Set ℕ :=
  {k : ℕ | ∃ hk : k + 1 < p.length,
    VertexComplete G (p[k]'(Nat.lt_of_succ_lt hk)) Y ∧ VertexComplete G (p[k + 1]'hk) Y}

/-- **The `Y`-complete edges of an induced path are exactly its `Y`-complete consecutive
pairs.**  Two vertices of an induced path are adjacent iff their positions differ by one, so
`k ↦ s(pₖ, pₖ₊₁)` is a bijection from `YEdgeIdx` onto the edge set counted by 18.3. -/
theorem yEdges_ncard_eq_index_ncard {G : SimpleGraph V} {Y : Set V} {p : List V}
    (hp : IsPathList G p) :
    (HoleYEdgeParity.yEdges G Y p).ncard = (YEdgeIdx G Y p).ncard := by
  classical
  obtain ⟨hne, hnd, hadj⟩ := hp
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hne
  set d : V := p[0]'hpos with hd
  set f : ℕ → Sym2 V := fun k => s(p.getD k d, p.getD (k + 1) d) with hf
  have hgetD : ∀ (k : ℕ) (hk : k < p.length), p.getD k d = p[k]'hk :=
    fun k hk => List.getD_eq_getElem p d hk
  -- `f` sends the index set onto the edge set.
  have himg : HoleYEdgeParity.yEdges G Y p = f '' YEdgeIdx G Y p := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hadjuv, huY, hvY⟩
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hv
      rcases (hadj a b ha hb).mp hadjuv with hab | hba
      · refine ⟨a, ⟨by omega, ?_, ?_⟩, ?_⟩
        · exact huY
        · have : (p[a + 1]'(by omega)) = (p[b]'hb) := by congr 1
          rw [this]; exact hvY
        · simp only [hf]
          rw [hgetD a ha, hgetD (a + 1) (by omega)]
          congr 2
      · refine ⟨b, ⟨by omega, ?_, ?_⟩, ?_⟩
        · exact hvY
        · have : (p[b + 1]'(by omega)) = (p[a]'ha) := by congr 1
          rw [this]; exact huY
        · simp only [hf]
          rw [hgetD b hb, hgetD (b + 1) (by omega)]
          rw [show (p[b + 1]'(by omega)) = (p[a]'ha) by congr 1]
          exact Sym2.eq_swap
    · rintro ⟨k, ⟨hk, hkY, hk1Y⟩, rfl⟩
      refine ⟨p.getD k d, ?_, p.getD (k + 1) d, ?_, rfl, ?_, ?_, ?_⟩
      · rw [hgetD k (by omega)]; exact List.getElem_mem _
      · rw [hgetD (k + 1) hk]; exact List.getElem_mem _
      · rw [hgetD k (by omega), hgetD (k + 1) hk]
        exact (hadj k (k + 1) (by omega) hk).mpr (Or.inl rfl)
      · rw [hgetD k (by omega)]; exact hkY
      · rw [hgetD (k + 1) hk]; exact hk1Y
  -- `f` is injective on the index set.
  have hinj : Set.InjOn f (YEdgeIdx G Y p) := by
    rintro k ⟨hk, -, -⟩ l ⟨hl, -, -⟩ hkl
    simp only [hf] at hkl
    rw [hgetD k (by omega), hgetD (k + 1) hk, hgetD l (by omega), hgetD (l + 1) hl] at hkl
    have hinj' : ∀ (a b : ℕ) (ha : a < p.length) (hb : b < p.length),
        ((p[a]'ha) = (p[b]'hb) ↔ a = b) := by
      intro a b ha hb
      exact List.Nodup.getElem_inj_iff hnd
    rcases Sym2.eq_iff.mp hkl with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact (hinj' _ _ _ _).mp h1
    · exact absurd ((hinj' _ _ _ _).mp h2) (by have := (hinj' _ _ _ _).mp h1; omega)
  rw [himg, Set.ncard_image_of_injOn hinj]

open Classical in
/-- *"the number of elements of `{p₁, pₙ}` that are `Y`-complete"*, evaluated.

`VertexComplete` is not decidable, so the two `if`s are elaborated with
`Classical.propDecidable`; downstream callers should discharge any instance mismatch with
`split_ifs` (or `Subsingleton.elim`) rather than by trying to match the instance. -/
theorem ends_YComplete_ncard {G : SimpleGraph V} {Y : Set V} {p₁ pₙ : V} (hne : p₁ ≠ pₙ) :
    {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y}.ncard =
      (if VertexComplete G p₁ Y then 1 else 0) + (if VertexComplete G pₙ Y then 1 else 0) := by
  classical
  by_cases h1 : VertexComplete G p₁ Y <;> by_cases h2 : VertexComplete G pₙ Y
  · have hset : {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y} = {p₁, pₙ} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨fun h => h.1, ?_⟩
      rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, h1⟩
      · exact ⟨Or.inr rfl, h2⟩
    rw [hset, Set.ncard_pair hne, if_pos h1, if_pos h2]
  · have hset : {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y} = {p₁} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hw⟩
        · rfl
        · exact absurd hw h2
      · rintro rfl
        exact ⟨Or.inl rfl, h1⟩
    rw [hset, Set.ncard_singleton, if_pos h1, if_neg h2]
  · have hset : {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y} = {pₙ} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hw⟩
        · exact absurd hw h1
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h2⟩
    rw [hset, Set.ncard_singleton, if_neg h1, if_pos h2]
  · have hset : {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y} = (∅ : Set V) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro (rfl | rfl)
      · exact h1
      · exact h2
    rw [hset, Set.ncard_empty, if_neg h1, if_neg h2]

end Workspace.ProofLemmas.Thm183EdgeCount
