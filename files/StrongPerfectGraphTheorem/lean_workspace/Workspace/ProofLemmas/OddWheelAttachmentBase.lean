import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S16.Thm_16_1

/-!
# The base case `|F| = 1` of 16.2

PAPER (16.2, printed p. 98): *"We may assume that `F` is minimal.  If `|F| = 1` then the result
follows from 16.1, so we assume `|F| ≥ 2`."*

This module is that one sentence.  It matters more than its length suggests: the whole
`|F| ≥ 2` line of the printed proof ends in a **contradiction**, so the first two bullets of
16.2 — *"there is a vertex `v ∈ F` such that `(C, Y ∪ {v})` is a wheel"* and *"there is a vertex
`v ∈ F` with at least four neighbours in `C`, and a 3-vertex path …"* — can only ever be
produced here, out of 16.1's trichotomy.

The translation of 16.1's three bullets into 16.2's three is:

* 16.1's *"`v` has only two neighbours in `C`, and they are adjacent"* is **excluded** by 16.2's
  hypothesis that two attachments are nonadjacent;
* 16.1's *"`(C, Y ∪ {v})` is a wheel"* is 16.2's first bullet;
* 16.1's 3-vertex path splits on the number of neighbours of `v` in `C`: with at least four it is
  16.2's second bullet, and with exactly three — necessarily `p₁, p₂, p₃` themselves — the path
  `p₁-v-p₃` witnesses 16.2's **third** bullet, since then `v` has no neighbour in
  `{p₄, …, pₙ}`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentBase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-- A three-vertex induced path. -/
theorem isPathList_three {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬ G.Adj x z) (hxzne : x ≠ z) :
    IsPathList G [x, y, z] := by
  have hxy' : x ≠ y := hxy.ne
  have hyz' : y ≠ z := hyz.ne
  refine ⟨by simp, by simp [hxy', hyz', hxzne], ?_⟩
  have key : ∀ i j : ℕ, i < 3 → j < 3 →
      ∀ (hi : i < [x, y, z].length) (hj : j < [x, y, z].length),
      (G.Adj ([x, y, z][i]'hi) ([x, y, z][j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi3 hj3
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
      first
        | exact iff_of_false (fun h => G.irrefl h) (by first | omega | tauto)
        | exact iff_of_true hxy (by first | omega | tauto)
        | exact iff_of_true hyz (by first | omega | tauto)
        | exact iff_of_true hxy.symm (by first | omega | tauto)
        | exact iff_of_true hyz.symm (by first | omega | tauto)
        | exact iff_of_false hxz (by first | omega | tauto)
        | exact iff_of_false (fun h => hxz h.symm) (by first | omega | tauto)
  intro i j hi hj
  exact key i j (by simpa using hi) (by simpa using hj) hi hj

/-- **The base case of 16.2.**  PAPER: *"If `|F| = 1` then the result follows from 16.1."* -/
theorem base_case [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y : Set V} (hwheel : IsWheel G C Y)
    {v : V} (hvC : v ∉ C) (hvY : v ∉ Y) (hvnc : ¬ VertexComplete G v Y)
    {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : OppositeWheelParity G C Y a b)
    (hnonadj : ∃ x ∈ C, ∃ y ∈ C, G.Adj v x ∧ G.Adj v y ∧ x ≠ y ∧ ¬ G.Adj x y)
    {F : Set V} (hvF : v ∈ F) :
    (∃ w ∈ F, IsWheel G C (Y ∪ {w})) ∨
    (∃ w ∈ F, 4 ≤ (G.neighborSet w ∩ {u : V | u ∈ C}).ncard ∧
      ∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
        (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
        VertexComplete G p₁ (Y ∪ {w}) ∧ VertexComplete G p₂ (Y ∪ {w}) ∧
        VertexComplete G p₃ (Y ∪ {w}) ∧
        ∀ u ∈ C, G.Adj w u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) ∨
    (∃ p₁ p₂ p₃ : V,
      (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
      VertexComplete G p₁ Y ∧ VertexComplete G p₂ Y ∧ VertexComplete G p₃ Y ∧
      ∃ P : List V, IsPathFrom G P p₁ p₃ ∧ (∀ x ∈ SPGT.interior P, x ∈ F) ∧
        ∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u) := by
  classical
  obtain ⟨h161a, h161b⟩ :=
    _root_.Workspace.Statements.S16.SPGT.thm_16_1 G hG C Y hwheel v hvC hvY hvnc a b hva hvb hab
  rcases h161b with hb1 | hb2 | hb3
  · -- 16.1's first bullet is excluded: two attachments are nonadjacent
    exfalso
    obtain ⟨a₁, a₂, hne, hset, hadj, -, -⟩ := hb1
    obtain ⟨x, hxC, y, hyC, hvx, hvy, hxy, hnxy⟩ := hnonadj
    have hxmem : x ∈ ({a₁, a₂} : Set V) := by rw [← hset]; exact ⟨hxC, hvx⟩
    have hymem : y ∈ ({a₁, a₂} : Set V) := by rw [← hset]; exact ⟨hyC, hvy⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem hymem
    rcases hxmem with rfl | rfl <;> rcases hymem with rfl | rfl
    · exact hxy rfl
    · exact hnxy hadj
    · exact hnxy hadj.symm
    · exact hxy rfl
  · -- 16.1's 3-vertex path: split on the number of neighbours of `v` on the rim
    obtain ⟨p₁, p₂, p₃, hpath, harc, hc₁, hc₂, hc₃, hpar⟩ := hb2
    have hvp₁ : G.Adj v p₁ := (hc₁ v (Or.inr rfl)).symm
    have hvp₂ : G.Adj v p₂ := (hc₂ v (Or.inr rfl)).symm
    have hvp₃ : G.Adj v p₃ := (hc₃ v (Or.inr rfl)).symm
    by_cases hfour : 4 ≤ (G.neighborSet v ∩ {u : V | u ∈ C}).ncard
    · exact Or.inr (Or.inl ⟨v, hvF, hfour, p₁, p₂, p₃, hpath, harc, hc₁, hc₂, hc₃, hpar⟩)
    · -- exactly three neighbours, namely `p₁, p₂, p₃`
      refine Or.inr (Or.inr ⟨p₁, p₂, p₃, harc, fun u hu => hc₁ u (Or.inl hu),
        fun u hu => hc₂ u (Or.inl hu), fun u hu => hc₃ u (Or.inl hu), [p₁, v, p₃], ?_, ?_, ?_⟩)
      · -- `p₁-v-p₃` is an induced path
        have hnd : ([p₁, p₂, p₃] : List V).Nodup := hpath.2.1
        have h13 : p₁ ≠ p₃ := by
          intro he; rw [he] at hnd; simp at hnd
        have hn13 : ¬ G.Adj p₁ p₃ := by
          have hh := PathBasics.path_ends_not_adj hpath (by simp)
          simpa using hh
        exact ⟨isPathList_three hvp₁.symm hvp₃ hn13 h13, rfl, rfl⟩
      · intro z hz
        have hzv : z = v := by simpa [SPGT.interior] using hz
        rw [hzv]; exact hvF
      · -- `v` has no neighbour on `C` outside `{p₁, p₂, p₃}`
        intro z hz u huC hu₁ hu₂ hu₃ hadjz
        have hzv : z = v := by simpa [SPGT.interior] using hz
        rw [hzv] at hadjz
        -- the three known neighbours already exhaust `N(v) ∩ C`
        have hnd : ([p₁, p₂, p₃] : List V).Nodup := hpath.2.1
        have h12 : p₁ ≠ p₂ := by intro he; rw [he] at hnd; simp at hnd
        have h13 : p₁ ≠ p₃ := by intro he; rw [he] at hnd; simp at hnd
        have h23 : p₂ ≠ p₃ := by intro he; rw [he] at hnd; simp at hnd
        have hu₁' : p₁ ≠ u := fun he => hu₁ he.symm
        have hu₂' : p₂ ≠ u := fun he => hu₂ he.symm
        have hu₃' : p₃ ≠ u := fun he => hu₃ he.symm
        have hmemC : ∀ w : V, w ∈ ([p₁, p₂, p₃] : List V) → w ∈ C := by
          intro w hw
          obtain ⟨k, hk⟩ := harc
          rcases hk with hk | hk
          · exact List.mem_rotate.mp (hk.subset hw)
          · refine List.mem_rotate.mp (hk.subset ?_)
            simp only [List.mem_cons, List.mem_singleton] at hw ⊢
            tauto
        have hp₁C : p₁ ∈ C := hmemC p₁ (by simp)
        have hp₂C : p₂ ∈ C := hmemC p₂ (by simp)
        have hp₃C : p₃ ∈ C := hmemC p₃ (by simp)
        have hsub : ({p₁, p₂, p₃, u} : Set V) ⊆ G.neighborSet v ∩ {w : V | w ∈ C} := by
          intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact ⟨hvp₁, hp₁C⟩
          · exact ⟨hvp₂, hp₂C⟩
          · exact ⟨hvp₃, hp₃C⟩
          · exact ⟨hadjz, huC⟩
        have hcard : ({p₁, p₂, p₃, u} : Set V).ncard = 4 := by
          have e1 : p₁ ∉ ({p₂, p₃, u} : Set V) := by simp [h12, h13, hu₁']
          have e2 : p₂ ∉ ({p₃, u} : Set V) := by simp [h23, hu₂']
          have e3 : p₃ ∉ ({u} : Set V) := by simp [hu₃']
          rw [Set.ncard_insert_of_notMem e1 (Set.toFinite _),
            Set.ncard_insert_of_notMem e2 (Set.toFinite _),
            Set.ncard_insert_of_notMem e3 (Set.toFinite _), Set.ncard_singleton]
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
  · exact Or.inl ⟨v, hvF, hb3⟩

end Workspace.ProofLemmas.OddWheelAttachmentBase
