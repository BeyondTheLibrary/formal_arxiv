import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.ProofLemmas.PrismBasics

/-!
# A reflection of a triangle carries an antihole of length 6

The printed proof of **24.4** (Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph
Theorem*, printed p. 144) finishes its second case with

> *"… and it contains no reflection of the triangle since there is no antihole of length 6."*

The parenthetical justification is exactly this module: a reflection of a triangle induces a
prism on six vertices (as §17's definition itself remarks — *"Hence these six vertices induce a
prism"*), and the complement of a prism on six vertices is a six-cycle.

Concretely, if `{b₁,b₂,b₃}` is a reflection of `{a₁,a₂,a₃}` then in `Gᶜ`

* `aᵢ` is adjacent to `bⱼ` exactly when `i ≠ j` (the matched pairs `aᵢbᵢ` are the only `G`-edges
  between the two triangles);
* `aᵢ` is non-adjacent to `aⱼ` and `bᵢ` non-adjacent to `bⱼ` (both triples are `G`-triangles),

so `a₁-b₂-a₃-b₁-a₂-b₃-a₁` is a hole of `Gᶜ`, i.e. an antihole of `G`, and it has six vertices.

This does not correspond to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.ReflectionAntihole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT

/-- A three-element set written as a literal triple has pairwise distinct entries. -/
private theorem triple_distinct {V : Type*} {a b c : V}
    (h : ({a, b, c} : Set V).ncard = 3) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have key : ∀ x y : V, ({x, y} : Set V).ncard ≤ 2 := by
    intro x y
    calc ({x, y} : Set V).ncard ≤ ({y} : Set V).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have he : ({a, a, c} : Set V) = {a, c} := by ext x; simp
    rw [he] at h
    have := key a c
    omega
  · have he : ({a, b, a} : Set V) = {a, b} := by ext x; simp; tauto
    rw [he] at h
    have := key a b
    omega
  · have he : ({a, b, b} : Set V) = {a, b} := by ext x; simp
    rw [he] at h
    have := key a b
    omega

/-- **A reflection of a triangle is an antihole of length 6.**

If `{b₁,b₂,b₃}` is a reflection of the triangle `{a₁,a₂,a₃}` in `G`, then the six vertices,
listed in the cyclic order `a₁, b₂, a₃, b₁, a₂, b₃`, form a hole of `Gᶜ`. -/
theorem isAntiholeList_of_reflection {V : Type*} {G : SimpleGraph V}
    {a₁ a₂ a₃ b₁ b₂ b₃ : V}
    (h : Workspace.Types.TriangleCatching.SPGT.IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃) :
    Workspace.Types.Core.SPGT.IsAntiholeList G [a₁, b₂, a₃, b₁, a₂, b₃] := by
  obtain ⟨hTa, hTb, hdisj, hcross⟩ := h
  obtain ⟨ha12, ha13, ha23⟩ := triple_distinct hTa.1
  obtain ⟨hb12, hb13, hb23⟩ := triple_distinct hTb.1
  -- the two triangles are `G`-triangles
  have hGa12 : G.Adj a₁ a₂ := hTa.2 a₁ (by simp) a₂ (by simp) ha12
  have hGa13 : G.Adj a₁ a₃ := hTa.2 a₁ (by simp) a₃ (by simp) ha13
  have hGa23 : G.Adj a₂ a₃ := hTa.2 a₂ (by simp) a₃ (by simp) ha23
  have hGb12 : G.Adj b₁ b₂ := hTb.2 b₁ (by simp) b₂ (by simp) hb12
  have hGb13 : G.Adj b₁ b₃ := hTb.2 b₁ (by simp) b₃ (by simp) hb13
  have hGb23 : G.Adj b₂ b₃ := hTb.2 b₂ (by simp) b₃ (by simp) hb23
  -- the two triangles are disjoint
  have hab : ∀ x ∈ ({a₁, a₂, a₃} : Set V), ∀ y ∈ ({b₁, b₂, b₃} : Set V), x ≠ y := by
    intro x hx y hy hxy
    exact (Set.disjoint_left.mp hdisj hx) (hxy ▸ hy)
  have h1b1 : a₁ ≠ b₁ := hab _ (by simp) _ (by simp)
  have h1b2 : a₁ ≠ b₂ := hab _ (by simp) _ (by simp)
  have h1b3 : a₁ ≠ b₃ := hab _ (by simp) _ (by simp)
  have h2b1 : a₂ ≠ b₁ := hab _ (by simp) _ (by simp)
  have h2b2 : a₂ ≠ b₂ := hab _ (by simp) _ (by simp)
  have h2b3 : a₂ ≠ b₃ := hab _ (by simp) _ (by simp)
  have h3b1 : a₃ ≠ b₁ := hab _ (by simp) _ (by simp)
  have h3b2 : a₃ ≠ b₂ := hab _ (by simp) _ (by simp)
  have h3b3 : a₃ ≠ b₃ := hab _ (by simp) _ (by simp)
  -- the matched pairs are edges
  have hGab11 : G.Adj a₁ b₁ := (hcross a₁ (by simp) b₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
  have hGab22 : G.Adj a₂ b₂ := (hcross a₂ (by simp) b₂ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hGab33 : G.Adj a₃ b₃ := (hcross a₃ (by simp) b₃ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  -- and the mismatched pairs are not
  have hn12 : ¬ G.Adj a₁ b₂ := by
    intro hc
    rcases (hcross a₁ (by simp) b₂ (by simp)).mp hc with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact hb12 e.symm
    · exact ha12 e
    · exact ha13 e
  have hn13 : ¬ G.Adj a₁ b₃ := by
    intro hc
    rcases (hcross a₁ (by simp) b₃ (by simp)).mp hc with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact hb13 e.symm
    · exact ha12 e
    · exact ha13 e
  have hn21 : ¬ G.Adj a₂ b₁ := by
    intro hc
    rcases (hcross a₂ (by simp) b₁ (by simp)).mp hc with ⟨e, _⟩ | ⟨_, e⟩ | ⟨e, _⟩
    · exact ha12 e.symm
    · exact hb12 e
    · exact ha23 e
  have hn23 : ¬ G.Adj a₂ b₃ := by
    intro hc
    rcases (hcross a₂ (by simp) b₃ (by simp)).mp hc with ⟨e, _⟩ | ⟨_, e⟩ | ⟨e, _⟩
    · exact ha12 e.symm
    · exact hb23 e.symm
    · exact ha23 e
  have hn31 : ¬ G.Adj a₃ b₁ := by
    intro hc
    rcases (hcross a₃ (by simp) b₁ (by simp)).mp hc with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, e⟩
    · exact ha13 e.symm
    · exact ha23 e.symm
    · exact hb13 e
  have hn32 : ¬ G.Adj a₃ b₂ := by
    intro hc
    rcases (hcross a₃ (by simp) b₂ (by simp)).mp hc with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, e⟩
    · exact ha13 e.symm
    · exact ha23 e.symm
    · exact hb23 e
  -- reoriented copies, so that every case of the index bash sees the right orientation
  have hGb21 : G.Adj b₂ b₁ := hGb12.symm
  have hGab22' : G.Adj b₂ a₂ := hGab22.symm
  have hGa32 : G.Adj a₃ a₂ := hGa23.symm
  have hn12' : ¬ G.Adj b₂ a₃ := fun hc => hn32 hc.symm
  have hn21' : ¬ G.Adj b₁ a₂ := fun hc => hn21 hc.symm
  have e1 : b₂ ≠ a₃ := fun e => h3b2 e.symm
  have e2 : a₃ ≠ b₁ := h3b1
  have e3 : b₁ ≠ a₂ := fun e => h2b1 e.symm
  have e4 : a₂ ≠ b₃ := h2b3
  -- the remaining inequalities the `Nodup` clause needs
  have e5 : b₂ ≠ b₁ := fun e => hb12 e.symm
  have e6 : b₂ ≠ a₂ := fun e => h2b2 e.symm
  have e7 : a₃ ≠ a₂ := fun e => ha23 e.symm
  have hnd : ([a₁, b₂, a₃, b₁, a₂, b₃] : List V).Nodup := by
    simp [h1b2, ha13, h1b1, ha12, h1b3, e1, e5, e6, hb23, e2, e7, h3b3, e3, hb13, e4]
  refine PrismBasics.isHoleList_of_le (by simp) hnd ?_
  intro i j hi hj hij
  have hi6 : i < 6 := by simpa using hi
  have hj6 : j < 6 := by simpa using hj
  have hlen : ([a₁, b₂, a₃, b₁, a₂, b₃] : List V).length = 6 := by simp
  rw [hlen]
  clear hlen hab hdisj hcross hTa hTb
  interval_cases i <;> interval_cases j <;>
    simp [h1b2, hn12, e1, hn12', e2, hn31, e3, hn21', e4, hn23, h1b3, hn13,
      hGa13, hGab11, hGa12, hGb21, hGab22', hGb23, hGa32, hGab33, hGb13]

/-- The antihole produced by `isAntiholeList_of_reflection` has length `6`. -/
theorem holeLength_reflection {V : Type*} (a₁ a₂ a₃ b₁ b₂ b₃ : V) :
    Workspace.Types.Core.SPGT.holeLength [a₁, b₂, a₃, b₁, a₂, b₃] = 6 := by
  simp [Workspace.Types.Core.SPGT.holeLength]

end Workspace.ProofLemmas.ReflectionAntihole
