import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics

/-!
# Reading a knot with *prescribed* end labels

`Knots.IsKnot` existentially quantifies the eight end labels `a₁,b₁,a₂,b₂,x₁,y₁,x₂,y₂`, as
the paper does (*"we can label the ends of each `Pᵢ` as `aᵢ, bᵢ` … such that"*).  Statements
9.2 and 9.3 instead *name* the labels, by the extra hypotheses `IsPathFrom G P₁ a₁ b₁` etc.
Since `IsPathFrom` pins an end down as the head (resp. the last entry) of the list, the two
presentations agree; this module performs that identification once and for all, so that a
proof of 9.3 can quote every clause of the definition of a knot with the labels it was given.

This is the Lean counterpart of the paper's opening sentence of the proof of 9.3,

> *"Define `aᵢ, bᵢ, xᵢ, yᵢ (i = 1, 2) as usual."*

It also records the shape of an antipath of length `1`: it is the two-element list of its
ends, which is what case (1) of the proof of 9.3 uses (*"assume `Q₁, Q₂` have length 1"*).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.KnotLabels

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

/-- The two ends of a path are determined by the list. -/
theorem ends_eq {G : SimpleGraph V} {p : List V} {u v u' v' : V}
    (h : IsPathFrom G p u v) (h' : IsPathFrom G p u' v') : u = u' ∧ v = v' := by
  refine ⟨?_, ?_⟩
  · have := h.2.1.symm.trans h'.2.1
    exact Option.some_injective _ this
  · have := h.2.2.symm.trans h'.2.2
    exact Option.some_injective _ this

/-- **The definition of a knot, read with prescribed end labels.**

PAPER (opening of the proof of 9.3): *"Define `aᵢ, bᵢ, xᵢ, yᵢ (i = 1, 2) as usual."*  -/
theorem knot_labels {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂) {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂) :
    (∀ v ∈ P₁, v ∉ P₂) ∧ (∀ v ∈ P₁, v ∉ Q₁) ∧ (∀ v ∈ P₁, v ∉ Q₂) ∧
    (∀ v ∈ P₂, v ∉ Q₁) ∧ (∀ v ∈ P₂, v ∉ Q₂) ∧ (∀ v ∈ Q₁, v ∉ Q₂) ∧
    1 ≤ pathLength P₁ ∧ 1 ≤ pathLength P₂ ∧
    1 ≤ pathLength Q₁ ∧ 1 ≤ pathLength Q₂ ∧
    Anticomplete G {v : V | v ∈ P₁} {v : V | v ∈ P₂} ∧
    Complete G {v : V | v ∈ Q₁} {v : V | v ∈ Q₂} ∧
    (∀ u ∈ P₁, ∀ w ∈ ({x₁, y₁} : Set V),
      (G.Adj u w ↔ ((u = a₁ ∧ w = x₁) ∨ (u = b₁ ∧ w = y₁)))) ∧
    (∀ u ∈ P₁, ∀ w ∈ ({x₂, y₂} : Set V),
      (G.Adj u w ↔ ((u = a₁ ∧ w = x₂) ∨ (u = b₁ ∧ w = y₂)))) ∧
    (∀ u ∈ P₂, ∀ w ∈ ({x₁, y₁} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = x₁) ∨ (u = b₂ ∧ w = y₁)))) ∧
    (∀ u ∈ P₂, ∀ w ∈ ({x₂, y₂} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = y₂) ∨ (u = b₂ ∧ w = x₂)))) ∧
    (∀ u ∈ Q₁, ∀ w ∈ ({a₁, b₁} : Set V),
      (¬ G.Adj u w ↔ ((w = a₁ ∧ u = y₁) ∨ (w = b₁ ∧ u = x₁)))) ∧
    (∀ u ∈ Q₂, ∀ w ∈ ({a₁, b₁} : Set V),
      (¬ G.Adj u w ↔ ((w = a₁ ∧ u = y₂) ∨ (w = b₁ ∧ u = x₂)))) ∧
    (∀ u ∈ Q₁, ∀ w ∈ ({a₂, b₂} : Set V),
      (¬ G.Adj u w ↔ ((w = a₂ ∧ u = y₁) ∨ (w = b₂ ∧ u = x₁)))) ∧
    (∀ u ∈ Q₂, ∀ w ∈ ({a₂, b₂} : Set V),
      (¬ G.Adj u w ↔ ((w = a₂ ∧ u = x₂) ∨ (w = b₂ ∧ u = y₂)))) := by
  obtain ⟨a₁', b₁', a₂', b₂', x₁', y₁', x₂', y₂', hP1', hP2', hQ1', hQ2', rest⟩ := hknot
  obtain ⟨rfl, rfl⟩ := ends_eq hP1' hP₁
  obtain ⟨rfl, rfl⟩ := ends_eq hP2' hP₂
  obtain ⟨rfl, rfl⟩ := ends_eq hQ1' hQ₁
  obtain ⟨rfl, rfl⟩ := ends_eq hQ2' hQ₂
  exact rest

/-- A path of length `1` is the two-element list of its ends. -/
theorem eq_pair_of_length_one {G : SimpleGraph V} {p : List V} {u v : V}
    (h : IsPathFrom G p u v) (hlen : pathLength p = 1) : p = [u, v] := by
  obtain ⟨hpath, hhead, hlast⟩ := h
  have hl : p.length = 2 := by
    have := PathBasics.path_ne_nil hpath
    unfold pathLength at hlen
    cases p with
    | nil => simp at this
    | cons a t => simp only [List.length_cons] at hlen ⊢; omega
  match p, hl with
  | [a, b], _ =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast; rfl

/-- An antipath of length `1` is the two-element list of its ends. -/
theorem anti_eq_pair_of_length_one {G : SimpleGraph V} {p : List V} {u v : V}
    (h : IsAntipathFrom G p u v) (hlen : pathLength p = 1) : p = [u, v] :=
  eq_pair_of_length_one (G := Gᶜ) h hlen

end Workspace.ProofLemmas.KnotLabels
