import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.KnotFromTwist

/-!
# Small readings of the knot definition used by the 9.5 gap lemmas

The four bullets of `IsKnot` are stated with the ends of the four (anti)paths in one fixed
order.  Every application in 9.5 needs them in some other order, or "the other way round"
(*"the only vertex of `P₁` adjacent to `x₁` is `a₁`"*).  The lemmas here are those readings,
together with the two list facts (`reverse` does not change a vertex set, a strip has a rung)
that the reversals in `KnotFromTwist.exists_knot_of_twist` force on every caller.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95GapBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reversal does not change the vertex set of a list. -/
theorem mem_iff_of_rev {l l' : List V} (h : l' = l ∨ l' = l.reverse) (v : V) :
    v ∈ l' ↔ v ∈ l := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact List.mem_reverse

/-- A strip has at least one rung. -/
theorem exists_rung {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (h : IsStrip G R) : ∃ p : List V, IsSRung G R p := by
  obtain ⟨A, C, B⟩ := R
  obtain ⟨a, ha⟩ := h.2.2.2.1
  obtain ⟨p, hp, -⟩ := h.2.2.2.2.2 a (Set.mem_union_left _ (Set.mem_union_left _ ha))
  exact ⟨p, hp⟩

/-- Every vertex of a strip lies on some rung. -/
theorem exists_rung_through {G : SimpleGraph V} {Sx : Set V × Set V × Set V}
    (h : IsStrip G Sx) {v : V} (hv : v ∈ stripVertices Sx) :
    ∃ p : List V, IsSRung G Sx p ∧ v ∈ p := by
  obtain ⟨A, C, B⟩ := Sx
  exact h.2.2.2.2.2 v hv

/-- The two ends of a path are determined by the list. -/
theorem end_eq_of_same_path {G : SimpleGraph V} {p : List V} {a b c d : V}
    (h : IsPathFrom G p a b) (h' : IsPathFrom G p c d) : a = c ∧ b = d :=
  ⟨Option.some.inj (h.2.1.symm.trans h'.2.1), Option.some.inj (h.2.2.symm.trans h'.2.2)⟩

/-- Reading the third bullet of `IsKnot` "the other way round": the only vertex of `P`
adjacent to `c` is the end `a`. -/
theorem edge_end {G : SimpleGraph V} {P : List V} {a a' c c' : V} (hcc : c ≠ c')
    (E : ∀ u ∈ P, ∀ w ∈ ({c, c'} : Set V),
      (G.Adj u w ↔ ((u = a ∧ w = c) ∨ (u = a' ∧ w = c')))) :
    ∀ u ∈ P, u ≠ a → ¬ G.Adj u c := by
  intro u hu hua hadj
  rcases (E u hu c (Set.mem_insert _ _)).mp hadj with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hua h1
  · exact hcc h2

/-- The third bullet of `IsKnot` with the two ends of the antipath exchanged. -/
theorem swap_E {G : SimpleGraph V} {P : List V} {a a' c c' : V}
    (E : ∀ u ∈ P, ∀ w ∈ ({c, c'} : Set V),
      (G.Adj u w ↔ ((u = a ∧ w = c) ∨ (u = a' ∧ w = c')))) :
    ∀ u ∈ P, ∀ w ∈ ({c', c} : Set V),
      (G.Adj u w ↔ ((u = a' ∧ w = c') ∨ (u = a ∧ w = c))) := by
  intro u hu w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have h := E u hu w (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  tauto

/-- The fourth bullet of `IsKnot` with the two ends of the path exchanged. -/
theorem swap_N {G : SimpleGraph V} {Q : List V} {a a' x x' : V}
    (N : ∀ u ∈ Q, ∀ w ∈ ({a, a'} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = x') ∨ (w = a' ∧ u = x)))) :
    ∀ u ∈ Q, ∀ w ∈ ({a', a} : Set V),
      (¬ G.Adj u w ↔ ((w = a' ∧ u = x) ∨ (w = a ∧ u = x'))) := by
  intro u hu w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have h := N u hu w (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  tauto

/-- Reading the fourth bullet of `IsKnot`: the end `x` of the antipath is adjacent to the
end `a` of the path. -/
theorem adj_end {G : SimpleGraph V} {Q : List V} {a a' x x' : V}
    (haa : a ≠ a') (hxx : x ≠ x') (hxQ : x ∈ Q)
    (N : ∀ u ∈ Q, ∀ w ∈ ({a, a'} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = x') ∨ (w = a' ∧ u = x)))) :
    G.Adj x a := by
  by_contra h
  rcases (N x hxQ a (Set.mem_insert _ _)).mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact hxx h2
  · exact haa h1

/-- Reading the fourth bullet of `IsKnot`: every vertex of the antipath is adjacent to at
least one of the two ends of the path. -/
theorem cover_ends {G : SimpleGraph V} {Q : List V} {a a' x x' : V}
    (haa : a ≠ a') (hxx : x ≠ x')
    (N : ∀ u ∈ Q, ∀ w ∈ ({a, a'} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = x') ∨ (w = a' ∧ u = x)))) :
    ∀ u ∈ Q, G.Adj u a ∨ G.Adj u a' := by
  intro u hu
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  rcases (N u hu a (Set.mem_insert _ _)).mp h1 with ⟨-, e1⟩ | ⟨e1, -⟩
  · rcases (N u hu a' (Set.mem_insert_of_mem _ rfl)).mp h2 with ⟨e2, -⟩ | ⟨-, e2⟩
    · exact haa e2.symm
    · exact hxx (e2.symm.trans e1)
  · exact haa e1

/-- The two ends of a rung lie in the two end sets of the strip. -/
theorem srung_ends {G : SimpleGraph V} {Sx : Set V × Set V × Set V} {p : List V} {a b : V}
    (h : IsSRung G Sx p) (hab : IsPathFrom G p a b) : a ∈ Sx.1 ∧ b ∈ Sx.2.2 := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨a', b', hpath, haA, hbB, -, -, -⟩ := h
  obtain ⟨rfl, rfl⟩ := end_eq_of_same_path hpath hab
  exact ⟨haA, hbB⟩

/-- **PAPER (definition of parallel, p. 50).** A strip end is complete to two of the three
sets of an antistrip it is parallel (or co-parallel) to, and anticomplete to the third.  So
every vertex of the antistrip is adjacent to at least one of the two strip ends. -/
theorem cover_strip {G : SimpleGraph V} {Sx Tx : Set V × Set V × Set V} {a b : V}
    (hpar : ParallelStripAntistrip G Sx Tx ∨ CoParallel G Sx Tx)
    (haA : a ∈ Sx.1) (hbB : b ∈ Sx.2.2) :
    ∀ w ∈ stripVertices Tx, G.Adj a w ∨ G.Adj b w := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  simp only at haA hbB
  intro w hw
  have hw' : w ∈ X ∨ w ∈ Y ∨ w ∈ Z := by
    rcases hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hpar with ⟨⟨hA, hB⟩, -⟩ | hco
  · rcases hw' with h | h | h
    · exact Or.inl (hA a haA w (Or.inl h))
    · exact Or.inr (hB b hbB w (Or.inl h))
    · exact Or.inl (hA a haA w (Or.inr h))
  · obtain ⟨⟨hA, hB⟩, -⟩ := hco
    rcases hw' with h | h | h
    · exact Or.inr (hB b hbB w (Or.inl h))
    · exact Or.inl (hA a haA w (Or.inl h))
    · exact Or.inl (hA a haA w (Or.inr h))

/-- **PAPER (definition of parallel, p. 50).** On any antirung of an antistrip parallel or
co-parallel to a strip, one end is adjacent to the strip end `a` and not to `b`, and the other
end the other way round.  These two vertices are what tells the two ends of `F` apart. -/
theorem anchor {G : SimpleGraph V} {Sx Tx : Set V × Set V × Set V} {q : List V} {a b : V}
    (hpar : ParallelStripAntistrip G Sx Tx ∨ CoParallel G Sx Tx)
    (haA : a ∈ Sx.1) (hbB : b ∈ Sx.2.2) (hq : IsSRung Gᶜ Tx q) :
    ∃ z ∈ q, ∃ z' ∈ q, G.Adj a z ∧ ¬ G.Adj b z ∧ G.Adj b z' ∧ ¬ G.Adj a z' := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  simp only at haA hbB
  obtain ⟨x, y, hpath, hxX, hyY, -, -, -⟩ := hq
  obtain ⟨hxq, hyq⟩ := PathBasics.isPathFrom_ends_mem hpath
  rcases hpar with ⟨⟨hA, hB⟩, hAX, hAY⟩ | hco
  · exact ⟨x, hxq, y, hyq, hA a haA x (Or.inl hxX),
      fun h => hAX x hxX b (Or.inl hbB) h.symm,
      hB b hbB y (Or.inl hyY), fun h => hAY y hyY a (Or.inl haA) h.symm⟩
  · obtain ⟨⟨hA, hB⟩, hAX, hAY⟩ := hco
    exact ⟨y, hyq, x, hxq, hA a haA y (Or.inl hyY),
      fun h => hAX y hyY b (Or.inl hbB) h.symm,
      hB b hbB x (Or.inl hxX), fun h => hAY x hxX a (Or.inl haA) h.symm⟩

/-- **PAPER (definition of parallel, p. 50), sharpened along a rung.**  On any antirung of an
antistrip parallel or co-parallel to a strip, there is a vertex adjacent to the rung end `a`
and to no other vertex of the rung, and one adjacent to `b` and to no other vertex of the
rung.  (For a parallel pair these are the two ends of the antirung; the paper writes them
`xⱼ` and `yⱼ`.) -/
theorem rung_anchor {G : SimpleGraph V} {Sx Tx : Set V × Set V × Set V} {p q : List V}
    {a b : V} (hpar : ParallelStripAntistrip G Sx Tx ∨ CoParallel G Sx Tx)
    (hp : IsSRung G Sx p) (hpab : IsPathFrom G p a b) (hq : IsSRung Gᶜ Tx q) :
    ∃ z ∈ q, ∃ z' ∈ q,
      (G.Adj a z ∧ ∀ v ∈ p, v ≠ a → ¬ G.Adj v z) ∧
      (G.Adj b z' ∧ ∀ v ∈ p, v ≠ b → ¬ G.Adj v z') := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  obtain ⟨a2, b2, hpath2, haA0, hbB0, htri0⟩ := KnotFromTwist.isSRung_trichotomy hp
  obtain ⟨f1, f2⟩ := end_eq_of_same_path hpath2 hpab
  have haA : a ∈ A := f1 ▸ haA0
  have hbB : b ∈ B := f2 ▸ hbB0
  obtain ⟨x, y, hqpath, hxX, hyY, -, -, -⟩ := hq
  obtain ⟨hxq, hyq⟩ := PathBasics.isPathFrom_ends_mem hqpath
  have htri' : ∀ v ∈ p, v = a ∨ v = b ∨ v ∈ C := by
    intro v hv
    have h := htri0 v hv
    rw [f1, f2] at h
    exact h
  rcases hpar with ⟨⟨hA, hB⟩, hAX, hAY⟩ | hco
  · refine ⟨x, hxq, y, hyq, ⟨hA a haA x (Or.inl hxX), ?_⟩,
      ⟨hB b hbB y (Or.inl hyY), ?_⟩⟩
    · intro v hv hva hadj
      rcases htri' v hv with h | h | h
      · exact hva h
      · exact hAX x hxX v (Or.inl (h ▸ hbB)) hadj.symm
      · exact hAX x hxX v (Or.inr h) hadj.symm
    · intro v hv hvb hadj
      rcases htri' v hv with h | h | h
      · exact hAY y hyY v (Or.inl (h ▸ haA)) hadj.symm
      · exact hvb h
      · exact hAY y hyY v (Or.inr h) hadj.symm
  · obtain ⟨⟨hA, hB⟩, hAX, hAY⟩ := hco
    refine ⟨y, hyq, x, hxq, ⟨hA a haA y (Or.inl hyY), ?_⟩,
      ⟨hB b hbB x (Or.inl hxX), ?_⟩⟩
    · intro v hv hva hadj
      rcases htri' v hv with h | h | h
      · exact hva h
      · exact hAX y hyY v (Or.inl (h ▸ hbB)) hadj.symm
      · exact hAX y hyY v (Or.inr h) hadj.symm
    · intro v hv hvb hadj
      rcases htri' v hv with h | h | h
      · exact hAY x hxX v (Or.inl (h ▸ haA)) hadj.symm
      · exact hvb h
      · exact hAY x hxX v (Or.inr h) hadj.symm

/-- The two end sets of a strip are disjoint. -/
theorem strip_ends_disjoint {G : SimpleGraph V} {Sx : Set V × Set V × Set V}
    (h : IsStrip G Sx) : Disjoint Sx.1 Sx.2.2 := by
  obtain ⟨A, C, B⟩ := Sx
  exact h.1

/-- **PAPER (9.5(1), fourth and fifth consequences, p. 52).**  For a strip and an antistrip
that are parallel or co-parallel, the two ends of a rung are both adjacent to every vertex of
the middle set of the antistrip, and exactly one of them is adjacent to each vertex of the two
end sets. -/
theorem end_pattern {G : SimpleGraph V} {Sx Tx : Set V × Set V × Set V} {a b : V}
    (hpar : ParallelStripAntistrip G Sx Tx ∨ CoParallel G Sx Tx)
    (haA : a ∈ Sx.1) (hbB : b ∈ Sx.2.2) :
    (∀ z ∈ Tx.2.1, G.Adj a z ∧ G.Adj b z) ∧
    (∀ z ∈ Tx.1 ∪ Tx.2.2, ¬ (G.Adj a z ∧ G.Adj b z)) := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  simp only at haA hbB ⊢
  rcases hpar with ⟨⟨hA, hB⟩, hAX, hAY⟩ | hco
  · refine ⟨fun z hz => ⟨hA a haA z (Or.inr hz), hB b hbB z (Or.inr hz)⟩, ?_⟩
    rintro z (hz | hz) ⟨h1, h2⟩
    · exact hAX z hz b (Or.inl hbB) h2.symm
    · exact hAY z hz a (Or.inl haA) h1.symm
  · obtain ⟨⟨hA, hB⟩, hAX, hAY⟩ := hco
    refine ⟨fun z hz => ⟨hA a haA z (Or.inr hz), hB b hbB z (Or.inr hz)⟩, ?_⟩
    rintro z (hz | hz) ⟨h1, h2⟩
    · exact hAY z hz a (Or.inl haA) h1.symm
    · exact hAX z hz b (Or.inl hbB) h2.symm

end Workspace.ProofLemmas.Thm95GapBasics
