import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.Statements.S14.Thm_14_1

/-!
# From a double diamond to a maximal cube

The proof of 14.3 (printed p. 91) opens:

> *"Suppose for a contradiction that `G` contains a double diamond; then it contains a cube, and so
> there is a maximal cube `(A, B, C, D)` in `G`, forming `K`.  Let `F` be the set of all minor
> vertices in `V(G) \ V(K)`, and `Y` the set of all major ones."*

All three moves are here.

* `isCube_of_doubleDiamond` — the cube inside a double diamond is
  `A = {a₁,a₂}`, `B = {b₁,b₂}`, `C = {a₃,a₄}`, `D = {b₃,b₄}`.  The split is forced: a *square*
  `a₁-b₁-b₂-a₂-a₁` has its two `A`-vertices **adjacent** and its two `B`-vertices adjacent, while
  an *antisquare* has both pairs non-adjacent; and the only non-adjacent pairs of a double
  diamond are `a₃a₄` and `b₃b₄`.  Note the antisquare has to be read as `a₃-b₄-b₃-a₄-a₃`, with the
  two `D`-vertices **crossed**, since `a₃b₃` and `a₄b₄` are edges of `G` and hence non-edges of
  `Gᶜ`.
* `exists_maximalCube` — maximise `(A ∪ B ∪ C ∪ D).ncard`.  That measure works because the four
  sets of a cube are pairwise disjoint: if `(A,B,C,D) ⊆ (A',B',C',D')` componentwise and, say,
  `A ≠ A'`, a vertex of `A' \ A` lies in no one of `B, C, D` either (it would then lie in `B'`,
  `C'` or `D'`, which are disjoint from `A'`), so the union grows strictly.
* `minor_or_major` — the dichotomy of 14.1, repackaged as `MinorForCube ∨ MajorForCube`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CubeExtraction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-! ### Four-vertex holes and two-element pairs -/

theorem nodup_four {x y z w : V} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : x ≠ w)
    (h4 : y ≠ z) (h5 : y ≠ w) (h6 : z ≠ w) : ([x, y, z, w] : List V).Nodup := by
  simp [h1, h2, h3, h4, h5, h6]

theorem isHoleList_four {G : SimpleGraph V} {x y z w : V}
    (hnd : ([x, y, z, w] : List V).Nodup)
    (e1 : G.Adj x y) (e2 : G.Adj y z) (e3 : G.Adj z w) (e4 : G.Adj w x)
    (n1 : ¬ G.Adj x z) (n2 : ¬ G.Adj y w) : IsHoleList G [x, y, z, w] := by
  have n1' : ¬ G.Adj z x := fun h => n1 h.symm
  have n2' : ¬ G.Adj w y := fun h => n2 h.symm
  refine ⟨by simp, hnd, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp [e1, e2, e3, e4, e1.symm, e2.symm, e3.symm, e4.symm, n1, n2, n1', n2']

theorem disjoint_pair {x y z w : V} (h1 : x ≠ z) (h2 : x ≠ w) (h3 : y ≠ z) (h4 : y ≠ w) :
    Disjoint ({x, y} : Set V) ({z, w} : Set V) := by
  rw [Set.disjoint_left]
  intro s hs ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

theorem complete_pair {G : SimpleGraph V} {x y z w : V}
    (h1 : G.Adj x z) (h2 : G.Adj x w) (h3 : G.Adj y z) (h4 : G.Adj y w) :
    Complete G ({x, y} : Set V) ({z, w} : Set V) := by
  intro s hs t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> rw [hs, ht] <;> assumption

theorem anticomplete_pair {G : SimpleGraph V} {x y z w : V}
    (h1 : ¬ G.Adj x z) (h2 : ¬ G.Adj x w) (h3 : ¬ G.Adj y z) (h4 : ¬ G.Adj y w) :
    Anticomplete G ({x, y} : Set V) ({z, w} : Set V) := by
  intro s hs t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> rw [hs, ht] <;> assumption

/-- A two-element pair is square-connected to another as soon as the two squares obtained by
swapping the roles both exist. -/
theorem squareConnected_pair {G : SimpleGraph V} {a₁ a₂ b₁ b₂ : V}
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (h₁ : IsSquare G ({a₁, a₂} : Set V) ({b₁, b₂} : Set V) a₁ b₁ b₂ a₂)
    (h₂ : IsSquare G ({a₁, a₂} : Set V) ({b₁, b₂} : Set V) a₂ b₂ b₁ a₁) :
    SquareConnected G ({a₁, a₂} : Set V) ({b₁, b₂} : Set V) := by
  have hsplit : ∀ (p q : V) (X Y : Set V), X ∪ Y = ({p, q} : Set V) → Disjoint X Y →
      X.Nonempty → Y.Nonempty → (p ∈ X ∧ q ∈ Y) ∨ (q ∈ X ∧ p ∈ Y) := by
    intro p q X Y hXY hd hX hY
    obtain ⟨s, hs⟩ := hX
    obtain ⟨t, ht⟩ := hY
    have hsm : s ∈ ({p, q} : Set V) := by rw [← hXY]; exact Or.inl hs
    have htm : t ∈ ({p, q} : Set V) := by rw [← hXY]; exact Or.inr ht
    have hst : s ≠ t := fun he => (Set.disjoint_left.mp hd hs) (by rw [he]; exact ht)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsm htm
    rcases hsm with hsm | hsm <;> rcases htm with htm | htm
    · exact absurd (hsm.trans htm.symm) hst
    · exact Or.inl ⟨by rw [← hsm]; exact hs, by rw [← htm]; exact ht⟩
    · exact Or.inr ⟨by rw [← hsm]; exact hs, by rw [← htm]; exact ht⟩
    · exact absurd (hsm.trans htm.symm) hst
  refine ⟨⟨⟨a₁, by simp, a₂, by simp, ha⟩, ⟨b₁, by simp, b₂, by simp, hb⟩⟩, ?_, ?_⟩
  · intro X Y hXY hd hX hY
    rcases hsplit a₁ a₂ X Y hXY hd hX hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a₁, b₁, b₂, a₂, h₁, h1, h2⟩
    · exact ⟨a₂, b₂, b₁, a₁, h₂, h1, h2⟩
  · intro X Y hXY hd hX hY
    rcases hsplit b₁ b₂ X Y hXY hd hX hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a₁, b₁, b₂, a₂, h₁, h1, h2⟩
    · exact ⟨a₂, b₂, b₁, a₁, h₂, h1, h2⟩

/-! ### The cube inside a double diamond -/

theorem isCube_of_doubleDiamond {G : SimpleGraph V} {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V}
    (h : IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄) :
    IsCube G ({a₁, a₂} : Set V) ({b₁, b₂} : Set V) ({a₃, a₄} : Set V) ({b₃, b₄} : Set V) := by
  obtain ⟨hnd, ⟨e12, e13, e14, e23, e24, n34⟩, ⟨f12, f13, f14, f23, f24, m34⟩,
    ⟨g1, g2, g3, g4⟩, ⟨k12, k13, k14, k21, k23, k24, k31, k32, k34, k41, k42, k43⟩⟩ := h
  have p12 : a₁ ≠ a₂ := by rintro rfl; simp at hnd
  have p13 : a₁ ≠ a₃ := by rintro rfl; simp at hnd
  have p14 : a₁ ≠ a₄ := by rintro rfl; simp at hnd
  have p15 : a₁ ≠ b₁ := by rintro rfl; simp at hnd
  have p16 : a₁ ≠ b₂ := by rintro rfl; simp at hnd
  have p17 : a₁ ≠ b₃ := by rintro rfl; simp at hnd
  have p18 : a₁ ≠ b₄ := by rintro rfl; simp at hnd
  have p23 : a₂ ≠ a₃ := by rintro rfl; simp at hnd
  have p24 : a₂ ≠ a₄ := by rintro rfl; simp at hnd
  have p25 : a₂ ≠ b₁ := by rintro rfl; simp at hnd
  have p26 : a₂ ≠ b₂ := by rintro rfl; simp at hnd
  have p27 : a₂ ≠ b₃ := by rintro rfl; simp at hnd
  have p28 : a₂ ≠ b₄ := by rintro rfl; simp at hnd
  have p34 : a₃ ≠ a₄ := by rintro rfl; simp at hnd
  have p35 : a₃ ≠ b₁ := by rintro rfl; simp at hnd
  have p36 : a₃ ≠ b₂ := by rintro rfl; simp at hnd
  have p37 : a₃ ≠ b₃ := by rintro rfl; simp at hnd
  have p38 : a₃ ≠ b₄ := by rintro rfl; simp at hnd
  have p45 : a₄ ≠ b₁ := by rintro rfl; simp at hnd
  have p46 : a₄ ≠ b₂ := by rintro rfl; simp at hnd
  have p47 : a₄ ≠ b₃ := by rintro rfl; simp at hnd
  have p48 : a₄ ≠ b₄ := by rintro rfl; simp at hnd
  have p56 : b₁ ≠ b₂ := by rintro rfl; simp at hnd
  have p57 : b₁ ≠ b₃ := by rintro rfl; simp at hnd
  have p58 : b₁ ≠ b₄ := by rintro rfl; simp at hnd
  have p67 : b₂ ≠ b₃ := by rintro rfl; simp at hnd
  have p68 : b₂ ≠ b₄ := by rintro rfl; simp at hnd
  have p78 : b₃ ≠ b₄ := by rintro rfl; simp at hnd
  refine ⟨⟨⟨disjoint_pair p15 p16 p25 p26, disjoint_pair p13 p14 p23 p24,
      disjoint_pair p17 p18 p27 p28, disjoint_pair p35.symm p45.symm p36.symm p46.symm,
      disjoint_pair p57 p58 p67 p68, disjoint_pair p37 p38 p47 p48⟩,
    ⟨a₁, by simp⟩, ⟨b₁, by simp⟩, ⟨a₃, by simp⟩, ⟨b₃, by simp⟩⟩,
    ⟨complete_pair e13 e14 e23 e24, complete_pair f13 f14 f23 f24,
      anticomplete_pair k13 k14 k23 k24,
      anticomplete_pair (fun hx => k31 hx.symm) (fun hx => k41 hx.symm)
        (fun hx => k32 hx.symm) (fun hx => k42 hx.symm)⟩, ?_, ?_⟩
  · -- `(A,B)` is square-connected, via the squares `a₁-b₁-b₂-a₂` and `a₂-b₂-b₁-a₁`
    refine squareConnected_pair p12 p56 ⟨?_, by simp, by simp, by simp, by simp⟩
      ⟨?_, by simp, by simp, by simp, by simp⟩
    · exact isHoleList_four (nodup_four p15 p16 p12 p56 p25.symm p26.symm)
        g1 f12 g2.symm e12.symm k12 (fun hx => k21 hx.symm)
    · exact isHoleList_four (nodup_four p26 p25 p12.symm p56.symm p16.symm p15.symm)
        g2 f12.symm g1.symm e12 k21 (fun hx => k12 hx.symm)
  · -- `(C,D)` is antisquare-connected, via the *crossed* antisquares `a₃-b₄-b₃-a₄` and
    -- `a₄-b₃-b₄-a₃`
    show SquareConnected Gᶜ ({a₃, a₄} : Set V) ({b₃, b₄} : Set V)
    rw [Set.pair_comm b₃ b₄]
    refine squareConnected_pair p34 p78.symm ⟨?_, by simp, by simp, by simp, by simp⟩
      ⟨?_, by simp, by simp, by simp, by simp⟩
    · exact isHoleList_four (nodup_four p38 p37 p34 p78.symm p48.symm p47.symm)
        ⟨p38, k34⟩ ⟨p78.symm, fun hx => m34 hx.symm⟩ ⟨p47.symm, fun hx => k43 hx.symm⟩
        ⟨p34.symm, fun hx => n34 hx.symm⟩
        (fun hx => hx.2 g3) (fun hx => hx.2 g4.symm)
    · exact isHoleList_four (nodup_four p47 p48 p34.symm p78 p37.symm p38.symm)
        ⟨p47, k43⟩ ⟨p78, m34⟩ ⟨p38.symm, fun hx => k34 hx.symm⟩ ⟨p34, n34⟩
        (fun hx => hx.2 g4) (fun hx => hx.2 g3.symm)

/-! ### Maximal cubes -/

theorem exists_maximalCube [Fintype V] (G : SimpleGraph V)
    (hex : ∃ A B C D : Set V, IsCube G A B C D) :
    ∃ A B C D : Set V, MaximalCube G A B C D := by
  classical
  obtain ⟨⟨A, B, C, D⟩, hcube, hmax⟩ :=
    ExtremalChoice.exists_max_nat
      (fun t : Set V × Set V × Set V × Set V => IsCube G t.1 t.2.1 t.2.2.1 t.2.2.2)
      (fun t => (t.1 ∪ t.2.1 ∪ t.2.2.1 ∪ t.2.2.2).ncard) (Fintype.card V)
      (fun t _ => ExtremalChoice.ncard_le_card _)
      (by obtain ⟨A, B, C, D, h⟩ := hex; exact ⟨⟨A, B, C, D⟩, h⟩)
  simp only at hcube hmax
  refine ⟨A, B, C, D, hcube, ?_⟩
  intro A' B' C' D' hcube' hA hB hC hD
  have hle := hmax ⟨A', B', C', D'⟩ hcube'
  simp only at hle
  have hsub : A ∪ B ∪ C ∪ D ⊆ A' ∪ B' ∪ C' ∪ D' := by
    rintro x (((h | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (hA h)))
    · exact Or.inl (Or.inl (Or.inr (hB h)))
    · exact Or.inl (Or.inr (hC h))
    · exact Or.inr (hD h)
  have hUeq : A ∪ B ∪ C ∪ D = A' ∪ B' ∪ C' ∪ D' :=
    Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  obtain ⟨⟨dA'B', dA'C', dA'D', dB'C', dB'D', dC'D'⟩, -⟩ := hcube'.1
  refine ⟨Set.Subset.antisymm hA ?_, Set.Subset.antisymm hB ?_, Set.Subset.antisymm hC ?_,
    Set.Subset.antisymm hD ?_⟩
  · intro x hx
    have hxU : x ∈ A ∪ B ∪ C ∪ D := by rw [hUeq]; exact Or.inl (Or.inl (Or.inl hx))
    rcases hxU with ((h | h) | h) | h
    · exact h
    · exact absurd (hB h) (Set.disjoint_left.mp dA'B' hx)
    · exact absurd (hC h) (Set.disjoint_left.mp dA'C' hx)
    · exact absurd (hD h) (Set.disjoint_left.mp dA'D' hx)
  · intro x hx
    have hxU : x ∈ A ∪ B ∪ C ∪ D := by rw [hUeq]; exact Or.inl (Or.inl (Or.inr hx))
    rcases hxU with ((h | h) | h) | h
    · exact absurd (hA h) (Set.disjoint_left.mp dA'B'.symm hx)
    · exact h
    · exact absurd (hC h) (Set.disjoint_left.mp dB'C' hx)
    · exact absurd (hD h) (Set.disjoint_left.mp dB'D' hx)
  · intro x hx
    have hxU : x ∈ A ∪ B ∪ C ∪ D := by rw [hUeq]; exact Or.inl (Or.inr hx)
    rcases hxU with ((h | h) | h) | h
    · exact absurd (hA h) (Set.disjoint_left.mp dA'C'.symm hx)
    · exact absurd (hB h) (Set.disjoint_left.mp dB'C'.symm hx)
    · exact h
    · exact absurd (hD h) (Set.disjoint_left.mp dC'D' hx)
  · intro x hx
    have hxU : x ∈ A ∪ B ∪ C ∪ D := by rw [hUeq]; exact Or.inr hx
    rcases hxU with ((h | h) | h) | h
    · exact absurd (hA h) (Set.disjoint_left.mp dA'D'.symm hx)
    · exact absurd (hB h) (Set.disjoint_left.mp dB'D'.symm hx)
    · exact absurd (hC h) (Set.disjoint_left.mp dC'D'.symm hx)
    · exact h

/-! ### The minor / major dichotomy -/

/-- PAPER (printed p. 88): *"Say a vertex `v ∈ V(G) \ V(K)` is minor if the first case of 14.1
applies to it, and major if the second case applies."* -/
theorem minor_or_major [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : InF5 G)
    {A B C D : Set V} (hcube : MaximalCube G A B C D) {v : V} (hv : v ∉ A ∪ B ∪ C ∪ D) :
    MinorForCube G A B C D v ∨ MajorForCube G A B C D v := by
  rcases _root_.Workspace.Statements.S14.SPGT.thm_14_1 G hG A B C D hcube v hv
    (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) rfl with h | h
  · exact Or.inl ⟨hv, h.1, h.2⟩
  · exact Or.inr ⟨hv, h.1, h.2⟩

end Workspace.ProofLemmas.CubeExtraction
