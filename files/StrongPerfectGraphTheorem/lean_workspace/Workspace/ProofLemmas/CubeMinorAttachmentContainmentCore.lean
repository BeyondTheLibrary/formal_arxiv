import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.DoubleDiamond
import Workspace.Types.Prisms
import Workspace.Types.Appearances
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.CyclicPathConcatenationIsHole
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.CubeMajorCoreContradiction
import Workspace.ProofLemmas.FiveHoleBasics
import Workspace.ProofLemmas.SquareConnectedAdjoinByCrossingSquare
import Workspace.Statements.S02.Thm_2_4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*}

/-! ## Squares -/

theorem isSquare_mono {G : SimpleGraph V} {S S' T T' : Set V} {a₁ b₁ b₂ a₂ : V}
    (hS : S ⊆ S') (hT : T ⊆ T') (h : IsSquare G S T a₁ b₁ b₂ a₂) :
    IsSquare G S' T' a₁ b₁ b₂ a₂ :=
  ⟨h.1, hS h.2.1, hS h.2.2.1, hT h.2.2.2.1, hT h.2.2.2.2⟩

theorem isSquare_rev {G : SimpleGraph V} {S T : Set V} {a₁ b₁ b₂ a₂ : V}
    (h : IsSquare G S T a₁ b₁ b₂ a₂) : IsSquare G S T a₂ b₂ b₁ a₁ := by
  refine ⟨?_, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  have := HoleBasics.isHoleList_reverse h.1
  simpa using this

/-- The `T`-side twin: a square of `(S,T)` is a square of `(T,S)` after rotating by two. -/
theorem isSquare_swap {G : SimpleGraph V} {S T : Set V} {a₁ b₁ b₂ a₂ : V}
    (h : IsSquare G S T a₁ b₁ b₂ a₂) : IsSquare G T S b₂ a₂ a₁ b₁ := by
  refine ⟨?_, h.2.2.2.2, h.2.2.2.1, h.2.2.1, h.2.1⟩
  have := HoleBasics.isHoleList_rotate h.1 2
  simpa [List.rotate_eq_drop_append_take] using this

theorem squareConnected_symm {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) : SquareConnected G T S := by
  obtain ⟨⟨hS, hT⟩, hA, hB⟩ := h
  refine ⟨⟨hT, hS⟩, ?_, ?_⟩
  · intro X Y hXY hdisj hX hY
    obtain ⟨a₁, b₁, b₂, a₂, hsq, hb₁, hb₂⟩ :=
      hB Y X (by rw [Set.union_comm]; exact hXY) hdisj.symm hY hX
    exact ⟨b₂, a₂, a₁, b₁, isSquare_swap hsq, hb₂, hb₁⟩
  · intro X Y hXY hdisj hX hY
    obtain ⟨a₁, b₁, b₂, a₂, hsq, ha₁, ha₂⟩ :=
      hA Y X (by rw [Set.union_comm]; exact hXY) hdisj.symm hY hX
    exact ⟨b₂, a₂, a₁, b₁, isSquare_swap hsq, ha₂, ha₁⟩

/-- A partition of `S` into `P ∩ S` and `S \ P` yields a square crossing it. -/
theorem exists_square_cross_left {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) (P : Set V)
    (hP : (S ∩ P).Nonempty) (hQ : (S \ P).Nonempty) :
    ∃ a₁ b₁ b₂ a₂, IsSquare G S T a₁ b₁ b₂ a₂ ∧ a₁ ∈ P ∧ a₂ ∉ P := by
  obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, h2⟩ :=
    h.2.1 (S ∩ P) (S \ P)
      (by ext u; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]; tauto)
      (by rw [Set.disjoint_left]; rintro u ⟨-, hu⟩ ⟨-, hu'⟩; exact hu' hu)
      hP hQ
  exact ⟨a₁, b₁, b₂, a₂, hsq, h1.2, h2.2⟩

theorem exists_square_cross_right {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) (P : Set V)
    (hP : (T ∩ P).Nonempty) (hQ : (T \ P).Nonempty) :
    ∃ a₁ b₁ b₂ a₂, IsSquare G S T a₁ b₁ b₂ a₂ ∧ b₁ ∈ P ∧ b₂ ∉ P := by
  obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, h2⟩ :=
    h.2.2 (T ∩ P) (T \ P)
      (by ext u; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]; tauto)
      (by rw [Set.disjoint_left]; rintro u ⟨-, hu⟩ ⟨-, hu'⟩; exact hu' hu)
      hP hQ
  exact ⟨a₁, b₁, b₂, a₂, hsq, h1.2, h2.2⟩

/-- Every vertex of `S` sits in a square, as its first corner. -/
theorem exists_square_of_mem_left {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {s : V} (hs : s ∈ S) :
    ∃ b₁ b₂ a₂, IsSquare G S T s b₁ b₂ a₂ := by
  obtain ⟨u, hu, v, hv, huv⟩ := h.1.1
  have hQ : (S \ {s}).Nonempty := by
    by_cases hus : u = s
    · exact ⟨v, hv, fun hv' => huv (hus.trans (Set.mem_singleton_iff.mp hv').symm)⟩
    · exact ⟨u, hu, fun hu' => hus (Set.mem_singleton_iff.mp hu')⟩
  obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, h2⟩ :=
    exists_square_cross_left h {s} ⟨s, hs, rfl⟩ hQ
  rw [Set.mem_singleton_iff] at h1
  exact ⟨b₁, b₂, a₂, h1 ▸ hsq⟩

theorem exists_square_of_mem_right {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {t : V} (ht : t ∈ T) :
    ∃ a₁ b₂ a₂, IsSquare G S T a₁ t b₂ a₂ := by
  obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left (squareConnected_symm h) ht
  exact ⟨b₁, a₂, b₂, isSquare_rev (isSquare_swap hsq)⟩

/-- Every vertex of `S` has a neighbour in `T`. -/
theorem exists_adj_right {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {s : V} (hs : s ∈ S) : ∃ t ∈ T, G.Adj s t := by
  obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left h hs
  exact ⟨b₁, hsq.2.2.2.1, (CubeMajorCoreContradiction.square_adj hsq).1⟩

/-- Every vertex of `S` has a non-neighbour in `T`. -/
theorem exists_not_adj_right {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {s : V} (hs : s ∈ S) : ∃ t ∈ T, ¬ G.Adj s t := by
  obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left h hs
  exact ⟨b₂, hsq.2.2.2.2, (CubeMajorCoreContradiction.square_adj hsq).2.2.2.2.1⟩

theorem exists_adj_left {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {t : V} (ht : t ∈ T) : ∃ s ∈ S, G.Adj t s :=
  exists_adj_right (squareConnected_symm h) ht

theorem exists_not_adj_left {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {t : V} (ht : t ∈ T) : ∃ s ∈ S, ¬ G.Adj t s :=
  exists_not_adj_right (squareConnected_symm h) ht

/-! ## Adjoining one new vertex to each side of a square-connected pair -/

theorem squareConnected_adjoin_both {G : SimpleGraph V} {S T : Set V} {x y : V}
    (h : SquareConnected G S T) (hxS : x ∉ S) (hyT : y ∉ T)
    (hcrossS : ∃ b₁ b₂ a₂, IsSquare G (S ∪ {x}) (T ∪ {y}) x b₁ b₂ a₂ ∧ a₂ ∈ S)
    (hcrossT : ∃ a₁ b₂ a₂, IsSquare G (S ∪ {x}) (T ∪ {y}) a₁ y b₂ a₂ ∧ b₂ ∈ T) :
    SquareConnected G (S ∪ {x}) (T ∪ {y}) := by
  obtain ⟨cb₁, cb₂, ca₂, hcS, hca₂⟩ := hcrossS
  obtain ⟨da₁, db₂, da₂, hcT, hdb₂⟩ := hcrossT
  have hmono : ∀ {a₁ b₁ b₂ a₂ : V}, IsSquare G S T a₁ b₁ b₂ a₂ →
      IsSquare G (S ∪ {x}) (T ∪ {y}) a₁ b₁ b₂ a₂ :=
    fun hsq => isSquare_mono Set.subset_union_left Set.subset_union_left hsq
  refine ⟨⟨h.1.1.mono Set.subset_union_left, h.1.2.mono Set.subset_union_left⟩, ?_, ?_⟩
  · -- partitions of `S ∪ {x}`
    intro X Y hXY hdisj hX hY
    by_cases hSX : (S ∩ X).Nonempty
    · by_cases hSY : (S ∩ Y).Nonempty
      · obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, h2⟩ :=
          h.2.1 (S ∩ X) (S ∩ Y)
            (by
              ext u
              simp only [Set.mem_union, Set.mem_inter_iff]
              constructor
              · rintro (⟨hu, -⟩ | ⟨hu, -⟩) <;> exact hu
              · intro hu
                have : u ∈ X ∪ Y := by rw [hXY]; exact Or.inl hu
                rcases this with h' | h'
                · exact Or.inl ⟨hu, h'⟩
                · exact Or.inr ⟨hu, h'⟩)
            (by
              rw [Set.disjoint_left]
              rintro u ⟨-, hu⟩ ⟨-, hu'⟩
              exact (Set.disjoint_left.mp hdisj hu) hu')
            hSX hSY
        exact ⟨a₁, b₁, b₂, a₂, hmono hsq, h1.2, h2.2⟩
      · -- `Y ⊆ {x}` so `Y = {x}`
        have hYx : ∀ u ∈ Y, u = x := by
          intro u hu
          have : u ∈ S ∪ {x} := by rw [← hXY]; exact Or.inr hu
          rcases this with h' | h'
          · exact absurd ⟨u, h', hu⟩ hSY
          · exact h'
        obtain ⟨u, hu⟩ := hY
        have hxY : x ∈ Y := (hYx u hu) ▸ hu
        have hSXsub : S ⊆ X := by
          intro s hs
          have : s ∈ X ∪ Y := by rw [hXY]; exact Or.inl hs
          rcases this with h' | h'
          · exact h'
          · exact absurd ⟨s, hs, h'⟩ hSY
        exact ⟨ca₂, cb₂, cb₁, x, isSquare_rev hcS, hSXsub hca₂, hxY⟩
    · have hXx : ∀ u ∈ X, u = x := by
        intro u hu
        have : u ∈ S ∪ {x} := by rw [← hXY]; exact Or.inl hu
        rcases this with h' | h'
        · exact absurd ⟨u, h', hu⟩ hSX
        · exact h'
      obtain ⟨u, hu⟩ := hX
      have hxX : x ∈ X := (hXx u hu) ▸ hu
      have hSYsub : S ⊆ Y := by
        intro s hs
        have : s ∈ X ∪ Y := by rw [hXY]; exact Or.inl hs
        rcases this with h' | h'
        · exact absurd ⟨s, hs, h'⟩ hSX
        · exact h'
      exact ⟨x, cb₁, cb₂, ca₂, hcS, hxX, hSYsub hca₂⟩
  · -- partitions of `T ∪ {y}`
    intro X Y hXY hdisj hX hY
    by_cases hTX : (T ∩ X).Nonempty
    · by_cases hTY : (T ∩ Y).Nonempty
      · obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, h2⟩ :=
          h.2.2 (T ∩ X) (T ∩ Y)
            (by
              ext u
              simp only [Set.mem_union, Set.mem_inter_iff]
              constructor
              · rintro (⟨hu, -⟩ | ⟨hu, -⟩) <;> exact hu
              · intro hu
                have : u ∈ X ∪ Y := by rw [hXY]; exact Or.inl hu
                rcases this with h' | h'
                · exact Or.inl ⟨hu, h'⟩
                · exact Or.inr ⟨hu, h'⟩)
            (by
              rw [Set.disjoint_left]
              rintro u ⟨-, hu⟩ ⟨-, hu'⟩
              exact (Set.disjoint_left.mp hdisj hu) hu')
            hTX hTY
        exact ⟨a₁, b₁, b₂, a₂, hmono hsq, h1.2, h2.2⟩
      · have hYy : ∀ u ∈ Y, u = y := by
          intro u hu
          have : u ∈ T ∪ {y} := by rw [← hXY]; exact Or.inr hu
          rcases this with h' | h'
          · exact absurd ⟨u, h', hu⟩ hTY
          · exact h'
        obtain ⟨u, hu⟩ := hY
        have hyY : y ∈ Y := (hYy u hu) ▸ hu
        have hTXsub : T ⊆ X := by
          intro t ht
          have : t ∈ X ∪ Y := by rw [hXY]; exact Or.inl ht
          rcases this with h' | h'
          · exact h'
          · exact absurd ⟨t, ht, h'⟩ hTY
        exact ⟨da₂, db₂, y, da₁, isSquare_rev hcT, hTXsub hdb₂, hyY⟩
    · have hXy : ∀ u ∈ X, u = y := by
        intro u hu
        have : u ∈ T ∪ {y} := by rw [← hXY]; exact Or.inl hu
        rcases this with h' | h'
        · exact absurd ⟨u, h', hu⟩ hTX
        · exact h'
      obtain ⟨u, hu⟩ := hX
      have hyX : y ∈ X := (hXy u hu) ▸ hu
      have hTYsub : T ⊆ Y := by
        intro t ht
        have : t ∈ X ∪ Y := by rw [hXY]; exact Or.inl ht
        rcases this with h' | h'
        · exact absurd ⟨t, ht, h'⟩ hTX
        · exact h'
      exact ⟨da₁, y, db₂, da₂, hcT, hyX, hTYsub hdb₂⟩

/-! ## Elementary complement bookkeeping -/

theorem adj_of_not_compl_adj {G : SimpleGraph V} {u v : V} (hne : u ≠ v)
    (h : ¬ Gᶜ.Adj u v) : G.Adj u v := by
  simp only [SimpleGraph.compl_adj, not_and, not_not] at h
  exact h hne

theorem not_adj_of_compl_adj {G : SimpleGraph V} {u v : V} (h : Gᶜ.Adj u v) : ¬ G.Adj u v := by
  simp only [SimpleGraph.compl_adj] at h
  exact h.2

theorem complete_symm {G : SimpleGraph V} {X Y : Set V} (h : Complete G X Y) :
    Complete G Y X := fun y hy x hx => (h x hx y hy).symm

/-! ## The `(A,B,C,D) ↦ (B,A,D,C)` symmetry of a cube -/

theorem union4_swap (A B C D : Set V) : B ∪ A ∪ D ∪ C = A ∪ B ∪ C ∪ D := by
  ext u; simp only [Set.mem_union]; tauto

theorem cube_swap {G : SimpleGraph V} {A B C D : Set V} (h : IsCube G A B C D) :
    IsCube G B A D C := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := h
  exact ⟨⟨⟨dAB.symm, dBD, dBC, dAD, dAC, dCD.symm⟩, nB, nA, nD, nC⟩,
    ⟨cBD, cAC, aBC, aAD⟩, squareConnected_symm sAB, squareConnected_symm sCD⟩

theorem maximalCube_swap {G : SimpleGraph V} {A B C D : Set V} (h : MaximalCube G A B C D) :
    MaximalCube G B A D C := by
  refine ⟨cube_swap h.1, ?_⟩
  intro A' B' C' D' hcube hBA' hAB' hDC' hCD'
  obtain ⟨e1, e2, e3, e4⟩ := h.2 B' A' D' C' (cube_swap hcube) hAB' hBA' hCD' hDC'
  exact ⟨e2, e1, e4, e3⟩

theorem minorForCube_swap {G : SimpleGraph V} {A B C D : Set V} {v : V}
    (h : MinorForCube G A B C D v) : MinorForCube G B A D C v := by
  obtain ⟨h1, h2, h3⟩ := h
  have hU : B ∪ A ∪ D ∪ C = A ∪ B ∪ C ∪ D := union4_swap A B C D
  have hBA : B ∪ A = A ∪ B := Set.union_comm B A
  have hDC : D ∪ C = C ∪ D := Set.union_comm D C
  refine ⟨?_, ?_, ?_⟩
  · rw [hU]; exact h1
  · rw [hU, hBA, hDC]
    rcases h2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  · rw [hU]
    exact complete_symm h3

/-! ## The bad sets of the proof of 14.2 -/

/-- The negation of the first assertion of 14.2, for a single connected set of minor
vertices `F`. -/
def Bad (G : SimpleGraph V) (A B C D F : Set V) : Prop :=
  F ⊆ (A ∪ B ∪ C ∪ D)ᶜ ∧ ConnectedSet G F ∧
    (∀ v ∈ F, MinorForCube G A B C D v) ∧
    ¬ (attachments G F (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
       attachments G F (A ∪ B ∪ C ∪ D) ⊆ C ∪ D ∨
       attachments G F (A ∪ B ∪ C ∪ D) ⊆ A ∪ C ∨
       attachments G F (A ∪ B ∪ C ∪ D) ⊆ B ∪ D)

theorem bad_swap {G : SimpleGraph V} {A B C D F : Set V} (h : Bad G A B C D F) :
    Bad G B A D C F := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hU : B ∪ A ∪ D ∪ C = A ∪ B ∪ C ∪ D := union4_swap A B C D
  have hBA : B ∪ A = A ∪ B := Set.union_comm B A
  have hDC : D ∪ C = C ∪ D := Set.union_comm D C
  refine ⟨by rw [hU]; exact h1, h2, fun v hv => minorForCube_swap (h3 v hv), ?_⟩
  rw [hU, hBA, hDC]
  intro hc
  refine h4 ?_
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- PAPER (printed p. 88): *"We may assume that `X` meets both of `A`, `D`."*  A non-local
attachment set always meets one of the two *diagonal* pairs `{A, D}`, `{B, C}`; the
`(A,B,C,D) ↦ (B,A,D,C)` symmetry exchanges the two, which is what licenses the *"we may
assume"*. -/
theorem meets_diagonal {G : SimpleGraph V} {A B C D F : Set V} (h : Bad G A B C D F) :
    ((∃ x ∈ attachments G F (A ∪ B ∪ C ∪ D), x ∈ A) ∧
        (∃ y ∈ attachments G F (A ∪ B ∪ C ∪ D), y ∈ D)) ∨
      ((∃ x ∈ attachments G F (A ∪ B ∪ C ∪ D), x ∈ B) ∧
        (∃ y ∈ attachments G F (A ∪ B ∪ C ∪ D), y ∈ C)) := by
  obtain ⟨-, -, -, h4⟩ := h
  set X := attachments G F (A ∪ B ∪ C ∪ D) with hXdef
  have hXK : ∀ x ∈ X, x ∈ A ∪ B ∪ C ∪ D := fun x hx => hx.1
  have e1 : ¬ (X ⊆ A ∪ B) := fun hh => h4 (Or.inl hh)
  have e2 : ¬ (X ⊆ C ∪ D) := fun hh => h4 (Or.inr (Or.inl hh))
  have e3 : ¬ (X ⊆ A ∪ C) := fun hh => h4 (Or.inr (Or.inr (Or.inl hh)))
  have e4 : ¬ (X ⊆ B ∪ D) := fun hh => h4 (Or.inr (Or.inr (Or.inr hh)))
  rw [Set.not_subset] at e1 e2 e3 e4
  obtain ⟨u1, hu1, hu1'⟩ := e1
  obtain ⟨u2, hu2, hu2'⟩ := e2
  obtain ⟨u3, hu3, hu3'⟩ := e3
  obtain ⟨u4, hu4, hu4'⟩ := e4
  have d1 : (∃ x ∈ X, x ∈ C) ∨ (∃ x ∈ X, x ∈ D) := by
    rcases hXK u1 hu1 with (h' | h') | h'
    · rcases h' with h' | h'
      · exact absurd (Or.inl h') hu1'
      · exact absurd (Or.inr h') hu1'
    · exact Or.inl ⟨u1, hu1, h'⟩
    · exact Or.inr ⟨u1, hu1, h'⟩
  have d2 : (∃ x ∈ X, x ∈ A) ∨ (∃ x ∈ X, x ∈ B) := by
    rcases hXK u2 hu2 with (h' | h') | h'
    · rcases h' with h' | h'
      · exact Or.inl ⟨u2, hu2, h'⟩
      · exact Or.inr ⟨u2, hu2, h'⟩
    · exact absurd (Or.inl h') hu2'
    · exact absurd (Or.inr h') hu2'
  have d3 : (∃ x ∈ X, x ∈ B) ∨ (∃ x ∈ X, x ∈ D) := by
    rcases hXK u3 hu3 with (h' | h') | h'
    · rcases h' with h' | h'
      · exact absurd (Or.inl h') hu3'
      · exact Or.inl ⟨u3, hu3, h'⟩
    · exact absurd (Or.inr h') hu3'
    · exact Or.inr ⟨u3, hu3, h'⟩
  have d4 : (∃ x ∈ X, x ∈ A) ∨ (∃ x ∈ X, x ∈ C) := by
    rcases hXK u4 hu4 with (h' | h') | h'
    · rcases h' with h' | h'
      · exact Or.inl ⟨u4, hu4, h'⟩
      · exact absurd (Or.inl h') hu4'
    · exact Or.inr ⟨u4, hu4, h'⟩
    · exact absurd (Or.inr h') hu4'
  by_cases hA : ∃ x ∈ X, x ∈ A
  · by_cases hD : ∃ y ∈ X, y ∈ D
    · exact Or.inl ⟨hA, hD⟩
    · rcases d3 with hB | hD'
      · rcases d1 with hC | hD'
        · exact Or.inr ⟨hB, hC⟩
        · exact absurd hD' hD
      · exact absurd hD' hD
  · rcases d2 with hA' | hB
    · exact absurd hA' hA
    · rcases d4 with hA' | hC
      · exact absurd hA' hA
      · exact Or.inr ⟨hB, hC⟩

/-! ## List surgery -/

theorem mem_dropLast_iff {l : List V} {x : V} :
    x ∈ l.dropLast ↔ ∃ (i : ℕ) (h : i < l.length), i + 1 < l.length ∧ l[i]'h = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hl : l.dropLast.length = l.length - 1 := by simp
    rw [hl] at hi
    exact ⟨i, by omega, by omega, by simp⟩
  · rintro ⟨i, hi, hi2, rfl⟩
    exact ⟨i, by simp only [List.length_dropLast]; omega, by simp⟩

theorem mem_tail_iff {l : List V} {x : V} :
    x ∈ l.tail ↔ ∃ (i : ℕ) (h : i < l.length), 1 ≤ i ∧ l[i]'h = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hl : l.tail.length = l.length - 1 := by simp
    rw [hl] at hi
    exact ⟨i + 1, by omega, by omega, by simp⟩
  · rintro ⟨i, hi, hi1, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact ⟨j, by simp only [List.length_tail]; omega, by simp⟩

theorem mem_drop_iff {l : List V} {m : ℕ} {x : V} :
    x ∈ l.drop m ↔ ∃ (i : ℕ) (h : i < l.length), m ≤ i ∧ l[i]'h = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_drop] at hi
    exact ⟨m + i, by omega, by omega, by simp⟩
  · rintro ⟨i, hi, hmi, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
    exact ⟨j, by simp only [List.length_drop]; omega, by simp⟩

theorem mem_take_iff {l : List V} {m : ℕ} {x : V} :
    x ∈ l.take m ↔ ∃ (i : ℕ) (h : i < l.length), i < m ∧ l[i]'h = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_take] at hi
    exact ⟨i, by omega, by omega, by simp⟩
  · rintro ⟨i, hi, him, rfl⟩
    exact ⟨i, by simp only [List.length_take]; omega, by simp⟩

theorem getElem_mem_dropLast {l : List V} {i : ℕ} (h : i < l.length) (h2 : i + 1 < l.length) :
    l[i]'h ∈ l.dropLast := mem_dropLast_iff.mpr ⟨i, h, h2, rfl⟩

theorem getElem_mem_tail {l : List V} {i : ℕ} (h : i < l.length) (h1 : 1 ≤ i) :
    l[i]'h ∈ l.tail := mem_tail_iff.mpr ⟨i, h, h1, rfl⟩

theorem interior_getElem (p : List V) (k : ℕ) (hk : k < (SPGT.interior p).length) :
    (SPGT.interior p)[k]'hk = p[k + 1]'(by
      have := PathBasics.interior_length p; omega) := by
  have h := List.getElem_of_eq (PathBasics.interior_eq_drop_take p) hk
  rw [h]
  simp

/-! ## The configuration produced by the first paragraph of the printed proof -/

/-- PAPER (printed p. 88): *"Since all vertices in `F` are minor, it follows that `F` is a
path `f₁-f₂-⋯-f_k` of length `≥ 1`.  We may assume `f₁` is the unique vertex of `F` with a
neighbour in `A`, and `f_k` is the unique vertex of `F` with a neighbour in `D`.  Let `X₁, X₂`
be the sets of attachments in `V(K)` of `F \ {f_k}`, `F \ {f₁}` respectively.  From the
minimality of `F` it follows that `X₁` is a subset of one of `A ∪ B`, `A ∪ C`, and `X₂` is a
subset of one of `B ∪ D`, `C ∪ D`."* -/
structure PathConfig (G : SimpleGraph V) (A B C D : Set V) (f : List V) (a d : V) : Prop where
  path : IsPathList G f
  len : 2 ≤ f.length
  outside : ∀ z ∈ f, z ∉ A ∪ B ∪ C ∪ D
  memA : a ∈ A
  memD : d ∈ D
  adjA : ∀ (i : ℕ) (hi : i < f.length), G.Adj a (f[i]'hi) ↔ i = 0
  adjD : ∀ (i : ℕ) (hi : i < f.length), G.Adj d (f[i]'hi) ↔ i = f.length - 1
  uniqA : ∀ (i : ℕ) (hi : i < f.length), (∃ x ∈ A, G.Adj x (f[i]'hi)) → i = 0
  uniqD : ∀ (i : ℕ) (hi : i < f.length), (∃ x ∈ D, G.Adj x (f[i]'hi)) → i = f.length - 1
  minor : ∀ z ∈ f, MinorForCube G A B C D z
  locX1 : attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
          attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ C
  locX2 : attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ B ∪ D ∨
          attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ C ∪ D

theorem exists_pathConfig {G : SimpleGraph V} {A B C D : Set V}
    (hcube : IsCube G A B C D)
    (F : Set V) (hbad : Bad G A B C D F)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ¬ Bad G A B C D F')
    (a d : V) (haX : a ∈ attachments G F (A ∪ B ∪ C ∪ D)) (haA : a ∈ A)
    (hdX : d ∈ attachments G F (A ∪ B ∪ C ∪ D)) (hdD : d ∈ D) :
    ∃ f : List V, F = {z : V | z ∈ f} ∧ PathConfig G A B C D f a d := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  obtain ⟨hFK, hFconn, hFminor, hFloc⟩ := hbad
  have haK : a ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl (Or.inl haA))
  have hdK : d ∈ A ∪ B ∪ C ∪ D := Or.inr hdD
  -- a set attached to both `a ∈ A` and `d ∈ D` is never local
  have hnotlocal : ∀ S : Set V, a ∈ attachments G S (A ∪ B ∪ C ∪ D) →
      d ∈ attachments G S (A ∪ B ∪ C ∪ D) →
      ¬ (attachments G S (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
         attachments G S (A ∪ B ∪ C ∪ D) ⊆ C ∪ D ∨
         attachments G S (A ∪ B ∪ C ∪ D) ⊆ A ∪ C ∨
         attachments G S (A ∪ B ∪ C ∪ D) ⊆ B ∪ D) := by
    rintro S ha hd (h | h | h | h)
    · rcases h hd with h' | h'
      · exact Set.disjoint_left.mp dAD h' hdD
      · exact Set.disjoint_left.mp dBD h' hdD
    · rcases h ha with h' | h'
      · exact Set.disjoint_left.mp dAC haA h'
      · exact Set.disjoint_left.mp dAD haA h'
    · rcases h hd with h' | h'
      · exact Set.disjoint_left.mp dAD h' hdD
      · exact Set.disjoint_left.mp dCD h' hdD
    · rcases h ha with h' | h'
      · exact Set.disjoint_left.mp dAB haA h'
      · exact Set.disjoint_left.mp dAD haA h'
  have haF : a ∉ F := fun h => (hFK h) haK
  have hdF : d ∉ F := fun h => (hFK h) hdK
  have hne : a ≠ d := by
    intro he
    rw [he] at haA
    exact Set.disjoint_left.mp dAD haA hdD
  have hnadj : ¬ G.Adj a d := aAD a haA d hdD
  obtain ⟨p, hp, h3, hint, hintconn, ⟨ea, hea, hadja⟩, ⟨ed, hed, hadjd⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn hne hnadj haF hdF haX.2 hdX.2
  have hpl : IsPathList G p := hp.1
  have hfsubF : {z : V | z ∈ SPGT.interior p} ⊆ F := hint
  have haatt : a ∈ attachments G {z : V | z ∈ SPGT.interior p} (A ∪ B ∪ C ∪ D) :=
    ⟨haK, ea, hea, hadja⟩
  have hdatt : d ∈ attachments G {z : V | z ∈ SPGT.interior p} (A ∪ B ∪ C ∪ D) :=
    ⟨hdK, ed, hed, hadjd⟩
  have hFeq : F = {z : V | z ∈ SPGT.interior p} := by
    by_contra hcon
    refine hnotlocal _ haatt hdatt ?_
    by_contra hloc
    exact hmin _ hfsubF (fun he => hcon he.symm)
      ⟨hfsubF.trans hFK, hintconn, fun v hv => hFminor v (hfsubF hv), hloc⟩
  refine ⟨SPGT.interior p, hFeq, ?_⟩
  set f := SPGT.interior p with hfdef
  have hfK : ∀ z ∈ f, z ∉ A ∪ B ∪ C ∪ D := by
    intro z hz
    exact hFK (by rw [hFeq]; exact hz)
  have hfminor : ∀ z ∈ f, MinorForCube G A B C D z := by
    intro z hz
    exact hFminor z (by rw [hFeq]; exact hz)
  have hflen : f.length = p.length - 2 := PathBasics.interior_length p
  have hfne : f ≠ [] := PathBasics.interior_ne_nil hpl h3
  have hf1 : 1 ≤ f.length := List.length_pos_of_ne_nil hfne
  have hfpath : IsPathList G f := by
    rw [hfdef, PathBasics.interior_eq_drop_take]
    exact PathBasics.isPathList_take (PathBasics.isPathList_drop hpl (by omega)) (by omega)
  have hfnd : f.Nodup := PathBasics.path_nodup hfpath
  have hfget : ∀ (i : ℕ) (hi : i < f.length), f[i]'hi = p[i + 1]'(by omega) := by
    intro i hi
    exact interior_getElem p i hi
  have h0 : p[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
  have hlastp : p[p.length - 1]'(by omega) = d :=
    PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
  have hadjA : ∀ (i : ℕ) (hi : i < f.length), (G.Adj a (f[i]'hi) ↔ i = 0) := by
    intro i hi
    rw [hfget i hi, ← h0, PathBasics.path_adj_iff hpl (by omega) (by omega)]
    omega
  have hadjD : ∀ (i : ℕ) (hi : i < f.length), (G.Adj d (f[i]'hi) ↔ i = f.length - 1) := by
    intro i hi
    rw [hfget i hi, ← hlastp, PathBasics.path_adj_iff hpl (by omega) (by omega)]
    omega
  -- every proper connected subset of `f` has a local attachment set
  have hlocal_of_proper : ∀ F' : Set V, F' ⊆ {z : V | z ∈ f} → F' ≠ {z : V | z ∈ f} →
      ConnectedSet G F' →
      (attachments G F' (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
       attachments G F' (A ∪ B ∪ C ∪ D) ⊆ C ∪ D ∨
       attachments G F' (A ∪ B ∪ C ∪ D) ⊆ A ∪ C ∨
       attachments G F' (A ∪ B ∪ C ∪ D) ⊆ B ∪ D) := by
    intro F' hsub hne' hconn'
    by_contra hloc
    refine hmin F' (by rw [hFeq]; exact hsub) (by rw [hFeq]; exact hne') ?_
    refine ⟨?_, hconn', ?_, hloc⟩
    · intro z hz
      exact hfK z (hsub hz)
    · intro z hz
      exact hfminor z (hsub hz)
  -- `k ≥ 2`
  have hk2 : 2 ≤ f.length := by
    by_contra hcon
    have h1 : f.length = 1 := by omega
    have hall : ∀ z ∈ f, z = f[0]'(by omega) := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
      have : i = 0 := by omega
      subst this
      rfl
    have hsubN : attachments G {z : V | z ∈ f} (A ∪ B ∪ C ∪ D) ⊆
        G.neighborSet (f[0]'(by omega)) ∩ (A ∪ B ∪ C ∪ D) := by
      rintro v ⟨hvK, z, hz, hvz⟩
      exact ⟨by rw [SimpleGraph.mem_neighborSet, ← hall z hz]; exact hvz.symm, hvK⟩
    refine hFloc ?_
    rw [hFeq]
    rcases (hfminor _ (List.getElem_mem (show 0 < f.length by omega))).2.1 with h | h | h | h
    · exact Or.inl (hsubN.trans h)
    · exact Or.inr (Or.inl (hsubN.trans h))
    · exact Or.inr (Or.inr (Or.inl (hsubN.trans h)))
    · exact Or.inr (Or.inr (Or.inr (hsubN.trans h)))
  -- uniqueness of the `A`-attached and `D`-attached vertices of `f`
  have huniqA : ∀ (i : ℕ) (hi : i < f.length), (∃ x ∈ A, G.Adj x (f[i]'hi)) → i = 0 := by
    rintro i hi ⟨x, hxA, hxadj⟩
    by_contra hi0
    have hipos : 1 ≤ i := by omega
    have hsub : {z : V | z ∈ f.drop i} ⊆ {z : V | z ∈ f} :=
      fun z hz => List.drop_subset _ _ hz
    have hnotmem : (f[0]'(by omega)) ∉ f.drop i := by
      intro hmem
      obtain ⟨j, hj, hij, hje⟩ := mem_drop_iff.mp hmem
      have := (List.Nodup.getElem_inj_iff hfnd).mp hje
      omega
    have hne' : {z : V | z ∈ f.drop i} ≠ {z : V | z ∈ f} := by
      intro he
      refine hnotmem ?_
      have : (f[0]'(by omega)) ∈ {z : V | z ∈ f} := List.getElem_mem _
      rw [← he] at this
      exact this
    have hconn' : ConnectedSet G {z : V | z ∈ f.drop i} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_drop hfpath hi)
    have hxatt : x ∈ attachments G {z : V | z ∈ f.drop i} (A ∪ B ∪ C ∪ D) :=
      ⟨Or.inl (Or.inl (Or.inl hxA)), f[i]'hi, mem_drop_iff.mpr ⟨i, hi, le_refl i, rfl⟩, hxadj⟩
    have hdatt' : d ∈ attachments G {z : V | z ∈ f.drop i} (A ∪ B ∪ C ∪ D) :=
      ⟨hdK, f[f.length - 1]'(by omega),
        mem_drop_iff.mpr ⟨f.length - 1, by omega, by omega, rfl⟩,
        (hadjD (f.length - 1) (by omega)).mpr rfl⟩
    -- `x ∈ A` and `d ∈ D` make the attachment set non-local
    rcases hlocal_of_proper _ hsub hne' hconn' with h | h | h | h
    · rcases h hdatt' with h' | h'
      · exact Set.disjoint_left.mp dAD h' hdD
      · exact Set.disjoint_left.mp dBD h' hdD
    · rcases h hxatt with h' | h'
      · exact Set.disjoint_left.mp dAC hxA h'
      · exact Set.disjoint_left.mp dAD hxA h'
    · rcases h hdatt' with h' | h'
      · exact Set.disjoint_left.mp dAD h' hdD
      · exact Set.disjoint_left.mp dCD h' hdD
    · rcases h hxatt with h' | h'
      · exact Set.disjoint_left.mp dAB hxA h'
      · exact Set.disjoint_left.mp dAD hxA h'
  have huniqD : ∀ (i : ℕ) (hi : i < f.length),
      (∃ x ∈ D, G.Adj x (f[i]'hi)) → i = f.length - 1 := by
    rintro i hi ⟨x, hxD, hxadj⟩
    by_contra hi0
    have hilt : i + 1 < f.length := by omega
    have hsub : {z : V | z ∈ f.take (i + 1)} ⊆ {z : V | z ∈ f} :=
      fun z hz => List.take_subset _ _ hz
    have hnotmem : (f[f.length - 1]'(by omega)) ∉ f.take (i + 1) := by
      intro hmem
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hmem
      rw [List.length_take] at hj
      rw [List.getElem_take] at hje
      have := (List.Nodup.getElem_inj_iff hfnd).mp hje
      omega
    have hne' : {z : V | z ∈ f.take (i + 1)} ≠ {z : V | z ∈ f} := by
      intro he
      refine hnotmem ?_
      have : (f[f.length - 1]'(by omega)) ∈ {z : V | z ∈ f} := List.getElem_mem _
      rw [← he] at this
      exact this
    have hconn' : ConnectedSet G {z : V | z ∈ f.take (i + 1)} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_take hfpath (by omega))
    have hmemi : (f[i]'hi) ∈ f.take (i + 1) :=
      List.mem_iff_getElem.mpr ⟨i, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
    have hmem0 : (f[0]'(by omega)) ∈ f.take (i + 1) :=
      List.mem_iff_getElem.mpr ⟨0, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
    have hxatt : x ∈ attachments G {z : V | z ∈ f.take (i + 1)} (A ∪ B ∪ C ∪ D) :=
      ⟨Or.inr hxD, f[i]'hi, hmemi, hxadj⟩
    have haatt' : a ∈ attachments G {z : V | z ∈ f.take (i + 1)} (A ∪ B ∪ C ∪ D) :=
      ⟨haK, f[0]'(by omega), hmem0, (hadjA 0 (by omega)).mpr rfl⟩
    rcases hlocal_of_proper _ hsub hne' hconn' with h | h | h | h
    · rcases h hxatt with h' | h'
      · exact Set.disjoint_left.mp dAD h' hxD
      · exact Set.disjoint_left.mp dBD h' hxD
    · rcases h haatt' with h' | h'
      · exact Set.disjoint_left.mp dAC haA h'
      · exact Set.disjoint_left.mp dAD haA h'
    · rcases h hxatt with h' | h'
      · exact Set.disjoint_left.mp dAD h' hxD
      · exact Set.disjoint_left.mp dCD h' hxD
    · rcases h haatt' with h' | h'
      · exact Set.disjoint_left.mp dAB haA h'
      · exact Set.disjoint_left.mp dAD haA h'
  -- the two sets `X₁`, `X₂`
  have hlocX1 : attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
      attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ C := by
    have hsub : {z : V | z ∈ f.dropLast} ⊆ {z : V | z ∈ f} :=
      fun z hz => List.dropLast_subset _ hz
    have hnotmem : (f[f.length - 1]'(by omega)) ∉ f.dropLast := by
      intro hmem
      obtain ⟨j, hj, hj2, hje⟩ := mem_dropLast_iff.mp hmem
      have := (List.Nodup.getElem_inj_iff hfnd).mp hje
      omega
    have hne' : {z : V | z ∈ f.dropLast} ≠ {z : V | z ∈ f} := by
      intro he
      refine hnotmem ?_
      have : (f[f.length - 1]'(by omega)) ∈ {z : V | z ∈ f} := List.getElem_mem _
      rw [← he] at this
      exact this
    have hpath' : IsPathList G f.dropLast := by
      rw [List.dropLast_eq_take]
      exact PathBasics.isPathList_take hfpath (by omega)
    have hconn' : ConnectedSet G {z : V | z ∈ f.dropLast} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hpath'
    have haatt' : a ∈ attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) :=
      ⟨haK, f[0]'(by omega), getElem_mem_dropLast (by omega) (by omega),
        (hadjA 0 (by omega)).mpr rfl⟩
    rcases hlocal_of_proper _ hsub hne' hconn' with h | h | h | h
    · exact Or.inl h
    · exact absurd (h haatt') (by
        rintro (h' | h')
        · exact Set.disjoint_left.mp dAC haA h'
        · exact Set.disjoint_left.mp dAD haA h')
    · exact Or.inr h
    · exact absurd (h haatt') (by
        rintro (h' | h')
        · exact Set.disjoint_left.mp dAB haA h'
        · exact Set.disjoint_left.mp dAD haA h')
  have hlocX2 : attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ B ∪ D ∨
      attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ C ∪ D := by
    have hsub : {z : V | z ∈ f.tail} ⊆ {z : V | z ∈ f} :=
      fun z hz => List.tail_subset _ hz
    have hnotmem : (f[0]'(by omega)) ∉ f.tail := by
      intro hmem
      obtain ⟨j, hj, hj1, hje⟩ := mem_tail_iff.mp hmem
      have := (List.Nodup.getElem_inj_iff hfnd).mp hje
      omega
    have hne' : {z : V | z ∈ f.tail} ≠ {z : V | z ∈ f} := by
      intro he
      refine hnotmem ?_
      have : (f[0]'(by omega)) ∈ {z : V | z ∈ f} := List.getElem_mem _
      rw [← he] at this
      exact this
    have hpath' : IsPathList G f.tail := by
      rw [← List.drop_one]
      exact PathBasics.isPathList_drop hfpath (by omega)
    have hconn' : ConnectedSet G {z : V | z ∈ f.tail} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hpath'
    have hdatt' : d ∈ attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) :=
      ⟨hdK, f[f.length - 1]'(by omega), getElem_mem_tail (by omega) (by omega),
        (hadjD (f.length - 1) (by omega)).mpr rfl⟩
    rcases hlocal_of_proper _ hsub hne' hconn' with h | h | h | h
    · exact absurd (h hdatt') (by
        rintro (h' | h')
        · exact Set.disjoint_left.mp dAD h' hdD
        · exact Set.disjoint_left.mp dBD h' hdD)
    · exact Or.inr h
    · exact absurd (h hdatt') (by
        rintro (h' | h')
        · exact Set.disjoint_left.mp dAD h' hdD
        · exact Set.disjoint_left.mp dCD h' hdD)
    · exact Or.inl h
  exact ⟨hfpath, hk2, hfK, haA, hdD, hadjA, hadjD, huniqA, huniqD, hfminor, hlocX1, hlocX2⟩

/-! ## Building the holes and prisms of the printed proof -/

theorem isPathList_triple {G : SimpleGraph V} {a b c : V}
    (hnd : ([a, b, c] : List V).Nodup)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (n1 : ¬ G.Adj a c) :
    IsPathList G [a, b, c] := by
  have key : ∀ i j : ℕ, i < 3 → j < 3 →
      ∀ (hi : i < ([a, b, c] : List V).length) (hj : j < ([a, b, c] : List V).length),
        (G.Adj (([a, b, c] : List V)[i]'hi) (([a, b, c] : List V)[j]'hj) ↔
          (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi4 hj4
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

/-- Three paths glued cyclically form a hole.  Every hole of the printed proof of 14.2 has
this shape: a single vertex of `V(K)`, the path `f₁-⋯-f_k`, and a short return path through
`V(K)`. -/
theorem isHoleList_three_blocks {G : SimpleGraph V} {P₀ P₁ P₂ : List V}
    {s₀ t₀ s₁ t₁ s₂ t₂ : V}
    (h0 : IsPathFrom G P₀ s₀ t₀) (h1 : IsPathFrom G P₁ s₁ t₁) (h2 : IsPathFrom G P₂ s₂ t₂)
    (d01 : ∀ x ∈ P₀, x ∉ P₁) (d02 : ∀ x ∈ P₀, x ∉ P₂) (d12 : ∀ x ∈ P₁, x ∉ P₂)
    (l01 : ∀ x ∈ P₀, ∀ y ∈ P₁, (G.Adj x y ↔ (x = t₀ ∧ y = s₁)))
    (l12 : ∀ x ∈ P₁, ∀ y ∈ P₂, (G.Adj x y ↔ (x = t₁ ∧ y = s₂)))
    (l20 : ∀ x ∈ P₂, ∀ y ∈ P₀, (G.Adj x y ↔ (x = t₂ ∧ y = s₀)))
    (h4 : 4 ≤ P₀.length + P₁.length + P₂.length) :
    IsHoleList G (P₀ ++ P₁ ++ P₂) := by
  have hlist : ([P₀, P₁, P₂] : List (List V)).flatMap id = P₀ ++ P₁ ++ P₂ := by
    simp [List.flatMap_cons, List.append_assoc]
  have hd10 : ∀ x ∈ P₁, x ∉ P₀ := fun x hx hx' => d01 x hx' hx
  have hd20 : ∀ x ∈ P₂, x ∉ P₀ := fun x hx hx' => d02 x hx' hx
  have hd21 : ∀ x ∈ P₂, x ∉ P₁ := fun x hx hx' => d12 x hx' hx
  rw [← hlist]
  refine CyclicPathConcatenationIsHole.isHoleList_flatMap_of_cyclic G [P₀, P₁, P₂]
    (fun i => if i = 0 then s₀ else if i = 1 then s₁ else s₂)
    (fun i => if i = 0 then t₀ else if i = 1 then t₁ else t₂)
    (by simp) ?_ ?_ ?_ ?_ (by rw [hlist]; simp only [List.length_append]; omega)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · intro i j hi hj hij
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
      first
        | exact absurd rfl hij
        | exact d01 | exact d02 | exact d12 | exact hd10 | exact hd20 | exact hd21
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simpa using l01
    · simpa using l12
    · simpa using l20
  · intro i j hi hj hij h1' h2'
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all

/-- Assembling `FormPrism` from the data the paper writes down. -/
theorem formPrism_of_data {G : SimpleGraph V}
    {a₁ a₂ a₃ b₁ b₂ b₃ : V} {P₁ P₂ P₃ : List V}
    (ha12 : G.Adj a₁ a₂) (ha13 : G.Adj a₁ a₃) (ha23 : G.Adj a₂ a₃)
    (hb12 : G.Adj b₁ b₂) (hb13 : G.Adj b₁ b₃) (hb23 : G.Adj b₂ b₃)
    (n11 : a₁ ≠ b₁) (n12 : a₁ ≠ b₂) (n13 : a₁ ≠ b₃)
    (n21 : a₂ ≠ b₁) (n22 : a₂ ≠ b₂) (n23 : a₂ ≠ b₃)
    (n31 : a₃ ≠ b₁) (n32 : a₃ ≠ b₂) (n33 : a₃ ≠ b₃)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂) (hP₃ : IsPathFrom G P₃ a₃ b₃)
    (h12 : ∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)))
    (h13 : ∀ u ∈ P₁, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a₁ ∧ v = a₃) ∨ (u = b₁ ∧ v = b₃)))
    (h23 : ∀ u ∈ P₂, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a₂ ∧ v = a₃) ∨ (u = b₂ ∧ v = b₃))) :
    FormPrism G ![a₁, a₂, a₃] ![b₁, b₂, b₃] P₁ P₂ P₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact ha12 | exact ha13 | exact ha23
        | exact ha12.symm | exact ha13.symm | exact ha23.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact hb12 | exact hb13 | exact hb23
        | exact hb12.symm | exact hb13.symm | exact hb23.symm
  · intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  · simpa using hP₁
  · simpa using hP₂
  · simpa using hP₃
  · simpa using h12
  · simpa using h13
  · simpa using h23

/-! ## Small conveniences -/

theorem no_odd_hole {G : SimpleGraph V} (hG : Berge G) {c : List V} (h : IsHoleList G c) :
    Even c.length := hG.1 c h

theorem isPathFrom_self {G : SimpleGraph V} {l : List V} (h : IsPathList G l)
    (hpos : 0 < l.length) :
    IsPathFrom G l (l[0]'hpos) (l[l.length - 1]'(by omega)) := by
  refine ⟨h, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)]

theorem isPathFrom_take {G : SimpleGraph V} {l : List V} (h : IsPathList G l) {m : ℕ}
    (hm : 0 < m) (hml : m < l.length) :
    IsPathFrom G (l.take (m + 1)) (l[0]'(by omega)) (l[m]'hml) := by
  simpa using PathBasics.isPathFrom_slice h hm hml

theorem getElem_eq_iff {l : List V} (hnd : l.Nodup) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj ↔ i = j :=
  List.Nodup.getElem_inj_iff hnd

/-- From an antisquare through `d`: every vertex of `D` has a neighbour in `C`. -/
theorem exists_adj_of_mem_right {G : SimpleGraph V} {C D : Set V} (hdisj : Disjoint C D)
    (h : SquareConnected Gᶜ C D) {d : V} (hd : d ∈ D) : ∃ c ∈ C, G.Adj c d := by
  obtain ⟨c, hcC, hnadj⟩ := exists_not_adj_left h hd
  have hne : d ≠ c := fun he => Set.disjoint_left.mp hdisj hcC (he ▸ hd)
  exact ⟨c, hcC, (adj_of_not_compl_adj hne hnadj).symm⟩

/-- From an antisquare through `d`: every vertex of `D` has a non-neighbour in `C`. -/
theorem exists_not_adj_of_mem_right {G : SimpleGraph V} {C D : Set V}
    (h : SquareConnected Gᶜ C D) {d : V} (hd : d ∈ D) : ∃ c ∈ C, ¬ G.Adj c d := by
  obtain ⟨c, hcC, hadj⟩ := exists_adj_left h hd
  exact ⟨c, hcC, fun hh => not_adj_of_compl_adj hadj hh.symm⟩

theorem exists_adj_of_mem_left {G : SimpleGraph V} {C D : Set V} (hdisj : Disjoint C D)
    (h : SquareConnected Gᶜ C D) {c : V} (hc : c ∈ C) : ∃ d ∈ D, G.Adj c d := by
  obtain ⟨d, hdD, hnadj⟩ := exists_not_adj_right h hc
  have hne : c ≠ d := fun he => Set.disjoint_left.mp hdisj hc (he ▸ hdD)
  exact ⟨d, hdD, adj_of_not_compl_adj hne hnadj⟩

theorem exists_not_adj_of_mem_left {G : SimpleGraph V} {C D : Set V}
    (h : SquareConnected Gᶜ C D) {c : V} (hc : c ∈ C) : ∃ d ∈ D, ¬ G.Adj c d := by
  obtain ⟨d, hdD, hadj⟩ := exists_adj_right h hc
  exact ⟨d, hdD, not_adj_of_compl_adj hadj⟩

theorem noK4_of_inF3 {G : SimpleGraph V} (hG : InF3 G) :
    ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
  rintro ⟨n, H, K', ⟨hsub, ⟨φ⟩⟩, -⟩
  exact (hG.2 n H hsub).1 ⟨K', ⟨φ.symm⟩⟩

/-! ## Claim (1) -/

/-- PAPER (printed p. 88, inside (1)): *"If `k` is even, choose `a ∈ A` adjacent to `f₁`, and
`d ∈ D` adjacent to `f_k`, and `c ∈ C` adjacent to `d`; then `a-f₁-⋯-f_k-d-c-a` is an odd hole,
a contradiction."* -/
theorem claim_one_even {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : IsCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hnoC : ∀ c ∈ C, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj c (f[i]'hi))
    (hkeven : Even f.length) : False := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD, hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  obtain ⟨c, hcC, hcd⟩ := exists_adj_of_mem_right dCD sCD hdD
  have haK : a ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl (Or.inl haA))
  have hcK : c ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inr hcC)
  have hdK : d ∈ A ∪ B ∪ C ∪ D := Or.inr hdD
  have had : a ≠ d := by rintro rfl; exact Set.disjoint_left.mp dAD haA hdD
  have hac : a ≠ c := by rintro rfl; exact Set.disjoint_left.mp dAC haA hcC
  have hdc : d ≠ c := by rintro rfl; exact Set.disjoint_left.mp dCD hcC hdD
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  have hhole : IsHoleList G ([a] ++ f ++ [d, c]) := by
    refine isHoleList_three_blocks
      (P₀ := [a]) (P₁ := f) (P₂ := [d, c])
      (s₀ := a) (t₀ := a) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'(by omega))
      (s₂ := d) (t₂ := c)
      ⟨PathBasics.isPathList_singleton G a, rfl, rfl⟩
      (isPathFrom_self hfpath hfpos)
      ⟨PathBasics.isPathList_pair hcd.symm, rfl, rfl⟩
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx hx'
      simp only [List.mem_singleton] at hx
      subst hx
      exact hfout x hx' haK
    · intro x hx hmem
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · exact had h
      · exact hac h
    · intro x hx hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · exact hfne x hx d hdK h
      · exact hfne x hx c hcK h
    · intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
      rw [hadjA i hi]
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨-, h⟩
        exact (getElem_eq_iff hfnd hi hfpos).mp h
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · constructor
        · intro hadj
          have hii : i = f.length - 1 := (hadjD i hi).mp hadj.symm
          exact ⟨(getElem_eq_iff hfnd hi (by omega)).mpr hii, rfl⟩
        · rintro ⟨h, -⟩
          have hii : i = f.length - 1 := (getElem_eq_iff hfnd hi (by omega)).mp h
          exact ((hadjD i hi).mpr hii).symm
      · constructor
        · intro hadj
          exact absurd hadj.symm (hnoC _ hcC i hi)
        · rintro ⟨-, h⟩
          exact absurd h.symm hdc
    · intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · constructor
        · intro hadj
          exact absurd hadj.symm (aAD y haA x hdD)
        · rintro ⟨h, -⟩
          exact absurd h hdc
      · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => (cAC y haA x hcC).symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have hlen : ([a] ++ f ++ [d, c]).length = f.length + 3 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hev := no_odd_hole hG.1.1 hhole
  rw [hlen] at hev
  obtain ⟨m, hm⟩ := hkeven
  obtain ⟨n, hn⟩ := hev
  omega

/-- PAPER (printed p. 88, inside (1)): *"Suppose first that `f₁` is complete to `A`.  Since it
is minor, it has no neighbours in `B` (for no vertex in `B` is `A`-complete).  If there are no
edges between `B` and `F`, let `a₁-b₁-b₂-a₂-a₁` be a square, and let `d ∈ D` be adjacent to
`f_k`; then `a₁-b₁`, `a₂-b₂`, `f₁-⋯-f_k-d` form a long prism, a contradiction."*  This is the
`B`-anticomplete half of the `A`-complete sub-case. -/
theorem claim_one_odd_Acomp_noB {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : IsCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hk3 : 3 ≤ f.length)
    (hAcomp : ∀ x ∈ A, ∀ (h0 : 0 < f.length), G.Adj (f[0]'h0) x)
    (hnoB : ∀ b ∈ B, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj b (f[i]'hi)) : False := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD, hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inl (Or.inl (Or.inr h))
  have hmD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left sAB haA
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  -- the third path `f₁-⋯-f_k-d`
  have hdnotf : d ∉ f := fun hmem => hfne d hmem d (hmD hdD) rfl
  have hP₃ : IsPathFrom G (f ++ [d]) (f[0]'hfpos) d := by
    refine PathGlue.glue_path (isPathFrom_self hfpath hfpos)
      (⟨PathBasics.isPathList_singleton G d, rfl, rfl⟩) ?_ ?_
    · intro x hx hmem
      simp only [List.mem_singleton] at hmem
      exact hfne x hx d (hmD hdD) hmem
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.mem_singleton] at hy
      subst hy
      constructor
      · intro hadj
        exact ⟨(getElem_eq_iff hfnd hi (by omega)).mpr ((hadjD i hi).mp hadj.symm), rfl⟩
      · rintro ⟨h, -⟩
        exact ((hadjD i hi).mpr ((getElem_eq_iff hfnd hi (by omega)).mp h)).symm
  have hprism : FormPrism G ![a, a₂, f[0]'hfpos] ![b₁, b₂, d] [a, b₁] [a₂, b₂] (f ++ [d]) := by
    refine formPrism_of_data e30.symm (hAcomp a haA hfpos).symm (hAcomp a₂ ha₂A hfpos).symm
      e12 (cBD b₁ hb₁B d hdD) (cBD b₂ hb₂B d hdD)
      ne01 ne02 (by rintro rfl; exact Set.disjoint_left.mp dAD haA hdD)
      ne13.symm ne23.symm (by rintro rfl; exact Set.disjoint_left.mp dAD ha₂A hdD)
      (hfne _ (List.getElem_mem hfpos) b₁ (hmB hb₁B))
      (hfne _ (List.getElem_mem hfpos) b₂ (hmB hb₂B))
      (hfne _ (List.getElem_mem hfpos) d (hmD hdD))
      ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
      ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩ hP₃ ?_ ?_ ?_
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
      · exact ⟨fun hadj => absurd hadj n02,
          by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [absurd h ne23, absurd h ne01]⟩
      · exact ⟨fun hadj => absurd hadj n13,
          by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [absurd h ne01.symm, absurd h ne23.symm]⟩
      · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => e12⟩
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases List.mem_append.mp hv with hv' | hv'
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv'
        rcases hu with rfl | rfl
        · rw [hadjA i hi]
          constructor
          · rintro rfl; exact Or.inl ⟨rfl, rfl⟩
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact (getElem_eq_iff hfnd hi hfpos).mp h
            · exact absurd h ne01
        · constructor
          · intro hadj; exact absurd hadj (hnoB u hb₁B i hi)
          · rintro (⟨h, -⟩ | ⟨-, h⟩)
            · exact absurd h ne01.symm
            · exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
      · simp only [List.mem_singleton] at hv'
        subst hv'
        rcases hu with rfl | rfl
        · constructor
          · intro hadj; exact absurd hadj (aAD u haA v hdD)
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact absurd h.symm (hfne _ (List.getElem_mem hfpos) v (hmD hdD))
            · exact absurd h ne01
        · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => cBD u hb₁B v hdD⟩
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases List.mem_append.mp hv with hv' | hv'
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv'
        rcases hu with rfl | rfl
        · constructor
          · intro hadj
            have : i = 0 := huniqA i hi ⟨u, ha₂A, hadj⟩
            exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr this⟩
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · rw [h]
              exact (hAcomp u ha₂A hfpos).symm
            · exact absurd h ne23.symm
        · constructor
          · intro hadj; exact absurd hadj (hnoB u hb₂B i hi)
          · rintro (⟨h, -⟩ | ⟨-, h⟩)
            · exact absurd h ne23
            · exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
      · simp only [List.mem_singleton] at hv'
        subst hv'
        rcases hu with rfl | rfl
        · constructor
          · intro hadj; exact absurd hadj (aAD u ha₂A v hdD)
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact absurd h.symm (hfne _ (List.getElem_mem hfpos) v (hmD hdD))
            · exact absurd h ne23.symm
        · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => cBD u hb₂B v hdD⟩
  have hlong : 1 < pathLength (f ++ [d]) := by
    simp only [pathLength, List.length_append, List.length_cons, List.length_nil]
    omega
  exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inr (Or.inr hlong)⟩

/-- PAPER (printed p. 88, inside (1)): *"Choose `i` with `1 ≤ i ≤ k` minimum such that `f_i` has
a neighbour in `B`.  If `f_i` is not complete to `B`, choose a square `a₁-b₁-b₂-a₂-a₁` such that
`f_i` is adjacent to `b₁` and not to `b₂`; then `b₁` can be linked onto the triangle
`{f₁, a₁, a₂}`, via `b₁-f_i-⋯-f₁`, `b₁-a₁`, `b₁-b₂-a₂`, contrary to 2.4."* -/
theorem claim_one_odd_Acomp_link [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : IsCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hAcomp : ∀ x ∈ A, ∀ (h0 : 0 < f.length), G.Adj (f[0]'h0) x)
    (i₀ : ℕ) (hi₀ : i₀ < f.length) (hi₀pos : 1 ≤ i₀)
    (hb₀ : ∃ b ∈ B, G.Adj (f[i₀]'hi₀) b)
    (hnotcomp : ∃ b ∈ B, ¬ G.Adj (f[i₀]'hi₀) b)
    (hminB : ∀ (j : ℕ) (hj : j < f.length), j < i₀ → ∀ b ∈ B, ¬ G.Adj (f[j]'hj) b) :
    False := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD, hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inl (Or.inl (Or.inr h))
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  -- the square with `f_i` adjacent to `b₁` and not to `b₂`
  obtain ⟨b, hbB, hbadj⟩ := hb₀
  obtain ⟨b', hb'B, hb'adj⟩ := hnotcomp
  obtain ⟨a₁, b₁, b₂, a₂, hsq, hb₁P, hb₂P⟩ :=
    exists_square_cross_right sAB {x : V | G.Adj (f[i₀]'hi₀) x} ⟨b, hbB, hbadj⟩
      ⟨b', hb'B, hb'adj⟩
  have ha₁A : a₁ ∈ A := hsq.2.1
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  -- decoding membership in the initial stretch `f₁-⋯-f_i`
  have hmemtake : ∀ x ∈ f.take (i₀ + 1), ∃ (j : ℕ) (hj : j < f.length), j ≤ i₀ ∧ f[j]'hj = x := by
    intro x hx
    obtain ⟨j, hj, hji, hjx⟩ := mem_take_iff.mp hx
    exact ⟨j, hj, by omega, hjx⟩
  have hnoB_take : ∀ (j : ℕ) (hj : j < f.length), j ≤ i₀ → ¬ G.Adj (f[j]'hj) b₂ := by
    intro j hj hji
    rcases Nat.lt_or_ge j i₀ with h | h
    · exact hminB j hj h b₂ hb₂B
    · have : j = i₀ := by omega
      subst this
      exact hb₂P
  have hlink : VertexLinkedOntoTriangle G b₁ (f[0]'hfpos) a₁ a₂
      (f.take (i₀ + 1)) [a₁] [b₂, a₂] := by
    refine ⟨⟨PathBasics.isPathList_take hfpath (by omega),
        PathBasics.isPathList_singleton G a₁, PathBasics.isPathList_pair e23⟩,
      ⟨?_, ?_, ?_⟩, ⟨?_, Or.inl rfl, Or.inr rfl⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro x hx hmem
      obtain ⟨j, hj, -, rfl⟩ := hmemtake x hx
      simp only [List.mem_singleton] at hmem
      exact hfne _ (List.getElem_mem hj) a₁ (hmA ha₁A) hmem
    · intro x hx hmem
      obtain ⟨j, hj, -, rfl⟩ := hmemtake x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · exact hfne _ (List.getElem_mem hj) b₂ (hmB hb₂B) h
      · exact hfne _ (List.getElem_mem hj) a₂ (hmA ha₂A) h
    · intro x hx hmem
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · exact ne02 h
      · exact ne03 h
    · exact Or.inl (by
        rw [List.head?_eq_getElem?,
          List.getElem?_eq_getElem (show 0 < (f.take (i₀ + 1)).length by
            simp only [List.length_take]; omega)]
        exact congrArg some (by simp))
    · intro x hx y hy
      obtain ⟨j, hj, hji, rfl⟩ := hmemtake x hx
      simp only [List.mem_singleton] at hy
      subst hy
      constructor
      · intro hadj
        exact ⟨(getElem_eq_iff hfnd hj hfpos).mpr (huniqA j hj ⟨y, ha₁A, hadj.symm⟩), rfl⟩
      · rintro ⟨h, -⟩
        rw [h]
        exact hAcomp y ha₁A hfpos
    · intro x hx y hy
      obtain ⟨j, hj, hji, rfl⟩ := hmemtake x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · constructor
        · intro hadj; exact absurd hadj (hnoB_take j hj hji)
        · rintro ⟨-, h⟩; exact absurd h ne23
      · constructor
        · intro hadj
          exact ⟨(getElem_eq_iff hfnd hj hfpos).mpr (huniqA j hj ⟨y, ha₂A, hadj.symm⟩), rfl⟩
        · rintro ⟨h, -⟩
          rw [h]
          exact hAcomp y ha₂A hfpos
    · intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · constructor
        · intro hadj; exact absurd hadj n02
        · rintro ⟨-, h⟩; exact absurd h ne23
      · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => e30.symm⟩
    · exact ⟨f[i₀]'hi₀,
        mem_take_iff.mpr ⟨i₀, hi₀, by omega, rfl⟩, hb₁P.symm⟩
    · exact ⟨a₁, by simp, e01.symm⟩
    · exact ⟨b₂, by simp, e12⟩
  have h24 := Workspace.Statements.S02.SPGT.thm_2_4 G hG.1.1 b₁ (f[0]'hfpos) a₁ a₂
    ⟨_, _, _, hlink⟩
  have hnf0 : ¬ G.Adj b₁ (f[0]'hfpos) := by
    intro hadj
    exact hminB 0 hfpos (by omega) b₁ hb₁B hadj.symm
  rcases h24 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact hnf0 h
  · exact hnf0 h
  · exact n13 h

/-- The `f₁`-is-`A`-complete half of claim (1). -/
theorem claim_one_odd_Acomp [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hnoC : ∀ c ∈ C, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj c (f[i]'hi))
    (hodd : Odd f.length)
    (hAcomp : ∀ x ∈ A, ∀ (h0 : 0 < f.length), G.Adj (f[0]'h0) x) : False := by
  classical
  have hcfg_saved : PathConfig G A B C D f a d := hcfg
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD,
    hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hk3 : 3 ≤ f.length := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inr h))
  have hmC : ∀ {u : V}, u ∈ C → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inr h)
  have hmD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  have hnoB0 : ∀ b ∈ B, ¬ G.Adj (f[0]'hfpos) b := by
    intro b hbB hfb
    obtain ⟨a', ha'A, hba'⟩ := exists_not_adj_left sAB hbB
    have hf0minor := hfminor (f[0]'hfpos) (List.getElem_mem hfpos)
    have ha'N : a' ∈ G.neighborSet (f[0]'hfpos) ∩ (A ∪ B ∪ C ∪ D) ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using hAcomp a' ha'A hfpos, hmA ha'A⟩,
        Or.inl ha'A⟩
    have hbN : b ∈ G.neighborSet (f[0]'hfpos) ∩ (A ∪ B ∪ C ∪ D) ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using hfb, hmB hbB⟩, Or.inl hbB⟩
    exact hba' (hf0minor.2.2 a' ha'N b hbN).symm
  by_cases hBF : ∃ (i : ℕ) (hi : i < f.length), ∃ b ∈ B, G.Adj (f[i]'hi) b
  · let Q : ℕ → Prop := fun i => ∃ hi : i < f.length, ∃ b ∈ B, G.Adj (f[i]'hi) b
    have hQ : ∃ i, Q i := hBF
    let i₀ : ℕ := Nat.find hQ
    obtain ⟨hi₀, b₀, hb₀B, hb₀⟩ := Nat.find_spec hQ
    have hminB : ∀ (j : ℕ) (hj : j < f.length), j < i₀ →
        ∀ b ∈ B, ¬ G.Adj (f[j]'hj) b := by
      intro j hj hji b hbB hjb
      have hle : i₀ ≤ j := Nat.find_min' hQ ⟨hj, b, hbB, hjb⟩
      omega
    have hi₀pos : 1 ≤ i₀ := by
      by_contra h
      have hi₀zero : i₀ = 0 := by omega
      have hbzero : G.Adj (f[0]'hfpos) b₀ := by
        simpa only [i₀, hi₀zero] using hb₀
      exact hnoB0 b₀ hb₀B hbzero
    by_cases hBcomp : ∀ b ∈ B, G.Adj (f[i₀]'hi₀) b
    · obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left sAB haA
      have ha₂A : a₂ ∈ A := hsq.2.2.1
      have hb₁B : b₁ ∈ B := hsq.2.2.2.1
      have hb₂B : b₂ ∈ B := hsq.2.2.2.2
      obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
        CubeMajorCoreContradiction.square_adj hsq
      have hmemtake : ∀ x ∈ f.take (i₀ + 1),
          ∃ (j : ℕ) (hj : j < f.length), j ≤ i₀ ∧ f[j]'hj = x := by
        intro x hx
        obtain ⟨j, hj, hji, hjx⟩ := mem_take_iff.mp hx
        exact ⟨j, hj, by omega, hjx⟩
      have hP₃ : IsPathFrom G (f.take (i₀ + 1)) (f[0]'hfpos) (f[i₀]'hi₀) :=
        isPathFrom_take hfpath hi₀pos hi₀
      have hcross12 : ∀ u ∈ [a, b₁], ∀ v ∈ [a₂, b₂],
          (G.Adj u v ↔ (u = a ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)) := by
        intro u hu v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
        · exact ⟨fun hadj => absurd hadj n02,
            by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [absurd h ne23, absurd h ne01]⟩
        · exact ⟨fun hadj => absurd hadj n13,
            by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [absurd h ne01.symm, absurd h ne23.symm]⟩
        · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => e12⟩
      have hcross13 : ∀ u ∈ [a, b₁], ∀ v ∈ f.take (i₀ + 1),
          (G.Adj u v ↔ (u = a ∧ v = f[0]'hfpos) ∨
            (u = b₁ ∧ v = f[i₀]'hi₀)) := by
        intro u hu v hv
        obtain ⟨j, hj, hji, rfl⟩ := hmemtake v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hua | hub
        · subst u
          constructor
          · intro hadj
            have hj0 := huniqA j hj ⟨a, haA, hadj⟩
            exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hj hfpos).mpr hj0⟩
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · rw [h]; exact (hAcomp a haA hfpos).symm
            · exact absurd h ne01
        · subst u
          constructor
          · intro hadj
            have hjnlt : ¬ j < i₀ := fun hlt => hminB j hj hlt b₁ hb₁B hadj.symm
            have hji₀ : j = i₀ := by omega
            exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hj hi₀).mpr hji₀⟩
          · rintro (⟨h, -⟩ | ⟨-, h⟩)
            · exact absurd h ne01.symm
            · rw [h]; exact (hBcomp b₁ hb₁B).symm
      have hcross23 : ∀ u ∈ [a₂, b₂], ∀ v ∈ f.take (i₀ + 1),
          (G.Adj u v ↔ (u = a₂ ∧ v = f[0]'hfpos) ∨
            (u = b₂ ∧ v = f[i₀]'hi₀)) := by
        intro u hu v hv
        obtain ⟨j, hj, hji, rfl⟩ := hmemtake v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hua | hub
        · subst u
          constructor
          · intro hadj
            have hj0 := huniqA j hj ⟨a₂, ha₂A, hadj⟩
            exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hj hfpos).mpr hj0⟩
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · rw [h]; exact (hAcomp a₂ ha₂A hfpos).symm
            · exact absurd h ne23.symm
        · subst u
          constructor
          · intro hadj
            have hjnlt : ¬ j < i₀ := fun hlt => hminB j hj hlt b₂ hb₂B hadj.symm
            have hji₀ : j = i₀ := by omega
            exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hj hi₀).mpr hji₀⟩
          · rintro (⟨h, -⟩ | ⟨-, h⟩)
            · exact absurd h ne23
            · rw [h]; exact (hBcomp b₂ hb₂B).symm
      have hprism : FormPrism G ![a, a₂, f[0]'hfpos] ![b₁, b₂, f[i₀]'hi₀]
          [a, b₁] [a₂, b₂] (f.take (i₀ + 1)) := by
        refine formPrism_of_data e30.symm (hAcomp a haA hfpos).symm
          (hAcomp a₂ ha₂A hfpos).symm e12 (hBcomp b₁ hb₁B).symm
          (hBcomp b₂ hb₂B).symm ne01 ne02
          (hfne _ (List.getElem_mem hi₀) a (hmA haA)).symm ne13.symm ne23.symm
          (hfne _ (List.getElem_mem hi₀) a₂ (hmA ha₂A)).symm
          (hfne _ (List.getElem_mem hfpos) b₁ (hmB hb₁B))
          (hfne _ (List.getElem_mem hfpos) b₂ (hmB hb₂B))
          (fun he => by
            have := (getElem_eq_iff hfnd hfpos hi₀).mp he
            omega)
          ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
          ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩ hP₃ hcross12 hcross13 hcross23
      have hi₀eq : i₀ = 1 := by
        by_contra hne
        have hlong : 1 < pathLength (f.take (i₀ + 1)) := by
          simp only [pathLength, List.length_take]
          omega
        exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inr (Or.inr hlong)⟩
      have hi1 : 1 < f.length := by omega
      have hf01 : G.Adj (f[0]'hfpos) (f[1]'hi1) := by
        rw [PathBasics.path_adj_iff hfpath hfpos hi1]
        omega
      obtain ⟨c, hcC, hcd⟩ := exists_adj_of_mem_right dCD sCD hdD
      have hf0D : ∀ z ∈ D, ¬ G.Adj (f[0]'hfpos) z := by
        intro z hz hadj
        have hz0 := huniqD 0 hfpos ⟨z, hz, hadj.symm⟩
        omega
      have hf1D : ∀ z ∈ D, ¬ G.Adj (f[1]'hi1) z := by
        intro z hz hadj
        have hz1 := huniqD 1 hi1 ⟨z, hz, hadj.symm⟩
        omega
      have hsquare : IsSquare Gᶜ (C ∪ {f[0]'hfpos}) (D ∪ {f[1]'hi1})
          (f[0]'hfpos) d (f[1]'hi1) c := by
        refine ⟨?_, Or.inr rfl, Or.inl hcC, Or.inl hdD, Or.inr rfl⟩
        apply FiveHoleBasics.isHoleList_four
        · apply FiveHoleBasics.nodup_four
          · exact hfne _ (List.getElem_mem hfpos) d (hmD hdD)
          · intro he
            have := (getElem_eq_iff hfnd hfpos hi1).mp he
            omega
          · exact hfne _ (List.getElem_mem hfpos) c (hmC hcC)
          · exact (hfne _ (List.getElem_mem hi1) d (hmD hdD)).symm
          · intro he
            exact Set.disjoint_left.mp dCD hcC (he ▸ hdD)
          · exact hfne _ (List.getElem_mem hi1) c (hmC hcC)
        · simpa [SimpleGraph.compl_adj] using
            ⟨(hfne _ (List.getElem_mem hfpos) d (hmD hdD)), hf0D d hdD⟩
        · simpa [SimpleGraph.compl_adj] using
            ⟨(hfne _ (List.getElem_mem hi1) d (hmD hdD)).symm,
              fun h => hf1D d hdD h.symm⟩
        · simpa [SimpleGraph.compl_adj] using
            ⟨hfne _ (List.getElem_mem hi1) c (hmC hcC),
              fun h => hnoC c hcC 1 hi1 h.symm⟩
        · simpa [SimpleGraph.compl_adj] using
            ⟨(hfne _ (List.getElem_mem hfpos) c (hmC hcC)).symm,
              hnoC c hcC 0 hfpos⟩
        · simp only [SimpleGraph.compl_adj, not_and, not_not]
          exact fun _ => hf01
        · simp only [SimpleGraph.compl_adj, not_and, not_not]
          exact fun _ => hcd.symm
      have hsCD : SquareConnected Gᶜ (C ∪ {f[0]'hfpos}) (D ∪ {f[1]'hi1}) := by
        apply squareConnected_adjoin_both sCD
          (fun h => hfout _ (List.getElem_mem hfpos) (Or.inl (Or.inr h)))
          (fun h => hfout _ (List.getElem_mem hi1) (Or.inr h))
        · exact ⟨d, f[1]'hi1, c, hsquare, hcC⟩
        · exact ⟨c, d, f[0]'hfpos, isSquare_rev hsquare, hdD⟩
      have hnewcube : IsCube G A B (C ∪ {f[0]'hfpos}) (D ∪ {f[1]'hi1}) := by
        refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, nA, nB, nC.mono Set.subset_union_left,
          nD.mono Set.subset_union_left⟩, ⟨?_, ?_, ?_, ?_⟩, sAB, hsCD⟩
        · exact dAB
        · rw [Set.disjoint_left]
          rintro x hx (hxC | hx0)
          · exact Set.disjoint_left.mp dAC hx hxC
          · rw [Set.mem_singleton_iff] at hx0
            subst x
            exact hfout _ (List.getElem_mem hfpos) (hmA hx)
        · rw [Set.disjoint_left]
          rintro x hx (hxD | hx1)
          · exact Set.disjoint_left.mp dAD hx hxD
          · rw [Set.mem_singleton_iff] at hx1
            subst x
            exact hfout _ (List.getElem_mem hi1) (hmA hx)
        · rw [Set.disjoint_left]
          rintro x hx (hxC | hx0)
          · exact Set.disjoint_left.mp dBC hx hxC
          · rw [Set.mem_singleton_iff] at hx0
            subst x
            exact hfout _ (List.getElem_mem hfpos) (hmB hx)
        · rw [Set.disjoint_left]
          rintro x hx (hxD | hx1)
          · exact Set.disjoint_left.mp dBD hx hxD
          · rw [Set.mem_singleton_iff] at hx1
            subst x
            exact hfout _ (List.getElem_mem hi1) (hmB hx)
        · rw [Set.disjoint_left]
          rintro x (hxC | hx0) (hxD | hx1)
          · exact Set.disjoint_left.mp dCD hxC hxD
          · rw [Set.mem_singleton_iff] at hx1
            subst x
            exact hfout _ (List.getElem_mem hi1) (hmC hxC)
          · rw [Set.mem_singleton_iff] at hx0
            subst x
            exact hfout _ (List.getElem_mem hfpos) (hmD hxD)
          · rw [Set.mem_singleton_iff] at hx0 hx1
            have := (getElem_eq_iff hfnd hfpos hi1).mp (hx0.symm.trans hx1)
            omega
        · rintro x hx y (hyC | hy0)
          · exact cAC x hx y hyC
          · rw [Set.mem_singleton_iff] at hy0
            subst y
            exact (hAcomp x hx hfpos).symm
        · rintro x hx y (hyD | hy1)
          · exact cBD x hx y hyD
          · rw [Set.mem_singleton_iff] at hy1
            subst y
            simpa [hi₀eq] using (hBcomp x hx).symm
        · rintro x hx y (hyD | hy1)
          · exact aAD x hx y hyD
          · rw [Set.mem_singleton_iff] at hy1
            subst y
            intro hadj
            have := huniqA 1 hi1 ⟨x, hx, hadj⟩
            omega
        · rintro x hx y (hyC | hy0)
          · exact aBC x hx y hyC
          · rw [Set.mem_singleton_iff] at hy0
            subst y
            intro hadj
            exact hnoB0 x hx hadj.symm
      obtain ⟨-, -, hCeq, -⟩ := hcube.2 A B (C ∪ {f[0]'hfpos})
        (D ∪ {f[1]'hi1}) hnewcube (le_refl A) (le_refl B)
        Set.subset_union_left Set.subset_union_left
      have hf0C' : f[0]'hfpos ∈ C ∪ {f[0]'hfpos} := Or.inr (by simp)
      have hf0C : f[0]'hfpos ∈ C := by
        rw [hCeq]
        exact hf0C'
      exact hfout _ (List.getElem_mem hfpos) (hmC hf0C)
    · push_neg at hBcomp
      obtain ⟨b', hb'B, hb'⟩ := hBcomp
      exact claim_one_odd_Acomp_link hG hcube.1 hcfg_saved hAcomp i₀ hi₀ hi₀pos
        ⟨b₀, hb₀B, hb₀⟩ ⟨b', hb'B, hb'⟩ hminB
  · have hnoB : ∀ b ∈ B, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj b (f[i]'hi) := by
      intro b hb i hi hadj
      exact hBF ⟨i, hi, b, hb, hadj.symm⟩
    exact claim_one_odd_Acomp_noB hG hcube.1 hcfg_saved hk3 hAcomp hnoB

/-- The non-`A`-complete half of claim (1). -/
theorem claim_one_odd_notAcomp [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hnoC : ∀ c ∈ C, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj c (f[i]'hi))
    (hodd : Odd f.length)
    (hnotAcomp : ¬ ∀ x ∈ A, ∀ (h0 : 0 < f.length), G.Adj (f[0]'h0) x) : False := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD,
    hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inr h))
  have hmC : ∀ {u : V}, u ∈ C → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inr h)
  have hmD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  push_neg at hnotAcomp
  obtain ⟨a', ha'A, h0, ha'non⟩ := hnotAcomp
  obtain ⟨a₁, b₁, b₂, a₂, hsq, ha₁P, ha₂P⟩ :=
    exists_square_cross_left sAB {x : V | G.Adj (f[0]'hfpos) x}
      ⟨a, haA, ((hadjA 0 hfpos).mpr rfl).symm⟩ ⟨a', ha'A, ha'non⟩
  have ha₁A : a₁ ∈ A := hsq.2.1
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  have hnoa₂ : ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj a₂ (f[i]'hi) := by
    intro i hi hadj
    have hi0 := huniqA i hi ⟨a₂, ha₂A, hadj⟩
    subst i
    exact ha₂P hadj.symm
  have hreturn : IsPathFrom G [d, b₂, a₂] d a₂ := by
    refine ⟨isPathList_triple ?_ (cBD b₂ hb₂B d hdD).symm e23
      (fun h => aAD a₂ ha₂A d hdD h.symm), ?_, ?_⟩
    · have hdb : d ≠ b₂ := fun he => Set.disjoint_left.mp dBD hb₂B (he ▸ hdD)
      have hda : d ≠ a₂ := fun he => Set.disjoint_left.mp dAD ha₂A (he ▸ hdD)
      simp [hdb, hda, ne23]
    · rfl
    · rfl
  have hb₂F : ∃ (i : ℕ) (hi : i < f.length), G.Adj b₂ (f[i]'hi) := by
    by_contra hnone
    push_neg at hnone
    have hhole : IsHoleList G ([a₁] ++ f ++ [d, b₂, a₂]) := by
      refine isHoleList_three_blocks
        (P₀ := [a₁]) (P₁ := f) (P₂ := [d, b₂, a₂])
        (s₀ := a₁) (t₀ := a₁) (s₁ := f[0]'hfpos)
        (t₁ := f[f.length - 1]'(by omega)) (s₂ := d) (t₂ := a₂)
        ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩
        (isPathFrom_self hfpath hfpos)
        hreturn ?_ ?_ ?_ ?_ ?_ ?_ (by simp)
      · intro x hx hx'
        simp only [List.mem_singleton] at hx
        subst x
        exact hfout _ hx' (hmA ha₁A)
      · intro x hx hmem
        simp only [List.mem_singleton] at hx
        subst x
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h
        · exact Set.disjoint_left.mp dAD ha₁A (h ▸ hdD)
        · exact ne02 h
        · exact ne03 h
      · intro x hx hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h
        · exact hfne x hx d (hmD hdD) h
        · exact hfne x hx b₂ (hmB hb₂B) h
        · exact hfne x hx a₂ (hmA ha₂A) h
      · intro x hx y hy
        simp only [List.mem_singleton] at hx
        subst x
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
        constructor
        · intro hadj
          have hi0 := huniqA i hi ⟨a₁, ha₁A, hadj⟩
          exact ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr hi0⟩
        · rintro ⟨-, h⟩
          rw [h]
          exact ha₁P.symm
      · intro x hx y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with hyd | hyb | hya
        · subst y
          constructor
          · intro hadj
            have hiLast := huniqD i hi ⟨d, hdD, hadj.symm⟩
            exact ⟨(getElem_eq_iff hfnd hi (by omega)).mpr hiLast, rfl⟩
          · rintro ⟨h, -⟩
            have hiLast := (getElem_eq_iff hfnd hi (by omega)).mp h
            exact ((hadjD i hi).mpr hiLast).symm
        · subst y
          constructor
          · exact fun hadj => absurd hadj.symm (hnone i hi)
          · rintro ⟨-, h⟩
            exfalso
            exact Set.disjoint_left.mp dBD hb₂B (h ▸ hdD)
        · subst y
          constructor
          · exact fun hadj => absurd hadj.symm (hnoa₂ i hi)
          · rintro ⟨-, h⟩
            exfalso
            exact Set.disjoint_left.mp dAD ha₂A (h ▸ hdD)
      · intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst y
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hxd | hxb | hxa
        · subst x
          constructor
          · intro hadj
            exfalso
            exact aAD a₁ ha₁A d hdD hadj.symm
          · rintro ⟨h, -⟩
            exfalso
            exact Set.disjoint_left.mp dAD ha₂A (h ▸ hdD)
        · subst x
          constructor
          · intro hadj
            exfalso
            exact n02 hadj.symm
          · rintro ⟨h, -⟩
            exfalso
            exact ne23 h
        · subst x
          exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => e30⟩
    have hev := no_odd_hole hG.1.1 hhole
    simp only [List.length_append, List.length_cons, List.length_nil] at hev
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨n, hn⟩ := hev
    omega
  let Q : ℕ → Prop := fun i => ∃ hi : i < f.length, G.Adj b₂ (f[i]'hi)
  have hQ : ∃ i, Q i := hb₂F
  let i₀ : ℕ := Nat.find hQ
  obtain ⟨hi₀, hb₂i⟩ := Nat.find_spec hQ
  have hminb₂ : ∀ (j : ℕ) (hj : j < f.length), j < i₀ → ¬ G.Adj b₂ (f[j]'hj) := by
    intro j hj hji hadj
    have hle : i₀ ≤ j := Nat.find_min' hQ ⟨hj, hadj⟩
    omega
  have hi₀pos : 1 ≤ i₀ := by
    by_contra h
    have hi₀zero : i₀ = 0 := by omega
    have hb₂0 : G.Adj b₂ (f[0]'hfpos) := by
      simpa only [i₀, hi₀zero] using hb₂i
    have hf0minor := hfminor (f[0]'hfpos) (List.getElem_mem hfpos)
    have ha₁N : a₁ ∈ G.neighborSet (f[0]'hfpos) ∩ (A ∪ B ∪ C ∪ D) ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using ha₁P, hmA ha₁A⟩, Or.inl ha₁A⟩
    have hb₂N : b₂ ∈ G.neighborSet (f[0]'hfpos) ∩ (A ∪ B ∪ C ∪ D) ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using hb₂0.symm, hmB hb₂B⟩, Or.inl hb₂B⟩
    exact n02 (hf0minor.2.2 a₁ ha₁N b₂ hb₂N)
  have hmemtake : ∀ x ∈ f.take (i₀ + 1),
      ∃ (j : ℕ) (hj : j < f.length), j ≤ i₀ ∧ f[j]'hj = x := by
    intro x hx
    obtain ⟨j, hj, hji, hjx⟩ := mem_take_iff.mp hx
    exact ⟨j, hj, by omega, hjx⟩
  have hjump : ∀ d' ∈ D, i₀ = f.length - 1 ∧ G.Adj (f[f.length - 1]'(by omega)) d' := by
    intro d' hd'D
    obtain ⟨c', hc'C, hc'd'⟩ := exists_adj_of_mem_right dCD sCD hd'D
    let av : Fin 3 → V := ![a₁, a₂, c']
    let bv : Fin 3 → V := ![b₁, b₂, d']
    let Rv : Fin 3 → List V := ![[a₁, b₁], [a₂, b₂], [c', d']]
    let Kp : Set V := {v : V | v ∈ Rv 0} ∪ {v : V | v ∈ Rv 1} ∪ {v : V | v ∈ Rv 2}
    let Fp : Set V := {v : V | v ∈ f.take (i₀ + 1)}
    have ha₁c' : a₁ ≠ c' := by
      intro h
      exact Set.disjoint_left.mp dAC ha₁A (h ▸ hc'C)
    have ha₁d' : a₁ ≠ d' := by
      intro h
      exact Set.disjoint_left.mp dAD ha₁A (h ▸ hd'D)
    have hb₁c' : b₁ ≠ c' := by
      intro h
      exact Set.disjoint_left.mp dBC hb₁B (h ▸ hc'C)
    have hb₁d' : b₁ ≠ d' := by
      intro h
      exact Set.disjoint_left.mp dBD hb₁B (h ▸ hd'D)
    have ha₂c' : a₂ ≠ c' := by
      intro h
      exact Set.disjoint_left.mp dAC ha₂A (h ▸ hc'C)
    have ha₂d' : a₂ ≠ d' := by
      intro h
      exact Set.disjoint_left.mp dAD ha₂A (h ▸ hd'D)
    have hb₂c' : b₂ ≠ c' := by
      intro h
      exact Set.disjoint_left.mp dBC hb₂B (h ▸ hc'C)
    have hb₂d' : b₂ ≠ d' := by
      intro h
      exact Set.disjoint_left.mp dBD hb₂B (h ▸ hd'D)
    have hc'ne_d' : c' ≠ d' := by
      intro h
      exact Set.disjoint_left.mp dCD hc'C (h ▸ hd'D)
    have hcross12 : ∀ u ∈ [a₁, b₁], ∀ v ∈ [a₂, b₂],
        (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)) := by
      intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · subst u; subst v; simp [e30.symm]
      · subst u; subst v; simp [n02, ne01, ne23]
      · subst u; subst v; simp [n13, ne01.symm, ne23.symm]
      · subst u; subst v; simp [e12]
    have hcross13 : ∀ u ∈ [a₁, b₁], ∀ v ∈ [c', d'],
        (G.Adj u v ↔ (u = a₁ ∧ v = c') ∨ (u = b₁ ∧ v = d')) := by
      intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · subst u; subst v
        simp [cAC a₁ ha₁A c' hc'C]
      · subst u; subst v
        simp [aAD a₁ ha₁A d' hd'D, ne01, hc'ne_d'.symm]
      · subst u; subst v
        simp [aBC b₁ hb₁B c' hc'C, ne01.symm, hc'ne_d']
      · subst u; subst v
        simp [cBD b₁ hb₁B d' hd'D]
    have hcross23 : ∀ u ∈ [a₂, b₂], ∀ v ∈ [c', d'],
        (G.Adj u v ↔ (u = a₂ ∧ v = c') ∨ (u = b₂ ∧ v = d')) := by
      intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · subst u; subst v
        simp [cAC a₂ ha₂A c' hc'C]
      · subst u; subst v
        simp [aAD a₂ ha₂A d' hd'D, ne23.symm, hc'ne_d'.symm]
      · subst u; subst v
        simp [aBC b₂ hb₂B c' hc'C, ne23, hc'ne_d']
      · subst u; subst v
        simp [cBD b₂ hb₂B d' hd'D]
    have hprism : FormPrism G av bv (Rv 0) (Rv 1) (Rv 2) := by
      exact formPrism_of_data (G := G)
        e30.symm (cAC a₁ ha₁A c' hc'C) (cAC a₂ ha₂A c' hc'C)
        e12 (cBD b₁ hb₁B d' hd'D) (cBD b₂ hb₂B d' hd'D)
        ne01 ne02 ha₁d'
        ne13.symm ne23.symm ha₂d'
        hb₁c'.symm hb₂c'.symm hc'ne_d'
        ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
        ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
        ⟨PathBasics.isPathList_pair hc'd', rfl, rfl⟩
        hcross12 hcross13 hcross23
    have hKsub : Kp ⊆ A ∪ B ∪ C ∪ D := by
      intro x hx
      have hx' : ((x = a₁ ∨ x = b₁) ∨ (x = a₂ ∨ x = b₂)) ∨
          (x = c' ∨ x = d') := by
        simpa [Kp, Rv] using hx
      rcases hx' with (hAB | hAB') | hCD
      · rcases hAB with h | h
        · subst x; exact hmA ha₁A
        · subst x; exact hmB hb₁B
      · rcases hAB' with h | h
        · subst x; exact hmA ha₂A
        · subst x; exact hmB hb₂B
      · rcases hCD with h | h
        · subst x; exact hmC hc'C
        · subst x; exact hmD hd'D
    have hFpK : Fp ⊆ Kpᶜ := by
      intro x hx hxK
      exact hfout x (List.take_subset _ _ hx) (hKsub hxK)
    have hFpconn : ConnectedSet G Fp := by
      apply InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      exact PathBasics.isPathList_take hfpath (by omega)
    have hnoa₂att : a₂ ∉ attachments G Fp Kp := by
      rintro ⟨-, z, hz, haz⟩
      obtain ⟨j, hj, -, rfl⟩ := hmemtake z hz
      exact hnoa₂ j hj haz
    have ha₁att : a₁ ∈ attachments G Fp Kp := by
      refine ⟨?_, f[0]'hfpos, ?_, ha₁P.symm⟩
      · simp [Kp, Rv]
      · exact mem_take_iff.mpr ⟨0, hfpos, by omega, rfl⟩
    have hb₂att : b₂ ∈ attachments G Fp Kp := by
      refine ⟨?_, f[i₀]'hi₀, ?_, hb₂i⟩
      · simp [Kp, Rv]
      · exact mem_take_iff.mpr ⟨i₀, hi₀, by omega, rfl⟩
    have hnonlocal : ¬ LocalForPrism av bv (Rv 0) (Rv 1) (Rv 2)
        (attachments G Fp Kp) := by
      rintro (h | h | h | h | h)
      · have := h hb₂att
        simp [Rv, ne02.symm, ne12.symm] at this
      · have := h ha₁att
        simp [Rv, ne03, ne02] at this
      · have := h ha₁att
        have hA_C : a₁ ≠ c' := fun he => Set.disjoint_left.mp dAC ha₁A (he ▸ hc'C)
        have hA_D : a₁ ≠ d' := fun he => Set.disjoint_left.mp dAD ha₁A (he ▸ hd'D)
        simp [Rv, hA_C, hA_D] at this
      · have := h hb₂att
        have hB_A : b₂ ≠ a₁ := ne02.symm
        have hB_A2 : b₂ ≠ a₂ := ne23
        have hB_C : b₂ ≠ c' := fun he => Set.disjoint_left.mp dBC hb₂B (he ▸ hc'C)
        simp [av, hB_A, hB_A2, hB_C] at this
      · have := h ha₁att
        have hA_B1 : a₁ ≠ b₁ := ne01
        have hA_B2 : a₁ ≠ b₂ := ne02
        have hA_D : a₁ ≠ d' := fun he => Set.disjoint_left.mp dAD ha₁A (he ▸ hd'D)
        simp [bv, hA_B1, hA_B2, hA_D] at this
    have hnomaj : IsEvenPrism G av bv (Rv 0) (Rv 1) (Rv 2) →
        ∀ v ∈ Fp, ¬ MajorForPrism G av bv v := by
      intro _ v hv hmaj
      obtain ⟨j, hj, -, rfl⟩ := hmemtake v hv
      have hsub : (({av 0, av 1, av 2} : Set V) ∩ G.neighborSet (f[j]'hj)) ⊆ {a₁} := by
        intro x hx
        have hxtri : x = a₁ ∨ x = a₂ ∨ x = c' := by simpa [av] using hx.1
        rcases hxtri with h | h | h
        · simpa [h]
        · subst x
          exact absurd hx.2 (by
            simpa [SimpleGraph.mem_neighborSet] using fun hadj => hnoa₂ j hj hadj.symm)
        · subst x
          exact absurd hx.2 (by
            simpa [SimpleGraph.mem_neighborSet] using fun hadj => hnoC c' hc'C j hj hadj.symm)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hone : ({a₁} : Set V).ncard = 1 := Set.ncard_singleton a₁
      have htwo : 2 ≤ (({av 0, av 1, av 2} : Set V) ∩
          G.neighborSet (f[j]'hj)).ncard := hmaj.1
      exact (by omega : False)
    have hexR : ∃ v ∈ attachments G Fp Kp, v ∈ Rv 2 := by
      by_contra hnone
      have hprefix : IsPathFrom G (f.take (i₀ + 1))
          (f[0]'hfpos) (f[i₀]'hi₀) := isPathFrom_take hfpath hi₀pos hi₀
      have htakeLen : (f.take (i₀ + 1)).length = i₀ + 1 :=
        List.length_take_of_le (by omega)
      have hnoR : ∀ x ∈ Rv 2, ∀ z ∈ f.take (i₀ + 1), ¬ G.Adj z x := by
        intro x hx z hz hzx
        apply hnone
        refine ⟨x, ⟨?_, z, hz, hzx.symm⟩, hx⟩
        change x ∈ {v : V | v ∈ Rv 0} ∪ {v : V | v ∈ Rv 1} ∪ {v : V | v ∈ Rv 2}
        exact Or.inr hx
      have hhole₂ : IsHoleList G ([a₁] ++ f.take (i₀ + 1) ++ [b₂, a₂]) := by
        refine isHoleList_three_blocks
          (P₀ := [a₁]) (P₁ := f.take (i₀ + 1)) (P₂ := [b₂, a₂])
          (s₀ := a₁) (t₀ := a₁) (s₁ := f[0]'hfpos) (t₁ := f[i₀]'hi₀)
          (s₂ := b₂) (t₂ := a₂)
          ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩ hprefix
          ⟨PathBasics.isPathList_pair e23, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro x hx hx'
          simp only [List.mem_singleton] at hx
          subst x
          exact hfout a₁ (List.take_subset _ _ hx') (hmA ha₁A)
        · intro x hx hmem
          simp only [List.mem_singleton] at hx
          subst x
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h
          · exact ne02 h
          · exact ne03 h
        · intro x hx hmem
          apply hfout x (List.take_subset _ _ hx)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · exact hmB hb₂B
          · exact hmA ha₂A
        · intro x hx y hy
          simp only [List.mem_singleton] at hx
          subst x
          obtain ⟨j, hj, -, rfl⟩ := hmemtake y hy
          constructor
          · intro hadj
            have hj0 := huniqA j hj ⟨a₁, ha₁A, hadj⟩
            exact ⟨rfl, (getElem_eq_iff hfnd hj hfpos).mpr hj0⟩
          · rintro ⟨-, h⟩
            rw [h]
            exact ha₁P.symm
        · intro x hx y hy
          obtain ⟨j, hj, hji, rfl⟩ := hmemtake x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · constructor
            · intro hadj
              have hnlt : ¬ j < i₀ := fun hlt => hminb₂ j hj hlt hadj.symm
              have hji₀ : j = i₀ := by omega
              exact ⟨(getElem_eq_iff hfnd hj hi₀).mpr hji₀, rfl⟩
            · rintro ⟨h, -⟩
              rw [h]
              exact hb₂i.symm
          · constructor
            · exact fun hadj => absurd hadj.symm (hnoa₂ j hj)
            · rintro ⟨-, h⟩
              exact absurd h.symm ne23
        · intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst y
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · constructor
            · exact fun hadj => absurd hadj.symm n02
            · rintro ⟨h, -⟩
              exact absurd h ne23
          · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => e30⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, htakeLen]
          omega
      have hreturn₃ : IsPathFrom G [b₂, d', c'] b₂ c' := by
        refine ⟨isPathList_triple ?_ (cBD b₂ hb₂B d' hd'D) hc'd'.symm
          (aBC b₂ hb₂B c' hc'C), rfl, rfl⟩
        simp [hb₂d', hb₂c', hc'ne_d'.symm]
      have hnoDprefix : ∀ z ∈ f.take (i₀ + 1), ¬ G.Adj z d' :=
        hnoR d' (by simp [Rv])
      have hnoCprefix : ∀ z ∈ f.take (i₀ + 1), ¬ G.Adj z c' :=
        hnoR c' (by simp [Rv])
      have hnoD'a₁ : ¬ G.Adj d' a₁ :=
        fun h => aAD a₁ ha₁A d' hd'D h.symm
      have hc'a₁ : G.Adj c' a₁ := (cAC a₁ ha₁A c' hc'C).symm
      have hhole₃ : IsHoleList G ([a₁] ++ f.take (i₀ + 1) ++ [b₂, d', c']) := by
        refine isHoleList_three_blocks
          (P₀ := [a₁]) (P₁ := f.take (i₀ + 1)) (P₂ := [b₂, d', c'])
          (s₀ := a₁) (t₀ := a₁) (s₁ := f[0]'hfpos) (t₁ := f[i₀]'hi₀)
          (s₂ := b₂) (t₂ := c')
          ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩ hprefix hreturn₃
          ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro x hx hx'
          simp only [List.mem_singleton] at hx
          subst x
          exact hfout a₁ (List.take_subset _ _ hx') (hmA ha₁A)
        · intro x hx hmem
          simp only [List.mem_singleton] at hx
          subst x
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h | h
          · exact ne02 h
          · exact ha₁d' h
          · exact ha₁c' h
        · intro x hx hmem
          apply hfout x (List.take_subset _ _ hx)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact hmB hb₂B
          · exact hmD hd'D
          · exact hmC hc'C
        · intro x hx y hy
          simp only [List.mem_singleton] at hx
          subst x
          obtain ⟨j, hj, -, rfl⟩ := hmemtake y hy
          constructor
          · intro hadj
            have hj0 := huniqA j hj ⟨a₁, ha₁A, hadj⟩
            exact ⟨rfl, (getElem_eq_iff hfnd hj hfpos).mpr hj0⟩
          · rintro ⟨-, h⟩
            rw [h]
            exact ha₁P.symm
        · intro x hx y hy
          obtain ⟨j, hj, hji, rfl⟩ := hmemtake x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl
          · constructor
            · intro hadj
              have hnlt : ¬ j < i₀ := fun hlt => hminb₂ j hj hlt hadj.symm
              have hji₀ : j = i₀ := by omega
              exact ⟨(getElem_eq_iff hfnd hj hi₀).mpr hji₀, rfl⟩
            · rintro ⟨h, -⟩
              rw [h]
              exact hb₂i.symm
          · constructor
            · exact fun hadj => (hnoDprefix (f[j]'hj) hx hadj).elim
            · rintro ⟨-, h⟩
              exact absurd h.symm hb₂d'
          · constructor
            · exact fun hadj => (hnoCprefix (f[j]'hj) hx hadj).elim
            · rintro ⟨-, h⟩
              exact absurd h.symm hb₂c'
        · intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst y
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · constructor
            · exact fun hadj => absurd hadj.symm n02
            · rintro ⟨h, -⟩
              exact absurd h hb₂c'
          · constructor
            · exact fun hadj => (hnoD'a₁ hadj).elim
            · rintro ⟨h, -⟩
              exact absurd h.symm hc'ne_d'
          · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => hc'a₁⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, htakeLen]
          omega
      have heven₂ := no_odd_hole hG.1.1 hhole₂
      have heven₃ := no_odd_hole hG.1.1 hhole₃
      have hlen₂ : ([a₁] ++ f.take (i₀ + 1) ++ [b₂, a₂]).length = i₀ + 4 := by
        simp only [List.length_append, List.length_cons, List.length_nil, htakeLen]
        omega
      have hlen₃ : ([a₁] ++ f.take (i₀ + 1) ++ [b₂, d', c']).length = i₀ + 5 := by
        simp only [List.length_append, List.length_cons, List.length_nil, htakeLen]
        omega
      rw [hlen₂] at heven₂
      rw [hlen₃] at heven₃
      obtain ⟨m, hm⟩ := heven₂
      obtain ⟨n, hn⟩ := heven₃
      omega
    obtain ⟨v, ⟨hvK, z, hz, hvz⟩, hvR⟩ := hexR
    obtain ⟨j, hj, hji, rfl⟩ := hmemtake z hz
    have hvR' : v = c' ∨ v = d' := by simpa [Rv] using hvR
    rcases hvR' with hvc | hvd
    · subst v
      exact absurd hvz (hnoC c' hc'C j hj)
    · subst v
      have hjlast : j = f.length - 1 := huniqD j hj ⟨d', hd'D, hvz⟩
      have hiLast : i₀ = f.length - 1 := by omega
      refine ⟨hiLast, ?_⟩
      simpa [hjlast] using hvz.symm
  have hi₀last : i₀ = f.length - 1 := (hjump d hdD).1
  have hDcomp : ∀ d' ∈ D, G.Adj (f[f.length - 1]'(by omega)) d' :=
    fun d' hd' => (hjump d' hd').2
  obtain ⟨c, hcC, hcd⟩ := exists_adj_of_mem_right dCD sCD hdD
  have hlast : f.length - 1 < f.length := by omega
  have ha₁notf : a₁ ∉ f := by
    intro hmem
    exact hfout a₁ hmem (hmA ha₁A)
  have ha₁other : ∀ x ∈ f, x ≠ f[0]'hfpos → ¬ G.Adj a₁ x := by
    intro x hx hx0 hadj
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    have hjzero : j = 0 := huniqA j hj ⟨a₁, ha₁A, hjx ▸ hadj⟩
    apply hx0
    exact hjx.symm.trans ((getElem_eq_iff hfnd hj hfpos).mpr hjzero)
  have hP₁ : IsPathFrom G (a₁ :: f) a₁ (f[f.length - 1]'hlast) := by
    exact PathAttach.isPathFrom_cons (isPathFrom_self hfpath hfpos) ha₁P.symm
      ha₁notf ha₁other
  have hP₂ : IsPathFrom G [a₂, b₂] a₂ b₂ :=
    ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
  have hP₃ : IsPathFrom G [c, d] c d :=
    ⟨PathBasics.isPathList_pair hcd, rfl, rfl⟩
  have hb₂last : G.Adj (f[f.length - 1]'hlast) b₂ := by
    have helem : f[i₀]'hi₀ = f[f.length - 1]'hlast :=
      (getElem_eq_iff hfnd hi₀ hlast).mpr hi₀last
    rw [← helem]
    exact hb₂i.symm
  have hdlast : G.Adj (f[f.length - 1]'hlast) d :=
    ((hadjD (f.length - 1) hlast).mpr rfl).symm
  have hcross12long : ∀ u ∈ a₁ :: f, ∀ v ∈ [a₂, b₂],
      (G.Adj u v ↔
        (u = a₁ ∧ v = a₂) ∨ (u = f[f.length - 1]'hlast ∧ v = b₂)) := by
    intro u hu v hv
    simp only [List.mem_cons] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hu with hua₁ | huf
    · subst u
      rcases hv with hva₂ | hvb₂
      · subst v
        exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
      · subst v
        constructor
        · exact fun hadj => absurd hadj n02
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h ne23
          · exact absurd h (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A)).symm
    · obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp huf
      subst u
      rcases hv with hva₂ | hvb₂
      · subst v
        constructor
        · intro hadj
          exact (hnoa₂ j hj hadj.symm).elim
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (hfne _ (List.getElem_mem hj) a₁ (hmA ha₁A))
          · exact absurd h.symm ne23
      · subst v
        constructor
        · intro hadj
          have hjnotlt : ¬ j < i₀ := fun hji => hminb₂ j hj hji hadj.symm
          have hjeq : j = f.length - 1 := by omega
          exact Or.inr ⟨(getElem_eq_iff hfnd hj hlast).mpr hjeq, rfl⟩
        · rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact absurd h (hfne _ (List.getElem_mem hj) a₁ (hmA ha₁A))
          · rw [h]
            exact hb₂last
  have hcross13long : ∀ u ∈ a₁ :: f, ∀ v ∈ [c, d],
      (G.Adj u v ↔
        (u = a₁ ∧ v = c) ∨ (u = f[f.length - 1]'hlast ∧ v = d)) := by
    intro u hu v hv
    simp only [List.mem_cons] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hu with hua₁ | huf
    · subst u
      rcases hv with hvc | hvd
      · subst v
        exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => cAC a₁ ha₁A c hcC⟩
      · subst v
        constructor
        · exact fun hadj => absurd hadj (aAD a₁ ha₁A d hdD)
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h (fun he => Set.disjoint_left.mp dCD hcC (he ▸ hdD))
          · exact absurd h (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A)).symm
    · obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp huf
      subst u
      rcases hv with hvc | hvd
      · subst v
        constructor
        · exact fun hadj => absurd hadj.symm (hnoC c hcC j hj)
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (hfne _ (List.getElem_mem hj) a₁ (hmA ha₁A))
          · exact absurd h (fun he => Set.disjoint_left.mp dCD hcC (he ▸ hdD))
      · subst v
        constructor
        · intro hadj
          have hjeq : j = f.length - 1 := (hadjD j hj).mp hadj.symm
          exact Or.inr ⟨(getElem_eq_iff hfnd hj hlast).mpr hjeq, rfl⟩
        · rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact absurd h (hfne _ (List.getElem_mem hj) a₁ (hmA ha₁A))
          · rw [h]
            exact hdlast
  have hcross23long : ∀ u ∈ [a₂, b₂], ∀ v ∈ [c, d],
      (G.Adj u v ↔ (u = a₂ ∧ v = c) ∨ (u = b₂ ∧ v = d)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with hua₂ | hub₂ <;> rcases hv with hvc | hvd
    · subst u; subst v
      simp [cAC a₂ ha₂A c hcC]
    · subst u; subst v
      have hcdne : c ≠ d := fun he => Set.disjoint_left.mp dCD hcC (he ▸ hdD)
      simp [aAD a₂ ha₂A d hdD, ne23.symm, hcdne.symm]
    · subst u; subst v
      have hcdne : c ≠ d := fun he => Set.disjoint_left.mp dCD hcC (he ▸ hdD)
      simp [aBC b₂ hb₂B c hcC, ne23, hcdne]
    · subst u; subst v
      simp [cBD b₂ hb₂B d hdD]
  have hprism : FormPrism G
      ![a₁, a₂, c] ![f[f.length - 1]'hlast, b₂, d]
      (a₁ :: f) [a₂, b₂] [c, d] := by
    refine formPrism_of_data
      e30.symm (cAC a₁ ha₁A c hcC) (cAC a₂ ha₂A c hcC)
      hb₂last (hDcomp d hdD) (cBD b₂ hb₂B d hdD)
      ?_ ne02 ?_ ?_ ne23.symm ?_ ?_ ?_ ?_
      hP₁ hP₂ hP₃ hcross12long hcross13long hcross23long
    · exact (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A)).symm
    · intro he
      exact Set.disjoint_left.mp dAD ha₁A (he ▸ hdD)
    · exact (hfne _ (List.getElem_mem hlast) a₂ (hmA ha₂A)).symm
    · intro he
      exact Set.disjoint_left.mp dAD ha₂A (he ▸ hdD)
    · exact (hfne _ (List.getElem_mem hlast) c (hmC hcC)).symm
    · intro he
      exact Set.disjoint_left.mp dBC hb₂B (he ▸ hcC)
    · intro he
      exact Set.disjoint_left.mp dCD hcC (he ▸ hdD)
  have hlong : 1 < pathLength (a₁ :: f) := by
    simp only [pathLength, List.length_cons]
    omega
  exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inl hlong⟩

/-- PAPER (printed p. 88), claim (1). -/
theorem claim_one [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hX1 : attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ B)
    (hX2 : attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ B ∪ D) : False := by
  classical
  have hcfg_saved := hcfg
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD,
    hfminor, -, -⟩ := hcfg
  have hmC : ∀ {u : V}, u ∈ C → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inr h)
  have hnoC : ∀ c ∈ C, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj c (f[i]'hi) := by
    intro c hcC i hi hadj
    by_cases hilast : i + 1 < f.length
    · have hcatt : c ∈ attachments G {z : V | z ∈ f.dropLast}
          (A ∪ B ∪ C ∪ D) :=
        ⟨hmC hcC, f[i]'hi, getElem_mem_dropLast hi hilast, hadj⟩
      rcases hX1 hcatt with hcA | hcB
      · exact Set.disjoint_left.mp dAC hcA hcC
      · exact Set.disjoint_left.mp dBC hcB hcC
    · have hi1 : 1 ≤ i := by omega
      have hcatt : c ∈ attachments G {z : V | z ∈ f.tail}
          (A ∪ B ∪ C ∪ D) :=
        ⟨hmC hcC, f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
      rcases hX2 hcatt with hcB | hcD
      · exact Set.disjoint_left.mp dBC hcB hcC
      · exact Set.disjoint_left.mp dCD hcC hcD
  rcases Nat.even_or_odd f.length with heven | hodd
  · exact claim_one_even hG hcube.1 hcfg_saved hnoC heven
  · by_cases hAcomp : ∀ x ∈ A, ∀ (h0 : 0 < f.length), G.Adj (f[0]'h0) x
    · exact claim_one_odd_Acomp hG hcube hcfg_saved hnoC hodd hAcomp
    · exact claim_one_odd_notAcomp hG hcube hcfg_saved hnoC hodd hAcomp

/-- A square whose two `A`-corners both see the first vertex of `f`, while neither
`B`-corner sees `f`, gives the long prism used at the start of paper claim (2). -/
theorem long_prism_of_square_front
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : IsCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    {a₁ b₁ b₂ a₂ : V} (hsq : IsSquare G A B a₁ b₁ b₂ a₂)
    (ha₁f : G.Adj (f[0]'(by have := hcfg.len; omega)) a₁)
    (ha₂f : G.Adj (f[0]'(by have := hcfg.len; omega)) a₂)
    (hnoB : ∀ b ∈ B, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj b (f[i]'hi)) : False := by
  have ha₁f_saved : G.Adj (f[0]'(by have := hcfg.len; omega)) a₁ := ha₁f
  have ha₂f_saved : G.Adj (f[0]'(by have := hcfg.len; omega)) a₂ := ha₂f
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  have hfpath := hcfg.path
  have hk2 := hcfg.len
  have hfout := hcfg.outside
  have haA := hcfg.memA
  have hdD := hcfg.memD
  have hadjA := hcfg.adjA
  have hadjD := hcfg.adjD
  have huniqA := hcfg.uniqA
  have huniqD := hcfg.uniqD
  have hfminor := hcfg.minor
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inr h))
  have hmD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  have ha₁A : a₁ ∈ A := hsq.2.1
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  have hP₃ : IsPathFrom G (f ++ [d]) (f[0]'hfpos) d := by
    refine PathGlue.glue_path (isPathFrom_self hfpath hfpos)
      ⟨PathBasics.isPathList_singleton G d, rfl, rfl⟩ ?_ ?_
    · intro x hx hmem
      simp only [List.mem_singleton] at hmem
      exact hfne x hx d (hmD hdD) hmem
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.mem_singleton] at hy
      subst y
      constructor
      · intro hadj
        exact ⟨(getElem_eq_iff hfnd hi (by omega)).mpr ((hadjD i hi).mp hadj.symm), rfl⟩
      · rintro ⟨h, -⟩
        exact ((hadjD i hi).mpr ((getElem_eq_iff hfnd hi (by omega)).mp h)).symm
  have hcross12 : ∀ u ∈ [a₁, b₁], ∀ v ∈ [a₂, b₂],
      (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · subst u; subst v; simp [e30.symm]
    · subst u; subst v; simp [n02, ne01, ne23]
    · subst u; subst v; simp [n13, ne01.symm, ne23.symm]
    · subst u; subst v; simp [e12]
  have hcross13 : ∀ u ∈ [a₁, b₁], ∀ v ∈ f ++ [d],
      (G.Adj u v ↔ (u = a₁ ∧ v = f[0]'hfpos) ∨ (u = b₁ ∧ v = d)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases List.mem_append.mp hv with hvf | hvd
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvf
      rcases hu with hua | hub
      · subst u
        constructor
        · intro hadj
          have hi0 := huniqA i hi ⟨a₁, ha₁A, hadj⟩
          exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr hi0⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · rw [h]; exact ha₁f_saved.symm
          · exact absurd h ne01
      · subst u
        constructor
        · intro hadj
          exact (hnoB b₁ hb₁B i hi hadj).elim
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h ne01.symm
          · exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
    · simp only [List.mem_singleton] at hvd
      subst v
      rcases hu with hua | hub
      · subst u
        constructor
        · intro hadj; exact (aAD a₁ ha₁A d hdD hadj).elim
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h.symm (hfne _ (List.getElem_mem hfpos) d (hmD hdD))
          · exact absurd h ne01
      · subst u
        exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => cBD b₁ hb₁B d hdD⟩
  have hcross23 : ∀ u ∈ [a₂, b₂], ∀ v ∈ f ++ [d],
      (G.Adj u v ↔ (u = a₂ ∧ v = f[0]'hfpos) ∨ (u = b₂ ∧ v = d)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases List.mem_append.mp hv with hvf | hvd
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvf
      rcases hu with hua | hub
      · subst u
        constructor
        · intro hadj
          have hi0 := huniqA i hi ⟨a₂, ha₂A, hadj⟩
          exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr hi0⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · rw [h]; exact ha₂f_saved.symm
          · exact absurd h ne23.symm
      · subst u
        constructor
        · intro hadj
          exact (hnoB b₂ hb₂B i hi hadj).elim
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h ne23
          · exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
    · simp only [List.mem_singleton] at hvd
      subst v
      rcases hu with hua | hub
      · subst u
        constructor
        · intro hadj; exact (aAD a₂ ha₂A d hdD hadj).elim
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h.symm (hfne _ (List.getElem_mem hfpos) d (hmD hdD))
          · exact absurd h ne23.symm
      · subst u
        exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => cBD b₂ hb₂B d hdD⟩
  have hprism : FormPrism G ![a₁, a₂, f[0]'hfpos] ![b₁, b₂, d]
      [a₁, b₁] [a₂, b₂] (f ++ [d]) := by
    refine formPrism_of_data e30.symm ha₁f_saved.symm ha₂f_saved.symm
      e12 (cBD b₁ hb₁B d hdD) (cBD b₂ hb₂B d hdD)
      ne01 ne02 (by intro h; exact Set.disjoint_left.mp dAD ha₁A (h ▸ hdD))
      ne13.symm ne23.symm (by intro h; exact Set.disjoint_left.mp dAD ha₂A (h ▸ hdD))
      (hfne _ (List.getElem_mem hfpos) b₁ (hmB hb₁B))
      (hfne _ (List.getElem_mem hfpos) b₂ (hmB hb₂B))
      (hfne _ (List.getElem_mem hfpos) d (hmD hdD))
      ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
      ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩ hP₃
      hcross12 hcross13 hcross23
  have hlong : 1 < pathLength (f ++ [d]) := by
    simp only [pathLength, List.length_append, List.length_cons, List.length_nil]
    omega
  exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inr (Or.inr hlong)⟩

/-- PAPER (printed p. 89), claim (2). -/
theorem claim_two [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hX1 : attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ C)
    (hX2 : attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ C ∪ D) : False := by
  classical
  have hcfg_saved := hcfg
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD,
    hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inr h))
  have hmD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  have hnoB : ∀ b ∈ B, ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj b (f[i]'hi) := by
    intro b hbB i hi hadj
    by_cases hilast : i + 1 < f.length
    · have hbatt : b ∈ attachments G {z : V | z ∈ f.dropLast}
          (A ∪ B ∪ C ∪ D) :=
        ⟨hmB hbB, f[i]'hi, getElem_mem_dropLast hi hilast, hadj⟩
      rcases hX1 hbatt with hbA | hbC
      · exact Set.disjoint_left.mp dAB hbA hbB
      · exact Set.disjoint_left.mp dBC hbB hbC
    · have hi1 : 1 ≤ i := by omega
      have hbatt : b ∈ attachments G {z : V | z ∈ f.tail}
          (A ∪ B ∪ C ∪ D) :=
        ⟨hmB hbB, f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
      rcases hX2 hbatt with hbC | hbD
      · exact Set.disjoint_left.mp dBC hbB hbC
      · exact Set.disjoint_left.mp dBD hbB hbD
  obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left sAB haA
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  have haf : G.Adj (f[0]'hfpos) a := ((hadjA 0 hfpos).mpr rfl).symm
  by_cases ha₂f : G.Adj (f[0]'hfpos) a₂
  · exact long_prism_of_square_front hG hcube.1 hcfg_saved hsq haf ha₂f hnoB
  · have hnoa₂ : ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj a₂ (f[i]'hi) := by
      intro i hi hadj
      have hi0 := huniqA i hi ⟨a₂, ha₂A, hadj⟩
      have helem : f[i]'hi = f[0]'hfpos := (getElem_eq_iff hfnd hi hfpos).mpr hi0
      exact ha₂f (helem ▸ hadj.symm)
    have hP₃ : IsPathFrom G (f ++ [d]) (f[0]'hfpos) d := by
      refine PathGlue.glue_path (isPathFrom_self hfpath hfpos)
        ⟨PathBasics.isPathList_singleton G d, rfl, rfl⟩ ?_ ?_
      · intro x hx hmem
        simp only [List.mem_singleton] at hmem
        exact hfne x hx d (hmD hdD) hmem
      · intro x hx y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        simp only [List.mem_singleton] at hy
        subst y
        constructor
        · intro hadj
          exact ⟨(getElem_eq_iff hfnd hi (by omega)).mpr ((hadjD i hi).mp hadj.symm), rfl⟩
        · rintro ⟨h, -⟩
          exact ((hadjD i hi).mpr ((getElem_eq_iff hfnd hi (by omega)).mp h)).symm
    have hlink : VertexLinkedOntoTriangle G a b₁ b₂ d [b₁] [a₂, b₂] (f ++ [d]) := by
      refine ⟨⟨PathBasics.isPathList_singleton G b₁, PathBasics.isPathList_pair e23.symm,
          hP₃.1⟩, ⟨?_, ?_, ?_⟩,
        ⟨Or.inl rfl, Or.inr rfl, Or.inr hP₃.2.2⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · intro x hx hmem
        simp only [List.mem_singleton] at hx
        subst x
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h
        · exact ne13 h
        · exact ne12 h
      · intro x hx hmem
        simp only [List.mem_singleton] at hx
        subst x
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hfne _ hmem b₁ (hmB hb₁B) rfl
        · simp only [List.mem_singleton] at hmem
          exact Set.disjoint_left.mp dBD hb₁B (hmem ▸ hdD)
      · intro x hx hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases List.mem_append.mp hmem with hmem | hmem
        · rcases hx with h | h
          · subst x; exact hfne _ hmem a₂ (hmA ha₂A) rfl
          · subst x; exact hfne _ hmem b₂ (hmB hb₂B) rfl
        · have hxd : x = d := by simpa using hmem
          rcases hx with h | h
          · exact Set.disjoint_left.mp dAD ha₂A ((h.symm.trans hxd) ▸ hdD)
          · exact Set.disjoint_left.mp dBD hb₂B ((h.symm.trans hxd) ▸ hdD)
      · intro x hx y hy
        simp only [List.mem_singleton] at hx
        subst x
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with h | h
        · subst y
          simp [n13, ne23.symm]
        · subst y
          exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => e12⟩
      · intro x hx y hy
        simp only [List.mem_singleton] at hx
        subst x
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
          constructor
          · intro hadj; exact (hnoB b₁ hb₁B i hi hadj).elim
          · rintro ⟨-, h⟩
            exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
        · simp only [List.mem_singleton] at hy
          subst y
          exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => cBD b₁ hb₁B d hdD⟩
      · intro x hx y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
          rcases hx with h | h
          · subst x
            constructor
            · intro hadj; exact (hnoa₂ i hi hadj).elim
            · rintro ⟨-, h⟩
              exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
          · subst x
            constructor
            · intro hadj; exact (hnoB b₂ hb₂B i hi hadj).elim
            · rintro ⟨-, h⟩
              exact absurd h (hfne _ (List.getElem_mem hi) d (hmD hdD))
        · simp only [List.mem_singleton] at hy
          subst y
          rcases hx with h | h
          · subst x
            constructor
            · intro hadj; exact (aAD a₂ ha₂A d hdD hadj).elim
            · rintro ⟨h, -⟩
              exact absurd h ne23.symm
          · subst x
            exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => cBD b₂ hb₂B d hdD⟩
      · exact ⟨b₁, by simp, e01⟩
      · exact ⟨a₂, by simp, e30.symm⟩
      · exact ⟨f[0]'hfpos, List.mem_append_left _ (List.getElem_mem hfpos),
          (hadjA 0 hfpos).mpr rfl⟩
    have h24 := Workspace.Statements.S02.SPGT.thm_2_4 G hG.1.1 a b₁ b₂ d
      ⟨_, _, _, hlink⟩
    rcases h24 with ⟨-, hab₂⟩ | ⟨-, had⟩ | ⟨hab₂, -⟩
    · exact n02 hab₂
    · exact aAD a haA d hdD had
    · exact n02 hab₂

/-- PAPER (printed p. 89), claim (3). -/
theorem claim_three [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hX1sub : attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ B)
    (hX2sub : attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ C ∪ D) : False := by
  classical
  have hcfg_saved := hcfg
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD,
    hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hlast : f.length - 1 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  let K : Set V := A ∪ B ∪ C ∪ D
  let X1 : Set V := attachments G {z : V | z ∈ f.dropLast} K
  let X2 : Set V := attachments G {z : V | z ∈ f.tail} K
  have hX1sub' : X1 ⊆ A ∪ B := by simpa [X1, K] using hX1sub
  have hX2sub' : X2 ⊆ C ∪ D := by simpa [X2, K] using hX2sub
  have hmA : ∀ {u : V}, u ∈ A → u ∈ K := fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ K := fun h => Or.inl (Or.inl (Or.inr h))
  have hmC : ∀ {u : V}, u ∈ C → u ∈ K := fun h => Or.inl (Or.inr h)
  have hmD : ∀ {u : V}, u ∈ D → u ∈ K := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ K → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  have hABCD : Disjoint (A ∪ B) (C ∪ D) := by
    rw [Set.disjoint_left]
    rintro x (hxA | hxB) (hxC | hxD)
    · exact Set.disjoint_left.mp dAC hxA hxC
    · exact Set.disjoint_left.mp dAD hxA hxD
    · exact Set.disjoint_left.mp dBC hxB hxC
    · exact Set.disjoint_left.mp dBD hxB hxD
  have hXdisj : Disjoint X1 X2 := Set.disjoint_of_subset hX1sub' hX2sub' hABCD
  have hX1index : ∀ x ∈ X1, ∀ (i : ℕ) (hi : i < f.length),
      G.Adj x (f[i]'hi) → i = 0 := by
    intro x hx i hi hadj
    by_contra hi0
    have hi1 : 1 ≤ i := by omega
    have hx2 : x ∈ X2 := by
      exact ⟨hx.1, f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
    exact Set.disjoint_left.mp hXdisj hx hx2
  have hX2index : ∀ x ∈ X2, ∀ (i : ℕ) (hi : i < f.length),
      G.Adj x (f[i]'hi) → i = f.length - 1 := by
    intro x hx i hi hadj
    by_contra hilast
    have hin : i + 1 < f.length := by omega
    have hx1 : x ∈ X1 := by
      exact ⟨hx.1, f[i]'hi, getElem_mem_dropLast hi hin, hadj⟩
    exact Set.disjoint_left.mp hXdisj hx1 hx
  have hX1adj0 : ∀ x ∈ X1, G.Adj x (f[0]'hfpos) := by
    intro x hx
    have hx_saved := hx
    obtain ⟨-, z, hz, hxz⟩ := hx
    obtain ⟨i, hi, hiend, hiz⟩ := mem_dropLast_iff.mp hz
    have hxi : G.Adj x (f[i]'hi) := hiz.symm ▸ hxz
    have hi0 := hX1index x hx_saved i hi hxi
    have helem : f[i]'hi = f[0]'hfpos := (getElem_eq_iff hfnd hi hfpos).mpr hi0
    exact helem ▸ hxi
  have hX2adjlast : ∀ x ∈ X2, G.Adj x (f[f.length - 1]'hlast) := by
    intro x hx
    have hx_saved := hx
    obtain ⟨-, z, hz, hxz⟩ := hx
    obtain ⟨i, hi, hi1, hiz⟩ := mem_tail_iff.mp hz
    have hxi : G.Adj x (f[i]'hi) := hiz.symm ▸ hxz
    have hilast := hX2index x hx_saved i hi hxi
    have helem : f[i]'hi = f[f.length - 1]'hlast :=
      (getElem_eq_iff hfnd hi hlast).mpr hilast
    exact helem ▸ hxi
  have haX1 : a ∈ X1 := by
    exact ⟨hmA haA, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega),
      (hadjA 0 hfpos).mpr rfl⟩
  have hdX2 : d ∈ X2 := by
    exact ⟨hmD hdD, f[f.length - 1]'hlast, getElem_mem_tail hlast (by omega),
      (hadjD (f.length - 1) hlast).mpr rfl⟩
  have hnotX2BD : ¬ X2 ⊆ B ∪ D := by
    intro h
    exact claim_one hG hcube hcfg_saved hX1sub (by simpa [X2, K] using h)
  rw [Set.not_subset] at hnotX2BD
  obtain ⟨c₀, hc₀X2, hc₀not⟩ := hnotX2BD
  have hc₀C : c₀ ∈ C := by
    rcases hX2sub' hc₀X2 with hc | hd
    · exact hc
    · exact absurd (Or.inr hd) hc₀not
  have hnotX1AC : ¬ X1 ⊆ A ∪ C := by
    intro h
    exact claim_two hG hcube hcfg_saved (by simpa [X1, K] using h) hX2sub
  rw [Set.not_subset] at hnotX1AC
  obtain ⟨b₀, hb₀X1, hb₀not⟩ := hnotX1AC
  have hb₀B : b₀ ∈ B := by
    rcases hX1sub' hb₀X1 with ha | hb
    · exact absurd (Or.inl ha) hb₀not
    · exact hb
  have hfirstHole : IsHoleList G ([a] ++ f ++ [c₀]) := by
    refine isHoleList_three_blocks
      (P₀ := [a]) (P₁ := f) (P₂ := [c₀])
      (s₀ := a) (t₀ := a) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'hlast)
      (s₂ := c₀) (t₂ := c₀)
      ⟨PathBasics.isPathList_singleton G a, rfl, rfl⟩
      (isPathFrom_self hfpath hfpos)
      ⟨PathBasics.isPathList_singleton G c₀, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ (by simp; omega)
    · intro x hx hx'
      simp only [List.mem_singleton] at hx
      subst x
      exact hfout _ hx' (show a ∈ A ∪ B ∪ C ∪ D from Or.inl (Or.inl (Or.inl haA)))
    · intro x hx hmem
      have hxa : x = a := by simpa using hx
      have hxc : x = c₀ := by simpa using hmem
      exact Set.disjoint_left.mp dAC haA ((hxa.symm.trans hxc) ▸ hc₀C)
    · intro x hx hmem
      have hxc : x = c₀ := by simpa using hmem
      exact hfne x hx c₀ (hmC hc₀C) hxc
    · intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst x
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
      rw [hadjA i hi]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨-, h⟩; exact (getElem_eq_iff hfnd hi hfpos).mp h
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.mem_singleton] at hy
      subst y
      constructor
      · intro hadj
        have hilast := hX2index c₀ hc₀X2 i hi hadj.symm
        exact ⟨(getElem_eq_iff hfnd hi hlast).mpr hilast, rfl⟩
      · rintro ⟨h, -⟩
        rw [h]
        exact (hX2adjlast c₀ hc₀X2).symm
    · intro x hx y hy
      simp only [List.mem_singleton] at hx hy
      subst x; subst y
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => (cAC a haA c₀ hc₀C).symm⟩
  have hfeven : Even f.length := by
    have hev := no_odd_hole hG.1.1 hfirstHole
    simp only [List.length_append, List.length_cons, List.length_nil] at hev
    obtain ⟨n, hn⟩ := hev
    refine ⟨n - 1, ?_⟩
    omega
  have hAout : (A \ X1).Nonempty := by
    obtain ⟨a', ha'A, ha'b₀⟩ := exists_not_adj_left sAB hb₀B
    refine ⟨a', ha'A, ?_⟩
    intro ha'X1
    have hf0minor := hfminor (f[0]'hfpos) (List.getElem_mem hfpos)
    have ha'N : a' ∈ G.neighborSet (f[0]'hfpos) ∩ K ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX1adj0 a' ha'X1).symm, hmA ha'A⟩,
        Or.inl ha'A⟩
    have hbN : b₀ ∈ G.neighborSet (f[0]'hfpos) ∩ K ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX1adj0 b₀ hb₀X1).symm, hmB hb₀B⟩,
        Or.inl hb₀B⟩
    exact ha'b₀ (hf0minor.2.2 a' ha'N b₀ hbN).symm
  have hBout : (B \ X1).Nonempty := by
    obtain ⟨b', hb'B, hab'⟩ := exists_not_adj_right sAB haA
    refine ⟨b', hb'B, ?_⟩
    intro hb'X1
    have hf0minor := hfminor (f[0]'hfpos) (List.getElem_mem hfpos)
    have haN : a ∈ G.neighborSet (f[0]'hfpos) ∩ K ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX1adj0 a haX1).symm, hmA haA⟩,
        Or.inl haA⟩
    have hbN : b' ∈ G.neighborSet (f[0]'hfpos) ∩ K ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX1adj0 b' hb'X1).symm, hmB hb'B⟩,
        Or.inl hb'B⟩
    exact hab' (hf0minor.2.2 a haN b' hbN)
  have hCout : (C \ X2).Nonempty := by
    obtain ⟨c', hc'C, hc'd⟩ := exists_not_adj_of_mem_right sCD hdD
    refine ⟨c', hc'C, ?_⟩
    intro hc'X2
    have hlastminor := hfminor (f[f.length - 1]'hlast) (List.getElem_mem hlast)
    have hcN : c' ∈ G.neighborSet (f[f.length - 1]'hlast) ∩ K ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX2adjlast c' hc'X2).symm, hmC hc'C⟩,
        Or.inr hc'C⟩
    have hdN : d ∈ G.neighborSet (f[f.length - 1]'hlast) ∩ K ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX2adjlast d hdX2).symm, hmD hdD⟩,
        Or.inr hdD⟩
    exact hc'd (hlastminor.2.2 c' hcN d hdN)
  have hDout : (D \ X2).Nonempty := by
    obtain ⟨d', hd'D, hc₀d'⟩ := exists_not_adj_of_mem_left sCD hc₀C
    refine ⟨d', hd'D, ?_⟩
    intro hd'X2
    have hlastminor := hfminor (f[f.length - 1]'hlast) (List.getElem_mem hlast)
    have hcN : c₀ ∈ G.neighborSet (f[f.length - 1]'hlast) ∩ K ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX2adjlast c₀ hc₀X2).symm, hmC hc₀C⟩,
        Or.inr hc₀C⟩
    have hdN : d' ∈ G.neighborSet (f[f.length - 1]'hlast) ∩ K ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX2adjlast d' hd'X2).symm, hmD hd'D⟩,
        Or.inr hd'D⟩
    exact hc₀d' (hlastminor.2.2 c₀ hcN d' hdN)
  obtain ⟨a₁, b₁, b₂, a₂, habsq, ha₁X1, ha₂notX1⟩ :=
    exists_square_cross_left sAB X1 ⟨a, haA, haX1⟩ hAout
  obtain ⟨c₁, d₁, d₂, c₂, hcdsq, hd₁X2, hd₂notX2⟩ :=
    exists_square_cross_right sCD X2 ⟨d, hdD, hdX2⟩ hDout
  have ha₁A : a₁ ∈ A := habsq.2.1
  have ha₂A : a₂ ∈ A := habsq.2.2.1
  have hb₁B : b₁ ∈ B := habsq.2.2.2.1
  have hb₂B : b₂ ∈ B := habsq.2.2.2.2
  have hc₁C : c₁ ∈ C := hcdsq.2.1
  have hc₂C : c₂ ∈ C := hcdsq.2.2.1
  have hd₁D : d₁ ∈ D := hcdsq.2.2.2.1
  have hd₂D : d₂ ∈ D := hcdsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj habsq
  obtain ⟨q01, q12, q23, q30, qn02, qn13, qne01, qne02, qne03, qne12, qne13,
    qne23⟩ := CubeMajorCoreContradiction.square_adj hcdsq
  have ha₁X1' : a₁ ∈ X1 := ha₁X1
  have hd₁X2' : d₁ ∈ X2 := hd₁X2
  have hf0b₂ : ¬ G.Adj (f[0]'hfpos) b₂ := by
    intro hadj
    have hb₂X1 : b₂ ∈ X1 :=
      ⟨hmB hb₂B, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega), hadj.symm⟩
    have hf0minor := hfminor (f[0]'hfpos) (List.getElem_mem hfpos)
    have haN : a₁ ∈ G.neighborSet (f[0]'hfpos) ∩ K ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX1adj0 a₁ ha₁X1').symm, hmA ha₁A⟩,
        Or.inl ha₁A⟩
    have hbN : b₂ ∈ G.neighborSet (f[0]'hfpos) ∩ K ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using hadj, hmB hb₂B⟩, Or.inl hb₂B⟩
    exact n02 (hf0minor.2.2 a₁ haN b₂ hbN)
  have hlastc₁ : ¬ G.Adj (f[f.length - 1]'hlast) c₁ := by
    intro hadj
    have hc₁X2 : c₁ ∈ X2 :=
      ⟨hmC hc₁C, f[f.length - 1]'hlast, getElem_mem_tail hlast (by omega), hadj.symm⟩
    have hlastminor := hfminor (f[f.length - 1]'hlast) (List.getElem_mem hlast)
    have hcN : c₁ ∈ G.neighborSet (f[f.length - 1]'hlast) ∩ K ∩ (A ∪ C) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using hadj, hmC hc₁C⟩, Or.inr hc₁C⟩
    have hdN : d₁ ∈ G.neighborSet (f[f.length - 1]'hlast) ∩ K ∩ (B ∪ D) :=
      ⟨⟨by simpa [SimpleGraph.mem_neighborSet] using (hX2adjlast d₁ hd₁X2').symm, hmD hd₁D⟩,
        Or.inr hd₁D⟩
    exact not_adj_of_compl_adj q01 (hlastminor.2.2 c₁ hcN d₁ hdN)
  have hd₂c₁ : G.Adj d₂ c₁ :=
    (adj_of_not_compl_adj qne02 qn02).symm
  have hreturn : IsPathFrom G [d₁, b₂, d₂, c₁] d₁ c₁ := by
    refine ⟨PathGlue.isPathList_four
      (FiveHoleBasics.nodup_four
        (fun h => Set.disjoint_left.mp dBD hb₂B (h.symm ▸ hd₁D))
        qne12 qne01.symm
        (fun h => Set.disjoint_left.mp dBD hb₂B (h ▸ hd₂D))
        (fun h => Set.disjoint_left.mp dBC hb₂B (h ▸ hc₁C)) qne02.symm)
      (cBD b₂ hb₂B d₁ hd₁D).symm (cBD b₂ hb₂B d₂ hd₂D) hd₂c₁
      (not_adj_of_compl_adj q12)
      (fun h => not_adj_of_compl_adj q01 h.symm)
      (aBC b₂ hb₂B c₁ hc₁C), rfl, rfl⟩
  have hnob₂ : ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj (f[i]'hi) b₂ := by
    intro i hi hadj
    by_cases hin : i + 1 < f.length
    · have hbX1 : b₂ ∈ X1 :=
        ⟨hmB hb₂B, f[i]'hi, getElem_mem_dropLast hi hin, hadj.symm⟩
      have hi0 := hX1index b₂ hbX1 i hi hadj.symm
      have helem : f[i]'hi = f[0]'hfpos := (getElem_eq_iff hfnd hi hfpos).mpr hi0
      exact hf0b₂ (helem ▸ hadj)
    · have hi1 : 1 ≤ i := by omega
      have hbX2 : b₂ ∈ X2 :=
        ⟨hmB hb₂B, f[i]'hi, getElem_mem_tail hi hi1, hadj.symm⟩
      rcases hX2sub' hbX2 with hbC | hbD
      · exact Set.disjoint_left.mp dBC hb₂B hbC
      · exact Set.disjoint_left.mp dBD hb₂B hbD
  have hnod₂ : ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj (f[i]'hi) d₂ := by
    intro i hi hadj
    by_cases hi0 : i = 0
    · subst i
      have hdX1 : d₂ ∈ X1 :=
        ⟨hmD hd₂D, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega), hadj.symm⟩
      rcases hX1sub' hdX1 with hdA | hdB
      · exact Set.disjoint_left.mp dAD hdA hd₂D
      · exact Set.disjoint_left.mp dBD hdB hd₂D
    · have hi1 : 1 ≤ i := by omega
      exact hd₂notX2 ⟨hmD hd₂D, f[i]'hi, getElem_mem_tail hi hi1, hadj.symm⟩
  have hnoc₁ : ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj (f[i]'hi) c₁ := by
    intro i hi hadj
    by_cases hin : i + 1 < f.length
    · have hcX1 : c₁ ∈ X1 :=
        ⟨hmC hc₁C, f[i]'hi, getElem_mem_dropLast hi hin, hadj.symm⟩
      rcases hX1sub' hcX1 with hcA | hcB
      · exact Set.disjoint_left.mp dAC hcA hc₁C
      · exact Set.disjoint_left.mp dBC hcB hc₁C
    · have hieq : i = f.length - 1 := by omega
      have helem : f[i]'hi = f[f.length - 1]'hlast :=
        (getElem_eq_iff hfnd hi hlast).mpr hieq
      exact hlastc₁ (helem ▸ hadj)
  have hfinalHole : IsHoleList G ([a₁] ++ f ++ [d₁, b₂, d₂, c₁]) := by
    refine isHoleList_three_blocks
      (P₀ := [a₁]) (P₁ := f) (P₂ := [d₁, b₂, d₂, c₁])
      (s₀ := a₁) (t₀ := a₁) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'hlast)
      (s₂ := d₁) (t₂ := c₁)
      ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩
      (isPathFrom_self hfpath hfpos) hreturn ?_ ?_ ?_ ?_ ?_ ?_ (by simp)
    · intro x hx hx'
      simp only [List.mem_singleton] at hx
      subst x
      exact hfout _ hx' (hmA ha₁A)
    · intro x hx hmem
      simp only [List.mem_singleton] at hx
      subst x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h
      · exact Set.disjoint_left.mp dAD ha₁A (h ▸ hd₁D)
      · exact Set.disjoint_left.mp dAB ha₁A (h ▸ hb₂B)
      · exact Set.disjoint_left.mp dAD ha₁A (h ▸ hd₂D)
      · exact Set.disjoint_left.mp dAC ha₁A (h ▸ hc₁C)
    · intro x hx hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h
      · exact hfne x hx d₁ (hmD hd₁D) h
      · exact hfne x hx b₂ (hmB hb₂B) h
      · exact hfne x hx d₂ (hmD hd₂D) h
      · exact hfne x hx c₁ (hmC hc₁C) h
    · intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst x
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
      constructor
      · intro hadj
        have hi0 := hX1index a₁ ha₁X1' i hi hadj
        exact ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr hi0⟩
      · rintro ⟨-, h⟩
        rw [h]
        exact hX1adj0 a₁ ha₁X1'
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h | h
      · subst y
        constructor
        · intro hadj
          have hilast := hX2index d₁ hd₁X2' i hi hadj.symm
          exact ⟨(getElem_eq_iff hfnd hi hlast).mpr hilast, rfl⟩
        · rintro ⟨h, -⟩
          rw [h]
          exact (hX2adjlast d₁ hd₁X2').symm
      · subst y
        exact ⟨fun hadj => (hnob₂ i hi hadj).elim,
          by rintro ⟨-, h⟩; exact (Set.disjoint_left.mp dBD hb₂B (h ▸ hd₁D)).elim⟩
      · subst y
        exact ⟨fun hadj => (hnod₂ i hi hadj).elim,
          by rintro ⟨-, h⟩; exact (qne12 h.symm).elim⟩
      · subst y
        exact ⟨fun hadj => (hnoc₁ i hi hadj).elim,
          by rintro ⟨-, h⟩; exact (qne01 h).elim⟩
    · intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h
      · subst x
        constructor
        · intro hadj; exact (aAD a₁ ha₁A d₁ hd₁D hadj.symm).elim
        · rintro ⟨h, -⟩; exact (qne01 h.symm).elim
      · subst x
        constructor
        · intro hadj; exact (n02 hadj.symm).elim
        · rintro ⟨h, -⟩; exact (Set.disjoint_left.mp dBC hb₂B (h ▸ hc₁C)).elim
      · subst x
        constructor
        · intro hadj; exact (aAD a₁ ha₁A d₂ hd₂D hadj.symm).elim
        · rintro ⟨h, -⟩; exact (qne02 h.symm).elim
      · subst x
        exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => (cAC a₁ ha₁A c₁ hc₁C).symm⟩
  have hevenFinal := no_odd_hole hG.1.1 hfinalHole
  simp only [List.length_append, List.length_cons, List.length_nil] at hevenFinal
  obtain ⟨m, hm⟩ := hfeven
  obtain ⟨n, hn⟩ := hevenFinal
  omega

/-- PAPER (printed pp. 89--90), claim (4). -/
theorem claim_four [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    {f : List V} {a d : V} (hcfg : PathConfig G A B C D f a d)
    (hX1sub : attachments G {z : V | z ∈ f.dropLast} (A ∪ B ∪ C ∪ D) ⊆ A ∪ C)
    (hX2sub : attachments G {z : V | z ∈ f.tail} (A ∪ B ∪ C ∪ D) ⊆ B ∪ D) : False := by
  classical
  have hcfg_saved := hcfg
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  obtain ⟨hfpath, hk2, hfout, haA, hdD, hadjA, hadjD, huniqA, huniqD,
    hfminor, -, -⟩ := hcfg
  have hfpos : 0 < f.length := by omega
  have hlast : f.length - 1 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  let K : Set V := A ∪ B ∪ C ∪ D
  let X1 : Set V := attachments G {z : V | z ∈ f.dropLast} K
  let X2 : Set V := attachments G {z : V | z ∈ f.tail} K
  have hX1sub' : X1 ⊆ A ∪ C := by simpa [X1, K] using hX1sub
  have hX2sub' : X2 ⊆ B ∪ D := by simpa [X2, K] using hX2sub
  have hmA : ∀ {u : V}, u ∈ A → u ∈ K := fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ K := fun h => Or.inl (Or.inl (Or.inr h))
  have hmC : ∀ {u : V}, u ∈ C → u ∈ K := fun h => Or.inl (Or.inr h)
  have hmD : ∀ {u : V}, u ∈ D → u ∈ K := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ K → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw
  have hACBD : Disjoint (A ∪ C) (B ∪ D) := by
    rw [Set.disjoint_left]
    rintro x (hxA | hxC) (hxB | hxD)
    · exact Set.disjoint_left.mp dAB hxA hxB
    · exact Set.disjoint_left.mp dAD hxA hxD
    · exact Set.disjoint_left.mp dBC hxB hxC
    · exact Set.disjoint_left.mp dCD hxC hxD
  have hXdisj : Disjoint X1 X2 := Set.disjoint_of_subset hX1sub' hX2sub' hACBD
  have hX1index : ∀ x ∈ X1, ∀ (i : ℕ) (hi : i < f.length),
      G.Adj x (f[i]'hi) → i = 0 := by
    intro x hx i hi hadj
    by_contra hi0
    have hi1 : 1 ≤ i := by omega
    have hx2 : x ∈ X2 := ⟨hx.1, f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
    exact Set.disjoint_left.mp hXdisj hx hx2
  have hX2index : ∀ x ∈ X2, ∀ (i : ℕ) (hi : i < f.length),
      G.Adj x (f[i]'hi) → i = f.length - 1 := by
    intro x hx i hi hadj
    by_contra hilast
    have hin : i + 1 < f.length := by omega
    have hx1 : x ∈ X1 := ⟨hx.1, f[i]'hi, getElem_mem_dropLast hi hin, hadj⟩
    exact Set.disjoint_left.mp hXdisj hx1 hx
  have hX1adj0 : ∀ x ∈ X1, G.Adj x (f[0]'hfpos) := by
    intro x hx
    have hx_saved := hx
    obtain ⟨-, z, hz, hxz⟩ := hx
    obtain ⟨i, hi, hiend, hiz⟩ := mem_dropLast_iff.mp hz
    have hxi : G.Adj x (f[i]'hi) := hiz.symm ▸ hxz
    have hi0 := hX1index x hx_saved i hi hxi
    exact (getElem_eq_iff hfnd hi hfpos).mpr hi0 ▸ hxi
  have hX2adjlast : ∀ x ∈ X2, G.Adj x (f[f.length - 1]'hlast) := by
    intro x hx
    have hx_saved := hx
    obtain ⟨-, z, hz, hxz⟩ := hx
    obtain ⟨i, hi, hi1, hiz⟩ := mem_tail_iff.mp hz
    have hxi : G.Adj x (f[i]'hi) := hiz.symm ▸ hxz
    have hilast := hX2index x hx_saved i hi hxi
    exact (getElem_eq_iff hfnd hi hlast).mpr hilast ▸ hxi
  have haX1 : a ∈ X1 :=
    ⟨hmA haA, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega),
      (hadjA 0 hfpos).mpr rfl⟩
  have hdX2 : d ∈ X2 :=
    ⟨hmD hdD, f[f.length - 1]'hlast, getElem_mem_tail hlast (by omega),
      (hadjD (f.length - 1) hlast).mpr rfl⟩
  have hnotX1AB : ¬ X1 ⊆ A ∪ B := by
    intro h
    exact claim_one hG hcube hcfg_saved (by simpa [X1, K] using h) hX2sub
  rw [Set.not_subset] at hnotX1AB
  obtain ⟨c₀, hc₀X1, hc₀not⟩ := hnotX1AB
  have hc₀C : c₀ ∈ C := by
    rcases hX1sub' hc₀X1 with ha | hc
    · exact absurd (Or.inl ha) hc₀not
    · exact hc
  have hnotX2CD : ¬ X2 ⊆ C ∪ D := by
    intro h
    exact claim_two hG hcube hcfg_saved hX1sub (by simpa [X2, K] using h)
  rw [Set.not_subset] at hnotX2CD
  obtain ⟨b₀, hb₀X2, hb₀not⟩ := hnotX2CD
  have hb₀B : b₀ ∈ B := by
    rcases hX2sub' hb₀X2 with hb | hd
    · exact hb
    · exact absurd (Or.inr hd) hb₀not
  rcases Nat.even_or_odd f.length with hfeven | hfodd
  · have hnoLeft : ∀ x ∈ A ∪ C, x ∉ X1 →
        ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj x (f[i]'hi) := by
      intro x hxside hxnot i hi hadj
      by_cases hin : i + 1 < f.length
      · exact hxnot ⟨hxside.elim hmA hmC, f[i]'hi, getElem_mem_dropLast hi hin, hadj⟩
      · have hi1 : 1 ≤ i := by omega
        have hx2 : x ∈ X2 :=
          ⟨hxside.elim hmA hmC, f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
        rcases hxside with hxA | hxC <;> rcases hX2sub' hx2 with hxB | hxD
        · exact Set.disjoint_left.mp dAB hxA hxB
        · exact Set.disjoint_left.mp dAD hxA hxD
        · exact Set.disjoint_left.mp dBC hxB hxC
        · exact Set.disjoint_left.mp dCD hxC hxD
    have hnoRight : ∀ x ∈ B ∪ D, x ∉ X2 →
        ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj x (f[i]'hi) := by
      intro x hxside hxnot i hi hadj
      by_cases hi0 : i = 0
      · subst i
        have hx1 : x ∈ X1 :=
          ⟨hxside.elim hmB hmD, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega), hadj⟩
        rcases hxside with hxB | hxD <;> rcases hX1sub' hx1 with hxA | hxC
        · exact Set.disjoint_left.mp dAB hxA hxB
        · exact Set.disjoint_left.mp dBC hxB hxC
        · exact Set.disjoint_left.mp dAD hxA hxD
        · exact Set.disjoint_left.mp dCD hxC hxD
      · have hi1 : 1 ≤ i := by omega
        exact hxnot ⟨hxside.elim hmB hmD, f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
    have even_forbidden : ∀ (p q r : V), p ∈ X1 → q ∈ X2 → r ∈ K →
        (∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj r (f[i]'hi)) →
        G.Adj q r → G.Adj r p → ¬ G.Adj p q → False := by
      intro p q r hp hq hrK hrno hqr hrp hnpq
      have hpq : p ≠ q := fun h => Set.disjoint_left.mp hXdisj hp (h ▸ hq)
      have hpr : p ≠ r := hrp.ne.symm
      have hqrne : q ≠ r := hqr.ne
      have hreturn : IsPathFrom G [q, r] q r :=
        ⟨PathBasics.isPathList_pair hqr, rfl, rfl⟩
      have hhole : IsHoleList G ([p] ++ f ++ [q, r]) := by
        refine isHoleList_three_blocks
          (P₀ := [p]) (P₁ := f) (P₂ := [q, r])
          (s₀ := p) (t₀ := p) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'hlast)
          (s₂ := q) (t₂ := r)
          ⟨PathBasics.isPathList_singleton G p, rfl, rfl⟩
          (isPathFrom_self hfpath hfpos) hreturn ?_ ?_ ?_ ?_ ?_ ?_ (by simp; omega)
        · intro x hx hxf
          simp only [List.mem_singleton] at hx
          subst x; exact hfout _ hxf hp.1
        · intro x hx hmem
          have hxp : x = p := by simpa using hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with hxq | hxr
          · exact hpq (hxp.symm.trans hxq)
          · exact hpr (hxp.symm.trans hxr)
        · intro x hxf hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with hxq | hxr
          · exact hfne x hxf q hq.1 hxq
          · exact hfne x hxf r hrK hxr
        · intro x hx y hy
          simp only [List.mem_singleton] at hx
          subst x
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
          constructor
          · intro hadj
            exact ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr (hX1index p hp i hi hadj)⟩
          · rintro ⟨-, h⟩; rw [h]; exact hX1adj0 p hp
        · intro x hx y hy
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hyq | hyr
          · subst y
            constructor
            · intro hadj
              exact ⟨(getElem_eq_iff hfnd hi hlast).mpr
                (hX2index q hq i hi hadj.symm), rfl⟩
            · rintro ⟨h, -⟩; rw [h]; exact (hX2adjlast q hq).symm
          · subst y
            constructor
            · intro hadj; exact (hrno i hi hadj.symm).elim
            · rintro ⟨-, h⟩; exact (hqrne h.symm).elim
        · intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst y
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hxq | hxr
          · subst x
            constructor
            · intro hadj; exact (hnpq hadj.symm).elim
            · rintro ⟨h, -⟩; exact (hqrne h).elim
          · subst x
            exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => hrp⟩
      have hev := no_odd_hole hG.1.1 hhole
      simp only [List.length_append, List.length_cons, List.length_nil] at hev
      obtain ⟨m, hm⟩ := hfeven
      obtain ⟨n, hn⟩ := hev
      omega
    have hAin_Bout : Anticomplete G (A ∩ X1) (B \ X2) := by
      rintro x ⟨hxA, hxX⟩ y ⟨hyB, hyout⟩ hxy
      exact even_forbidden x d y hxX hdX2 (hmB hyB)
        (hnoRight y (Or.inl hyB) hyout) (cBD y hyB d hdD).symm hxy.symm
        (aAD x hxA d hdD)
    have hAout_Bin : Anticomplete G (A \ X1) (B ∩ X2) := by
      rintro x ⟨hxA, hxout⟩ y ⟨hyB, hyX⟩ hxy
      exact even_forbidden c₀ y x hc₀X1 hyX (hmA hxA)
        (hnoLeft x (Or.inl hxA) hxout) hxy.symm (cAC x hxA c₀ hc₀C)
        (fun h => aBC y hyB c₀ hc₀C h.symm)
    have hCin_Dout : Anticomplete G (C ∩ X1) (D \ X2) := by
      rintro x ⟨hxC, hxX⟩ y ⟨hyD, hyout⟩ hxy
      exact even_forbidden x b₀ y hxX hb₀X2 (hmD hyD)
        (hnoRight y (Or.inr hyD) hyout) (cBD b₀ hb₀B y hyD) hxy.symm
        (fun h => aBC b₀ hb₀B x hxC h.symm)
    have hCout_Din : Anticomplete G (C \ X1) (D ∩ X2) := by
      rintro x ⟨hxC, hxout⟩ y ⟨hyD, hyX⟩ hxy
      exact even_forbidden a y x haX1 hyX (hmC hxC)
        (hnoLeft x (Or.inr hxC) hxout) hxy.symm (cAC a haA x hxC).symm
        (aAD a haA y hyD)
    obtain ⟨b, hbB, hab⟩ := exists_adj_right sAB haA
    have hbX2 : b ∈ X2 := by
      by_contra hbnot
      exact hAin_Bout a ⟨haA, haX1⟩ b ⟨hbB, hbnot⟩ hab
    obtain ⟨d', hd'D, hc₀d'⟩ := exists_adj_of_mem_left dCD sCD hc₀C
    have hd'X2 : d' ∈ X2 := by
      by_contra hd'not
      exact hCin_Dout c₀ ⟨hc₀C, hc₀X1⟩ d' ⟨hd'D, hd'not⟩ hc₀d'
    have hcross12 : ∀ u ∈ [a, b], ∀ v ∈ [c₀, d'],
        (G.Adj u v ↔ (u = a ∧ v = c₀) ∨ (u = b ∧ v = d')) := by
      intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · subst u; subst v; simp [cAC a haA c₀ hc₀C]
      · subst u; subst v
        have hcdne : c₀ ≠ d' := fun h => Set.disjoint_left.mp dCD hc₀C (h ▸ hd'D)
        simp [aAD a haA d' hd'D, hab.ne, hcdne.symm]
      · subst u; subst v
        have hacne : a ≠ c₀ := fun h => Set.disjoint_left.mp dAC haA (h ▸ hc₀C)
        have hcdne : c₀ ≠ d' := fun h => Set.disjoint_left.mp dCD hc₀C (h ▸ hd'D)
        simp [aBC b hbB c₀ hc₀C, hab.ne.symm, hacne.symm, hcdne]
      · subst u; subst v; simp [cBD b hbB d' hd'D]
    have hcross13 : ∀ u ∈ [a, b], ∀ v ∈ f,
        (G.Adj u v ↔ (u = a ∧ v = f[0]'hfpos) ∨
          (u = b ∧ v = f[f.length - 1]'hlast)) := by
      intro u hu v hv
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hua | hub
      · subst u
        constructor
        · intro hadj
          exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr
            (hX1index a haX1 i hi hadj)⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · rw [h]; exact hX1adj0 a haX1
          · exact absurd h hab.ne
      · subst u
        constructor
        · intro hadj
          exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hi hlast).mpr
            (hX2index b hbX2 i hi hadj)⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hab.ne.symm
          · rw [h]; exact hX2adjlast b hbX2
    have hcross23 : ∀ u ∈ [c₀, d'], ∀ v ∈ f,
        (G.Adj u v ↔ (u = c₀ ∧ v = f[0]'hfpos) ∨
          (u = d' ∧ v = f[f.length - 1]'hlast)) := by
      intro u hu v hv
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with huc | hud
      · subst u
        constructor
        · intro hadj
          exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr
            (hX1index c₀ hc₀X1 i hi hadj)⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · rw [h]; exact hX1adj0 c₀ hc₀X1
          · exact absurd h (fun he => Set.disjoint_left.mp dCD hc₀C (he ▸ hd'D))
      · subst u
        constructor
        · intro hadj
          exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hi hlast).mpr
            (hX2index d' hd'X2 i hi hadj)⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (fun he => Set.disjoint_left.mp dCD hc₀C (he.symm ▸ hd'D))
          · rw [h]; exact hX2adjlast d' hd'X2
    have hprism : FormPrism G ![a, c₀, f[0]'hfpos]
        ![b, d', f[f.length - 1]'hlast] [a, b] [c₀, d'] f := by
      refine formPrism_of_data (cAC a haA c₀ hc₀C) (hX1adj0 a haX1)
        (hX1adj0 c₀ hc₀X1) (cBD b hbB d' hd'D) (hX2adjlast b hbX2)
        (hX2adjlast d' hd'X2)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ⟨PathBasics.isPathList_pair hab, rfl, rfl⟩
        ⟨PathBasics.isPathList_pair hc₀d', rfl, rfl⟩
        (isPathFrom_self hfpath hfpos) hcross12 hcross13 hcross23
      · intro h; exact Set.disjoint_left.mp dAB haA (h ▸ hbB)
      · intro h; exact Set.disjoint_left.mp dAD haA (h ▸ hd'D)
      · exact (hfne _ (List.getElem_mem hlast) a (hmA haA)).symm
      · intro h; exact Set.disjoint_left.mp dBC hbB (h ▸ hc₀C)
      · intro h; exact Set.disjoint_left.mp dCD hc₀C (h ▸ hd'D)
      · exact (hfne _ (List.getElem_mem hlast) c₀ (hmC hc₀C)).symm
      · exact hfne _ (List.getElem_mem hfpos) b (hmB hbB)
      · exact hfne _ (List.getElem_mem hfpos) d' (hmD hd'D)
      · intro h
        have := (getElem_eq_iff hfnd hfpos hlast).mp h
        omega
    have hlen : f.length = 2 := by
      have hle : f.length ≤ 2 := by
        by_contra h
        have hlong : 1 < pathLength f := by simp [pathLength]; omega
        exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inr (Or.inr hlong)⟩
      omega
    by_cases hCcomp : ∀ c ∈ C, G.Adj (f[0]'hfpos) c
    · have hCX1 : ∀ c ∈ C, c ∈ X1 := by
        intro c hcC
        exact ⟨hmC hcC, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega),
          (hCcomp c hcC).symm⟩
      have hDX2 : ∀ d₀ ∈ D, d₀ ∈ X2 := by
        intro d₀ hd₀D
        obtain ⟨c, hcC, hcd₀⟩ := exists_adj_of_mem_right dCD sCD hd₀D
        by_contra hd₀not
        exact hCin_Dout c ⟨hcC, hCX1 c hcC⟩ d₀ ⟨hd₀D, hd₀not⟩ hcd₀
      have hDcomp : ∀ d₀ ∈ D, G.Adj (f[1]'(by omega)) d₀ := by
        intro d₀ hd₀D
        have hadj := (hX2adjlast d₀ (hDX2 d₀ hd₀D)).symm
        have helem : f[f.length - 1]'hlast = f[1]'(by omega) :=
          (getElem_eq_iff hfnd hlast (by omega)).mpr (by omega)
        exact helem ▸ hadj
      have hf01 : G.Adj (f[0]'hfpos) (f[1]'(by omega)) := by
        rw [PathBasics.path_adj_iff hfpath hfpos (by omega)]
        omega
      have hnoD0 : ∀ d₀ ∈ D, ¬ G.Adj (f[0]'hfpos) d₀ := by
        intro d₀ hd₀D hadj
        have := huniqD 0 hfpos ⟨d₀, hd₀D, hadj.symm⟩
        omega
      have hnoC1 : ∀ c ∈ C, ¬ G.Adj (f[1]'(by omega)) c := by
        intro c hcC hadj
        have hcX2 : c ∈ X2 :=
          ⟨hmC hcC, f[1]'(by omega), getElem_mem_tail (by omega) (by omega), hadj.symm⟩
        rcases hX2sub' hcX2 with hcB | hcD
        · exact Set.disjoint_left.mp dBC hcB hcC
        · exact Set.disjoint_left.mp dCD hcC hcD
      have hf0b : ¬ G.Adj (f[0]'hfpos) b := by
        intro hadj
        have hi := hX2index b hbX2 0 hfpos hadj.symm
        omega
      have hf1a : ¬ G.Adj (f[1]'(by omega)) a := by
        intro hadj
        have hi := hX1index a haX1 1 (by omega) hadj.symm
        omega
      have hf0f1ne : f[0]'hfpos ≠ f[1]'(by omega) := by
        intro he
        have := (getElem_eq_iff hfnd hfpos (by omega)).mp he
        omega
      have hnewSquare : IsSquare G (A ∪ {f[0]'hfpos}) (B ∪ {f[1]'(by omega)})
          (f[0]'hfpos) (f[1]'(by omega)) b a := by
        refine ⟨FiveHoleBasics.isHoleList_four
          (FiveHoleBasics.nodup_four hf0f1ne
            (hfne _ (List.getElem_mem hfpos) b (hmB hbB))
            (hfne _ (List.getElem_mem hfpos) a (hmA haA))
            (hfne _ (List.getElem_mem (show 1 < f.length by omega)) b (hmB hbB))
            (hfne _ (List.getElem_mem (show 1 < f.length by omega)) a (hmA haA))
            (fun he => Set.disjoint_left.mp dAB haA (he.symm ▸ hbB)))
          hf01 (by
            have hadj := (hX2adjlast b hbX2).symm
            have helem : f[f.length - 1]'hlast = f[1]'(by omega) :=
              (getElem_eq_iff hfnd hlast (by omega)).mpr (by omega)
            exact helem ▸ hadj)
          hab.symm (hX1adj0 a haX1)
          hf0b hf1a, Or.inr rfl, Or.inl haA, Or.inr rfl, Or.inl hbB⟩
      have hsAB' : SquareConnected G (A ∪ {f[0]'hfpos}) (B ∪ {f[1]'(by omega)}) := by
        apply squareConnected_adjoin_both sAB
          (fun h => hfout _ (List.getElem_mem hfpos) (show f[0]'hfpos ∈ K from hmA h))
          (fun h => hfout _ (List.getElem_mem (show 1 < f.length by omega))
            (show f[1]'(by omega) ∈ K from hmB h))
        · exact ⟨f[1]'(by omega), b, a, hnewSquare, haA⟩
        · exact ⟨f[0]'hfpos, b, a, hnewSquare, hbB⟩
      have hnewCube : IsCube G (A ∪ {f[0]'hfpos}) (B ∪ {f[1]'(by omega)}) C D := by
        refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, dCD⟩,
          nA.mono Set.subset_union_left, nB.mono Set.subset_union_left, nC, nD⟩,
          ⟨?_, ?_, ?_, ?_⟩, hsAB', sCD⟩
        · rw [Set.disjoint_left]
          rintro x (hxA | hx0) (hxB | hx1)
          · exact Set.disjoint_left.mp dAB hxA hxB
          · rw [Set.mem_singleton_iff] at hx1
            subst x; exact hfout _ (List.getElem_mem (show 1 < f.length by omega)) (hmA hxA)
          · rw [Set.mem_singleton_iff] at hx0
            subst x; exact hfout _ (List.getElem_mem hfpos) (hmB hxB)
          · rw [Set.mem_singleton_iff] at hx0 hx1
            exact hf0f1ne (hx0.symm.trans hx1)
        · rw [Set.disjoint_left]
          rintro x (hxA | hx0) hxC
          · exact Set.disjoint_left.mp dAC hxA hxC
          · rw [Set.mem_singleton_iff] at hx0
            subst x; exact hfout _ (List.getElem_mem hfpos) (hmC hxC)
        · rw [Set.disjoint_left]
          rintro x (hxA | hx0) hxD
          · exact Set.disjoint_left.mp dAD hxA hxD
          · rw [Set.mem_singleton_iff] at hx0
            subst x; exact hfout _ (List.getElem_mem hfpos) (hmD hxD)
        · rw [Set.disjoint_left]
          rintro x (hxB | hx1) hxC
          · exact Set.disjoint_left.mp dBC hxB hxC
          · rw [Set.mem_singleton_iff] at hx1
            subst x; exact hfout _ (List.getElem_mem (show 1 < f.length by omega)) (hmC hxC)
        · rw [Set.disjoint_left]
          rintro x (hxB | hx1) hxD
          · exact Set.disjoint_left.mp dBD hxB hxD
          · rw [Set.mem_singleton_iff] at hx1
            subst x; exact hfout _ (List.getElem_mem (show 1 < f.length by omega)) (hmD hxD)
        · rintro x (hxA | hx0) y hyC
          · exact cAC x hxA y hyC
          · rw [Set.mem_singleton_iff] at hx0
            subst x; exact hCcomp y hyC
        · rintro x (hxB | hx1) y hyD
          · exact cBD x hxB y hyD
          · rw [Set.mem_singleton_iff] at hx1
            subst x; exact hDcomp y hyD
        · rintro x (hxA | hx0) y hyD
          · exact aAD x hxA y hyD
          · rw [Set.mem_singleton_iff] at hx0
            subst x; exact hnoD0 y hyD
        · rintro x (hxB | hx1) y hyC
          · exact aBC x hxB y hyC
          · rw [Set.mem_singleton_iff] at hx1
            subst x; exact hnoC1 y hyC
      obtain ⟨hAeq, -, -, -⟩ := hcube.2 (A ∪ {f[0]'hfpos})
        (B ∪ {f[1]'(by omega)}) C D hnewCube Set.subset_union_left Set.subset_union_left
        (le_refl C) (le_refl D)
      have hf0A' : f[0]'hfpos ∈ A ∪ {f[0]'hfpos} := Or.inr (by simp)
      have hf0A : f[0]'hfpos ∈ A := by rw [hAeq]; exact hf0A'
      exact hfout _ (List.getElem_mem hfpos) (show f[0]'hfpos ∈ K from hmA hf0A)
    · push_neg at hCcomp
      obtain ⟨c', hc'C, hc'f0⟩ := hCcomp
      have hc'out : c' ∈ C \ X1 := ⟨hc'C, fun hc'X => hc'f0 (hX1adj0 c' hc'X).symm⟩
      obtain ⟨c₁, d₁, d₂, c₂, hcdsq, hc₁X1, hc₂notX1⟩ :=
        exists_square_cross_left sCD X1 ⟨c₀, hc₀C, hc₀X1⟩ ⟨c', hc'C, hc'out.2⟩
      have hc₁C : c₁ ∈ C := hcdsq.2.1
      have hc₂C : c₂ ∈ C := hcdsq.2.2.1
      have hd₁D : d₁ ∈ D := hcdsq.2.2.2.1
      have hd₂D : d₂ ∈ D := hcdsq.2.2.2.2
      obtain ⟨q01, q12, q23, q30, qn02, qn13, qne01, qne02, qne03, qne12,
        qne13, qne23⟩ := CubeMajorCoreContradiction.square_adj hcdsq
      have hc₁d₂ : G.Adj c₁ d₂ := adj_of_not_compl_adj qne02 qn02
      have hc₂d₁ : G.Adj c₂ d₁ := (adj_of_not_compl_adj qne13 qn13).symm
      have hd₂X2 : d₂ ∈ X2 := by
        by_contra hd₂not
        exact hCin_Dout c₁ ⟨hc₁C, hc₁X1⟩ d₂ ⟨hd₂D, hd₂not⟩ hc₁d₂
      have hd₁notX2 : d₁ ∉ X2 := by
        intro hd₁X2
        exact hCout_Din c₂ ⟨hc₂C, hc₂notX1⟩ d₁ ⟨hd₁D, hd₁X2⟩ hc₂d₁
      by_cases hAcomp : ∀ a₀ ∈ A, G.Adj (f[0]'hfpos) a₀
      · have hAX1 : ∀ a₀ ∈ A, a₀ ∈ X1 := by
          intro a₀ ha₀A
          exact ⟨hmA ha₀A, f[0]'hfpos, getElem_mem_dropLast hfpos (by omega),
            (hAcomp a₀ ha₀A).symm⟩
        have hBX2 : ∀ b₀ ∈ B, b₀ ∈ X2 := by
          intro b₀ hb₀B
          obtain ⟨a₀, ha₀A, hb₀a₀⟩ := exists_adj_left sAB hb₀B
          by_contra hb₀not
          exact hAin_Bout a₀ ⟨ha₀A, hAX1 a₀ ha₀A⟩ b₀ ⟨hb₀B, hb₀not⟩ hb₀a₀.symm
        have hBcomp : ∀ b₀ ∈ B, G.Adj (f[1]'(by omega)) b₀ := by
          intro b₀ hb₀B
          have hadj := (hX2adjlast b₀ (hBX2 b₀ hb₀B)).symm
          have helem : f[f.length - 1]'hlast = f[1]'(by omega) :=
            (getElem_eq_iff hfnd hlast (by omega)).mpr (by omega)
          exact helem ▸ hadj
        have hf01 : G.Adj (f[0]'hfpos) (f[1]'(by omega)) := by
          rw [PathBasics.path_adj_iff hfpath hfpos (by omega)]
          omega
        have hf0d₁ : ¬ G.Adj (f[0]'hfpos) d₁ :=
          fun hadj => hnoRight d₁ (Or.inr hd₁D) hd₁notX2 0 hfpos hadj.symm
        have hf1d₁ : ¬ G.Adj (f[1]'(by omega)) d₁ :=
          fun hadj => hnoRight d₁ (Or.inr hd₁D) hd₁notX2 1 (by omega) hadj.symm
        have hf0c₂ : ¬ G.Adj (f[0]'hfpos) c₂ :=
          fun hadj => hnoLeft c₂ (Or.inr hc₂C) hc₂notX1 0 hfpos hadj.symm
        have hf1c₂ : ¬ G.Adj (f[1]'(by omega)) c₂ :=
          fun hadj => hnoLeft c₂ (Or.inr hc₂C) hc₂notX1 1 (by omega) hadj.symm
        have hf0f1ne : f[0]'hfpos ≠ f[1]'(by omega) := by
          intro he
          have := (getElem_eq_iff hfnd hfpos (by omega)).mp he
          omega
        have hnewAntiSquare : IsSquare Gᶜ (C ∪ {f[0]'hfpos})
            (D ∪ {f[1]'(by omega)}) (f[0]'hfpos) d₁ (f[1]'(by omega)) c₂ := by
          refine ⟨FiveHoleBasics.isHoleList_four
            (FiveHoleBasics.nodup_four
              (hfne _ (List.getElem_mem hfpos) d₁ (hmD hd₁D)) hf0f1ne
              (hfne _ (List.getElem_mem hfpos) c₂ (hmC hc₂C))
              (hfne _ (List.getElem_mem (show 1 < f.length by omega)) d₁ (hmD hd₁D)).symm
              (fun h => Set.disjoint_left.mp dCD hc₂C (h ▸ hd₁D))
              (hfne _ (List.getElem_mem (show 1 < f.length by omega)) c₂ (hmC hc₂C)))
            ?_ ?_ ?_ ?_ ?_ ?_, Or.inr rfl, Or.inl hc₂C, Or.inl hd₁D, Or.inr rfl⟩
          · simpa [SimpleGraph.compl_adj] using
              ⟨hfne _ (List.getElem_mem hfpos) d₁ (hmD hd₁D), hf0d₁⟩
          · simpa [SimpleGraph.compl_adj] using
              ⟨(hfne _ (List.getElem_mem (show 1 < f.length by omega)) d₁ (hmD hd₁D)).symm,
                fun h => hf1d₁ h.symm⟩
          · simpa [SimpleGraph.compl_adj] using
              ⟨hfne _ (List.getElem_mem (show 1 < f.length by omega)) c₂ (hmC hc₂C), hf1c₂⟩
          · simpa [SimpleGraph.compl_adj] using
              ⟨(hfne _ (List.getElem_mem hfpos) c₂ (hmC hc₂C)).symm,
                fun h => hf0c₂ h.symm⟩
          · simp only [SimpleGraph.compl_adj, not_and, not_not]
            exact fun _ => hf01
          · simp only [SimpleGraph.compl_adj, not_and, not_not]
            exact fun _ => hc₂d₁.symm
        have hsCD' : SquareConnected Gᶜ (C ∪ {f[0]'hfpos})
            (D ∪ {f[1]'(by omega)}) := by
          apply squareConnected_adjoin_both sCD
            (fun h => hfout _ (List.getElem_mem hfpos) (show f[0]'hfpos ∈ K from hmC h))
            (fun h => hfout _ (List.getElem_mem (show 1 < f.length by omega))
              (show f[1]'(by omega) ∈ K from hmD h))
          · exact ⟨d₁, f[1]'(by omega), c₂, hnewAntiSquare, hc₂C⟩
          · exact ⟨c₂, d₁, f[0]'hfpos, isSquare_rev hnewAntiSquare, hd₁D⟩
        have hnoA1 : ∀ a₀ ∈ A, ¬ G.Adj a₀ (f[1]'(by omega)) := by
          intro a₀ ha₀A hadj
          have hi := hX1index a₀ (hAX1 a₀ ha₀A) 1 (by omega) hadj
          omega
        have hnoB0 : ∀ b₀ ∈ B, ¬ G.Adj b₀ (f[0]'hfpos) := by
          intro b₀ hb₀B hadj
          have hi := hX2index b₀ (hBX2 b₀ hb₀B) 0 hfpos hadj
          omega
        have hnewCube : IsCube G A B (C ∪ {f[0]'hfpos})
            (D ∪ {f[1]'(by omega)}) := by
          refine ⟨⟨⟨dAB, ?_, ?_, ?_, ?_, ?_⟩, nA, nB,
            nC.mono Set.subset_union_left, nD.mono Set.subset_union_left⟩,
            ⟨?_, ?_, ?_, ?_⟩, sAB, hsCD'⟩
          · rw [Set.disjoint_left]
            rintro x hxA (hxC | hx0)
            · exact Set.disjoint_left.mp dAC hxA hxC
            · rw [Set.mem_singleton_iff] at hx0
              subst x; exact hfout _ (List.getElem_mem hfpos) (hmA hxA)
          · rw [Set.disjoint_left]
            rintro x hxA (hxD | hx1)
            · exact Set.disjoint_left.mp dAD hxA hxD
            · rw [Set.mem_singleton_iff] at hx1
              subst x; exact hfout _ (List.getElem_mem (show 1 < f.length by omega)) (hmA hxA)
          · rw [Set.disjoint_left]
            rintro x hxB (hxC | hx0)
            · exact Set.disjoint_left.mp dBC hxB hxC
            · rw [Set.mem_singleton_iff] at hx0
              subst x; exact hfout _ (List.getElem_mem hfpos) (hmB hxB)
          · rw [Set.disjoint_left]
            rintro x hxB (hxD | hx1)
            · exact Set.disjoint_left.mp dBD hxB hxD
            · rw [Set.mem_singleton_iff] at hx1
              subst x; exact hfout _ (List.getElem_mem (show 1 < f.length by omega)) (hmB hxB)
          · rw [Set.disjoint_left]
            rintro x (hxC | hx0) (hxD | hx1)
            · exact Set.disjoint_left.mp dCD hxC hxD
            · rw [Set.mem_singleton_iff] at hx1
              subst x; exact hfout _ (List.getElem_mem (show 1 < f.length by omega)) (hmC hxC)
            · rw [Set.mem_singleton_iff] at hx0
              subst x; exact hfout _ (List.getElem_mem hfpos) (hmD hxD)
            · rw [Set.mem_singleton_iff] at hx0 hx1
              exact hf0f1ne (hx0.symm.trans hx1)
          · rintro x hxA y (hyC | hy0)
            · exact cAC x hxA y hyC
            · rw [Set.mem_singleton_iff] at hy0
              subst y; exact (hAcomp x hxA).symm
          · rintro x hxB y (hyD | hy1)
            · exact cBD x hxB y hyD
            · rw [Set.mem_singleton_iff] at hy1
              subst y; exact (hBcomp x hxB).symm
          · rintro x hxA y (hyD | hy1)
            · exact aAD x hxA y hyD
            · rw [Set.mem_singleton_iff] at hy1
              subst y; exact hnoA1 x hxA
          · rintro x hxB y (hyC | hy0)
            · exact aBC x hxB y hyC
            · rw [Set.mem_singleton_iff] at hy0
              subst y; exact hnoB0 x hxB
        obtain ⟨-, -, hCeq, -⟩ := hcube.2 A B (C ∪ {f[0]'hfpos})
          (D ∪ {f[1]'(by omega)}) hnewCube (le_refl A) (le_refl B)
          Set.subset_union_left Set.subset_union_left
        have hf0C' : f[0]'hfpos ∈ C ∪ {f[0]'hfpos} := Or.inr (by simp)
        have hf0C : f[0]'hfpos ∈ C := by rw [hCeq]; exact hf0C'
        exact hfout _ (List.getElem_mem hfpos) (show f[0]'hfpos ∈ K from hmC hf0C)
      · push_neg at hAcomp
        obtain ⟨a', ha'A, ha'f0⟩ := hAcomp
        have ha'out : a' ∈ A \ X1 :=
          ⟨ha'A, fun ha'X => ha'f0 (hX1adj0 a' ha'X).symm⟩
        obtain ⟨a₁, b₁, b₂, a₂, habsq, ha₁X1, ha₂notX1⟩ :=
          exists_square_cross_left sAB X1 ⟨a, haA, haX1⟩ ⟨a', ha'A, ha'out.2⟩
        have ha₁A : a₁ ∈ A := habsq.2.1
        have ha₂A : a₂ ∈ A := habsq.2.2.1
        have hb₁B : b₁ ∈ B := habsq.2.2.2.1
        have hb₂B : b₂ ∈ B := habsq.2.2.2.2
        obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13,
          ne23⟩ := CubeMajorCoreContradiction.square_adj habsq
        have hb₁X2 : b₁ ∈ X2 := by
          by_contra hb₁not
          exact hAin_Bout a₁ ⟨ha₁A, ha₁X1⟩ b₁ ⟨hb₁B, hb₁not⟩ e01
        have hb₂notX2 : b₂ ∉ X2 := by
          intro hb₂X2
          exact hAout_Bin a₂ ⟨ha₂A, ha₂notX1⟩ b₂ ⟨hb₂B, hb₂X2⟩ e23.symm
        have hnod₁ := hnoRight d₁ (Or.inr hd₁D) hd₁notX2
        have hnob₂ := hnoRight b₂ (Or.inl hb₂B) hb₂notX2
        have hnoc₂ := hnoLeft c₂ (Or.inr hc₂C) hc₂notX1
        have hP₂ : IsPathFrom G [d₂, b₂, d₁, c₂] d₂ c₂ := by
          refine ⟨PathGlue.isPathList_four
            (FiveHoleBasics.nodup_four
              (fun h => Set.disjoint_left.mp dBD hb₂B (h.symm ▸ hd₂D))
              qne12.symm qne23
              (fun h => Set.disjoint_left.mp dBD hb₂B (h ▸ hd₁D))
              (fun h => Set.disjoint_left.mp dBC hb₂B (h ▸ hc₂C)) qne13)
            (cBD b₂ hb₂B d₂ hd₂D).symm (cBD b₂ hb₂B d₁ hd₁D) hc₂d₁.symm
            (fun h => not_adj_of_compl_adj q12 h.symm)
            (not_adj_of_compl_adj q23) (aBC b₂ hb₂B c₂ hc₂C), rfl, rfl⟩
        have hhole : IsHoleList G ([a₁] ++ f ++ [d₂, b₂, d₁, c₂]) := by
          refine isHoleList_three_blocks
            (P₀ := [a₁]) (P₁ := f) (P₂ := [d₂, b₂, d₁, c₂])
            (s₀ := a₁) (t₀ := a₁) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'hlast)
            (s₂ := d₂) (t₂ := c₂)
            ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩
            (isPathFrom_self hfpath hfpos) hP₂ ?_ ?_ ?_ ?_ ?_ ?_ (by simp)
          · intro x hx hxf
            simp only [List.mem_singleton] at hx
            subst x; exact hfout _ hxf (hmA ha₁A)
          · intro x hx hmem
            simp only [List.mem_singleton] at hx
            subst x
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h | h | h | h
            · exact Set.disjoint_left.mp dAD ha₁A (h ▸ hd₂D)
            · exact Set.disjoint_left.mp dAB ha₁A (h ▸ hb₂B)
            · exact Set.disjoint_left.mp dAD ha₁A (h ▸ hd₁D)
            · exact Set.disjoint_left.mp dAC ha₁A (h ▸ hc₂C)
          · intro x hxf hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h | h | h | h
            · exact hfne x hxf d₂ (hmD hd₂D) h
            · exact hfne x hxf b₂ (hmB hb₂B) h
            · exact hfne x hxf d₁ (hmD hd₁D) h
            · exact hfne x hxf c₂ (hmC hc₂C) h
          · intro x hx y hy
            simp only [List.mem_singleton] at hx
            subst x
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
            constructor
            · intro hadj
              exact ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr
                (hX1index a₁ ha₁X1 i hi hadj)⟩
            · rintro ⟨-, h⟩; rw [h]; exact hX1adj0 a₁ ha₁X1
          · intro x hx y hy
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with h | h | h | h
            · subst y
              constructor
              · intro hadj
                exact ⟨(getElem_eq_iff hfnd hi hlast).mpr
                  (hX2index d₂ hd₂X2 i hi hadj.symm), rfl⟩
              · rintro ⟨h, -⟩; rw [h]; exact (hX2adjlast d₂ hd₂X2).symm
            · subst y
              constructor
              · intro hadj; exact (hnob₂ i hi hadj.symm).elim
              · rintro ⟨-, h⟩
                exact (Set.disjoint_left.mp dBD hb₂B (h ▸ hd₂D)).elim
            · subst y
              constructor
              · intro hadj; exact (hnod₁ i hi hadj.symm).elim
              · rintro ⟨-, h⟩; exact (qne12 h).elim
            · subst y
              constructor
              · intro hadj; exact (hnoc₂ i hi hadj.symm).elim
              · rintro ⟨-, h⟩; exact (qne23 h.symm).elim
          · intro x hx y hy
            simp only [List.mem_singleton] at hy
            subst y
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with h | h | h | h
            · subst x
              constructor
              · intro hadj; exact (aAD a₁ ha₁A d₂ hd₂D hadj.symm).elim
              · rintro ⟨h, -⟩; exact (qne23 h).elim
            · subst x
              constructor
              · intro hadj; exact (n02 hadj.symm).elim
              · rintro ⟨h, -⟩
                exact (Set.disjoint_left.mp dBC hb₂B (h ▸ hc₂C)).elim
            · subst x
              constructor
              · intro hadj; exact (aAD a₁ ha₁A d₁ hd₁D hadj.symm).elim
              · rintro ⟨h, -⟩; exact (qne13 h).elim
            · subst x
              exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => (cAC a₁ ha₁A c₂ hc₂C).symm⟩
        have hev := no_odd_hole hG.1.1 hhole
        simp only [List.length_append, List.length_cons, List.length_nil] at hev
        obtain ⟨n, hn⟩ := hev
        omega
  · have hantiX : Anticomplete G X1 X2 := by
      intro x hx y hy hxy
      have hhole : IsHoleList G ([x] ++ f ++ [y]) := by
        refine isHoleList_three_blocks
          (P₀ := [x]) (P₁ := f) (P₂ := [y])
          (s₀ := x) (t₀ := x) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'hlast)
          (s₂ := y) (t₂ := y)
          ⟨PathBasics.isPathList_singleton G x, rfl, rfl⟩
          (isPathFrom_self hfpath hfpos)
          ⟨PathBasics.isPathList_singleton G y, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ (by simp; omega)
        · intro z hz hzf
          simp only [List.mem_singleton] at hz
          subst z
          exact hfout _ hzf hx.1
        · intro z hz hzy
          have hzx : z = x := by simpa using hz
          have hzy' : z = y := by simpa using hzy
          exact Set.disjoint_left.mp hXdisj hx ((hzx.symm.trans hzy') ▸ hy)
        · intro z hzf hzy
          have hzy' : z = y := by simpa using hzy
          exact hfne z hzf y hy.1 hzy'
        · intro z hz w hw
          simp only [List.mem_singleton] at hz
          subst z
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
          constructor
          · intro hadj
            exact ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr (hX1index x hx i hi hadj)⟩
          · rintro ⟨-, h⟩
            rw [h]
            exact hX1adj0 x hx
        · intro z hz w hw
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          simp only [List.mem_singleton] at hw
          subst w
          constructor
          · intro hadj
            exact ⟨(getElem_eq_iff hfnd hi hlast).mpr (hX2index y hy i hi hadj.symm), rfl⟩
          · rintro ⟨h, -⟩
            rw [h]
            exact (hX2adjlast y hy).symm
        · intro z hz w hw
          simp only [List.mem_singleton] at hz hw
          subst z; subst w
          exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => hxy.symm⟩
      have hev := no_odd_hole hG.1.1 hhole
      simp only [List.length_append, List.length_cons, List.length_nil] at hev
      obtain ⟨m, hm⟩ := hfodd
      obtain ⟨n, hn⟩ := hev
      omega
    have hAout : (A \ X1).Nonempty := by
      obtain ⟨a', ha'A, hb₀a'⟩ := exists_adj_left sAB hb₀B
      exact ⟨a', ha'A, fun ha'X => hantiX a' ha'X b₀ hb₀X2 hb₀a'.symm⟩
    have hBout : (B \ X2).Nonempty := by
      obtain ⟨b', hb'B, hab'⟩ := exists_adj_right sAB haA
      exact ⟨b', hb'B, fun hb'X => hantiX a haX1 b' hb'X hab'⟩
    have hCout : (C \ X1).Nonempty := by
      obtain ⟨c', hc'C, hc'd⟩ := exists_adj_of_mem_right dCD sCD hdD
      exact ⟨c', hc'C, fun hc'X => hantiX c' hc'X d hdX2 hc'd⟩
    have hDout : (D \ X2).Nonempty := by
      obtain ⟨d', hd'D, hc₀d'⟩ := exists_adj_of_mem_left dCD sCD hc₀C
      exact ⟨d', hd'D, fun hd'X => hantiX c₀ hc₀X1 d' hd'X hc₀d'⟩
    obtain ⟨a₁, b₁, b₂, a₂, habsq, ha₁X1, ha₂notX1⟩ :=
      exists_square_cross_left sAB X1 ⟨a, haA, haX1⟩ hAout
    obtain ⟨c₁, d₁, d₂, c₂, hcdsq, hd₁X2, hd₂notX2⟩ :=
      exists_square_cross_right sCD X2 ⟨d, hdD, hdX2⟩ hDout
    have ha₁A : a₁ ∈ A := habsq.2.1
    have ha₂A : a₂ ∈ A := habsq.2.2.1
    have hb₁B : b₁ ∈ B := habsq.2.2.2.1
    have hb₂B : b₂ ∈ B := habsq.2.2.2.2
    have hc₁C : c₁ ∈ C := hcdsq.2.1
    have hc₂C : c₂ ∈ C := hcdsq.2.2.1
    have hd₁D : d₁ ∈ D := hcdsq.2.2.2.1
    have hd₂D : d₂ ∈ D := hcdsq.2.2.2.2
    obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
      CubeMajorCoreContradiction.square_adj habsq
    obtain ⟨q01, q12, q23, q30, qn02, qn13, qne01, qne02, qne03, qne12, qne13,
      qne23⟩ := CubeMajorCoreContradiction.square_adj hcdsq
    have hb₁notX2 : b₁ ∉ X2 := fun hb₁X2 => hantiX a₁ ha₁X1 b₁ hb₁X2 e01
    have hc₂d₁ : G.Adj c₂ d₁ := (adj_of_not_compl_adj qne13 qn13).symm
    have hc₂notX1 : c₂ ∉ X1 := fun hc₂X1 => hantiX c₂ hc₂X1 d₁ hd₁X2 hc₂d₁
    have hno_of_notX1_left : ∀ x ∈ A ∪ C, x ∉ X1 →
        ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj x (f[i]'hi) := by
      intro x hxside hxnot i hi hadj
      by_cases hin : i + 1 < f.length
      · exact hxnot ⟨(hxside.elim hmA hmC), f[i]'hi, getElem_mem_dropLast hi hin, hadj⟩
      · have hi1 : 1 ≤ i := by omega
        have hx2 : x ∈ X2 :=
          ⟨(hxside.elim hmA hmC), f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
        rcases hxside with hxA | hxC <;> rcases hX2sub' hx2 with hxB | hxD
        · exact Set.disjoint_left.mp dAB hxA hxB
        · exact Set.disjoint_left.mp dAD hxA hxD
        · exact Set.disjoint_left.mp dBC hxB hxC
        · exact Set.disjoint_left.mp dCD hxC hxD
    have hno_of_notX2_right : ∀ x ∈ B ∪ D, x ∉ X2 →
        ∀ (i : ℕ) (hi : i < f.length), ¬ G.Adj x (f[i]'hi) := by
      intro x hxside hxnot i hi hadj
      by_cases hi0 : i = 0
      · subst i
        have hx1 : x ∈ X1 :=
          ⟨(hxside.elim hmB hmD), f[0]'hfpos, getElem_mem_dropLast hfpos (by omega), hadj⟩
        rcases hxside with hxB | hxD <;> rcases hX1sub' hx1 with hxA | hxC
        · exact Set.disjoint_left.mp dAB hxA hxB
        · exact Set.disjoint_left.mp dBC hxB hxC
        · exact Set.disjoint_left.mp dAD hxA hxD
        · exact Set.disjoint_left.mp dCD hxC hxD
      · have hi1 : 1 ≤ i := by omega
        exact hxnot ⟨(hxside.elim hmB hmD), f[i]'hi, getElem_mem_tail hi hi1, hadj⟩
    have hnoa₂ := hno_of_notX1_left a₂ (Or.inl ha₂A) ha₂notX1
    by_cases hb₂X2 : b₂ ∈ X2
    · have hnoc₂ := hno_of_notX1_left c₂ (Or.inr hc₂C) hc₂notX1
      have ha₁notf : a₁ ∉ f := fun hmem => hfout _ hmem (show a₁ ∈ A ∪ B ∪ C ∪ D from hmA ha₁A)
      have ha₁other : ∀ z ∈ f, z ≠ f[0]'hfpos → ¬ G.Adj a₁ z := by
        intro z hz hz0 hadj
        obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz
        have hi0 := hX1index a₁ ha₁X1 i hi (hiz ▸ hadj)
        exact hz0 (hiz.symm.trans ((getElem_eq_iff hfnd hi hfpos).mpr hi0))
      have hP₃ : IsPathFrom G (a₁ :: f) a₁ (f[f.length - 1]'hlast) :=
        PathAttach.isPathFrom_cons (isPathFrom_self hfpath hfpos) (hX1adj0 a₁ ha₁X1)
          ha₁notf ha₁other
      have hcross12 : ∀ u ∈ [a₂, b₂], ∀ v ∈ [c₂, d₁],
          (G.Adj u v ↔ (u = a₂ ∧ v = c₂) ∨ (u = b₂ ∧ v = d₁)) := by
        intro u hu v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · subst u; subst v; simp [cAC a₂ ha₂A c₂ hc₂C]
        · subst u; subst v
          have hcdne : c₂ ≠ d₁ := fun h => Set.disjoint_left.mp dCD hc₂C (h ▸ hd₁D)
          simp [aAD a₂ ha₂A d₁ hd₁D, ne23.symm, hcdne.symm]
        · subst u; subst v
          have hcdne : c₂ ≠ d₁ := fun h => Set.disjoint_left.mp dCD hc₂C (h ▸ hd₁D)
          simp [aBC b₂ hb₂B c₂ hc₂C, ne23, hcdne]
        · subst u; subst v; simp [cBD b₂ hb₂B d₁ hd₁D]
      have hcross13 : ∀ u ∈ [a₂, b₂], ∀ v ∈ a₁ :: f,
          (G.Adj u v ↔ (u = a₂ ∧ v = a₁) ∨
            (u = b₂ ∧ v = f[f.length - 1]'hlast)) := by
        intro u hu v hv
        simp only [List.mem_cons] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hv with hva₁ | hvf
        · subst v
          rcases hu with hua₂ | hub₂
          · subst u; simp [e30]
          · subst u
            constructor
            · intro hadj; exact (n02 hadj.symm).elim
            · intro h
              have h' : a₁ = f[f.length - 1]'hlast := by simpa [ne23] using h
              exact (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A) h'.symm).elim
        · obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hvf
          subst v
          rcases hu with hua₂ | hub₂
          · subst u
            constructor
            · intro hadj; exact (hnoa₂ i hi hadj).elim
            · rintro (⟨-, h⟩ | ⟨h, -⟩)
              · exact absurd h (hfne _ (List.getElem_mem hi) a₁ (hmA ha₁A))
              · exact absurd h ne23.symm
          · subst u
            constructor
            · intro hadj
              have hilast := hX2index b₂ hb₂X2 i hi hadj
              exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hi hlast).mpr hilast⟩
            · rintro (⟨h, -⟩ | ⟨-, h⟩)
              · exact absurd h ne23
              · rw [h]
                exact hX2adjlast b₂ hb₂X2
      have hcross23 : ∀ u ∈ [c₂, d₁], ∀ v ∈ a₁ :: f,
          (G.Adj u v ↔ (u = c₂ ∧ v = a₁) ∨
            (u = d₁ ∧ v = f[f.length - 1]'hlast)) := by
        intro u hu v hv
        simp only [List.mem_cons] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hv with hva₁ | hvf
        · subst v
          rcases hu with huc₂ | hud₁
          · subst u; simp [(cAC a₁ ha₁A c₂ hc₂C).symm]
          · subst u
            constructor
            · intro hadj; exact (aAD a₁ ha₁A d₁ hd₁D hadj.symm).elim
            · rintro (⟨h, -⟩ | ⟨-, h⟩)
              · exact (Set.disjoint_left.mp dCD hc₂C (h.symm ▸ hd₁D)).elim
              · exact (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A) h.symm).elim
        · obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hvf
          subst v
          rcases hu with huc₂ | hud₁
          · subst u
            constructor
            · intro hadj; exact (hnoc₂ i hi hadj).elim
            · rintro (⟨-, h⟩ | ⟨h, -⟩)
              · exact absurd h (hfne _ (List.getElem_mem hi) a₁ (hmA ha₁A))
              · exact absurd h (fun he => Set.disjoint_left.mp dCD hc₂C (he ▸ hd₁D))
          · subst u
            constructor
            · intro hadj
              have hilast := hX2index d₁ hd₁X2 i hi hadj
              exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hi hlast).mpr hilast⟩
            · rintro (⟨h, -⟩ | ⟨-, h⟩)
              · exact absurd h (fun he => Set.disjoint_left.mp dCD hc₂C (he.symm ▸ hd₁D))
              · rw [h]
                exact hX2adjlast d₁ hd₁X2
      have hprism : FormPrism G ![a₂, c₂, a₁]
          ![b₂, d₁, f[f.length - 1]'hlast] [a₂, b₂] [c₂, d₁] (a₁ :: f) := by
        refine formPrism_of_data
          (cAC a₂ ha₂A c₂ hc₂C) e30 (cAC a₁ ha₁A c₂ hc₂C).symm
          (cBD b₂ hb₂B d₁ hd₁D) (hX2adjlast b₂ hb₂X2)
          (hX2adjlast d₁ hd₁X2)
          ne23.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
          ⟨PathBasics.isPathList_pair hc₂d₁, rfl, rfl⟩ hP₃
          hcross12 hcross13 hcross23
        · intro h; exact Set.disjoint_left.mp dAD ha₂A (h ▸ hd₁D)
        · exact (hfne _ (List.getElem_mem hlast) a₂ (hmA ha₂A)).symm
        · intro h; exact Set.disjoint_left.mp dBC hb₂B (h.symm ▸ hc₂C)
        · intro h; exact Set.disjoint_left.mp dCD hc₂C (h ▸ hd₁D)
        · exact (hfne _ (List.getElem_mem hlast) c₂ (hmC hc₂C)).symm
        · exact ne02
        · intro h; exact Set.disjoint_left.mp dAD ha₁A (h.symm ▸ hd₁D)
        · exact (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A)).symm
      have hlong : 1 < pathLength (a₁ :: f) := by simp [pathLength]; omega
      exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inr (Or.inr hlong)⟩
    · have hnob₂ := hno_of_notX2_right b₂ (Or.inl hb₂B) hb₂X2
      have hreturn : IsPathFrom G [d₁, b₂, a₂] d₁ a₂ := by
        refine ⟨isPathList_triple ?_ (cBD b₂ hb₂B d₁ hd₁D).symm e23
          (fun h => aAD a₂ ha₂A d₁ hd₁D h.symm), rfl, rfl⟩
        have hd₁b₂ : d₁ ≠ b₂ := fun h => Set.disjoint_left.mp dBD hb₂B (h.symm ▸ hd₁D)
        have hd₁a₂ : d₁ ≠ a₂ := fun h => Set.disjoint_left.mp dAD ha₂A (h.symm ▸ hd₁D)
        simp [hd₁b₂, hd₁a₂, ne23]
      have hhole : IsHoleList G ([a₁] ++ f ++ [d₁, b₂, a₂]) := by
        refine isHoleList_three_blocks
          (P₀ := [a₁]) (P₁ := f) (P₂ := [d₁, b₂, a₂])
          (s₀ := a₁) (t₀ := a₁) (s₁ := f[0]'hfpos) (t₁ := f[f.length - 1]'hlast)
          (s₂ := d₁) (t₂ := a₂)
          ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩
          (isPathFrom_self hfpath hfpos) hreturn ?_ ?_ ?_ ?_ ?_ ?_ (by simp)
        · intro x hx hxf
          simp only [List.mem_singleton] at hx
          subst x; exact hfout _ hxf (hmA ha₁A)
        · intro x hx hmem
          simp only [List.mem_singleton] at hx
          subst x
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h | h
          · exact Set.disjoint_left.mp dAD ha₁A (h ▸ hd₁D)
          · exact ne02 h
          · exact ne03 h
        · intro x hx hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h | h
          · exact hfne x hx d₁ (hmD hd₁D) h
          · exact hfne x hx b₂ (hmB hb₂B) h
          · exact hfne x hx a₂ (hmA ha₂A) h
        · intro x hx y hy
          simp only [List.mem_singleton] at hx
          subst x
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
          constructor
          · intro hadj
            exact ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr (hX1index a₁ ha₁X1 i hi hadj)⟩
          · rintro ⟨-, h⟩; rw [h]; exact hX1adj0 a₁ ha₁X1
        · intro x hx y hy
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with h | h | h
          · subst y
            constructor
            · intro hadj
              exact ⟨(getElem_eq_iff hfnd hi hlast).mpr
                (hX2index d₁ hd₁X2 i hi hadj.symm), rfl⟩
            · rintro ⟨h, -⟩; rw [h]; exact (hX2adjlast d₁ hd₁X2).symm
          · subst y
            exact ⟨fun hadj => (hnob₂ i hi hadj.symm).elim,
              by rintro ⟨-, h⟩; exact (Set.disjoint_left.mp dBD hb₂B (h ▸ hd₁D)).elim⟩
          · subst y
            exact ⟨fun hadj => (hnoa₂ i hi hadj.symm).elim,
              by rintro ⟨-, h⟩; exact (Set.disjoint_left.mp dAD ha₂A (h ▸ hd₁D)).elim⟩
        · intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst y
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h
          · subst x
            constructor
            · intro hadj; exact (aAD a₁ ha₁A d₁ hd₁D hadj.symm).elim
            · rintro ⟨h, -⟩
              exact (Set.disjoint_left.mp dAD (h.symm ▸ ha₂A) hd₁D).elim
          · subst x
            constructor
            · intro hadj; exact (n02 hadj.symm).elim
            · rintro ⟨h, -⟩; exact (ne23 h).elim
          · subst x
            exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => e30⟩
      have hev := no_odd_hole hG.1.1 hhole
      simp only [List.length_append, List.length_cons, List.length_nil] at hev
      obtain ⟨m, hm⟩ := hfodd
      obtain ⟨n, hn⟩ := hev
      omega

/-! ## Minimal-counterexample assembly -/

/-- The first assertion of paper theorem 14.2. -/
theorem cubeMinorAttachmentContainment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF5 G)
    (A B C D : Set V) (hcube : MaximalCube G A B C D)
    (F : Set V) (hF : F ⊆ (A ∪ B ∪ C ∪ D)ᶜ) (hFconn : ConnectedSet G F)
    (hFminor : ∀ v ∈ F, MinorForCube G A B C D v)
    (X : Set V) (hX : X = attachments G F (A ∪ B ∪ C ∪ D)) :
    X ⊆ A ∪ B ∨ X ⊆ C ∪ D ∨ X ⊆ A ∪ C ∨ X ⊆ B ∪ D := by
  classical
  subst X
  by_contra hlocal
  have hbadF : Bad G A B C D F := ⟨hF, hFconn, hFminor, hlocal⟩
  let P : ℕ → Prop := fun n => ∃ F₀ : Set V, Bad G A B C D F₀ ∧ F₀.ncard = n
  have hP : ∃ n, P n := ⟨F.ncard, F, hbadF, rfl⟩
  let n₀ : ℕ := Nat.find hP
  obtain ⟨F₀, hbad₀, hcard₀⟩ := Nat.find_spec hP
  have hmin : ∀ F' : Set V, F' ⊆ F₀ → F' ≠ F₀ → ¬ Bad G A B C D F' := by
    intro F' hsub hne hbad'
    have hlt : F'.ncard < F₀.ncard :=
      Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩) (Set.toFinite _)
    have hle : n₀ ≤ F'.ncard := Nat.find_min' hP ⟨F', hbad', rfl⟩
    omega
  rcases meets_diagonal hbad₀ with hAD | hBC
  · obtain ⟨⟨a, haX, haA⟩, ⟨d, hdX, hdD⟩⟩ := hAD
    obtain ⟨f, hF₀, hcfg⟩ :=
      exists_pathConfig hcube.1 F₀ hbad₀ hmin a d haX haA hdX hdD
    rcases hcfg.locX1 with hAB | hAC
    · rcases hcfg.locX2 with hBD | hCD
      · exact claim_one hG hcube hcfg hAB hBD
      · exact claim_three hG hcube hcfg hAB hCD
    · rcases hcfg.locX2 with hBD | hCD
      · exact claim_four hG hcube hcfg hAC hBD
      · exact claim_two hG hcube hcfg hAC hCD
  · obtain ⟨⟨b, hbX, hbB⟩, ⟨c, hcX, hcC⟩⟩ := hBC
    have hcube' : MaximalCube G B A D C := maximalCube_swap hcube
    have hbad₀' : Bad G B A D C F₀ := bad_swap hbad₀
    have hmin' : ∀ F' : Set V, F' ⊆ F₀ → F' ≠ F₀ → ¬ Bad G B A D C F' := by
      intro F' hsub hne hbad'
      exact hmin F' hsub hne (bad_swap hbad')
    have hU : B ∪ A ∪ D ∪ C = A ∪ B ∪ C ∪ D := union4_swap A B C D
    have hbX' : b ∈ attachments G F₀ (B ∪ A ∪ D ∪ C) := by
      rw [hU]
      exact hbX
    have hcX' : c ∈ attachments G F₀ (B ∪ A ∪ D ∪ C) := by
      rw [hU]
      exact hcX
    obtain ⟨f, hF₀, hcfg⟩ :=
      exists_pathConfig hcube'.1 F₀ hbad₀' hmin' b c hbX' hbB hcX' hcC
    rcases hcfg.locX1 with hBA | hBD
    · rcases hcfg.locX2 with hAC | hDC
      · exact claim_one hG hcube' hcfg hBA hAC
      · exact claim_three hG hcube' hcfg hBA hDC
    · rcases hcfg.locX2 with hAC | hDC
      · exact claim_four hG hcube' hcfg hBD hAC
      · exact claim_two hG hcube' hcfg hBD hDC

end Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore
