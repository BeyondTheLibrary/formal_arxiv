import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm121Symmetry

/-!
# 12.1, case (1) of the printed proof

PAPER (printed p. 69): *"(1) If `v` is left- or right-diagonal then the theorem holds.*

*For assume `v` is right-diagonal say.  If it has no neighbours in `A ∪ C` then statement 3 of
the theorem holds, so we assume there is a step `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` such that `v` has
a neighbour in `R₁ \ b₁`.  Hence it can be linked onto the triangle `{a₀, a₁, a₂}`, via
`v`-`a₀`, the path from `v` to `a₁` with interior in `R₁ \ b₁`, and the path from `v` to `a₂`
with interior in `R₂`, and so by 2.4, `v` has a neighbour in `A`.  So it is major, and therefore
statement 2 holds.  This proves (1)."*

(The left-diagonal case is the mirror image, obtained by exchanging `A` with `B` and `a₀` with
`b₀`.)  The result cited is 2.4, the Roussel–Rubio "linking onto a triangle" lemma.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm121Case1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

section Helpers

variable {V : Type*} {G : SimpleGraph V} {A C B : Set V}

/-- Every vertex of a rung of the strip `(A, C, B)` lies in `V(S) = A ∪ B ∪ C`. -/
private theorem rung_mem_union {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : ∀ y ∈ p, y ∈ A ∪ B ∪ C := by
  intro y hy
  by_cases hya : y = a
  · exact Or.inl (Or.inl (by rw [hya]; exact h.2.1))
  by_cases hyb : y = b
  · exact Or.inl (Or.inr (by rw [hyb]; exact h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 y
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr ⟨hy, hya, hyb⟩))

/-- A vertex of a rung which is neither of its two ends lies in `C`. -/
private theorem rung_mem_C {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) {y : V} (hy : y ∈ p) (hya : y ≠ a) (hyb : y ≠ b) :
    y ∈ C :=
  h.2.2.2.2.2 y ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr
    ⟨hy, hya, hyb⟩)

/-- A step is symmetric in its two rungs. -/
private theorem step_symm {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) : IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  obtain ⟨h1, h2, hdisj, hadj⟩ := h
  refine ⟨h2, h1, ?_, ?_⟩
  · intro x hx hx'
    exact hdisj x hx' hx
  · intro u hu w hw
    rw [SimpleGraph.adj_comm]
    have := hadj w hw u hu
    tauto

/-- The paper's *"the path from `v` to `a₁` with interior in `R₁ \ b₁`"* needs the initial
segment `R₁ \ b₁` of a rung: dropping the last vertex of a path with distinct ends leaves a
path with the same first vertex, whose vertices are exactly those of the original other than
its last one. -/
private theorem init_path {p : List V} {u w : V}
    (hp : IsPathFrom G p u w) (huw : u ≠ w) :
    IsPathList G p.dropLast ∧ p.dropLast.head? = some u ∧
      ∀ y : V, (y ∈ p.dropLast ↔ (y ∈ p ∧ y ≠ w)) := by
  have hne : p ≠ [] := hp.1.1
  have hnd : p.Nodup := hp.1.2.1
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hne
  have hlast : p.getLast hne = w := by
    have h := hp.2.2
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  have h2 : 2 ≤ p.length := by
    by_contra hc
    push_neg at hc
    have h1 : p.length = 1 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    subst ha
    have e1 : a = u := by simpa using hp.2.1
    have e2 : a = w := by simpa using hp.2.2
    exact huw (by rw [← e1, e2])
  have hdl : p.dropLast = p.take (p.length - 1) := List.dropLast_eq_take
  refine ⟨?_, ?_, ?_⟩
  · rw [hdl]
    exact Workspace.ProofLemmas.PathBasics.isPathList_take hp.1 (by omega)
  · have h0 : 0 < (p.take (p.length - 1)).length := by
      rw [List.length_take]; omega
    rw [hdl, List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    congr 1
    rw [List.getElem_take]
    exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 hpos
  · intro y
    rw [Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hnd hne, hlast]

end Helpers

/-- The right-diagonal half of case (1) — the case the paper writes out. -/
private theorem rightDiagonalCase {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (hrd : RightDiagonal G A C B a₀ R₀ b₀ v) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  have hlen : 3 ≤ SPGT.pathLength R₀ := hK.1.2.2
  have hls : IsLeftStar G A C B a₀ := hban.2.2.1
  have hvS : v ∉ A ∪ B ∪ C := fun h => hv (Or.inr h)
  have hvB : SPGT.VertexComplete G v B := fun x hx => hrd.2 x (Or.inl hx)
  have hva₀ : G.Adj v a₀ := hrd.2 a₀ (Or.inr rfl)
  have ha₀R₀ : a₀ ∈ R₀ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hban.1).1
  have ha₀b₀ : a₀ ≠ b₀ :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hban.1 (by omega)
  by_cases hAC : ∃ x ∈ A ∪ C, G.Adj v x
  · -- PAPER: *"so we assume there is a step `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` such that `v` has a
    -- neighbour in `R₁ \ b₁`"*
    obtain ⟨x, hxAC, hvx⟩ := hAC
    have hxS : x ∈ A ∪ B ∪ C := by
      rcases hxAC with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hxmem⟩ := hS.2.2.2.1 x hxS
    -- name the rung containing `x` as the first one
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hxR₁⟩ :
        ∃ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
          IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ x ∈ R₁ := by
      rcases hxmem with h | h
      · exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, h⟩
      · exact ⟨a₂, R₂, b₂, a₁, R₁, b₁, step_symm hstep, h⟩
    obtain ⟨hr₁, hr₂, hdisj, hcross⟩ := hstep
    have ha₁A : a₁ ∈ A := hr₁.2.1
    have hb₁B : b₁ ∈ B := hr₁.2.2.1
    have ha₂A : a₂ ∈ A := hr₂.2.1
    have hb₂B : b₂ ∈ B := hr₂.2.2.1
    have ha₂R₂ : a₂ ∈ R₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).1
    have hb₂R₂ : b₂ ∈ R₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).2
    have ha₁b₁ : a₁ ≠ b₁ := by
      rintro rfl
      exact (hS.1.1.le_bot ⟨ha₁A, hb₁B⟩ : a₁ ∈ (⊥ : Set V))
    have ha₂b₂ : a₂ ≠ b₂ := by
      rintro rfl
      exact (hS.1.1.le_bot ⟨ha₂A, hb₂B⟩ : a₂ ∈ (⊥ : Set V))
    -- `x` is not `b₁`, since `x ∈ A ∪ C` and `b₁ ∈ B`
    have hxb₁ : x ≠ b₁ := by
      rintro rfl
      rcases hxAC with hx | hx
      · exact (hS.1.1.le_bot ⟨hx, hb₁B⟩ : x ∈ (⊥ : Set V))
      · exact (hS.1.2.2.le_bot ⟨hb₁B, hx⟩ : x ∈ (⊥ : Set V))
    obtain ⟨hP₂path, hP₂head, hP₂mem⟩ := init_path hr₁.1 ha₁b₁
    -- the three paths of the link onto the triangle `{a₀, a₁, a₂}`
    have hlink : (G.Adj v a₀ ∧ G.Adj v a₁) ∨ (G.Adj v a₀ ∧ G.Adj v a₂) ∨
        (G.Adj v a₁ ∧ G.Adj v a₂) := by
      refine _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v a₀ a₁ a₂
        ⟨[a₀], R₁.dropLast, R₂, ⟨Workspace.ProofLemmas.PathBasics.isPathList_singleton G a₀,
          hP₂path, hr₂.1.1⟩, ⟨?_, ?_, ?_⟩, ⟨Or.inl rfl, Or.inl hP₂head, Or.inl hr₂.1.2.1⟩,
          ⟨?_, ?_, ?_⟩, ⟨⟨a₀, List.mem_singleton_self a₀, hva₀⟩,
            ⟨x, (hP₂mem x).mpr ⟨hxR₁, hxb₁⟩, hvx⟩, ⟨b₂, hb₂R₂, hvB b₂ hb₂B⟩⟩⟩
      · -- `a₀ ∉ R₁ \ b₁`
        intro y hy
        rw [List.mem_singleton] at hy
        subst hy
        intro hc
        exact hls.1 (rung_mem_union hr₁ y ((hP₂mem y).mp hc).1)
      · -- `a₀ ∉ R₂`
        intro y hy
        rw [List.mem_singleton] at hy
        subst hy
        intro hc
        exact hls.1 (rung_mem_union hr₂ y hc)
      · -- `R₁ \ b₁` is disjoint from `R₂`
        intro y hy
        exact hdisj y ((hP₂mem y).mp hy).1
      · -- the only edge between `{a₀}` and `R₁ \ b₁` is `a₀a₁`
        intro y hy z hz
        rw [List.mem_singleton] at hy
        subst hy
        obtain ⟨hzR₁, hzb₁⟩ := (hP₂mem z).mp hz
        constructor
        · intro hadj
          refine ⟨rfl, ?_⟩
          by_contra hza₁
          exact hls.2.2 z (Or.inr (rung_mem_C hr₁ hzR₁ hza₁ hzb₁)) hadj
        · rintro ⟨-, rfl⟩
          exact hls.2.1 z ha₁A
      · -- the only edge between `{a₀}` and `R₂` is `a₀a₂`
        intro y hy z hz
        rw [List.mem_singleton] at hy
        subst hy
        constructor
        · intro hadj
          refine ⟨rfl, ?_⟩
          by_contra hza₂
          by_cases hzb₂ : z = b₂
          · exact hls.2.2 z (Or.inl (by rw [hzb₂]; exact hb₂B)) hadj
          · exact hls.2.2 z (Or.inr (rung_mem_C hr₂ hz hza₂ hzb₂)) hadj
        · rintro ⟨-, rfl⟩
          exact hls.2.1 z ha₂A
      · -- the only edge between `R₁ \ b₁` and `R₂` is `a₁a₂`
        intro y hy z hz
        obtain ⟨hyR₁, hyb₁⟩ := (hP₂mem y).mp hy
        rw [hcross y hyR₁ z hz]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h.1 hyb₁
        · exact fun h => Or.inl h
    -- PAPER: *"and so by 2.4, `v` has a neighbour in `A`.  So it is major, and therefore
    -- statement 2 holds."*
    have hvA : ∃ y ∈ A, G.Adj v y := by
      rcases hlink with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact ⟨a₁, ha₁A, h⟩
      · exact ⟨a₂, ha₂A, h⟩
      · exact ⟨a₁, ha₁A, h⟩
    obtain ⟨b, hbB⟩ := hS.2.1.2
    exact Or.inr (Or.inl ⟨⟨hv, hvA, ⟨b, hbB, hvB b hbB⟩, ⟨a₀, ha₀R₀, hva₀⟩⟩,
      Or.inr (Or.inl hrd)⟩)
  · -- PAPER: *"If it has no neighbours in `A ∪ C` then statement 3 of the theorem holds"*
    push_neg at hAC
    exact Or.inr (Or.inr (Or.inr ⟨⟨hvS, hvB, hAC⟩, a₀, ha₀R₀, ha₀b₀, hva₀⟩))

/-- **12.1 (1)**: *"If `v` is left- or right-diagonal then the theorem holds."* -/
theorem thm121Case1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (hdiag : LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  rcases hdiag with hld | hrd
  · -- PAPER: *"assume `v` is right-diagonal **say**"* — the left-diagonal case is the mirror
    -- image, obtained by exchanging the two ends of the strip.
    refine Workspace.ProofLemmas.Thm121Symmetry.thm121SwapConclusion G A C B a₀ b₀ R₀ v ?_
    have hv' : v ∉ staircaseVertices B C A R₀.reverse := by
      rw [Workspace.ProofLemmas.Thm121Symmetry.thm121SwapVertices A C B R₀]; exact hv
    exact rightDiagonalCase G hG B C A b₀ a₀ R₀.reverse
      (Workspace.ProofLemmas.Thm121Symmetry.thm121SwapStaircase G A C B a₀ b₀ R₀ hK) v hv'
      ⟨hv', hld.2⟩
  · exact rightDiagonalCase G hG A C B a₀ b₀ R₀ hK v hv hrd

end Workspace.ProofLemmas.Thm121Case1
