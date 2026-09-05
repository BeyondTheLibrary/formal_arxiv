import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.Thm94ClosingEnlarge
import Workspace.ProofLemmas.Thm94ClosingMaximal

/-!
# The enlargement contradiction in the closing paragraph of 9.4
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94ClosingContradiction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (9.4, closing paragraph): if `f` copies the first end of one strip on every
antistrip and has a neighbour farther along a rung, adjoining `f` to that end contradicts the
maximality of the striation. -/
theorem adjoin_left_contradiction {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hmax : MaximalStriation G S T) {f : V}
    (hfL : f ∉ striationVertices S T) (i : Fin m) {A C B : Set V}
    (hSi : S i = (A, C, B)) {P : List V} {a b : V}
    (hP : IsSRung G (S i) P) (hPab : IsPathFrom G P a b) (ha : a ∈ A)
    (hnear : ∃ z ∈ ({z : V | z ∈ P} \ {a} : Set V), G.Adj f z)
    (hcopy : ∀ j : Fin n, ∀ z ∈ stripVertices (T j), G.Adj f z ↔ G.Adj a z)
    (hfanti : ∀ k : Fin m, i ≠ k → VertexAnticomplete G f (stripVertices (S k))) : False := by
  let R : Set V × Set V × Set V := (A ∪ {f}, C, B)
  have hSold : IsStrip G (A, C, B) := by rw [← hSi]; exact hmax.1.1 i
  have hfstrip : f ∉ stripVertices ((A, C, B) : Set V × Set V × Set V) := by
    rw [← hSi]
    intro hf
    exact hfL (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hf⟩))
  have hP' : IsSRung G (A, C, B) P := by rwa [← hSi]
  have hR : IsStrip G R :=
    Thm94ClosingEnlarge.isStrip_adjoin_left hSold hfstrip hP' hPab hnear
  have hverts : stripVertices R = stripVertices (S i) ∪ {f} := by
    rw [hSi]
    ext x
    simp only [R, stripVertices, Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hpar : ∀ j : Fin n, ParallelStripAntistrip G (S i) (T j) →
      ParallelStripAntistrip G R (T j) := by
    intro j h
    rw [hSi] at h
    exact Thm94ClosingEnlarge.parallel_adjoin_left ha (hcopy j) h
  have hco : ∀ j : Fin n, CoParallel G (S i) (T j) → CoParallel G R (T j) := by
    intro j h
    rw [hSi] at h
    exact Thm94ClosingEnlarge.coParallel_adjoin_left ha (hcopy j) h
  have hodd := Thm94ClosingEnlarge.odd_rungs_of_replacement hG hmax.1 hfL i R hR hverts
    hfanti hpar hco
  exact Thm94ClosingMaximal.replacement_contradicts_maximality hmax hfL i R hR hverts hodd
    hfanti hpar hco

/-- The last-end mirror of `adjoin_left_contradiction`. -/
theorem adjoin_right_contradiction {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hmax : MaximalStriation G S T) {f : V}
    (hfL : f ∉ striationVertices S T) (i : Fin m) {A C B : Set V}
    (hSi : S i = (A, C, B)) {P : List V} {a b : V}
    (hP : IsSRung G (S i) P) (hPab : IsPathFrom G P a b) (hb : b ∈ B)
    (hnear : ∃ z ∈ ({z : V | z ∈ P} \ {b} : Set V), G.Adj f z)
    (hcopy : ∀ j : Fin n, ∀ z ∈ stripVertices (T j), G.Adj f z ↔ G.Adj b z)
    (hfanti : ∀ k : Fin m, i ≠ k → VertexAnticomplete G f (stripVertices (S k))) : False := by
  let R : Set V × Set V × Set V := (A, C, B ∪ {f})
  have hSold : IsStrip G (A, C, B) := by rw [← hSi]; exact hmax.1.1 i
  have hfstrip : f ∉ stripVertices ((A, C, B) : Set V × Set V × Set V) := by
    rw [← hSi]
    intro hf
    exact hfL (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hf⟩))
  have hP' : IsSRung G (A, C, B) P := by rwa [← hSi]
  have hR : IsStrip G R :=
    Thm94ClosingEnlarge.isStrip_adjoin_right hSold hfstrip hP' hPab hnear
  have hverts : stripVertices R = stripVertices (S i) ∪ {f} := by
    rw [hSi]
    ext x
    simp only [R, stripVertices, Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hpar : ∀ j : Fin n, ParallelStripAntistrip G (S i) (T j) →
      ParallelStripAntistrip G R (T j) := by
    intro j h
    rw [hSi] at h
    exact Thm94ClosingEnlarge.parallel_adjoin_right hb (hcopy j) h
  have hco : ∀ j : Fin n, CoParallel G (S i) (T j) → CoParallel G R (T j) := by
    intro j h
    rw [hSi] at h
    exact Thm94ClosingEnlarge.coParallel_adjoin_right hb (hcopy j) h
  have hodd := Thm94ClosingEnlarge.odd_rungs_of_replacement hG hmax.1 hfL i R hR hverts
    hfanti hpar hco
  exact Thm94ClosingMaximal.replacement_contradicts_maximality hmax hfL i R hR hverts hodd
    hfanti hpar hco

end Workspace.ProofLemmas.Thm94ClosingContradiction
