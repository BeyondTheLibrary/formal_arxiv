import Workspace.ProofLemmas.Thm93KnotSubdivision
import Workspace.ProofLemmas.Thm93KnotHostIso

/-!
# The knot dictionary for the canonical appearance

PAPER (9.3, printed p. 48, and the table in `AppearanceFromKnot`): the four cross edges of the
degenerate four-cycle are `x₁ = c₁c₂`, `y₂ = c₂c₃`, `y₁ = c₃c₄`, `x₂ = c₄c₁`, and the two
branches `c₁c₃`, `c₂c₄` carry the two paths `P₁`, `P₂`.

This file reads the incident-edge stars `δ_H(cᵢ)` and the two branches back as sets of
vertices of `graph m n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93KnotDictionary

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93KnotModel
open Workspace.ProofLemmas.Thm93KnotHost
open Workspace.ProofLemmas.Thm93KnotSubdivision

variable {m n : ℕ}

theorem mem_incidentEdges_iff (hm : 2 ≤ m) (hn : 2 ≤ n) (c : Host m n) (u : Vertex m n) :
    edgeOf m n u ∈ incidentEdges (host m n) c ↔ c ∈ edgeOf m n u :=
  ⟨fun h => h.2, fun h => ⟨edgeOf_mem_edgeSet (by omega) (by omega) u, h⟩⟩

theorem c1_mem_edgeOf (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n) :
    c1 m n ∈ edgeOf m n u ↔
      u = cross 0 ∨ u = cross 1 ∨ u = Sum.inl (⟨0, by omega⟩ : Fin m) := by
  rcases u with i | j | k
  · have hi := i.isLt
    simp [edgeOf, c1, cross, Sym2.mem_iff, Fin.ext_iff]
    omega
  · simp [edgeOf, c1, cross, Sym2.mem_iff]
  · have hne : (0 : ℕ) ≠ m := by omega
    fin_cases k <;>
      simp [edgeOf, c1, c2, c3, c4, cross, Sym2.mem_iff, Fin.ext_iff, hne] <;> omega

theorem c2_mem_edgeOf (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n) :
    c2 m n ∈ edgeOf m n u ↔
      u = cross 0 ∨ u = cross 3 ∨ u = Sum.inr (Sum.inl (⟨0, by omega⟩ : Fin n)) := by
  rcases u with i | j | k
  · simp [edgeOf, c2, cross, Sym2.mem_iff]
  · have hj := j.isLt
    simp [edgeOf, c2, cross, Sym2.mem_iff, Fin.ext_iff]
    omega
  · have hne : (0 : ℕ) ≠ n := by omega
    fin_cases k <;>
      simp [edgeOf, c1, c2, c3, c4, cross, Sym2.mem_iff, Fin.ext_iff, hne] <;> omega

theorem c3_mem_edgeOf (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n) :
    c3 m n ∈ edgeOf m n u ↔
      u = cross 2 ∨ u = cross 3 ∨ u = Sum.inl (⟨m - 1, by omega⟩ : Fin m) := by
  rcases u with i | j | k
  · have hi := i.isLt
    simp [edgeOf, c3, cross, Sym2.mem_iff, Fin.ext_iff, Fin.val_last]
    omega
  · simp [edgeOf, c3, cross, Sym2.mem_iff]
  · have hne : (0 : ℕ) ≠ m := by omega
    fin_cases k <;>
      simp [edgeOf, c1, c2, c3, c4, cross, Sym2.mem_iff, Fin.ext_iff, Fin.val_last, hne] <;>
      omega

theorem c4_mem_edgeOf (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n) :
    c4 m n ∈ edgeOf m n u ↔
      u = cross 2 ∨ u = cross 1 ∨ u = Sum.inr (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) := by
  rcases u with i | j | k
  · simp [edgeOf, c4, cross, Sym2.mem_iff]
  · have hj := j.isLt
    simp [edgeOf, c4, cross, Sym2.mem_iff, Fin.ext_iff, Fin.val_last]
    omega
  · have hne : (0 : ℕ) ≠ n := by omega
    fin_cases k <;>
      simp [edgeOf, c1, c2, c3, c4, cross, Sym2.mem_iff, Fin.ext_iff, Fin.val_last, hne] <;>
      omega

theorem edgeOf_mem_trackEdges_chainA (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n) :
    edgeOf m n u ∈ trackEdges (chainA m n) ↔ ∃ i : Fin m, u = Sum.inl i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := mem_trackEdges_chainA.mp h
    exact ⟨i, edgeOf_injective hm hn hi⟩
  · rintro ⟨i, rfl⟩
    exact mem_trackEdges_chainA.mpr ⟨i, rfl⟩

theorem edgeOf_mem_trackEdges_chainB (hm : 2 ≤ m) (hn : 2 ≤ n) (u : Vertex m n) :
    edgeOf m n u ∈ trackEdges (chainB m n) ↔ ∃ j : Fin n, u = Sum.inr (Sum.inl j) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_trackEdges_chainB.mp h
    exact ⟨j, edgeOf_injective hm hn hj⟩
  · rintro ⟨j, rfl⟩
    exact mem_trackEdges_chainB.mpr ⟨j, rfl⟩

end Workspace.ProofLemmas.Thm93KnotDictionary
