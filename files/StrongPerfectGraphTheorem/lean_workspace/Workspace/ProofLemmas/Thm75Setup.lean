import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# Setup vocabulary for the proof of 7.5

PAPER (proof of 7.5, printed p. 35): *"For each edge `uv` of `J`, let `Buv` be the branch of `H`
with ends `u, v`, and let `Ruv` be the path `L(Buv)` of `L(H)`.  For each `v ∈ V(J)` let `Nv` be
the clique of `L(H)` with vertex set `δ_H(v)`. … some vertex of `G` is nonadjacent in `G` to at
most one vertex of `Nc₁` and to at most one vertex of `Nc₂`.  We say such a vertex `v` is
`Bc₁c₂`-dominant with respect to `L(H)`. … Let `Y` be a maximal anticonnected set of vertices
each with at most one non-neighbour in `Nc₁` and at most one non-neighbour in `Nc₂`."*

This module records the two proof-local notions (`NSet`, the clique `N_c` read as a set of
vertices of `G`; and `IsDominantFor`, the paper's "`B`-dominant") and proves the existence of the
maximal anticonnected set `Y` that the proof fixes.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- PAPER: *"For each `v ∈ V(J)` let `Nv` be the clique of `L(H)` with vertex set `δ_H(v)`."*

The vertices of `L(H)` are the edges of `H`, and `φ` identifies them with the vertices of `G`
lying in `K`, so `N_c` is the image under `φ` of `δ_H(c) = incidentEdges H c`.  This is exactly
the set that 5.8 calls `N c` (see the hypothesis `hN` of `thm_5_8`). -/
def NSet {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) : Set V :=
  {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
    e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)}

/-- PAPER: *"some vertex of `G` is nonadjacent in `G` to at most one vertex of `Nc₁` and to at
most one vertex of `Nc₂`.  We say such a vertex `v` is `Bc₁c₂`-dominant with respect to
`L(H)`."*

"Nonadjacent to at most one vertex of `N`" is `(N \ G.neighborSet v).Subsingleton`, matching the
encoding of `Overshadowed.IsOvershadowedAppearance`. -/
def IsDominantFor {V : Type*} (G : SimpleGraph V) (N₁ N₂ : Set V) (v : V) : Prop :=
  (N₁ \ G.neighborSet v).Subsingleton ∧ (N₂ \ G.neighborSet v).Subsingleton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: *"Let `Y` be a maximal anticonnected set of vertices each with at most one
non-neighbour in `Nc₁` and at most one non-neighbour in `Nc₂`."*

Given one vertex `v` with the property `P` (in the application, one `Bc₁c₂`-dominant vertex,
supplied by the hypothesis that the appearance is overshadowed), there is a maximal anticonnected
set of vertices with property `P`, and it may be taken to contain `v`.  Maximality is stated as
the paper uses it: no strictly larger anticonnected set of `P`-vertices exists. -/
theorem exists_maximal_anticonnected {G : SimpleGraph V} (P : V → Prop) (v : V) (hv : P v) :
    ∃ Y : Set V, v ∈ Y ∧ AnticonnectedSet G Y ∧ (∀ y ∈ Y, P y) ∧
      ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' → (∀ y ∈ Y', P y) → Y' = Y := by
  classical
  set 𝒞 : Set (Set V) :=
    {Z : Set V | v ∈ Z ∧ AnticonnectedSet G Z ∧ ∀ y ∈ Z, P y} with h𝒞
  have hsingle : ({v} : Set V) ∈ 𝒞 := by
    refine ⟨rfl, ?_, ?_⟩
    · -- a singleton is (anti)connected
      intro a b
      have : a = b := Subtype.ext (by
        have ha : (a : V) = v := a.2
        have hb : (b : V) = v := b.2
        rw [ha, hb])
      exact this ▸ SimpleGraph.Reachable.refl a
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hv
  have hfin : 𝒞.Finite := Set.toFinite _
  obtain ⟨Y, hYmax⟩ := Set.Finite.exists_maximal hfin ⟨{v}, hsingle⟩
  obtain ⟨hvY, hYanti, hYP⟩ := hYmax.1
  refine ⟨Y, hvY, hYanti, hYP, ?_⟩
  intro Y' hsub hanti hP
  have hY'𝒞 : Y' ∈ 𝒞 := ⟨hsub hvY, hanti, hP⟩
  exact Set.Subset.antisymm (hYmax.2 hY'𝒞 hsub) hsub

end Workspace.ProofLemmas.Thm75Setup
