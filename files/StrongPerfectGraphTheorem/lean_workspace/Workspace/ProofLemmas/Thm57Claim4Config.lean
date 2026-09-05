import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.TrackSlice

/-!
# 5.7 (4): the auxiliary graph `K` on the six ends

PAPER (printed p. 24):

> *"For `1 ≤ i ≤ 3` let `xᵢ` have ends `aᵢ, bᵢ`, where `a₁, a₂, a₃` have the same biparity.
> Let `K` be the graph with vertex set `{a₁,a₂,a₃,b₁,b₂,b₃}`, in which two vertices of `K`
> are adjacent if there is a track in `A` joining them not using any other vertex of `K`."*

This file only sets up that auxiliary graph and records the two easy facts about it: it is
symmetric, and both of its ends lie in `A`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm57Claim4Config

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The six ends of the three marked edges — the vertex set of the auxiliary graph `K`. -/
def Terminals (x : Fin 3 → Sym2 W) : Set W := {u | ∃ i, u ∈ x i}

theorem mem_terminals {x : Fin 3 → Sym2 W} {i : Fin 3} {u : W} (h : u ∈ x i) :
    u ∈ Terminals x := ⟨i, h⟩

/-- **Adjacency in `K`**: *"two vertices of `K` are adjacent if there is a track in `A`
joining them not using any other vertex of `K`"*.  Tracks *in `A`* are tracks of `H \ X`
all of whose vertices lie in `A`. -/
def KAdj (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W) (x : Fin 3 → Sym2 W)
    (u v : W) : Prop :=
  ∃ P : List W, IsTrackFrom (H.deleteEdges X) P u v ∧ (∀ z ∈ P, z ∈ A) ∧
    (∀ z ∈ P, z ∈ Terminals x → z = u ∨ z = v)

theorem kAdj_symm {H : SimpleGraph W} {X : Set (Sym2 W)} {A : Set W} {x : Fin 3 → Sym2 W}
    {u v : W} (h : KAdj H X A x u v) : KAdj H X A x v u := by
  obtain ⟨P, hP, hPA, hPT⟩ := h
  exact ⟨P.reverse, Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hP,
    fun z hz => hPA z (List.mem_reverse.mp hz),
    fun z hz hzT => (hPT z (List.mem_reverse.mp hz) hzT).symm⟩

theorem kAdj_mem_left {H : SimpleGraph W} {X : Set (Sym2 W)} {A : Set W} {x : Fin 3 → Sym2 W}
    {u v : W} (h : KAdj H X A x u v) : u ∈ A := by
  obtain ⟨P, hP, hPA, -⟩ := h
  exact hPA u (List.mem_of_mem_head? (by exact hP.2.1))

theorem kAdj_mem_right {H : SimpleGraph W} {X : Set (Sym2 W)} {A : Set W} {x : Fin 3 → Sym2 W}
    {u v : W} (h : KAdj H X A x u v) : v ∈ A :=
  kAdj_mem_left (kAdj_symm h)

/-- An edge of `K` between ends of two *different* marked edges is an
`EndpointCleanConnection`, so the colour step already proved in `Thm57Claim4Core` applies to
it: *"If some two of `a₁,a₂,a₃` are adjacent in `K`, then the corresponding track in `A` is
even, contrary to the hypothesis of the theorem"*. -/
theorem kAdj_col_ne {H : SimpleGraph W} {X : Set (Sym2 W)} {A : Set W} {x : Fin 3 → Sym2 W}
    {col : H.Coloring Bool}
    (hdisj : ∀ i j, i ≠ j → DisjointEdges (x i) (x j))
    (hpair : ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      (IsTrackFrom (H.deleteEdges X) P u v ∧ (∀ z ∈ P, z ∈ x i → z = u) ∧
        (∀ z ∈ P, z ∈ x j → z = v)) → col u ≠ col v)
    {i j : Fin 3} (hij : i ≠ j) {u v : W} (hu : u ∈ x i) (hv : v ∈ x j)
    (h : KAdj H X A x u v) : col u ≠ col v := by
  obtain ⟨P, hP, -, hPT⟩ := h
  refine hpair i j hij u v P hu hv ⟨hP, ?_, ?_⟩
  · intro z hz hzi
    rcases hPT z hz (mem_terminals hzi) with h | h
    · exact h
    · exact absurd (h ▸ hzi) (fun hc => hdisj i j hij v ⟨hc, hv⟩)
  · intro z hz hzj
    rcases hPT z hz (mem_terminals hzj) with h | h
    · exact absurd (h ▸ hzj) (fun hc => hdisj i j hij u ⟨hu, hc⟩)
    · exact h

end Workspace.ProofLemmas.Thm57Claim4Config
