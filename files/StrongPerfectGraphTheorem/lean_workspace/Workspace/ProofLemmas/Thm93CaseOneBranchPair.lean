import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# An edge between two branch-vertices is a branch

PAPER (9.3, printed p. 48): the four edges of the named four-cycle of a degenerate `K₄`
appearance are branches of `H` all by themselves.  The paper uses this silently when it speaks
of *"the edge `b₁b₂` of `J`"* and identifies it with a branch of `H`.

This module proves the one fact needed: a track `[u, v]` given by an edge of `H` both of whose
ends are branch-vertices is a branch of `H`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm93CaseOneBranchPair

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*}

/-- The edge set of the two-vertex track `[u, v]`. -/
theorem trackEdges_pair (u v : W) : trackEdges [u, v] = {s(u, v)} := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    subst this
    rfl
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

/-- `[u, v]` is a track from `u` to `v` whenever `uv` is an edge. -/
theorem isTrackFrom_pair {H : SimpleGraph W} {u v : W} (h : H.Adj u v) :
    IsTrackFrom H [u, v] u v := by
  refine ⟨⟨by simp, by simp [h.ne], ?_⟩, by simp, by simp⟩
  intro i hi
  have : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
  subst this
  exact h

/-- A track whose two ends are `u` and `v`, and on which `u` and `v` are consecutive, has
exactly two vertices. -/
theorem length_eq_two_of_ends_adjacent {q : List W} {u v : W}
    (hnd : q.Nodup) (hu : u ∈ q) (hv : v ∈ q)
    (hune : u ∉ trackInterior q) (hvne : v ∉ trackInterior q)
    (hedge : s(u, v) ∈ trackEdges q) : q.length = 2 := by
  have h0 : 0 < q.length := by
    rcases q with _ | ⟨a, l⟩
    · simp at hu
    · simp
  -- a vertex of `q` that is not internal sits at index `0` or at index `q.length - 1`
  have hidx : ∀ (j : ℕ) (hj : j < q.length), (q[j]'hj) ∉ trackInterior q →
      j = 0 ∨ j = q.length - 1 := by
    intro j hj hjn
    rcases DegenerateK4Tracks.mem_ends_of_notMem_interior (List.getElem_mem hj) hjn h0 with
      he | he
    · exact Or.inl ((hnd.getElem_inj_iff).mp he)
    · exact Or.inr ((hnd.getElem_inj_iff).mp he)
  obtain ⟨i, hi, hie⟩ := hedge
  have key : (i = 0 ∨ i = q.length - 1) → (i + 1 = 0 ∨ i + 1 = q.length - 1) →
      q.length = 2 := by omega
  rcases Sym2.eq_iff.mp hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key (hidx i (by omega) (h1 ▸ hune)) (hidx (i + 1) hi (h2 ▸ hvne))
  · exact key (hidx i (by omega) (h2 ▸ hvne)) (hidx (i + 1) hi (h1 ▸ hune))

/-- **An edge joining two branch-vertices is a branch.** -/
theorem isBranch_pair {H : SimpleGraph W} {u v : W} (h : H.Adj u v)
    (hu : u ∈ branchVertices H) (hv : v ∈ branchVertices H) : IsBranch H [u, v] := by
  refine ⟨(isTrackFrom_pair h).1, by intro w hw; simp [trackInterior] at hw, ?_⟩
  intro q' hq' hq'int hsub hmem
  have hu' : u ∈ q' := hmem u (by simp)
  have hv' : v ∈ q' := hmem v (by simp)
  have hedge : s(u, v) ∈ trackEdges q' := hsub (by rw [trackEdges_pair]; rfl)
  have hlen : q'.length = 2 :=
    length_eq_two_of_ends_adjacent hq'.2.1 hu' hv'
      (fun hc => hq'int u hc hu) (fun hc => hq'int v hc hv) hedge
  -- a two-vertex track has a single edge, and that edge is `uv`
  have : trackEdges q' = {s(q'[0]'(by omega), q'[1]'(by omega))} := by
    ext e
    constructor
    · rintro ⟨i, hi, rfl⟩
      have : i = 0 := by omega
      subst this
      rfl
    · rintro rfl
      exact ⟨0, by omega, rfl⟩
  rw [this, trackEdges_pair]
  rw [this] at hedge
  simp only [Set.mem_singleton_iff] at hedge
  rw [hedge]

end Workspace.ProofLemmas.Thm93CaseOneBranchPair
