import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.CycleArcPath
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.Thm58StarBranchMixedHoleCycle
import Workspace.ProofLemmas.Thm58StarBranchMixedHoleTrack

/-!
# The hole of 5.8 (6), and its two arcs

PAPER (proof of 5.8 (6), printed p. 28): *"Let `A` be the neighbours of `p₁` in `N_u` and
`B = N_u \ A`.  In `H` there is a cycle `C₂` using the branch between `v₁` and `v₂`, and using
an edge in `A` and an edge in `B`.  (To see this, divide `u` into two adjacent vertices, one
incident with the edges in `A` and the other with those in `B`, and use Menger's theorem to
deduce that there are two vertex-disjoint paths between these two vertices and `{v₁,v₂}`.)
Hence in `G`, there is a path between `N_{v₁}` and `N_{v₂}` using a unique edge of `N(u)`, and
that edge is between a vertex `a ∈ A` and some vertex in `B`."*

The rung of the cycle `C₂` is a hole `L` of `G` inside the appearance.  This file

* states that hole as the single remaining gap of claim (6) (`exists_mixed_hole`), and
* proves, with no gap, that the hole splits into the two arcs the link of 5.8 (6) needs
  (`arcs_of_hole`): with `a = L[0]` deleted and the edge `rs = L[k]L[k+1]` marked, the two
  pieces of `L` are induced paths of `G`, one ending at `r` and one ending at `s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchMixedHole

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ### The two arcs of a hole cut at one vertex and one edge -/

section Arcs

variable {L : List V}

private theorem hole_cycle (hL : IsHoleList G L) :
    ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
      (b = (a + 1) % L.length ∨ a = (b + 1) % L.length) → G.Adj L[a] L[b] :=
  fun a b ha hb hab => (hL.2.2 a b ha hb).mpr hab

private theorem hole_induced (hL : IsHoleList G L) :
    ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
      G.Adj L[a] L[b] →
        ((b = (a + 1) % L.length ∨ a = (b + 1) % L.length) ∨
          ((a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 0))) :=
  fun a b ha hb hab => Or.inl ((hL.2.2 a b ha hb).mp hab)

/-- **The two arcs.**  A hole `L` of length at least `k + 2`, cut at the vertex `L[0]` and at
the edge `L[k] L[k+1]`, falls apart into the induced path `L[1] ⋯ L[k]` and the induced path
`L[L.length-1] ⋯ L[k+1]`. -/
theorem arcs_of_hole (hL : IsHoleList G L) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k + 2 ≤ L.length) (x₀ : V) :
    ∃ T₁ T₂ : List V,
      IsPathFrom G T₁ (L[1]'(by have := hL.1; omega)) (L[k]'(by omega)) ∧
      IsPathFrom G T₂ (L[L.length - 1]'(by have := hL.1; omega)) (L[k+1]'(by omega)) ∧
      (∀ x ∈ T₁, ∃ i, 1 ≤ i ∧ i ≤ k ∧ ∃ hi : i < L.length, L[i]'hi = x) ∧
      (∀ x ∈ T₂, ∃ i, k + 1 ≤ i ∧ i < L.length ∧ ∃ hi : i < L.length, L[i]'hi = x) := by
  classical
  have hn4 : 4 ≤ L.length := hL.1
  have hnd : L.Nodup := hL.2.1
  set n := L.length with hn
  -- the first arc
  have h1 : IsPathFrom G (CycleArcPath.arc L x₀ 1 k)
      (CycleArcPath.cycAt L x₀ 1) (CycleArcPath.cycAt L x₀ (1 + k - 1)) := by
    refine CycleArcPath.arc_isPathFrom (hh := 0) (jj := 0) hnd hn4 (hole_cycle hL)
      (hole_induced hL) x₀ 1 k hk1 (by omega) ?_
    rintro t ht u hu ⟨hc1, hc2⟩
    rw [Nat.mod_eq_of_lt (show 1 + t < n by omega)] at hc1
    omega
  -- the second arc
  have h2 : IsPathFrom G (CycleArcPath.arc L x₀ (k+1) (n - 1 - k))
      (CycleArcPath.cycAt L x₀ (k+1))
      (CycleArcPath.cycAt L x₀ ((k+1) + (n - 1 - k) - 1)) := by
    refine CycleArcPath.arc_isPathFrom (hh := 0) (jj := 0) hnd hn4 (hole_cycle hL)
      (hole_induced hL) x₀ (k+1) (n - 1 - k) (by omega) (by omega) ?_
    rintro t ht u hu ⟨hc1, hc2⟩
    rw [Nat.mod_eq_of_lt (show k + 1 + t < n by omega)] at hc1
    omega
  refine ⟨CycleArcPath.arc L x₀ 1 k,
    (CycleArcPath.arc L x₀ (k+1) (n - 1 - k)).reverse, ?_, ?_, ?_, ?_⟩
  · have e1 : CycleArcPath.cycAt L x₀ 1 = L[1]'(by omega) :=
      CycleArcPath.cycAt_of_lt (by omega)
    have e2 : CycleArcPath.cycAt L x₀ (1 + k - 1) = L[k]'(by omega) := by
      rw [show 1 + k - 1 = k by omega]; exact CycleArcPath.cycAt_of_lt (by omega)
    rw [e1, e2] at h1; exact h1
  · have e1 : CycleArcPath.cycAt L x₀ (k+1) = L[k+1]'(by omega) :=
      CycleArcPath.cycAt_of_lt (by omega)
    have e2 : CycleArcPath.cycAt L x₀ ((k+1) + (n - 1 - k) - 1) = L[n - 1]'(by omega) := by
      rw [show (k+1) + (n - 1 - k) - 1 = n - 1 by omega]
      exact CycleArcPath.cycAt_of_lt (by omega)
    rw [e1, e2] at h2
    exact PathBasics.isPathFrom_reverse h2
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := (CycleArcPath.mem_arc_iff L x₀ 1 k x).mp hx
    exact ⟨1 + t, by omega, by omega, by omega,
      (CycleArcPath.cycAt_of_lt (by omega : 1 + t < L.length)).symm⟩
  · intro x hx
    rw [List.mem_reverse] at hx
    obtain ⟨t, ht, rfl⟩ := (CycleArcPath.mem_arc_iff L x₀ (k+1) (n - 1 - k) x).mp hx
    exact ⟨k + 1 + t, by omega, by omega, by omega,
      (CycleArcPath.cycAt_of_lt (by omega : k + 1 + t < L.length)).symm⟩

/-- The first arc contains `L[1]`. -/
theorem mem_arc_one (hL : IsHoleList G L) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ L.length)
    (x₀ : V) : (L[1]'(by have := hL.1; omega)) ∈ CycleArcPath.arc L x₀ 1 k := by
  rw [CycleArcPath.mem_arc_iff]
  exact ⟨0, by omega, (CycleArcPath.cycAt_of_lt (by omega : (1:ℕ) < L.length)).symm⟩

end Arcs

/-! ### The gap -/

variable {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"In `H` there is a cycle `C₂` using the
branch between `v₁` and `v₂`, and using an edge in `A` and an edge in `B`.  (To see this,
divide `u` into two adjacent vertices, one incident with the edges in `A` and the other with
those in `B`, and use Menger's theorem to deduce that there are two vertex-disjoint paths
between these two vertices and `{v₁,v₂}`.)  Hence in `G`, there is a path between `N_{v₁}`
and `N_{v₂}` using a unique edge of `N(u)`, and that edge is between a vertex `a ∈ A` and
some vertex in `B`."*

The rung of that cycle `C₂` is a hole `L` of `G` contained in the appearance.  Reading it
from the `A`-end `a` of its unique edge in `N(u)`, the vertex `a` is `L[0]`, no other vertex
of `L` is adjacent to `p₁` (that is what *"a unique edge of `N(u)`"* says, since the only
edges from `p₁` into the appearance land in `N(u)`), and the two neighbours `r`, `s` of `pₙ`
are the consecutive pair `L[k]`, `L[k+1]` on the branch part of the cycle. -/
theorem exists_mixed_hole (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : G.Adj r s) (hneighbors : ∀ x ∈ K, G.Adj p₂ x ↔ x = r ∨ x = s)
    (hA : ∃ a ∈ N c, G.Adj p₁ a) (hB : ∃ b ∈ N c, ¬ G.Adj p₁ b) :
    ∃ (L : List V) (a : V) (k : ℕ),
      IsHoleList G L ∧ (∀ x ∈ L, x ∈ K) ∧ L.head? = some a ∧
      a ∈ N c ∧ G.Adj p₁ a ∧
      (∀ x ∈ L, x ≠ a → ¬ G.Adj p₁ x) ∧
      1 ≤ k ∧ k + 2 ≤ L.length ∧ L[k]? = some r ∧ L[k+1]? = some s := by
  classical
  obtain ⟨a, haN, hpa⟩ := hA
  obtain ⟨b, hbN, hpb⟩ := hB
  rw [star_eq h c] at haN hbN
  obtain ⟨eA, heA, heAc, haeq⟩ := haN
  obtain ⟨eB, heB, heBc, hbeq⟩ := hbN
  obtain ⟨xA, rfl⟩ := Sym2.mem_iff_exists.mp heAc.2
  obtain ⟨xB, rfl⟩ := Sym2.mem_iff_exists.mp heBc.2
  have hxAB : xA ≠ xB := by
    rintro rfl
    exact hpb (by rw [hbeq, ← haeq]; exact hpa)
  obtain ⟨Q, D, w₁, w₂, j, hQ, hQ2, hQe, hD, hD3, hdisj, hj1, hj2, hcj, hxA', hxB'⟩ :=
    Thm58StarBranchMixedHoleTrack.exists_mixed_track h hcq heA heB hxAB
  refine Thm58StarBranchMixedHoleCycle.exists_hole h hQ hQ2 hD hD3 hdisj hj1 hj2 hcj hxA' hxB'
    heA (fun he => haeq ▸ hpa) (fun he => hbeq ▸ hpb) ?_ ?_ hrs
  · rw [hQe]; exact hr
  · rw [hQe]; exact hs

end Workspace.ProofLemmas.Thm58StarBranchMixedHole
