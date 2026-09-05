import Workspace.ProofLemmas.Connectivity58Cycle
import Workspace.ProofLemmas.Connectivity58Minimal
import Workspace.ProofLemmas.Thm55BranchReach
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.LineGraphDegree

/-!
# The cycle and the minimal track of 5.8 (6), on the host graph

PAPER (proof of 5.8 (6), printed p. 28): *"Choose a cycle `C₁` of `H` using the branch between
`v₁` and `v₂` and not using `u`, and choose a minimal track `S` in `H \ {v₁,v₂}` between `u` and
`V(C₁)`.  Let the ends of `S` be `u` and `w` say."*

`Connectivity58Cycle.exists_return_track` supplies the cycle as the branch `q` together with a
return track `D`.  Here the minimal track is added: it exists because deleting the two branch
vertices `v₁`, `v₂` from a cyclically 3-connected graph leaves the remaining branch vertices in
one piece, and it is made minimal by cutting it at its first vertex on `D`.  Its far end `w` is
an internal vertex of `D`, so the two arcs of `D` out of `w` are tracks from `w` to `v₁` and to
`v₂` meeting only at `w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Connectivity58Tracks

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
variable {J : SimpleGraph U} {H : SimpleGraph W}

/-- **The first sentence of 5.8 (6).**  A branch `q` with ends `v₁`, `v₂` and a branch-vertex
`c` off it admit a return track `D` (so `q` and `D` form the cycle `C₁`) and a track `S` from
`c` to an internal vertex `w` of `D` which meets `D` only at `w` and misses the branch
entirely. -/
theorem exists_cycle_and_minimal_track
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H) (hc3 : CyclicallyThreeConnected H)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) {v₁ v₂ : W}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H) {c : W} (hc : c ∈ branchVertices H) (hcq : c ∉ q) :
    ∃ (D S : List W) (w : W) (k : ℕ),
      IsTrackFrom H D v₁ v₂ ∧ c ∉ D ∧
      (∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂) ∧
      (∀ e ∈ trackEdges D, e ∉ trackEdges q) ∧
      0 < k ∧ k + 1 < D.length ∧ D[k]? = some w ∧
      IsTrackFrom H S c w ∧ 2 ≤ S.length ∧
      (∀ x ∈ S, x ∈ D → x = w) ∧ (∀ x ∈ S, x ∉ q) ∧
      (∀ y ∈ S, H.Adj c y → S[1]? = some y) := by
  classical
  have hdeg2 : ∀ x : W, 2 ≤ (H.neighborSet x).ncard :=
    LineGraphDegree.two_le_degree_of_isSubdivision hJ hsub
  obtain ⟨D, hD, hcD, hDq, hDe, z, hzD, hzb, hzv₁, hzv₂⟩ :=
    Connectivity58Cycle.exists_return_track hJ hsub hq hq2 hqe hbv₁ hbv₂ hc hcq
  -- `c` and `z` are branch vertices outside `{v₁, v₂}`
  have hv₁q : v₁ ∈ q := by
    have := hqe.2.1
    exact List.mem_of_mem_head? this
  have hv₂q : v₂ ∈ q := List.mem_of_mem_getLast? hqe.2.2
  have hcS : c ∈ ({v₁, v₂} : Set W)ᶜ := by
    rintro (h | h)
    · exact hcq (h ▸ hv₁q)
    · exact hcq ((show c = v₂ from h) ▸ hv₂q)
  have hzS : z ∈ ({v₁, v₂} : Set W)ᶜ := by
    rintro (h | h)
    · exact hzv₁ h
    · exact hzv₂ h
  have hcard : ({v₁, v₂} : Set W).ncard ≤ 2 := by
    have h1 := Set.ncard_insert_le v₁ ({v₂} : Set W)
    have h2 := Set.ncard_singleton v₂
    omega
  have hrch := Thm55BranchReach.branch_rchIn_compl_of_ncard_le_two hc3 _ hcard hc hzb hcS hzS
  obtain ⟨wlk, hwlk⟩ := NoCrossTrackBranch.walk_of_rchIn hrch
  obtain ⟨R, hR, hRsupp, -⟩ := NoCrossTrackBranch.exists_track_of_walk wlk
  have hRS : ∀ x ∈ R, x ∈ ({v₁, v₂} : Set W)ᶜ := fun x hx => hwlk x (hRsupp x hx)
  obtain ⟨S₀, w, hS₀, hwD, hS₀D, hS₀R, hS₀2⟩ :=
    Connectivity58Minimal.exists_first_hit hR {x : W | x ∈ D} hzD hcD
  obtain ⟨S, hS, hS2, hSS₀, hSchord⟩ :=
    Connectivity58Minimal.exists_no_chord_at_head hS₀ hS₀2
  have hSD : ∀ x ∈ S, x ∈ D → x = w := fun x hx => hS₀D x (hSS₀ x hx)
  have hSR : ∀ x ∈ S, x ∈ R := fun x hx => hS₀R x (hSS₀ x hx)
  have hv₁S : v₁ ∉ S := fun hh => hRS v₁ (hSR v₁ hh) (Or.inl rfl)
  have hv₂S : v₂ ∉ S := fun hh => hRS v₂ (hSR v₂ hh) (Or.inr rfl)
  have hSq : ∀ x ∈ S, x ∉ q :=
    Connectivity58Minimal.track_avoids_branch hdeg2 hq hqe hq2 hS hcq hv₁S hv₂S
  -- `w` is an internal vertex of `D`
  have hDpos : 0 < D.length := List.length_pos_of_ne_nil hD.1.1
  have hD0 : D[0]'hDpos = v₁ := track_head hD hDpos
  have hDl : D[D.length - 1]'(by omega) = v₂ := by
    have h' := hD.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : D.length - 1 < D.length)] at h'
    exact Option.some_injective _ h'
  obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.mp hwD
  have hwv₁ : w ≠ v₁ := by
    intro hh
    exact hv₁S (hh ▸ List.mem_of_mem_getLast? hS.2.2)
  have hwv₂ : w ≠ v₂ := by
    intro hh
    exact hv₂S (hh ▸ List.mem_of_mem_getLast? hS.2.2)
  have hDnd : D.Nodup := hD.1.2.1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (by rw [hD0] at hkw; exact hkw.symm) hwv₁
    · exact h
  have hklt : k + 1 < D.length := by
    rcases Nat.lt_or_ge (k + 1) D.length with h | h
    · exact h
    · exfalso
      apply hwv₂
      rw [← hkw, getElem_eq_of_index_eq D (show k = D.length - 1 by omega) hk (by omega), hDl]
  exact ⟨D, S, w, k, hD, hcD, hDq, hDe, hk0, hklt,
    by rw [List.getElem?_eq_getElem hk, hkw], hS, hS2, hSD, hSq, hSchord⟩

end Workspace.ProofLemmas.Connectivity58Tracks
