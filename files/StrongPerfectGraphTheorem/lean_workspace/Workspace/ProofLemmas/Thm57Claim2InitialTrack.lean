import Workspace.ProofLemmas.Thm57Claim2Join

/-! # The first edge of `X` on the branch window -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2InitialTrack

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.TrackSlice Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.Thm57Claim2Join

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- PAPER: *"there is a minimal subtrack `Qᵢ` of `C` containing `cᵢ` and an edge in `X`."*

The returned list is `Q₁` in reverse order, so its first edge is its only edge in `X`.
If the last edge of `C` is not in `X`, the returned list omits `c₂`. -/
theorem exists_initial_clean {H : SimpleGraph W} {X : Set (Sym2 W)}
    {C : List W} {c₁ c₂ : W} (hC : IsTrackFrom H C c₁ c₂) (hlen : 3 ≤ C.length)
    (hX : ∃ e ∈ trackEdges C, e ∈ X)
    (hlast : s(C[C.length - 2], C[C.length - 1]) ∉ X) :
    ∃ (P : List W) (d : W) (_hP : 2 ≤ P.length),
      IsTrackFrom H P d c₁ ∧ (∀ w ∈ P, w ∈ C) ∧ c₂ ∉ P ∧
      s(P[0], P[1]) ∈ X ∧
      ∀ e ∈ trackEdges P, e ∈ X → e = s(P[0], P[1]) := by
  classical
  have hex : ∃ k, ∃ hk : k + 1 < C.length, s(C[k]'(by omega), C[k + 1]'hk) ∈ X := by
    obtain ⟨e, ⟨k, hk, rfl⟩, he⟩ := hX
    exact ⟨k, hk, he⟩
  obtain ⟨k, hk, hkX, hmin⟩ : ∃ k, ∃ hk : k + 1 < C.length,
      s(C[k]'(by omega), C[k + 1]'hk) ∈ X ∧
      ∀ l (hl : l + 1 < C.length), l < k → s(C[l]'(by omega), C[l + 1]'hl) ∉ X := by
    obtain ⟨hk, hkX⟩ := Nat.find_spec hex
    refine ⟨Nat.find hex, hk, hkX, ?_⟩
    intro l hl hlk hlX
    have := Nat.find_min' hex ⟨hl, hlX⟩
    omega
  have hkfar : k + 2 < C.length := by
    by_contra h
    have hk' : k = C.length - 2 := by omega
    have hk'' : k + 1 = C.length - 1 := by omega
    apply hlast
    rwa [getElem_eq_of_index_eq C hk' (by omega) (by omega),
      getElem_eq_of_index_eq C hk'' (by omega) (by omega)] at hkX
  let Q := slice C 0 (k + 1)
  have hQlen : Q.length = k + 2 := by
    dsimp [Q]
    rw [length_slice C hk (by omega)]
    omega
  have hslice : (slice C 0 (k + 1)).length = k + 2 := hQlen
  have hQ : IsTrackFrom H Q c₁ C[k + 1] := by
    have h := isTrackFrom_slice hC.1 hk (show 0 ≤ k + 1 by omega)
    rwa [track_head hC] at h
  let P := Q.reverse
  have hPlen : P.length = k + 2 := by simpa only [P, List.length_reverse] using hQlen
  have hP : IsTrackFrom H P C[k + 1] c₁ := isTrackFrom_reverse hQ
  have hPmem : ∀ w ∈ P, w ∈ C := by
    intro w hw
    exact mem_of_mem_slice (List.mem_reverse.mp hw)
  have hc₂P : c₂ ∉ P := by
    intro h
    obtain ⟨l, hl, _, hlk, hlc⟩ := (mem_slice_iff hk (show 0 ≤ k + 1 by omega)).mp
      (List.mem_reverse.mp h)
    have hidx := hC.1.2.1.getElem_inj_iff.mp (hlc.trans (last_vertex hC).symm)
    omega
  have hfirst : s(P[0]'(by omega), P[1]'(by omega)) = s(C[k + 1]'hk, C[k]'(by omega)) := by
    dsimp only [P]
    simp only [List.getElem_reverse]
    rw [getElem_slice C (i := 0) (j := k + 1) (by omega) (by omega), getElem_slice C (i := 0) (j := k + 1) (by omega) (by omega),
      getElem_eq_of_index_eq C (show 0 + (Q.length - 1 - 0) = k + 1 by omega)
        (by omega) (by omega),
      getElem_eq_of_index_eq C (show 0 + (Q.length - 1 - 1) = k by omega)
        (by omega) (by omega)]
  refine ⟨P, C[k + 1], by omega, hP, hPmem, hc₂P, ?_, ?_⟩
  · have hXrev : s(C[k + 1], C[k]) ∈ X := by simpa only [Sym2.eq_swap] using hkX
    exact hfirst.symm ▸ hXrev
  · intro e he heX
    have heQ : e ∈ trackEdges Q := by simpa only [P, trackEdges_reverse] using he
    obtain ⟨l, hl, hel⟩ := heQ
    have hlC : l + 1 < C.length := by omega
    have heq : e = s(C[l]'(by omega), C[l + 1]'hlC) := by
      rw [getElem_slice C (i := 0) (j := k + 1) (by omega) (by omega), getElem_slice C (i := 0) (j := k + 1) (by omega) (by omega)] at hel
      simpa only [Nat.zero_add] using hel
    have hlk : l = k := by
      by_contra h
      exact hmin l hlC (by omega) (heq ▸ heX)
    have heq' : e = s(C[k], C[k + 1]) := by simpa only [hlk] using heq
    exact heq'.trans (Sym2.eq_swap.trans hfirst.symm)

end Workspace.ProofLemmas.Thm57Claim2InitialTrack
