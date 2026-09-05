import Workspace.ProofLemmas.Thm57Claim2SameEnds
import Workspace.ProofLemmas.Thm57Claim2InitialTrack

/-! # The two conflicting parities at the common neighbour in 5.7 (2) -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2CommonNeighbor

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.TrackSlice Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.Thm57Claim2Join Workspace.ProofLemmas.Thm57Claim2SameEnds
open Workspace.ProofLemmas.Thm57Claim2InitialTrack

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- PAPER: *"If `Q₁ = C` then ... `P₁ ∪ P₂` is the interior of an even track with
end-edges in `X` and no internal edges in `X`, contrary to the hypothesis."*

The same track shows that the final edge of `C` cannot belong to `X` at all. -/
theorem last_edge_not_X {H : SimpleGraph W} {X : Set (Sym2 W)}
    (hnotrack : NoEvenTrack57 H X) {C R : List W} {c₁ c₂ a : W}
    (hC : IsTrackFrom H C c₁ c₂) (hClen : 3 ≤ C.length)
    (hsame : SameBiparity H c₁ c₂) (hR : IsTrackFrom H R c₁ c₂) (hRlen : 2 ≤ R.length)
    (hmeet : ∀ w ∈ R, w ∈ C → w = c₁ ∨ w = c₂)
    (haC : a ∉ C) (haR : a ∉ R) (hadj : H.Adj c₁ a) (haX : s(c₁, a) ∈ X)
    (hclean : ∀ e ∈ trackEdges R, e ∉ X) :
    s(C[C.length - 2], C[C.length - 1]) ∉ X := by
  intro hX
  let d := C[C.length - 2]'(by omega)
  have hdC : d ∈ C := List.getElem_mem _
  have hdc₁ : d ≠ c₁ := by
    intro h
    have hidx := hC.1.2.1.getElem_inj_iff.mp (h.trans (track_head hC (by omega)).symm)
    omega
  have hdc₂ : d ≠ c₂ := by
    intro h
    have hidx := hC.1.2.1.getElem_inj_iff.mp (h.trans (last_vertex hC).symm)
    omega
  have hdR : d ∉ R := by
    intro h
    exact (hmeet d h hdC).elim hdc₁ hdc₂
  have hdcadj : H.Adj d c₂ := by
    have h := hC.1.2.2 (C.length - 2) (by omega)
    rw [getElem_eq_of_index_eq C (show C.length - 2 + 1 = C.length - 1 by omega)
      (by omega) (by omega), last_vertex hC] at h
    exact h
  have hP := pair_track hdcadj
  have hcommon : ∀ w ∈ [d, c₂], w ∈ R.reverse → w = c₂ := by
    intro w hw hwR
    rcases List.mem_cons.mp hw with h | h
    · exact (hdR (h ▸ List.mem_reverse.mp hwR)).elim
    · exact List.mem_singleton.mp h
  have haP : a ∉ [d, c₂] := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact haC (h ▸ hdC)
    · exact haC ((List.mem_singleton.mp h) ▸ List.mem_of_mem_getLast? hC.2.2)
  have hodd := clean_join_odd hnotrack hP (isTrackFrom_reverse hR) (by simp)
    (by simpa using hRlen) hcommon haP (by simpa using haR) hadj
    (by change s(d, c₂) ∈ X; simpa only [last_vertex hC] using hX) haX
    (by
      rintro e ⟨k, hk, rfl⟩ _
      have hk0 : k = 0 := by simpa using hk
      subst k
      rfl)
    (by simpa only [trackEdges_reverse] using hclean)
  have heven := hsame R hR
  simp only [trackLength, List.length_cons, List.length_nil, List.length_reverse,
    Nat.even_iff, Nat.odd_iff] at hodd heven
  omega

/-- PAPER: *"From the track `Q₁-c₁-P₁-b-P₂-c₂-a` ... `Q₁` is even; and from the track
`Q₁-c₁-P₁-b-P₃-a-c₂` ... `Q₁` is odd, a contradiction."*

Here `R` and `S` are the two routes through the three paths in the paper. -/
theorem two_routes_contradiction {H : SimpleGraph W} {X : Set (Sym2 W)}
    (hnotrack : NoEvenTrack57 H X) {C R S : List W} {c₁ c₂ a : W}
    (hC : IsTrackFrom H C c₁ c₂) (hClen : 3 ≤ C.length)
    (hsame : SameBiparity H c₁ c₂) (hR : IsTrackFrom H R c₁ c₂)
    (hS : IsTrackFrom H S c₁ a) (hRlen : 2 ≤ R.length) (hSlen : 2 ≤ S.length)
    (haC : a ∉ C) (haR : a ∉ R) (hc₂S : c₂ ∉ S)
    (hRmeet : ∀ w ∈ R, w ∈ C → w = c₁ ∨ w = c₂)
    (hSmeet : ∀ w ∈ S, w ∈ C → w = c₁)
    (hadj₁ : H.Adj c₁ a) (hadj₂ : H.Adj c₂ a)
    (hX₁ : s(c₁, a) ∈ X) (hX₂ : s(c₂, a) ∈ X)
    (hRclean : ∀ e ∈ trackEdges R, e ∉ X) (hSclean : ∀ e ∈ trackEdges S, e ∉ X)
    (hCX : ∃ e ∈ trackEdges C, e ∈ X) : False := by
  have hlast := last_edge_not_X hnotrack hC hClen hsame hR hRlen hRmeet
    haC haR hadj₁ hX₁ hRclean
  obtain ⟨P, d, hPlen, hP, hPmem, hc₂P, hPfirst, hPclean⟩ :=
    exists_initial_clean hC hClen hCX hlast
  have hcommonR : ∀ w ∈ P, w ∈ R → w = c₁ := by
    intro w hw hwR
    rcases hRmeet w hwR (hPmem w hw) with h | h
    · exact h
    · exact (hc₂P (h ▸ hw)).elim
  have hcommonS : ∀ w ∈ P, w ∈ S → w = c₁ :=
    fun w hw hwS => hSmeet w hwS (hPmem w hw)
  have haP : a ∉ P := fun h => haC (hPmem a h)
  have hoddR := clean_join_odd hnotrack hP hR hPlen hRlen hcommonR haP haR
    hadj₂ hPfirst hX₂ hPclean hRclean
  have hoddS := clean_join_odd hnotrack hP hS hPlen hSlen hcommonS hc₂P hc₂S
    hadj₂.symm hPfirst (by simpa only [Sym2.eq_swap] using hX₂) hPclean hSclean
  have hevenR := hsame R hR
  have hevenS := hsame _ (isTrackFrom_concat hS hadj₂.symm hc₂S)
  simp only [trackLength, List.length_append, List.length_singleton, Nat.even_iff,
    Nat.odd_iff] at hevenR hevenS hoddR hoddS
  omega

end Workspace.ProofLemmas.Thm57Claim2CommonNeighbor
