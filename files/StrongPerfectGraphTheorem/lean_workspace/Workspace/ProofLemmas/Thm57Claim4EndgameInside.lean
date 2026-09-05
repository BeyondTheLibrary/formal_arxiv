import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim4Basics

/-!
# 5.7 (4), last paragraph: the case where the new vertex lies on the old track

In the final paragraph of the printed proof of 5.7 (4) the paper produces an edge `sv ∈ X` with
`s ∈ V(S)` and `v ∉ V(S) ∪ {a₃, b₃}`, and then builds the three tracks
`b₁-a₁-P₁-b₃`, `P₄` and `x₃` that violate (3).  That construction needs `v` to be off the track
`P₁`.  This file settles the opposite case: if `v` is an *internal* vertex of the track from
`u` to `γ`, then the two halves of that track, each completed by the marked edge at its far end,
together with the single edge `sv`, already violate (3).

Everything is stated for an abstract track `P` from `u` to `γ` in `H \ X`, an abstract
`s`, and the two marked edges `uu'` and `γγ'`, so that the lemma can be used on either side of
the symmetry `a ↔ b`, `i ↔ j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim4EndgameInside

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Basics
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*}

/-- The three tracks out of an internal vertex `P[m]` of `P`: back to `u` and on to `u'`,
forward to `γ` and on to `γ'`, and the single edge to `s`. -/
theorem caseVInP
    (H : SimpleGraph W) (X : Set (Sym2 W))
    (hclaim3 :
      ¬ ∃ (c a₁ a₂ a₃ : W) (P₁ P₂ P₃ : List W)
          (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
        IsTrackFrom H P₁ c a₁ ∧ IsTrackFrom H P₂ c a₂ ∧ IsTrackFrom H P₃ c a₃ ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₂ → v = c) ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₃ → v = c) ∧
        (∀ v : W, v ∈ P₂ → v ∈ P₃ → v = c) ∧
        (∃ e ∈ trackEdges P₁, e ∈ X) ∧
        (∃ e ∈ trackEdges P₂, e ∈ X) ∧
        (∃ e ∈ trackEdges P₃, e ∈ X) ∧
        ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
         (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
         (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X)))
    {P : List W} {u γ u' γ' s : W} {m : ℕ}
    (hP : IsTrackFrom (H.deleteEdges X) P u γ)
    (hm1 : 1 ≤ m) (hm2 : m + 1 < P.length)
    (hu'P : u' ∉ P) (hγ'P : γ' ∉ P) (hu'γ' : u' ≠ γ')
    (hsP : s ∉ P) (hsu' : s ≠ u') (hsγ' : s ≠ γ')
    (hXu : s(u, u') ∈ X) (hXγ : s(γ, γ') ∈ X)
    (hXsv : s(P[m]'(by omega), s) ∈ X)
    (hadju : H.Adj u u') (hadjγ : H.Adj γ γ')
    (hadjs : H.Adj (P[m]'(by omega)) s) :
    False := by
  classical
  have hPne : 0 < P.length := by omega
  have hmlt : m < P.length := by omega
  have hP0 : P[0]'hPne = u := getElem_zero_of_head? hP.2.1 hPne
  have hPl : P[P.length - 1]'(by omega) = γ := getElem_last_of_getLast? hP.2.2 hPne
  set w : W := P[m]'hmlt with hwdef
  have hwP : w ∈ P := List.getElem_mem hmlt
  -- the two halves of `P`
  have hL : IsTrackFrom (H.deleteEdges X) (slice P 0 m) u w := by
    have h := isTrackFrom_slice (i := 0) (j := m) hP.1 hmlt (Nat.zero_le _)
    rw [hP0] at h
    exact h
  have hLlen : (slice P 0 m).length = m + 1 := by
    have := length_slice P hmlt (Nat.zero_le m); omega
  have hM : IsTrackFrom (H.deleteEdges X) (slice P m (P.length - 1)) w γ := by
    have h := isTrackFrom_slice (i := m) (j := P.length - 1) hP.1
      (show P.length - 1 < P.length by omega) (by omega)
    rw [hPl] at h
    exact h
  have hMlen : (slice P m (P.length - 1)).length = P.length - 1 - m + 1 :=
    length_slice P (show P.length - 1 < P.length by omega) (by omega)
  have hLr : IsTrackFrom (H.deleteEdges X) (slice P 0 m).reverse w u :=
    isTrackFrom_reverse hL
  have hLrlen : (slice P 0 m).reverse.length = m + 1 := by
    simp only [List.length_reverse]; exact hLlen
  -- the three tracks
  have hu'Lr : u' ∉ (slice P 0 m).reverse := by
    intro h; exact hu'P (mem_of_mem_slice (List.mem_reverse.mp h))
  have hγ'M : γ' ∉ slice P m (P.length - 1) := fun h => hγ'P (mem_of_mem_slice h)
  have hT1 : IsTrackFrom H ((slice P 0 m).reverse ++ [u']) w u' :=
    isTrackFrom_concat (isTrackFrom_of_delete hLr) hadju hu'Lr
  have hT2 : IsTrackFrom H (slice P m (P.length - 1) ++ [γ']) w γ' :=
    isTrackFrom_concat (isTrackFrom_of_delete hM) hadjγ hγ'M
  have hws : w ≠ s := fun h => hsP (h ▸ hwP)
  have hT3 : IsTrackFrom H [w, s] w s := by
    refine ⟨⟨by simp, by simp [hws], ?_⟩, by simp, by simp⟩
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using hadjs
  -- lengths
  have hlen1 : 2 ≤ ((slice P 0 m).reverse ++ [u']).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hLrlen]; omega
  have hlen2 : 2 ≤ (slice P m (P.length - 1) ++ [γ']).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hMlen]; omega
  have hlen3 : 2 ≤ ([w, s] : List W).length := by simp
  -- the marked edges
  have hE1 : s(u, u') ∈ trackEdges ((slice P 0 m).reverse ++ [u']) := by
    have hlast := getElem_last_of_getLast? hLr.2.2 (by omega : 0 < (slice P 0 m).reverse.length)
    have h := last_edge_mem_concat (by omega : 0 < (slice P 0 m).reverse.length) u'
    rwa [hlast] at h
  have hE2 : s(γ, γ') ∈ trackEdges (slice P m (P.length - 1) ++ [γ']) := by
    have hlast := getElem_last_of_getLast? hM.2.2
      (by omega : 0 < (slice P m (P.length - 1)).length)
    have h := last_edge_mem_concat (by omega : 0 < (slice P m (P.length - 1)).length) γ'
    rwa [hlast] at h
  have hE3 : s(w, s) ∈ trackEdges ([w, s] : List W) := ⟨0, by simp, by simp⟩
  -- the first edges
  have hF1 : s(((slice P 0 m).reverse ++ [u'])[0]'(by omega),
      ((slice P 0 m).reverse ++ [u'])[1]'(by omega)) ∉ X := by
    rw [first_edge_concat (by omega : 2 ≤ (slice P 0 m).reverse.length)]
    exact edge_not_mem_of_delete hLr.1 (by omega)
  have hF2 : s((slice P m (P.length - 1) ++ [γ'])[0]'(by omega),
      (slice P m (P.length - 1) ++ [γ'])[1]'(by omega)) ∉ X := by
    rw [first_edge_concat (by omega : 2 ≤ (slice P m (P.length - 1)).length)]
    exact edge_not_mem_of_delete hM.1 (by omega)
  -- the halves meet only at `w`
  have hLM : ∀ z : W, z ∈ slice P 0 m → z ∈ slice P m (P.length - 1) → z = w := by
    intro z h1 h2
    obtain ⟨k₁, hk₁, -, hk₁m, he₁⟩ := (mem_slice_iff hmlt (Nat.zero_le m)).mp h1
    obtain ⟨k₂, hk₂, hmk₂, -, he₂⟩ :=
      (mem_slice_iff (show P.length - 1 < P.length by omega) (by omega)).mp h2
    have hkk : k₁ = k₂ := hP.1.2.1.getElem_inj_iff.mp (he₁.trans he₂.symm)
    have hk : k₁ = m := by omega
    rw [hwdef, ← he₁]
    exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P hk hk₁ hmlt
  have hd12 : ∀ z : W, z ∈ (slice P 0 m).reverse ++ [u'] →
      z ∈ slice P m (P.length - 1) ++ [γ'] → z = w := by
    intro z h1 h2
    rcases mem_concat_iff.mp h1 with h1 | h1 <;> rcases mem_concat_iff.mp h2 with h2 | h2
    · exact hLM z (List.mem_reverse.mp h1) h2
    · exact absurd (h2 ▸ mem_of_mem_slice (List.mem_reverse.mp h1)) hγ'P
    · exact absurd (h1 ▸ mem_of_mem_slice h2) hu'P
    · exact absurd (h1.symm.trans h2) hu'γ'
  have hd13 : ∀ z : W, z ∈ (slice P 0 m).reverse ++ [u'] → z ∈ ([w, s] : List W) → z = w := by
    intro z h1 h3
    rcases List.mem_pair.mp h3 with rfl | rfl
    · rfl
    · rcases mem_concat_iff.mp h1 with h1 | h1
      · exact absurd (mem_of_mem_slice (List.mem_reverse.mp h1)) hsP
      · exact absurd h1 hsu'
  have hd23 : ∀ z : W, z ∈ slice P m (P.length - 1) ++ [γ'] →
      z ∈ ([w, s] : List W) → z = w := by
    intro z h2 h3
    rcases List.mem_pair.mp h3 with rfl | rfl
    · rfl
    · rcases mem_concat_iff.mp h2 with h2 | h2
      · exact absurd (mem_of_mem_slice h2) hsP
      · exact absurd h2 hsγ'
  exact hclaim3 ⟨w, u', γ', s,
    (slice P 0 m).reverse ++ [u'], slice P m (P.length - 1) ++ [γ'], [w, s],
    hlen1, hlen2, hlen3, hT1, hT2, hT3, hd12, hd13, hd23,
    ⟨_, hE1, hXu⟩, ⟨_, hE2, hXγ⟩, ⟨_, hE3, hXsv⟩, Or.inl ⟨hF1, hF2⟩⟩

end Workspace.ProofLemmas.Thm57Claim4EndgameInside
