import Workspace.ProofLemmas.SubdivisionTrackExpansion
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.TrackSlice

/-!
# A cycle through a prescribed edge of a 3-connected graph, avoiding a prescribed vertex

PAPER (proof of 5.8 (6), printed p. 28): *"Choose a cycle `C₁` of `H` using the branch between
`v₁` and `v₂` and not using `u`."*

The skeleton form of that sentence: in a 3-connected graph `J`, given an edge `b₁b₂` and a
vertex `u` distinct from both ends, there is a track from `b₁` to `b₂` which avoids `u` and
does not use the edge `b₁b₂` itself.  Adding the edge back closes it into a cycle.

The proof is the standard one and uses 3-connectivity only through *"deleting two vertices
leaves a connected graph"*: pick a neighbour `a` of `b₁` other than `b₂` and `u` (there is one
because every vertex has degree at least three), and join `a` to `b₂` inside `J` with `b₁` and
`u` deleted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Connectivity58Skeleton

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A neighbour of `b₁` different from two prescribed vertices. -/
theorem exists_third_neighbor {J : SimpleGraph U} (hJ : IsKConnected J 3)
    (b₁ x y : U) : ∃ a, J.Adj b₁ a ∧ a ≠ x ∧ a ≠ y := by
  classical
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ b₁
  by_contra hcon
  have hsub : J.neighborSet b₁ ⊆ ({x, y} : Set U) := by
    intro z hz
    by_contra hz'
    exact hcon ⟨z, hz, fun hh => hz' (by rw [hh]; exact Or.inl rfl),
      fun hh => hz' (by rw [hh]; exact Or.inr rfl)⟩
  have h1 : (J.neighborSet b₁).ncard ≤ ({x, y} : Set U).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set U).ncard ≤ 2 := by
    have := Set.ncard_insert_le x ({y} : Set U)
    simpa using this
  omega

/-- **The skeleton cycle, with a prescribed first edge.**  A track between the ends of an edge
of a 3-connected graph which starts along a prescribed edge, avoids a prescribed third vertex
and does not use the edge `b₁b₂`. -/
theorem exists_avoiding_track_first {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {b₁ b₂ u a : U} (hb : J.Adj b₁ b₂) (hba : J.Adj b₁ a) (hab₂ : a ≠ b₂) (hau : a ≠ u)
    (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂) :
    ∃ t : List U, IsTrackFrom J t b₁ b₂ ∧ u ∉ t ∧ s(b₁, b₂) ∉ trackEdges t ∧
      3 ≤ t.length ∧ t[1]? = some a := by
  classical
  set S : Set U := {b₁, u} with hS
  have hScard : S.ncard < 3 := by
    have h1 := Set.ncard_insert_le b₁ ({u} : Set U)
    have h2 := Set.ncard_singleton u
    simp only [hS]
    omega
  have hconn := hJ.2 S hScard
  have haS : a ∈ Sᶜ := by
    rintro (h | h)
    · exact hba.ne' h
    · exact hau h
  have hb₂S : b₂ ∈ Sᶜ := by
    rintro (h | h)
    · exact hb.ne' h
    · exact hu₂ h.symm
  have hrch : RchIn J Sᶜ a b₂ := ⟨haS, hb₂S, hconn.preconnected ⟨a, haS⟩ ⟨b₂, hb₂S⟩⟩
  obtain ⟨wlk, hwlk⟩ := NoCrossTrackBranch.walk_of_rchIn hrch
  obtain ⟨R, hR, hRsupp, -⟩ := NoCrossTrackBranch.exists_track_of_walk wlk
  have hRS : ∀ z ∈ R, z ∈ Sᶜ := fun z hz => hwlk z (hRsupp z hz)
  have hb₁R : b₁ ∉ R := fun hh => hRS b₁ hh (Or.inl rfl)
  have huR : u ∉ R := fun hh => hRS u hh (Or.inr rfl)
  have hR2 : 2 ≤ R.length := by
    have hne : R ≠ [] := hR.1.1
    by_contra hh
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (show R.length = 1 by
      have : 0 < R.length := List.length_pos_iff.mpr hne
      omega)
    rw [hz] at hR
    have h1 : z = a := Option.some.inj hR.2.1
    have h2 : z = b₂ := Option.some.inj hR.2.2
    exact hab₂ (h1.symm.trans h2)
  have ht : IsTrackFrom J (b₁ :: R) b₁ b₂ := by
    have h1 := TrackSlice.isTrackFrom_concat (TrackSlice.isTrackFrom_reverse hR)
      hba.symm (by simpa using hb₁R)
    have h2 := TrackSlice.isTrackFrom_reverse h1
    simpa using h2
  refine ⟨b₁ :: R, ht, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons]
    rintro (h | h)
    · exact hu₁ h
    · exact huR h
  · rintro ⟨i, hi, heq⟩
    have hnd : (b₁ :: R).Nodup := ht.1.2.1
    have h0 : (b₁ :: R)[0]'(by simp) = b₁ := rfl
    have hmem : b₁ ∈ s((b₁ :: R)[i]'(by omega), (b₁ :: R)[i + 1]'hi) := by
      rw [← heq]; exact Sym2.mem_mk_left _ _
    have hcase : (b₁ :: R)[i]'(by omega) = b₁ ∨ (b₁ :: R)[i + 1]'hi = b₁ := by
      rcases Sym2.mem_iff.mp hmem with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hi0 : i = 0 := by
      rcases hcase with h | h
      · have := hnd.getElem_inj_iff (hi := (by omega : i < (b₁ :: R).length))
          (hj := (by simp : 0 < (b₁ :: R).length))
        exact this.mp (by rw [h, h0])
      · have := hnd.getElem_inj_iff (hi := hi) (hj := (by simp : 0 < (b₁ :: R).length))
        have := this.mp (by rw [h, h0])
        omega
    subst hi0
    have hRa : R[0]'(by omega) = a := by
      have := hR.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < R.length)] at this
      exact Option.some_injective _ this
    have h1 : (b₁ :: R)[1]'hi = a := by
      rw [List.getElem_cons_succ]
      exact hRa
    rw [h0, h1] at heq
    have : b₂ = a := by
      have := (Sym2.congr_right (a := b₁) (b := b₂) (c := a)).mp heq
      exact this
    exact hab₂ this.symm
  · simp only [List.length_cons]
    omega
  · rw [List.getElem?_cons_succ]
    rw [← List.head?_eq_getElem?]; exact hR.2.1

/-- **The skeleton cycle.**  A track between the ends of an edge of a 3-connected graph which
avoids a prescribed third vertex and does not use the edge. -/
theorem exists_avoiding_track {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {b₁ b₂ u : U} (hb : J.Adj b₁ b₂) (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂) :
    ∃ t : List U, IsTrackFrom J t b₁ b₂ ∧ u ∉ t ∧ s(b₁, b₂) ∉ trackEdges t ∧
      3 ≤ t.length := by
  obtain ⟨a, hba, hab₂, hau⟩ := exists_third_neighbor hJ b₁ b₂ u
  obtain ⟨t, h1, h2, h3, h4, -⟩ := exists_avoiding_track_first hJ hb hba hab₂ hau hu₁ hu₂
  exact ⟨t, h1, h2, h3, h4⟩

end Workspace.ProofLemmas.Connectivity58Skeleton
