import Workspace.ProofLemmas.Thm55Structure
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.EnlargementFromNonlocalSplitAssembly

/-!
# Promoting the attachment vertices

The paper asserts the enlargement construction in the proofs of 7.5 and 8.5
(printed pp. 36–37 and 42–43), without giving the track-splitting construction.
After the construction below, connectivity, the added-edge subdivision, and the
exceptional `K₃,₃` case are proved in separate modules.
-/
set_option autoImplicit false
namespace Workspace.ProofLemmas.EnlargementFromNonlocalPromotion

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.NoCrossTrackBranch

/-- Data for the old skeleton with the two attachment vertices retained.
Its other vertices are branch vertices. The map `ι` identifies the two marked
vertices with the prescribed attachment vertices of `H`. -/
def Promotion {U W : Type*} (J : SimpleGraph U) (H : SimpleGraph W) (c₁ c₂ : W) : Prop :=
  ∃ (m : ℕ) (B : SimpleGraph (Fin m)) (a b : Fin m)
    (ι : Fin m → W) (T : Fin m → Fin m → List W),
    IsSubdivision J B ∧ SubData B H ι T ∧ ι a = c₁ ∧ ι b = c₂ ∧
    (∀ v, v ∈ branchVertices B ∨ v = a ∨ v = b) ∧
    (¬ ∃ q, IsBranch B q ∧ a ∈ q ∧ b ∈ q)

/-- **Split the one or two old tracks containing internal attachment vertices.**

PAPER (printed p. 42): "Then there is an appearance `L(H')` in `G` of some
`J`-enlargement `J'`, with `L(H)` an induced subgraph of `L(H')`."

This is only the subdivision bookkeeping in that assertion. Starting from the
tracks for `IsSubdivision J H`, split a track at each marked internal vertex; the
construction is carried out in `EnlargementFromNonlocalSplitCore` and assembled in
`EnlargementFromNonlocalSplitAssembly`.
The marks lie on distinct branches when both are internal, by `hnb`. The graph
`B` retains the old skeleton vertices and these marks. No added edge, new host
`D`, connectivity conclusion, or parity claim is part of this gap. -/
theorem split_internal_tracks_gap {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H) (c₁ c₂ : W)
    (hnb : ¬ ∃ q, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (hint : c₁ ∉ branchVertices H ∨ c₂ ∉ branchVertices H) :
    Promotion J H c₁ c₂ :=
  Workspace.ProofLemmas.EnlargementFromNonlocalSplitAssembly.promotionData_of_no_common_branch
    J hJ H hsub c₁ c₂ hnb hint

private theorem adjacent_of_common_branch {X : Type*} [Fintype X]
    {B : SimpleGraph X} (hB : IsKConnected B 3) {a b : X} (hab : a ≠ b)
    {q : List X} (hq : IsBranch B q) (ha : a ∈ q) (hb : b ∈ q) : B.Adj a b := by
  have hlen : q.length ≤ 2 := by
    by_contra hh
    have hm := mem_trackInterior_getElem q 0 (by omega)
    exact hq.2.1 _ hm (three_le_degree_of_three_connected B hB _)
  have hlen2 : q.length = 2 := by
    by_contra hn
    have hpos : 0 < q.length := List.length_pos_iff.mpr hq.1.1
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (show q.length = 1 by omega)
    have ha' : a = x := by simpa using ha
    have hb' : b = x := by simpa using hb
    exact hab (ha'.trans hb'.symm)
  obtain ⟨x, y, rfl⟩ := Workspace.ProofLemmas.PathGlue.length_eq_two hlen2
  have hxy : B.Adj x y := hq.1.2.2 0 (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact hxy
  · exact hxy.symm
  · exact (hab rfl).elim

/-- If both attachment vertices already belong to the skeleton, no splitting
is needed. The only open case is an internal attachment vertex. -/
theorem promote_vertices {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H) (c₁ c₂ : W) (hne : c₁ ≠ c₂)
    (hnb : ¬ ∃ q, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) :
    Promotion J H c₁ c₂ := by
  classical
  by_cases hboth : c₁ ∈ branchVertices H ∧ c₂ ∈ branchVertices H
  · let B := J.overFin rfl
    let e : J ≃g B := J.overFinIso rfl
    have hB : IsKConnected B 3 := isKConnected_of_iso e hJ
    have hBH : IsSubdivision B H := Thm85Five8Transported.isSubdivision_of_iso e hsub
    obtain ⟨ι, T, hs⟩ := exists_subData hBH
    have hbr := branch_eq_range hB hs
    obtain ⟨a, ha⟩ := hbr ▸ hboth.1
    obtain ⟨b, hb⟩ := hbr ▸ hboth.2
    have hab : a ≠ b := fun h => hne (ha.symm.trans ((congrArg ι h).trans hb))
    refine ⟨Fintype.card U, B, a, b, ι, T, ?_, hs, ha, hb, ?_, ?_⟩
    · exact isSubdivision_of_iso e (isSubdivision_self J)
    · intro v
      exact Or.inl (three_le_degree_of_three_connected B hB v)
    · rintro ⟨q, hq, haq, hbq⟩
      have hAdj := adjacent_of_common_branch hB hab hq haq hbq
      exact hnb ⟨T a b, Thm55Structure.subdivision_track_isBranch hB hs hAdj,
        ha ▸ List.mem_of_head? (hs.track a b hAdj).2.1,
        hb ▸ List.mem_of_getLast? (hs.track a b hAdj).2.2⟩
  · apply split_internal_tracks_gap J hJ H hsub c₁ c₂ hnb
    tauto

end Workspace.ProofLemmas.EnlargementFromNonlocalPromotion
