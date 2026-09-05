import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.RungReplacementDelete
import Workspace.ProofLemmas.RungReplacementBranchFacts
import Workspace.ProofLemmas.RungReplacementAddTrack
import Workspace.ProofLemmas.RungReplacementLabels

/-!
# Degrees after replacing one branch

The surgery of 7.5 changes the degree of no vertex at all:

* a vertex away from the old branch keeps exactly the neighbours it had;
* the two ends of the old branch lose their one neighbour on the old branch and gain their one
  neighbour on the new one;
* the new internal vertices have degree two, like the old ones they replace.

That is why the branch-vertices of the new graph are the images of the old ones, which is what
`Workspace.Types.Tracks.IsBranch` needs at the ends of every track.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementDegrees

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.RungReplacementDelete
open Workspace.ProofLemmas.RungReplacementAddTrack

variable {W Z : Type*} {H : SimpleGraph W} {D : SimpleGraph Z} {q : List W} {b₁ b₂ : W}
  {hb₁ : b₁ ∉ trackInterior q} {hb₂ : b₂ ∉ trackInterior q}
  {rho : resVerts q → Z} {q' : List Z}

/-! ### The new internal vertices have degree two -/

theorem neighborSet_new_interior
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    (j : ℕ) (hj : j + 2 < q'.length) :
    D.neighborSet (q'[j + 1]'(by omega)) ⊆
      {q'[j]'(by omega), q'[j + 2]'(by omega)} := by
  have hnd : q'.Nodup := hext.track.1.2.1
  intro y hy
  have hedge : s(q'[j + 1]'(by omega), y) ∈ D.edgeSet := hy
  rw [hext.edges] at hedge
  rcases hedge with ⟨e₀, he₀, heq⟩ | ⟨i, hi, heq⟩
  · exfalso
    have hmem : q'[j + 1]'(by omega) ∈ Sym2.map rho e₀ := by rw [heq]; simp
    obtain ⟨w, -, hw⟩ := Sym2.mem_map.mp hmem
    exact hext.newInterior _ (mem_trackInterior_getElem q' j (by omega)) ⟨w, hw⟩
  · have hmem : q'[j + 1]'(by omega) ∈ s(q'[i]'(by omega), q'[i + 1]'hi) := by
      rw [← heq]; simp
    rcases Sym2.mem_iff.mp hmem with h | h
    · have hij : j + 1 = i := hnd.getElem_inj_iff.mp h
      subst hij
      have hy2 : y = q'[j + 1 + 1]'hi := by
        rcases Sym2.eq_iff.mp heq with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2
        · exact absurd (hnd.getElem_inj_iff.mp h1) (by omega)
      right
      rw [hy2]
      exact getElem_eq_of_index_eq q' (by omega) hi (by omega)
    · have hij : j + 1 = i + 1 := hnd.getElem_inj_iff.mp h
      have hij' : i = j := by omega
      subst hij'
      have hy2 : y = q'[i]'(by omega) := by
        rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd (hnd.getElem_inj_iff.mp h1) (by omega)
        · exact h2
      left
      exact hy2

theorem not_branchVertex_new_interior
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    {x : Z} (hx : x ∈ trackInterior q') : x ∉ branchVertices D := by
  obtain ⟨j, hj, rfl⟩ := (mem_trackInterior_iff q' x).mp hx
  intro hcon
  have hle : (D.neighborSet (q'[j + 1]'(by omega))).ncard ≤ 2 := by
    refine le_trans (Set.ncard_le_ncard (neighborSet_new_interior hext j hj)
      (Set.toFinite _)) ?_
    exact le_trans (Set.ncard_insert_le _ _) (by simp)
  exact absurd hcon (by simp only [branchVertices, Set.mem_setOf_eq]; omega)

/-! ### Vertices away from the old branch keep their neighbours -/

/-- The neighbours of a retained vertex that is not on the new track. -/
theorem neighborSet_of_notMem_track
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    {w₀ : resVerts q} (hw : rho w₀ ∉ q') :
    D.neighborSet (rho w₀) = rho '' ((resGraph H q).neighborSet w₀) := by
  ext y
  constructor
  · intro hy
    have hedge : s(rho w₀, y) ∈ D.edgeSet := hy
    rw [hext.edges] at hedge
    rcases hedge with ⟨e₀, he₀, heq⟩ | ⟨i, hi, heq⟩
    · induction e₀ using Sym2.ind with
      | _ a b =>
        have heq' : s(rho a, rho b) = s(rho w₀, y) := heq
        rcases Sym2.eq_iff.mp heq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨b, by rw [← hext.inj h1]; exact he₀, h2⟩
        · exact ⟨a, by rw [← hext.inj h2]; exact (resGraph H q).symm he₀, h1⟩
    · exfalso
      have hmem : rho w₀ ∈ s(q'[i]'(by omega), q'[i + 1]'hi) := by rw [← heq]; simp
      rcases Sym2.mem_iff.mp hmem with h | h <;> exact hw (h ▸ List.getElem_mem _)
  · rintro ⟨y₀, hy₀, rfl⟩
    exact hext.oldAdj _ _ hy₀

/-- A vertex of `H` that is not on the deleted branch keeps all of its neighbours. -/
theorem neighborSet_resGraph_of_notMem
    (hclosed : ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q)
    {w : W} (hw : w ∉ q) (hw' : w ∉ trackInterior q) :
    Subtype.val '' ((resGraph H q).neighborSet ⟨w, hw'⟩) = H.neighborSet w := by
  ext y
  constructor
  · rintro ⟨y₀, hy₀, rfl⟩
    exact hy₀.1
  · intro hy
    have hyE : s(w, y) ∈ H.edgeSet := hy
    have hnot : s(w, y) ∉ trackEdges q := fun hcon =>
      hw (Workspace.ProofLemmas.RungReplacementBranchFacts.mem_list_of_mem_trackEdges hcon
        (by simp))
    have hy' : y ∉ trackInterior q := hclosed _ hyE hnot y (by simp)
    exact ⟨⟨y, hy'⟩, ⟨hy, hnot⟩, rfl⟩


/-- A retained vertex other than the two ends of the deleted branch does not lie on the new
track. -/
theorem rho_notMem_track
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    {w₀ : resVerts q} (h₁ : w₀ ≠ ⟨b₁, hb₁⟩) (h₂ : w₀ ≠ ⟨b₂, hb₂⟩) : rho w₀ ∉ q' := by
  intro hcon
  obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hcon
  rcases Workspace.ProofLemmas.RungReplacementLabels.index_of_rho hext w₀ j hj hjw with
    ⟨-, h⟩ | ⟨-, h⟩
  · exact h₁ h
  · exact h₂ h

variable [Finite W]

/-- **A branch-vertex away from the deleted branch stays a branch-vertex.** -/
theorem ncard_neighborSet_of_notMem
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    (hclosed : ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q)
    {w : W} (hw : w ∉ q) (hw' : w ∉ trackInterior q) (hnq' : rho ⟨w, hw'⟩ ∉ q') :
    (D.neighborSet (rho ⟨w, hw'⟩)).ncard = (H.neighborSet w).ncard := by
  rw [neighborSet_of_notMem_track hext hnq',
    Set.ncard_image_of_injective _ hext.inj,
    ← neighborSet_resGraph_of_notMem hclosed hw hw',
    Set.ncard_image_of_injective _ Subtype.val_injective]

/-- **The ends of the deleted branch stay branch-vertices**: each of them loses its neighbour on
the old branch and gains one on the new one. -/
theorem branchVertex_end [Finite Z]
    (hext : IsBranchExtension (resGraph H q) ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ D rho q')
    (hclosed : ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q)
    {c : W} (hc : c ∉ trackInterior q) {d : W} {z : Z}
    (hd : H.Adj c d) (hdq : s(c, d) ∈ trackEdges q)
    (huniq : ∀ y : W, H.Adj c y → s(c, y) ∈ trackEdges q → y = d)
    (hzadj : D.Adj (rho ⟨c, hc⟩) z)
    (hznot : ∀ y₀ : resVerts q, (resGraph H q).Adj ⟨c, hc⟩ y₀ → rho y₀ ≠ z)
    (hcb : c ∈ branchVertices H) : rho ⟨c, hc⟩ ∈ branchVertices D := by
  classical
  -- the residual adjacency at `c`
  have hres : ∀ y : W, H.Adj c y → y ≠ d →
      (resGraph H q).Adj ⟨c, hc⟩ (resEmb q c hc y) := by
    intro y hy hyd
    have hnot : s(c, y) ∉ trackEdges q := fun hcon => hyd (huniq y hy hcon)
    have hy' : y ∉ trackInterior q := hclosed _ hy hnot y (by simp)
    rw [resEmb_of_notMem q c hc hy']
    exact ⟨hy, hnot⟩
  set f : W → Z := fun y => if y = d then z else rho (resEmb q c hc y) with hf
  have hmaps : ∀ y ∈ H.neighborSet c, f y ∈ D.neighborSet (rho ⟨c, hc⟩) := by
    intro y hy
    by_cases hyd : y = d
    · simp only [hf, if_pos hyd]; exact hzadj
    · simp only [hf, if_neg hyd]
      exact hext.oldAdj _ _ (hres y hy hyd)
  have hinj : Set.InjOn f (H.neighborSet c) := by
    intro y₁ hy₁ y₂ hy₂ hEq
    by_cases h₁ : y₁ = d <;> by_cases h₂ : y₂ = d
    · rw [h₁, h₂]
    · exact absurd (by
        simp only [hf, if_pos h₁, if_neg h₂] at hEq
        exact hznot _ (hres y₂ hy₂ h₂) hEq.symm) (fun h => h)
    · exact absurd (by
        simp only [hf, if_neg h₁, if_pos h₂] at hEq
        exact hznot _ (hres y₁ hy₁ h₁) hEq) (fun h => h)
    · simp only [hf, if_neg h₁, if_neg h₂] at hEq
      have := hext.inj hEq
      rw [resEmb_of_notMem q c hc (hclosed _ hy₁ (fun hcon => h₁ (huniq y₁ hy₁ hcon)) y₁ (by simp)),
        resEmb_of_notMem q c hc
          (hclosed _ hy₂ (fun hcon => h₂ (huniq y₂ hy₂ hcon)) y₂ (by simp))] at this
      exact congrArg Subtype.val this
  have hle : (H.neighborSet c).ncard ≤ (D.neighborSet (rho ⟨c, hc⟩)).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj (Set.toFinite _)
  exact le_trans hcb hle

end Workspace.ProofLemmas.RungReplacementDegrees
