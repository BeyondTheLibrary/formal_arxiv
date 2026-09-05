import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm82BranchDelta

/-!
# 5.5 — the branch-free side of a two-vertex separation

This file proves the part of the paper's sentence

> *"Then one of `C,D` is contained in a branch of `H`."*

that identifies the branch once one side of the separation contains no branch-vertex.
Every path from an internal vertex of that side toward either end of its subdividing track
must hit the separator.  Since the separator has at most two vertices, those two hits exhaust
it.  Repeating this for every vertex of the side shows that all of them lie on the same
subdividing track.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm55Structure

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.NoCrossTrackBranch

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A named subdividing track is a branch when the graph being subdivided has minimum degree
at least three. -/
theorem subdivision_track_isBranch
    {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W}
    {ι : Fin n → W} {T : Fin n → Fin n → List W}
    (hJ : IsKConnected J 3) (hS : SubData J H ι T)
    {u v : Fin n} (huv : J.Adj u v) : IsBranch H (T u v) := by
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices
      hS.inj hS.track hS.len hS.disj hS.new
      (Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ)
  have hbrsub : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      hS.track hS.rev hS.disj hS.cover hS.edges
  exact Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
    (hS.track u v huv) (fun h => huv.ne (hS.inj h))
    (fun w hw hbranch => hS.new u v huv w hw (hbrsub hbranch))
    (hrange ⟨u, rfl⟩) (hrange ⟨v, rfl⟩)

/-- Two distinct common vertices force two subdividing tracks to represent the same original
edge. -/
theorem same_original_edge_of_two_common
    {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W}
    {ι : Fin n → W} {T : Fin n → Fin n → List W}
    (hS : SubData J H ι T)
    {a b c d : Fin n} (hab : J.Adj a b) (hcd : J.Adj c d)
    {x y : W} (hxy : x ≠ y)
    (hxab : x ∈ T a b) (hyab : y ∈ T a b)
    (hxcd : x ∈ T c d) (hycd : y ∈ T c d) : s(a, b) = s(c, d) := by
  by_contra hne
  have hxabi : x ∉ trackInterior (T a b) := fun hx => hS.disj a b c d hab hcd hne x hx hxcd
  have hyabi : y ∉ trackInterior (T a b) := fun hy => hS.disj a b c d hab hcd hne y hy hycd
  have hxcdi : x ∉ trackInterior (T c d) :=
    fun hx => hS.disj c d a b hcd hab (Ne.symm hne) x hx hxab
  have hycdi : y ∉ trackInterior (T c d) :=
    fun hy => hS.disj c d a b hcd hab (Ne.symm hne) y hy hyab
  have hxabEnds : x = ι a ∨ x = ι b :=
    Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (hS.track a b hab).2.1 (hS.track a b hab).2.2 hxab hxabi
  have hyabEnds : y = ι a ∨ y = ι b :=
    Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (hS.track a b hab).2.1 (hS.track a b hab).2.2 hyab hyabi
  have hxcdEnds : x = ι c ∨ x = ι d :=
    Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (hS.track c d hcd).2.1 (hS.track c d hcd).2.2 hxcd hxcdi
  have hycdEnds : y = ι c ∨ y = ι d :=
    Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (hS.track c d hcd).2.1 (hS.track c d hcd).2.2 hycd hycdi
  have orient : ∀ {p q : W}, p ≠ q →
      (x = p ∨ x = q) → (y = p ∨ y = q) →
      (x = p ∧ y = q) ∨ (x = q ∧ y = p) := by
    intro p q hpq hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact absurd (hx.trans hy.symm) hxy
  have hiab : ι a ≠ ι b := fun h => hab.ne (hS.inj h)
  have hicd : ι c ≠ ι d := fun h => hcd.ne (hS.inj h)
  rcases orient hiab hxabEnds hyabEnds with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩ <;>
    rcases orient hicd hxcdEnds hycdEnds with ⟨hxc, hyd⟩ | ⟨hxd, hyc⟩
  · apply hne
    apply Sym2.eq_iff.mpr
    exact Or.inl ⟨hS.inj (hxa.symm.trans hxc), hS.inj (hyb.symm.trans hyd)⟩
  · apply hne
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨hS.inj (hxa.symm.trans hxd), hS.inj (hyb.symm.trans hyc)⟩
  · apply hne
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨hS.inj (hya.symm.trans hyd), hS.inj (hxb.symm.trans hxc)⟩
  · apply hne
    apply Sym2.eq_iff.mpr
    exact Or.inl ⟨hS.inj (hya.symm.trans hyc), hS.inj (hxb.symm.trans hxd)⟩

/-- A branch-free closed side meeting the interior of a subdividing track forces two distinct
separator vertices to occur on that track, one on each side of the chosen vertex. -/
theorem separator_hits_both_sides
    {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W}
    {ι : Fin n → W} {T : Fin n → Fin n → List W}
    (hJ : IsKConnected J 3) (hSdata : SubData J H ι T)
    (S E : Set W) (hES : E ⊆ Sᶜ)
    (hEcl : ∀ e ∈ E, ∀ w ∈ Sᶜ, H.Adj e w → w ∈ E)
    (hEnb : ∀ e ∈ E, e ∉ branchVertices H)
    {a b : Fin n} (hab : J.Adj a b) {k : ℕ} (hk : k + 2 < (T a b).length)
    (hzE : (T a b)[k + 1]'(by omega) ∈ E) :
    ∃ (i j : ℕ) (hi : i < (T a b).length) (hj : j < (T a b).length),
      i < k + 1 ∧ k + 1 < j ∧ (T a b)[i]'hi ∈ S ∧ (T a b)[j]'hj ∈ S := by
  have hq : IsTrackFrom H (T a b) (ι a) (ι b) := hSdata.track a b hab
  have hbranchA : ι a ∈ branchVertices H := by
    rw [branch_eq_range hJ hSdata]
    exact ⟨a, rfl⟩
  have hbranchB : ι b ∈ branchVertices H := by
    rw [branch_eq_range hJ hSdata]
    exact ⟨b, rfl⟩
  have hznotS : (T a b)[k + 1]'(by omega) ∉ S := hES hzE
  have hleft : ∃ (i : ℕ) (hi : i < (T a b).length),
      i < k + 1 ∧ (T a b)[i]'hi ∈ S := by
    by_contra hnone
    push Not at hnone
    let L := Workspace.ProofLemmas.TrackSlice.slice (T a b) 0 (k + 1)
    have hL := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice
      (i := 0) (j := k + 1) hq.1 (by omega) (by omega)
    have hLX : ∀ w ∈ L, w ∈ Sᶜ := by
      intro w hw hwS
      obtain ⟨i, hi, -, hik, hiw⟩ :=
        (Workspace.ProofLemmas.TrackSlice.mem_slice_iff (R := T a b) (by omega) (by omega)).mp hw
      have hilt : i < k + 1 := by
        by_contra hnot
        have hieq : i = k + 1 := by omega
        apply hznotS
        have hiS : (T a b)[i]'hi ∈ S := by rw [hiw]; exact hwS
        exact SubdivisionCounting.getElem_eq_of_index_eq (T a b) hieq hi (by omega) ▸ hiS
      have hiS : (T a b)[i]'hi ∈ S := by rw [hiw]; exact hwS
      exact hnone i hi hilt hiS
    have hstart : (T a b)[k + 1]'(by omega) ∈ L := by
      apply (Workspace.ProofLemmas.TrackSlice.mem_slice_iff (R := T a b) (by omega) (by omega)).mpr
      exact ⟨k + 1, by omega, by omega, by omega, rfl⟩
    have hend : (T a b)[0]'(by omega) ∈ L := by
      apply (Workspace.ProofLemmas.TrackSlice.mem_slice_iff (R := T a b) (by omega) (by omega)).mpr
      exact ⟨0, by omega, by omega, by omega, rfl⟩
    have hrch : RchIn H Sᶜ ((T a b)[k + 1]'(by omega)) ((T a b)[0]'(by omega)) :=
      rchIn_of_chain L (List.isChain_iff_getElem.mpr hL.1.2.2) hLX hstart hend
    have hzeroE : (T a b)[0]'(by omega) ∈ E := rchIn_closed hEcl hzE hrch
    apply hEnb _ hzeroE
    rw [SubdivisionCounting.track_head hq (by omega)]
    exact hbranchA
  have hright : ∃ (j : ℕ) (hj : j < (T a b).length),
      k + 1 < j ∧ (T a b)[j]'hj ∈ S := by
    by_contra hnone
    push Not at hnone
    let R := Workspace.ProofLemmas.TrackSlice.slice (T a b) (k + 1) ((T a b).length - 1)
    have hR := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice
      (i := k + 1) (j := (T a b).length - 1) hq.1 (by omega) (by omega)
    have hRX : ∀ w ∈ R, w ∈ Sᶜ := by
      intro w hw hwS
      obtain ⟨j, hj, hkj, -, hjw⟩ :=
        (Workspace.ProofLemmas.TrackSlice.mem_slice_iff (R := T a b) (by omega) (by omega)).mp hw
      have hgt : k + 1 < j := by
        by_contra hnot
        have hjeq : j = k + 1 := by omega
        apply hznotS
        have hjS : (T a b)[j]'hj ∈ S := by rw [hjw]; exact hwS
        exact SubdivisionCounting.getElem_eq_of_index_eq (T a b) hjeq hj (by omega) ▸ hjS
      have hjS : (T a b)[j]'hj ∈ S := by rw [hjw]; exact hwS
      exact hnone j hj hgt hjS
    have hstart : (T a b)[k + 1]'(by omega) ∈ R := by
      apply (Workspace.ProofLemmas.TrackSlice.mem_slice_iff (R := T a b) (by omega) (by omega)).mpr
      exact ⟨k + 1, by omega, by omega, by omega, rfl⟩
    have hend : (T a b)[(T a b).length - 1]'(by omega) ∈ R := by
      apply (Workspace.ProofLemmas.TrackSlice.mem_slice_iff (R := T a b) (by omega) (by omega)).mpr
      exact ⟨(T a b).length - 1, by omega, by omega, by omega, rfl⟩
    have hrch : RchIn H Sᶜ ((T a b)[k + 1]'(by omega))
        ((T a b)[(T a b).length - 1]'(by omega)) :=
      rchIn_of_chain R (List.isChain_iff_getElem.mpr hR.1.2.2) hRX hstart hend
    have hlastE : (T a b)[(T a b).length - 1]'(by omega) ∈ E :=
      rchIn_closed hEcl hzE hrch
    apply hEnb _ hlastE
    have hlast : (T a b)[(T a b).length - 1]'(by omega) = ι b := by
      have h := hq.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
      exact Option.some_injective _ h
    rw [hlast]
    exact hbranchB
  obtain ⟨i, hiB, hi, hiS⟩ := hleft
  obtain ⟨j, hjB, hkj, hjS⟩ := hright
  exact ⟨i, j, hiB, hjB, hi, hkj, hiS, hjS⟩

/-- A nonempty branch-free side which is closed under adjacency outside a separator of size at
most two is contained, vertices and edges, in one branch. -/
theorem branchless_side_contained
    (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (S E : Set W) (hScard : S.ncard ≤ 2)
    (hEne : E.Nonempty) (hES : E ⊆ Sᶜ)
    (hEcl : ∀ e ∈ E, ∀ w ∈ Sᶜ, H.Adj e w → w ∈ E)
    (hEnb : ∀ e ∈ E, e ∉ branchVertices H) :
    ∃ q : List W, IsBranch H q ∧ E ∪ S ⊆ {v : W | v ∈ q} ∧
      {e ∈ H.edgeSet | ∀ w ∈ e, w ∈ E ∪ S} ⊆ trackEdges q := by
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hSdata⟩ := exists_subData hsub
  obtain ⟨z, hzE⟩ := hEne
  have hznotRange : z ∉ Set.range ι := by
    intro hz
    apply hEnb z hzE
    rw [branch_eq_range hJ hSdata]
    exact hz
  obtain ⟨a, b, hab, hzint⟩ :
      ∃ a b : Fin n, J.Adj a b ∧ z ∈ trackInterior (T a b) := by
    rcases hSdata.cover z with hz | hz
    · exact absurd ⟨hz.choose, hz.choose_spec.symm⟩ hznotRange
    · exact hz
  obtain ⟨k, hk, hkz⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (T a b) z).mp hzint
  have hkE : (T a b)[k + 1]'(by omega) ∈ E := by rw [hkz]; exact hzE
  obtain ⟨i, j, hi, hj, hik, hkj, hiS, hjS⟩ :=
    separator_hits_both_sides hJ hSdata S E hES hEcl hEnb hab hk hkE
  let x : W := (T a b)[i]'hi
  let y : W := (T a b)[j]'hj
  have hxy : x ≠ y := by
    intro h
    exact (by omega : i ≠ j) ((hSdata.track a b hab).1.2.1.getElem_inj_iff.mp h)
  have hxS : x ∈ S := hiS
  have hyS : y ∈ S := hjS
  have hpairS : ({x, y} : Set W) ⊆ S := by
    intro w hw
    rcases hw with rfl | rfl
    · exact hxS
    · exact hyS
  have hpairEq : ({x, y} : Set W) = S := by
    apply Set.eq_of_subset_of_ncard_le hpairS
    · rw [Set.ncard_pair hxy]
      exact hScard
  have hSsub : S ⊆ {w : W | w ∈ T a b} := by
    intro w hw
    rw [← hpairEq] at hw
    rcases hw with rfl | rfl
    · exact List.getElem_mem _
    · exact List.getElem_mem _
  have hEsub : E ⊆ {w : W | w ∈ T a b} := by
    intro w hwE
    have hwRange : w ∉ Set.range ι := by
      intro hw
      apply hEnb w hwE
      rw [branch_eq_range hJ hSdata]
      exact hw
    obtain ⟨c, d, hcd, hwint⟩ :
        ∃ c d : Fin n, J.Adj c d ∧ w ∈ trackInterior (T c d) := by
      rcases hSdata.cover w with hw | hw
      · exact absurd ⟨hw.choose, hw.choose_spec.symm⟩ hwRange
      · exact hw
    obtain ⟨m, hm, hmw⟩ :=
      (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (T c d) w).mp hwint
    have hmE : (T c d)[m + 1]'(by omega) ∈ E := by rw [hmw]; exact hwE
    obtain ⟨i', j', hi', hj', hi'lt, hj'gt, hi'S, hj'S⟩ :=
      separator_hits_both_sides hJ hSdata S E hES hEcl hEnb hcd hm hmE
    have hSsub' : S ⊆ {t : W | t ∈ T c d} := by
      have hxy' : (T c d)[i']'hi' ≠ (T c d)[j']'hj' := by
        intro heq
        have := (hSdata.track c d hcd).1.2.1.getElem_inj_iff.mp heq
        omega
      have hp : ({(T c d)[i']'hi', (T c d)[j']'hj'} : Set W) ⊆ S := by
        intro t ht
        rcases ht with rfl | rfl
        · exact hi'S
        · exact hj'S
      have hpEq : ({(T c d)[i']'hi', (T c d)[j']'hj'} : Set W) = S := by
        apply Set.eq_of_subset_of_ncard_le hp
        · rw [Set.ncard_pair hxy']
          exact hScard
      intro t ht
      rw [← hpEq] at ht
      rcases ht with rfl | rfl <;> exact List.getElem_mem _
    have hxT : x ∈ T c d := hSsub' hxS
    have hyT : y ∈ T c d := hSsub' hyS
    have hedgeEq := same_original_edge_of_two_common hSdata hab hcd hxy
      (List.getElem_mem _) (List.getElem_mem _) hxT hyT
    have hwlist : w ∈ T c d :=
      Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hwint
    rcases Sym2.eq_iff.mp hedgeEq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · subst c
      subst d
      exact hwlist
    · have hac' : c = b := hbc.symm
      have hbd' : d = a := had.symm
      subst c
      subst d
      rw [hSdata.rev a b hab] at hwlist
      simpa using hwlist
  have hVsub : E ∪ S ⊆ {w : W | w ∈ T a b} := Set.union_subset hEsub hSsub
  refine ⟨T a b, subdivision_track_isBranch hJ hSdata hab, hVsub, ?_⟩
  rintro e ⟨heH, heEnds⟩
  rw [hSdata.edges] at heH
  simp only [Set.mem_iUnion] at heH
  obtain ⟨c, d, hcd, m, hm, heq⟩ := heH
  let u : W := (T c d)[m]'(by omega)
  let v : W := (T c d)[m + 1]'hm
  have huv : u ≠ v := (hSdata.track c d hcd).1.2.2 m hm |>.ne
  have hue : u ∈ e := by rw [heq]; simp [u]
  have hve : v ∈ e := by rw [heq]; simp [v]
  have huq : u ∈ T a b := hVsub (heEnds u hue)
  have hvq : v ∈ T a b := hVsub (heEnds v hve)
  have hedgeEq := same_original_edge_of_two_common hSdata hab hcd huv
    huq hvq (List.getElem_mem _) (List.getElem_mem _)
  have hemem : e ∈ trackEdges (T c d) := ⟨m, hm, heq⟩
  rcases Sym2.eq_iff.mp hedgeEq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · subst c
    subst d
    exact hemem
  · have hac' : c = b := hbc.symm
    have hbd' : d = a := had.symm
    subst c
    subst d
    rw [hSdata.rev a b hab, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at hemem
    exact hemem

end Workspace.ProofLemmas.Thm55Structure
