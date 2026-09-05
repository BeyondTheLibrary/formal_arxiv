import Workspace.ProofLemmas.SubdivisionCounting

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT

private theorem bipartite_six_four_branches_cycle
    {W : Type*} [Fintype W] (H : SimpleGraph W)
    (a b c d : W) (hnd : [a, b, c, d].Nodup)
    (hbranch : branchVertices H = ({a, b, c, d} : Set W))
    (hbip : H.IsBipartite) (hcard : Fintype.card W = 6) :
    DegenerateK4Appearance H := by
  classical
  obtain ⟨color, hcolor⟩ := hbip
  have hproper {x y : W} (hxy : H.Adj x y) : color x ≠ color y := hcolor hxy
  have no_three_same (x y z q : W)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hbranch' : branchVertices H = ({x, y, z, q} : Set W))
      (hcxy : color x = color y) (hcxz : color x = color z) : False := by
    let A : Set W := {x, y, z}
    have hAcard : A.ncard = 3 := by simp [A, hxy, hxz, hyz]
    have hxbranch : x ∈ branchVertices H := by rw [hbranch']; simp
    have hybranch : y ∈ branchVertices H := by rw [hbranch']; simp
    have hzbranch : z ∈ branchVertices H := by rw [hbranch']; simp
    have hdisj (r : W) (hrA : r ∈ A) (hcr : color r = color x) :
        Disjoint A (H.neighborSet r) := by
      rw [Set.disjoint_left]
      intro w hwA hwr
      have hcw : color w = color x := by
        simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at hwA
        rcases hwA with rfl | rfl | rfl
        · exact rfl
        · exact hcxy.symm
        · exact hcxz.symm
      exact hproper hwr (hcr.trans hcw.symm)
    have neighbor_eq_three (r : W) (hrA : r ∈ A) (hcr : color r = color x)
        (hrbranch : r ∈ branchVertices H) : (H.neighborSet r).ncard = 3 := by
      have hr3 : 3 ≤ (H.neighborSet r).ncard := hrbranch
      have hu : (A ∪ H.neighborSet r).ncard ≤ (Set.univ : Set W).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard,
        Set.ncard_union_eq (hdisj r hrA hcr) (Set.toFinite _) (Set.toFinite _), hAcard] at hu
      omega
    have union_eq_univ (r : W) (hrA : r ∈ A) (hcr : color r = color x)
        (hrbranch : r ∈ branchVertices H) : A ∪ H.neighborSet r = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard,
        Set.ncard_union_eq (hdisj r hrA hcr) (Set.toFinite _) (Set.toFinite _), hAcard,
        neighbor_eq_three r hrA hcr hrbranch]
    have hNx : (H.neighborSet x).ncard = 3 :=
      neighbor_eq_three x (by simp [A]) rfl hxbranch
    have hNxq : H.neighborSet x ⊆ ({q} : Set W) := by
      intro w hw
      have hwA : w ∉ A := by
        intro hwA
        exact Set.disjoint_left.mp (hdisj x (by simp [A]) rfl) hwA hw
      have hwy : H.Adj y w := by
        have hu := union_eq_univ y (by simp [A]) hcxy.symm hybranch
        have : w ∈ A ∪ H.neighborSet y := by rw [hu]; simp
        exact this.resolve_left hwA
      have hwz : H.Adj z w := by
        have hu := union_eq_univ z (by simp [A]) hcxz.symm hzbranch
        have : w ∈ A ∪ H.neighborSet z := by rw [hu]; simp
        exact this.resolve_left hwA
      have hwbranch : w ∈ branchVertices H := by
        show 3 ≤ (H.neighborSet w).ncard
        have hsub : ({x, y, z} : Set W) ⊆ H.neighborSet w := by
          intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl | rfl
          · exact H.symm hw
          · exact H.symm hwy
          · exact H.symm hwz
        rw [← hAcard]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [hbranch'] at hwbranch
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwbranch
      rcases hwbranch with rfl | rfl | rfl | hq
      · exact absurd hwA (by simp [A])
      · exact absurd hwA (by simp [A])
      · exact absurd hwA (by simp [A])
      · exact hq
    have hle : (H.neighborSet x).ncard ≤ ({q} : Set W).ncard :=
      Set.ncard_le_ncard hNxq (Set.toFinite _)
    simp only [Set.ncard_singleton] at hle
    omega
  have hab : a ≠ b := by rintro rfl; simp at hnd
  have hac : a ≠ c := by rintro rfl; simp at hnd
  have had : a ≠ d := by rintro rfl; simp at hnd
  have hbc : b ≠ c := by rintro rfl; simp at hnd
  have hbd : b ≠ d := by rintro rfl; simp at hnd
  have hcd : c ≠ d := by rintro rfl; simp at hnd
  have hnd_abd : [a, b, d, c].Nodup := by
    simp [hab, hac, had, hbc, hbd, hcd, Ne.symm]
  have hnd_acb : [a, c, b, d].Nodup := by
    simp [hab, hac, had, hbc, hbd, hcd, Ne.symm]
  have hb_abdc : branchVertices H = ({a, b, d, c} : Set W) := by
    rw [hbranch]
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hb_acdb : branchVertices H = ({a, c, d, b} : Set W) := by
    rw [hbranch]
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hb_bcda : branchVertices H = ({b, c, d, a} : Set W) := by
    rw [hbranch]
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have ntabc : ¬ (color a = color b ∧ color a = color c) :=
    fun h => no_three_same a b c d hab hac hbc hbranch h.1 h.2
  have ntabd : ¬ (color a = color b ∧ color a = color d) :=
    fun h => no_three_same a b d c hab had hbd hb_abdc h.1 h.2
  have ntacd : ¬ (color a = color c ∧ color a = color d) :=
    fun h => no_three_same a c d b hac had hcd hb_acdb h.1 h.2
  have ntbcd : ¬ (color b = color c ∧ color b = color d) :=
    fun h => no_three_same b c d a hbc hbd hcd hb_bcda h.1 h.2
  have hcases :
      (color a = color b ∧ color c = color d ∧ color a ≠ color c) ∨
      (color a = color c ∧ color b = color d ∧ color a ≠ color b) ∨
      (color a = color d ∧ color b = color c ∧ color a ≠ color b) := by
    simp only [Fin.ext_iff] at ntabc ntabd ntacd ntbcd ⊢
    omega
  have adjacency_of_opposite {x y : W}
      (hx : x ∈ branchVertices H) (hy : y ∈ branchVertices H)
      (hxy : color x ≠ color y) : H.Adj x y := by
    let S : Set W := {w | color w = color x}
    let T : Set W := {w | color w ≠ color x}
    have hyT : y ∈ T := by exact fun heq => hxy heq.symm
    have hdisj : Disjoint S T := by
      rw [Set.disjoint_left]
      simp [S, T]
    have hST : S ∪ T = Set.univ := by
      ext w
      by_cases hw : color w = color x <;> simp [S, T, hw]
    have hNxT : H.neighborSet x ⊆ T := by
      intro w hw
      exact hproper (H.symm hw)
    have hNyS : H.neighborSet y ⊆ S := by
      intro w hw
      have hp := hproper hw
      simp only [S, Set.mem_setOf_eq, Fin.ext_iff] at hxy hp ⊢
      omega
    have hT3 : 3 ≤ T.ncard := le_trans hx (Set.ncard_le_ncard hNxT (Set.toFinite _))
    have hS3 : 3 ≤ S.ncard := le_trans hy (Set.ncard_le_ncard hNyS (Set.toFinite _))
    have hsum : S.ncard + T.ncard = 6 := by
      rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hST,
        Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    have hTcard : T.ncard = 3 := by omega
    have heq : H.neighborSet x = T := by
      apply Set.eq_of_subset_of_ncard_le hNxT
      rw [hTcard]
      exact hx
    have hyN : y ∈ H.neighborSet x := heq.symm ▸ hyT
    exact hyN
  rcases hcases with h | h | h
  · refine ⟨a, c, b, d, hnd_acb, ?_, ?_, ?_, ?_, ?_⟩
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp) h.2.2
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.1] using h.2.2.symm)
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.1, h.2.1] using h.2.2)
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.2.1] using h.2.2.symm)
    · rw [hbranch]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with rfl | rfl | rfl | rfl <;> simp
  · refine ⟨a, b, c, d, hnd, ?_, ?_, ?_, ?_, ?_⟩
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp) h.2.2
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.1] using h.2.2.symm)
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.1, h.2.1] using h.2.2)
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.2.1] using h.2.2.symm)
    · rw [hbranch]
  · refine ⟨a, b, d, c, hnd_abd, ?_, ?_, ?_, ?_, ?_⟩
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp) h.2.2
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.1] using h.2.2.symm)
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.1, h.2.1] using h.2.2)
    · exact adjacency_of_opposite (hbranch ▸ by simp) (hbranch ▸ by simp)
        (by simpa [h.2.1] using h.2.2.symm)
    · rw [hbranch]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with rfl | rfl | rfl | rfl <;> simp

/-- A bipartite subdivision of a graph isomorphic to `K₄` on exactly six vertices is a
degenerate appearance. -/
theorem SixVertexBipartiteK4SubdivisionDegenerate
    {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (H : SimpleGraph W)
    (hJ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hH : IsBipartiteSubdivision J H)
    (hcard : Fintype.card W = 6) :
    DegenerateAppearance J H := by
  classical
  obtain ⟨e⟩ := hJ
  obtain ⟨⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩, hbip⟩ := hH
  have hconn : IsKConnected J 3 :=
    SubdivisionCounting.isKConnected_of_iso e.symm SubdivisionCounting.k4_three_connected
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hconn
  have hrange : Set.range ι = branchVertices H := by
    apply Set.Subset.antisymm
    · exact SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg
    · exact SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  let a := ι (e.symm 0)
  let b := ι (e.symm 1)
  let c := ι (e.symm 2)
  let d := ι (e.symm 3)
  have hnd : [a, b, c, d].Nodup := by
    have hfin : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
    simpa [a, b, c, d] using hfin.map (hι.comp e.symm.injective)
  have hrange' : Set.range ι = ({a, b, c, d} : Set W) := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨i, rfl⟩ := e.symm.surjective u
      fin_cases i <;> simp [a, b, c, d]
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨e.symm 0, rfl⟩
      · exact ⟨e.symm 1, rfl⟩
      · exact ⟨e.symm 2, rfl⟩
      · exact ⟨e.symm 3, rfl⟩
  refine Or.inl ⟨⟨e⟩, bipartite_six_four_branches_cycle H a b c d hnd ?_ hbip hcard⟩
  rw [← hrange, hrange']

end Workspace.ProofLemmas
