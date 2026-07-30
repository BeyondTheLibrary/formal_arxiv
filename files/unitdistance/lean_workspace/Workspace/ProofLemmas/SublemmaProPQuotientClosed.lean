-- Cited from: Standard profinite group theory: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010 (quotients of pro-p groups by closed normal subgroups are pro-p).
-- Paper label: standard profinite fact (implicit in paper Step 2, tex 747-781)
-- NL statement: For a prime p, a pro-p group G (a compact Hausdorff totally-disconnected topological group in which every open normal subgroup has p-power index), and a closed normal subgroup N ≤ G, the quotient topological group G/N is again pro-p.
-- Proof outline. G/N inherits IsTopologicalGroup, CompactSpace, and (since N is closed and
-- normal) T3 hence T2 as Mathlib instances. The p-power-index condition transfers along the
-- surjective quotient map QuotientGroup.mk' N via Subgroup.index_comap_of_surjective: an open
-- normal H ≤ G/N pulls back to an open normal H.comap (mk' N) ≤ G of equal index, which is a
-- p-power by hypothesis. The key point is TotallyDisconnectedSpace (G/N): by
-- totallyDisconnectedSpace_iff_connectedComponent_one it suffices to show the connected
-- component of 1 is {1}, and in the compact Hausdorff quotient this component equals the
-- intersection of all clopen neighbourhoods of 1 (connectedComponent_eq_iInter_isClopen). Given
-- g ∉ N, ProfiniteGrp.closedSubgroup_eq_sInf_open expresses the closed subgroup N as the
-- infimum of the open subgroups containing it, so some open K ⊇ N has g ∉ K; its image K.map
-- (mk' N) is an open — hence clopen (OpenSubgroup.isClopen) — subgroup of G/N containing 1 but
-- not the class of g, separating that class from 1. Hence only 1 survives the intersection.
import Mathlib
import Workspace.Types.ProPGroup

open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000 in
theorem SublemmaProPQuotientClosed :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G]
      (N : Subgroup G) [N.Normal],
      IsClosed (N : Set G) → IsProP p G → IsProP p (G ⧸ N) := by
  intro p _ G _ _ N _ hNclosed hG
  obtain ⟨hTop, hCompact, hT2, hTD, hIndex⟩ := hG
  haveI : IsTopologicalGroup G := hTop
  haveI : CompactSpace G := hCompact
  haveI : T2Space G := hT2
  haveI : TotallyDisconnectedSpace G := hTD
  haveI : IsClosed (N : Set G) := hNclosed
  -- Quotient instances
  haveI hqTop : IsTopologicalGroup (G ⧸ N) := inferInstance
  haveI hqCompact : CompactSpace (G ⧸ N) := inferInstance
  haveI hqT3 : T3Space (G ⧸ N) := inferInstance
  haveI hqT2 : T2Space (G ⧸ N) := inferInstance
  refine ⟨hqTop, hqCompact, hqT2, ?_, ?_⟩
  · -- TotallyDisconnectedSpace (G ⧸ N)
    rw [totallyDisconnectedSpace_iff_connectedComponent_one]
    rw [connectedComponent_eq_iInter_isClopen]
    -- goal: ⋂ s : {s // IsClopen s ∧ (1:G⧸N) ∈ s}, s = {1}
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · -- 1 ∈ ⋂
      rw [Set.mem_iInter]
      intro s
      exact s.2.2
    · -- uniqueness: any y in the intersection equals 1
      intro y hy
      by_contra hne
      -- y ≠ 1. Lift y to g ∈ G with mk g = y, g ∉ N
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      -- g ∉ N since mk g ≠ 1
      have hgN : g ∉ N := by
        intro hgin
        exact hne ((QuotientGroup.eq_one_iff g).mpr hgin)
      -- N as closed subgroup; use closedSubgroup_eq_sInf_open
      have hNeq : (N : Subgroup G) = sInf {K : Subgroup G | IsOpen (K : Set G) ∧ (⟨N, hNclosed⟩ : ClosedSubgroup G) ≤ K} :=
        ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨N, hNclosed⟩
      -- since g ∉ N = sInf, there is open K ⊇ N with g ∉ K
      have hg_not_sInf : g ∉ sInf {K : Subgroup G | IsOpen (K : Set G) ∧ (⟨N, hNclosed⟩ : ClosedSubgroup G) ≤ K} := by
        rw [← hNeq]; exact hgN
      rw [Subgroup.mem_sInf] at hg_not_sInf
      push Not at hg_not_sInf
      obtain ⟨K, ⟨hKopen, hNK⟩, hgK⟩ := hg_not_sInf
      -- image π '' K is a clopen subgroup of G/N containing 1, not containing mk g
      set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
      have hNleK : N ≤ K := hNK
      -- π K = K.map π is open
      have hmapopen : IsOpen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        rw [Subgroup.coe_map]
        exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hKopen
      -- clopen
      have hmapclopen : IsClopen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
        (OpenSubgroup.isClopen ⟨K.map π, hmapopen⟩)
      -- 1 ∈ K.map π
      have h1mem : (1 : G ⧸ N) ∈ (K.map π : Subgroup (G ⧸ N)) := one_mem _
      -- mk g ∉ K.map π
      have hgmap : (π g) ∉ (K.map π : Subgroup (G ⧸ N)) := by
        rw [Subgroup.mem_map]
        rintro ⟨x, hxK, hx⟩
        -- hx : π x = π g, so x⁻¹ * g ∈ N ≤ K, and x ∈ K ⟹ g ∈ K, contradiction
        rw [hπ] at hx
        have hxgN : x⁻¹ * g ∈ N := by
          rw [← QuotientGroup.eq]
          exact hx
        have hxgK : x⁻¹ * g ∈ K := hNleK hxgN
        have : g ∈ K := by
          have := mul_mem hxK hxgK
          simpa using this
        exact hgK this
      -- (π g) lies in the intersection (it is y), hence in this clopen set containing 1
      have : (π g) ∈ ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        rw [Set.mem_iInter] at hy
        exact hy ⟨((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)), hmapclopen, h1mem⟩
      exact hgmap this
  · -- index condition: every open normal subgroup of G/N has p-power index
    intro H hHnorm hHopen
    set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
    have hcont : Continuous π := QuotientGroup.continuous_mk
    set K : Subgroup G := H.comap π with hK
    have hKnorm : K.Normal := hHnorm.comap π
    have hKopen : IsOpen (K : Set G) := by
      rw [hK, Subgroup.coe_comap]
      exact hcont.isOpen_preimage _ hHopen
    obtain ⟨k, hk⟩ := hIndex K hKnorm hKopen
    refine ⟨k, ?_⟩
    rw [← hk, hK]
    exact (Subgroup.index_comap_of_surjective H hsurj).symm
