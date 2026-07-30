import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.ProPGeneratorRankFrattini
import Workspace.ProofLemmas.SublemmaProPQuotientClosed
import Workspace.ProofLemmas.SublemmaTopFinGenQuotientClosed

/-!
# Generator rank of a pro-`p` group modulo a closed normal subgroup of the Frattini subgroup

`d(G/N) = d(G)` when `N` is the closed normal closure of finitely many elements of `Φ(G)`.
Extracted from `ProPFrattiniQuotientRanks` into its own file so that the *relation*-rank half
(`ProPRelationRankFrattiniQuotient`) can use it without an import cycle.
-/

set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace Workspace.ProofLemmas.ProPGeneratorRankQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]

/-- The comap of a maximal open subgroup of `G/N` (along `G ↠ G/N`) is a maximal open subgroup
of `G`. -/
theorem comap_maximalOpen (Mbar : Subgroup (G ⧸ N))
    (hMbar : IsMaximalOpenSubgroup Mbar) :
    IsMaximalOpenSubgroup (Mbar.comap (QuotientGroup.mk' N)) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπcont : Continuous π := QuotientGroup.continuous_mk
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_comap]; exact hπcont.isOpen_preimage _ hMbar.1
  · intro htop
    apply hMbar.2.1
    have h := Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar
    rw [htop, Subgroup.map_top_of_surjective π hπsurj] at h
    exact h.symm
  · intro K hKopen hMK
    have hNcomap : N ≤ Mbar.comap π := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx1 : π x = 1 := by
        rw [hπ, QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff x).mpr hx
      rw [hx1]; exact one_mem _
    have hNK : N ≤ K := le_trans hNcomap hMK
    have hcomapmapK : (K.map π).comap π = K := by
      rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
      exact sup_eq_left.mpr hNK
    have hmapKopen : IsOpen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
      rw [Subgroup.coe_map]
      exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hKopen
    have hMbarle : Mbar ≤ K.map π := by
      have h := Subgroup.map_mono (f := π) hMK
      rwa [Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar] at h
    rcases hMbar.2.2 (K.map π) hmapKopen hMbarle with h | h
    · left; rw [← hcomapmapK, h]
    · right; rw [← hcomapmapK, h, Subgroup.comap_top]

/-- For a maximal open subgroup `M` of `G` containing `N`, its image `M.map (G ↠ G/N)` is a maximal
open subgroup of `G/N`. -/
theorem map_maximalOpen (M : Subgroup G) (hM : IsMaximalOpenSubgroup M) (hNM : N ≤ M) :
    IsMaximalOpenSubgroup (M.map (QuotientGroup.mk' N)) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcm : (M.map π).comap π = M := by
    rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
    exact sup_eq_left.mpr hNM
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hM.1
  · intro htop
    apply hM.2.1
    rw [← hcm, htop, Subgroup.comap_top]
  · intro Kbar hKbaropen hMKbar
    have hcomapKbaropen : IsOpen ((Kbar.comap π : Subgroup G) : Set G) := by
      rw [Subgroup.coe_comap]
      exact (QuotientGroup.continuous_mk).isOpen_preimage _ hKbaropen
    have hMcomap : M ≤ Kbar.comap π := by
      rw [← hcm]; exact Subgroup.comap_mono hMKbar
    rcases hM.2.2 (Kbar.comap π) hcomapKbaropen hMcomap with h | h
    · left
      have hkk := Subgroup.map_comap_eq_self_of_surjective hπsurj Kbar
      rw [← hkk, h]
    · right
      have hkk := Subgroup.map_comap_eq_self_of_surjective hπsurj Kbar
      rw [← hkk, h, Subgroup.map_top_of_surjective π hπsurj]

/-- **Correspondence step.** If `N ⊆ Φ(G)`, the topological Frattini subgroup of `G` is the
preimage of the topological Frattini subgroup of `G/N` along `G ↠ G/N`. -/
theorem frattini_comap_eq (hNsub : N ≤ frattiniOpen G) :
    (frattiniOpen (G ⧸ N)).comap (QuotientGroup.mk' N) = frattiniOpen G := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro M hM
    have hNM : N ≤ M := le_trans hNsub (by rw [frattiniOpen]; exact sInf_le hM)
    have hmapM : IsMaximalOpenSubgroup (M.map π) := map_maximalOpen M hM hNM
    have hcm : (M.map π).comap π = M := by
      rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
      exact sup_eq_left.mpr hNM
    have hπxM : π x ∈ M.map π := by
      have hle : frattiniOpen (G ⧸ N) ≤ M.map π := by rw [frattiniOpen]; exact sInf_le hmapM
      exact hle hx
    have hxcomap : x ∈ (M.map π).comap π := by rw [Subgroup.mem_comap]; exact hπxM
    rwa [hcm] at hxcomap
  · intro x hx
    rw [Subgroup.mem_comap, frattiniOpen, Subgroup.mem_sInf]
    intro Mbar hMbar
    have hcomapMax : IsMaximalOpenSubgroup (Mbar.comap π) := comap_maximalOpen Mbar hMbar
    have hxin : x ∈ Mbar.comap π := by
      have hle : frattiniOpen G ≤ Mbar.comap π := by rw [frattiniOpen]; exact sInf_le hcomapMax
      exact hle hx
    rwa [Subgroup.mem_comap] at hxin

/-- The generator-rank half of Proposition 3.3: `d(G/N) = d(G)`. -/
theorem main (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    dRank (G ⧸ N) = dRank G := by
  -- N ⊆ Φ(G)
  haveI hΦnorm : (frattiniOpen G).Normal :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_normal p G hpro hfg
  have hΦopen : IsOpen ((frattiniOpen G : Subgroup G) : Set G) :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_isOpen p G hpro hfg
  have hΦclosed : IsClosed ((frattiniOpen G : Subgroup G) : Set G) :=
    Subgroup.isClosed_of_isOpen _ hΦopen
  have hrange : Set.range g ⊆ (frattiniOpen G : Set G) := by
    rintro _ ⟨i, rfl⟩; exact hg i
  have hnc : Subgroup.normalClosure (Set.range g) ≤ frattiniOpen G :=
    Subgroup.normalClosure_le_normal hrange
  have hNsub : N ≤ frattiniOpen G := by
    rw [hN]; exact Subgroup.topologicalClosure_minimal _ hnc hΦclosed
  have hNclosed : IsClosed (N : Set G) := by
    rw [hN]; exact Subgroup.isClosed_topologicalClosure _
  -- quotient is pro-p and top. finitely generated
  have hproQ : IsProP p (G ⧸ N) := SublemmaProPQuotientClosed p G N hNclosed hpro
  have hfgQ : TopFinitelyGenerated (G ⧸ N) := SublemmaTopFinGenQuotientClosed G N hfg
  haveI hNormQ : (frattiniOpen (G ⧸ N)).Normal :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_normal p (G ⧸ N) hproQ hfgQ
  -- Burnside rank formula for both groups
  obtain ⟨d, hdrank, hdcard⟩ := ProPGeneratorRankFrattini p G hpro hfg
  obtain ⟨d', hd'rank, hd'card⟩ := ProPGeneratorRankFrattini p (G ⧸ N) hproQ hfgQ
  -- Frattini quotients have equal cardinality via  G/Φ(G) ≅ (G/N)/Φ(G/N)
  have hcardeq : Nat.card (G ⧸ frattiniOpen G)
      = Nat.card ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) := by
    set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
    set σ : G →* ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) :=
      (QuotientGroup.mk' (frattiniOpen (G ⧸ N))).comp π with hσ
    have hσsurj : Function.Surjective σ := by
      rw [hσ, MonoidHom.coe_comp]
      exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hkerσ : σ.ker = frattiniOpen G := by
      have h1 : σ.ker = (frattiniOpen (G ⧸ N)).comap π := by
        rw [hσ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rw [h1]; exact frattini_comap_eq hNsub
    have e := QuotientGroup.quotientKerEquivOfSurjective σ hσsurj
    have hc : Nat.card (G ⧸ σ.ker)
        = Nat.card ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) := Nat.card_congr e.toEquiv
    rwa [hkerσ] at hc
  -- conclude d = d', hence dRank equal
  rw [hdcard, hd'card] at hcardeq
  have hdd : d = d' := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcardeq
  rw [hd'rank, hdrank, hdd]


end Workspace.ProofLemmas.ProPGeneratorRankQuotient
