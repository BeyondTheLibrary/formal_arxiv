import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.ProPGeneratorRankQuotient

/-!
# The relation-rank half of the pro-`p` Frattini-quotient proposition

`r(G/N) ≤ r(G) + k` when `N` is the closed normal closure of `g_1, …, g_k ∈ Φ(G)`.

Given a minimal pro-`p` presentation `π : freeProP p d ↠ G` with `m = r(G)` relations, lift each
`g_i` to `ĝ_i ∈ freeProP p d` and adjoin the `ĝ_i` as `k` further relations.  The resulting
`π' = (G ↠ G/N) ∘ π` is surjective, and its kernel `π⁻¹(N)` is exactly the closed normal closure
`M` of the enlarged relation family:

* `M ≤ π⁻¹(N)` because `π⁻¹(N)` is a closed normal subgroup containing all the new relations;
* `π⁻¹(N) ≤ M` because `M` is closed in the compact group `freeProP p d`, so `π(M)` is a closed
  normal subgroup of `G` containing every `g_i`, hence containing `N`; combined with
  `ker π ≤ M` this gives `π⁻¹(N) ⊆ M`.

Finally `d(G/N) = d(G)` (the generator-rank half, `ProPGeneratorRankQuotient.main`) makes the new
presentation a *minimal-generator* presentation of `G/N`, so it witnesses `r(G/N) ≤ m + k`.
The passage from "for every presentation of `G`" to the infima uses `tsub_le_iff_right` in `ℕ∞`.
-/

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.ProPRelationRank


/-- `freeProP p n` is compact (a closed subgroup of a product of finite discrete groups). -/
theorem compactSpace_freeProP (p n : ℕ) : CompactSpace (freeProP p n) := by
  have hclosed : IsClosed ((freeProPSubgroup p n : Set (ProdQuot p n))) :=
    Subgroup.isClosed_topologicalClosure _
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

/-- The quotient map as a continuous monoid hom. -/
def quotHom {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
    [N.Normal] : G →ₜ* (G ⧸ N) where
  toFun := QuotientGroup.mk' N
  map_one' := map_one _
  map_mul' := map_mul _
  continuous_toFun := continuous_quot_mk

@[simp] theorem quotHom_apply {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (x : G) : quotHom N x = QuotientGroup.mk' N x := rfl



/-- **Relation-rank half of Proposition 3.3 / A.8.**  If `g_1, …, g_k ∈ Φ(G)` and `N` is the closed
normal subgroup they generate, then `r(G/N) ≤ r(G) + k`. -/
theorem proPRelationRankFrattiniQuotient (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    relRank p (G ⧸ N) ≤ relRank p G + (k : ℕ∞) := by
  classical
  have hNclosed : IsClosed (N : Set G) := by
    rw [hN]; exact Subgroup.isClosed_topologicalClosure _
  have hdrank : dRank (G ⧸ N) = dRank G :=
    Workspace.ProofLemmas.ProPGeneratorRankQuotient.main p G hpro hfg k g hg N hN
  obtain ⟨_, hcomp, hT2, _, _⟩ := hpro
  haveI := hT2
  haveI := hcomp
  rw [← tsub_le_iff_right, relRank]
  apply le_sInf
  rintro c ⟨d, m, π, rels, hdr, hpres, rfl⟩
  rw [tsub_le_iff_right]
  haveI : CompactSpace (freeProP p d) := compactSpace_freeProP p d
  obtain ⟨hsurj, hker⟩ := hpres
  -- lifts of the `g i`
  choose ĝ hĝ using fun i => hsurj (g i)
  set rels' : Fin (m + k) → freeProP p d := Fin.append rels ĝ with hrels'
  set M : Subgroup (freeProP p d) :=
    (Subgroup.normalClosure (Set.range rels')).topologicalClosure with hM
  -- basic facts about the ranges
  have hrelsub : Set.range rels ⊆ Set.range rels' := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castAdd k j, by simp [hrels']⟩
  have hgsub : Set.range ĝ ⊆ Set.range rels' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.natAdd m i, by simp [hrels']⟩
  have hrangesub : Set.range rels' ⊆ Set.range rels ∪ Set.range ĝ := by
    rintro _ ⟨j, rfl⟩
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · exact Or.inl ⟨j₁, by simp [hrels']⟩
    · exact Or.inr ⟨j₂, by simp [hrels']⟩
  haveI : (Subgroup.normalClosure (Set.range rels')).Normal := Subgroup.normalClosure_normal
  haveI hMnormal : M.Normal := Subgroup.is_normal_topologicalClosure _
  have hMclosed : IsClosed (M : Set (freeProP p d)) := Subgroup.isClosed_topologicalClosure _
  -- `ker π ≤ M`
  have hkerM : MonoidHom.ker π.toMonoidHom ≤ M := by
    rw [← hker, hM]
    exact Subgroup.topologicalClosure_mono (Subgroup.normalClosure_le_normal
      (le_trans hrelsub Subgroup.subset_normalClosure))
  -- the quotient presentation
  set π' : freeProP p d →ₜ* (G ⧸ N) := (quotHom N).comp π with hπ'
  have hsurj' : Function.Surjective π' := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, rfl⟩
  have hkerπ' : MonoidHom.ker π'.toMonoidHom = N.comap π.toMonoidHom := by
    ext x
    simp [hπ', MonoidHom.mem_ker, Subgroup.mem_comap, QuotientGroup.eq_one_iff]
  -- `M = ker π'`
  have hMker : M = MonoidHom.ker π'.toMonoidHom := by
    rw [hkerπ']
    apply le_antisymm
    · -- `M ≤ π⁻¹ N`
      haveI : (N.comap π.toMonoidHom).Normal := Subgroup.Normal.comap ‹N.Normal› π.toMonoidHom
      have hclosed : IsClosed ((N.comap π.toMonoidHom : Subgroup (freeProP p d)) :
          Set (freeProP p d)) := hNclosed.preimage π.continuous_toFun
      refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rcases hrangesub hx with hx | hx
      · obtain ⟨j, rfl⟩ := hx
        have : rels j ∈ MonoidHom.ker π.toMonoidHom := by
          rw [← hker]
          exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        show rels j ∈ (N.comap π.toMonoidHom : Subgroup (freeProP p d))
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp this]
        exact N.one_mem
      · obtain ⟨i, rfl⟩ := hx
        have hgi : g i ∈ N := by
          rw [hN]
          exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨i, rfl⟩)
        show ĝ i ∈ (N.comap π.toMonoidHom : Subgroup (freeProP p d))
        rw [Subgroup.mem_comap]
        show π (ĝ i) ∈ N
        rw [hĝ i]
        exact hgi
    · -- `π⁻¹ N ≤ M`
      have hMcpt : IsCompact (M : Set (freeProP p d)) := hMclosed.isCompact
      have himgclosed : IsClosed ((Subgroup.map π.toMonoidHom M : Subgroup G) : Set G) := by
        have : ((Subgroup.map π.toMonoidHom M : Subgroup G) : Set G) = π '' (M : Set _) := rfl
        rw [this]
        exact (hMcpt.image π.continuous_toFun).isClosed
      haveI : (Subgroup.map π.toMonoidHom M).Normal := hMnormal.map _ hsurj
      have hNle : N ≤ Subgroup.map π.toMonoidHom M := by
        rw [hN]
        refine Subgroup.topologicalClosure_minimal _ ?_ himgclosed
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨ĝ i, Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (hgsub ⟨i, rfl⟩)),
          hĝ i⟩
      intro x hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨y, hyM, hy⟩ := hNle hx
      have hxy : x * y⁻¹ ∈ MonoidHom.ker π.toMonoidHom := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
      have : x * y⁻¹ ∈ M := hkerM hxy
      simpa using M.mul_mem this hyM
  -- conclude
  have hmem : ((m + k : ℕ) : ℕ∞) ∈ {c : ℕ∞ | ∃ (d' : ℕ) (m' : ℕ) (π'' : freeProP p d' →ₜ* (G ⧸ N))
      (rels'' : Fin m' → freeProP p d'),
      (d' : ℕ∞) = dRank (G ⧸ N) ∧ IsProPPresentation p d' π'' rels'' ∧ (m' : ℕ∞) = c} :=
    ⟨d, m + k, π', rels', hdr.trans hdrank.symm, ⟨hsurj', hMker⟩, rfl⟩
  calc relRank p (G ⧸ N) ≤ ((m + k : ℕ) : ℕ∞) := sInf_le hmem
    _ = (m : ℕ∞) + (k : ℕ∞) := by push_cast; ring

end Workspace.ProofLemmas.ProPRelationRank
