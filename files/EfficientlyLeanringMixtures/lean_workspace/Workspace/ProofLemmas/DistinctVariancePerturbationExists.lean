import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.VariancePerturbFamily

/-!
# Sub-lemma C (Step 3, Distinct-variance perturbation exists)

For the variance-perturbation family `S_δ` (component `i` has variance
`σᵢ² + δ·(i+1)/k`, see `Workspace.ProofLemmas.variancePerturb`), there is a
threshold `δ₀ > 0` such that for every `δ ∈ (0, δ₀)` the perturbed variances are
pairwise distinct (`Nodup`) and all strictly positive.

The variances-positive part is automatic from `variancePerturb` (it requires
`0 ≤ δ`); the genuine content is the `Nodup`, an elementary finite-bad-set
argument over the at most `k(k-1)/2` collision parameters.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

/-- **Existence of a distinct-variance perturbation threshold.**

If `S` has `k = S.components.length ≥ 1` components, then there is `δ₀ > 0` such
that for every `δ` with `0 < δ < δ₀` the perturbed combination
`variancePerturb S δ _` has pairwise-distinct variances (the list of `varSq`
values is `Nodup`) and every component variance is strictly positive. -/
theorem DistinctVariancePerturbationExists
    (S : SignedGaussianCombination)
    (hk : 1 ≤ S.components.length) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ →
        ((variancePerturb S δ (le_of_lt hδ)).components.map
            (fun p => p.2.varSq)).Nodup ∧
        (∀ p ∈ (variancePerturb S δ (le_of_lt hδ)).components, 0 < p.2.varSq) := by
  set k := S.components.length with hkdef
  set σ : Fin k → ℝ := fun i => (S.components.get i).2.varSq with hσdef
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  classical
  -- The finite set of "collision" parameters: for each ordered pair of distinct
  -- indices `(i, j)`, the unique `δ` solving `σᵢ + δ(i+1)/k = σⱼ + δ(j+1)/k`.
  set D : Finset ℝ :=
    (Finset.univ.filter (fun pr : Fin k × Fin k => pr.1 ≠ pr.2)).image
      (fun pr => (σ pr.1 - σ pr.2) * k / ((pr.2:ℝ) - (pr.1:ℝ))) with hDdef
  set Dpos : Finset ℝ := D.filter (fun x => 0 < x) with hDposdef
  -- The threshold: below the smallest *positive* collision value (or `1` if none).
  set δ₀ : ℝ := if h : Dpos.Nonempty then Dpos.min' h else 1 with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]; split
    · next h => exact (Finset.mem_filter.mp (Dpos.min'_mem h)).2
    · exact one_pos
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro δ hδ hδ0
  -- No `δ ∈ (0, δ₀)` is a collision value.
  have hnotinD : δ ∉ D := by
    intro hin
    by_cases hp : 0 < δ
    · have hmem : δ ∈ Dpos := Finset.mem_filter.mpr ⟨hin, hp⟩
      have hne : Dpos.Nonempty := ⟨δ, hmem⟩
      have : δ₀ ≤ δ := by rw [hδ₀def]; simp only [hne, dif_pos]; exact Finset.min'_le _ _ hmem
      linarith
    · linarith
  -- Hence the perturbed-variance function is injective on the index list.
  have hinj : ∀ i ∈ List.finRange k, ∀ j ∈ List.finRange k,
      σ i + δ * (↑↑i + 1) / ↑k = σ j + δ * (↑↑j + 1) / ↑k → i = j := by
    intro i _ j _ hij
    by_contra hne
    apply hnotinD
    rw [hDdef, Finset.mem_image]
    refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
    have hijR : ((j:ℝ) - (i:ℝ)) ≠ 0 := by
      have : (i:ℝ) ≠ (j:ℝ) := by exact_mod_cast (Fin.val_ne_of_ne hne)
      intro h; apply this; linarith
    field_simp
    field_simp at hij
    ring_nf
    ring_nf at hij
    nlinarith [hij, hk0]
  refine ⟨?_, ?_⟩
  · -- Pairwise-distinct variances (Nodup of the varSq list).
    show (List.map (fun p => p.2.varSq) (variancePerturb S δ (le_of_lt hδ)).components).Nodup
    unfold variancePerturb
    simp only [List.map_map, List.get_eq_getElem]
    apply List.Nodup.map_on (l := List.finRange k)
    · intro i hi j hj hh
      apply hinj i hi j hj
      simpa [perturbVarSq, hσdef] using hh
    · exact List.nodup_finRange _
  · -- All perturbed variances are strictly positive.
    intro p hp
    unfold variancePerturb at hp
    simp only [List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact perturbVarSq_pos (S.components.get i).2.varSq_pos (le_of_lt hδ) i.val
      S.components.length hk

end Workspace.ProofLemmas
